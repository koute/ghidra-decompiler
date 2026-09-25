use std::collections::BTreeSet;
use std::fmt::Write;
use std::ops::Bound;

use crate::address::{
    Address, ELEM_ADDR, SeqKey, SeqNum, calc_mask, coveringmask, leastsigbit_set, mostsigbit_set, pcode_left,
    pcode_right, popcount, sign_extend_size,
};
use crate::architecture::Architecture;
use crate::arena::Arena;
use crate::block::{BlockId, FlowBlock};
use crate::define_id;
use crate::error::{Error, Result};
use crate::funcdata::Funcdata;
use crate::marshal::{ATTRIB_NAME, ATTRIB_REF, ATTRIB_SPACE, ATTRIB_VALUE, Decoder, ELEM_VOID, ElementId, Encoder};
use crate::opcodes::{OpCode, get_opname};
use crate::oplist::{LinkedNode, ListLinks, OpList};
use crate::orderedindex::OrderedIndex;
use crate::space::SpaceType;
use crate::translate::{ATTRIB_CODE, ELEM_OP, ELEM_SPACEID};
use crate::typeop::{TypeOp, with_type_op};
use crate::types::TypeId;
use crate::varnode::VarnodeId;

pub const ELEM_IOP: ElementId = ElementId::new("iop", 113);
pub const ELEM_UNIMPL: ElementId = ElementId::new("unimpl", 114);

define_id!(OpId);

pub const IOP_SPACE_NAME: &str = "iop";

pub fn iop_space_encode_attributes(encoder: &mut dyn Encoder, _offset: u64) -> Result<()> {
    encoder.write_string(ATTRIB_SPACE, "iop");
    Ok(())
}

pub fn iop_space_encode_attributes_size(encoder: &mut dyn Encoder, _offset: u64, _size: i32) -> Result<()> {
    encoder.write_string(ATTRIB_SPACE, "iop");
    Ok(())
}

pub fn iop_space_print_raw(data: &Funcdata, out: &mut String, offset: u64) {
    let op = OpId(offset as u32);
    let pcode_op = data.op(op);
    if !pcode_op.is_branch() {
        let _ = write!(out, "{}", pcode_op.get_seq_num());
        return;
    }
    let bs = data.block(pcode_op.get_parent().expect("branch op has no parent block"));
    let bl = if bs.size_out() == 2 {
        if pcode_op.is_fallthru_true() {
            bs.get_out(0)
        } else {
            bs.get_out(1)
        }
    } else {
        bs.get_out(0)
    };
    let start = data.block(bl).get_start();
    out.push_str("code_");
    out.push(start.get_shortcut());
    start.print_raw(out);
}

pub fn iop_space_decode(_decoder: &mut dyn Decoder) -> Result<()> {
    Err(Error::Lowlevel("Should never decode iop space from stream".to_string()))
}

fn list_target(ops: &Arena<OpId, PcodeOp>, op: OpId) -> OpId {
    let slot = if ops.get(op).is_dead() {
        PcodeOp::INSERT_LIST
    } else {
        PcodeOp::BASIC_LIST
    };
    let mut retop = op;
    while (ops.get(retop).flags & PcodeOp::STARTMARK) == 0 {
        retop = ops
            .get(retop)
            .links(slot)
            .prev
            .expect("no instruction start before p-code op");
    }
    retop
}

fn list_next_op(ops: &Arena<OpId, PcodeOp>, blocks: &Arena<BlockId, FlowBlock>, op: OpId) -> Option<OpId> {
    let mut parent = ops.get(op).get_parent().expect("p-code op has no parent block");
    let mut iter = ops.get(op).links(PcodeOp::BASIC_LIST).next;
    while iter.is_none() {
        let block = blocks.get(parent);
        if block.size_out() != 1 && block.size_out() != 2 {
            return None;
        }
        parent = block.get_out(0);
        iter = blocks.get(parent).basic().op.front();
    }
    iter
}

pub(crate) fn find_common_block(blocks: &Arena<BlockId, FlowBlock>, bl1: BlockId, bl2: BlockId) -> Option<BlockId> {
    let mut marked: BTreeSet<BlockId> = BTreeSet::new();
    let mut common = None;
    let mut b1 = Some(bl1);
    let mut b2 = Some(bl2);
    loop {
        let Some(second) = b2 else {
            while let Some(first) = b1 {
                if marked.contains(&first) {
                    common = Some(first);
                    break;
                }
                b1 = blocks.get(first).immed_dom;
            }
            break;
        };
        let Some(first) = b1 else {
            let mut walk = Some(second);
            while let Some(current) = walk {
                if marked.contains(&current) {
                    common = Some(current);
                    break;
                }
                walk = blocks.get(current).immed_dom;
            }
            break;
        };
        if marked.contains(&first) {
            common = Some(first);
            break;
        }
        marked.insert(first);
        if marked.contains(&second) {
            common = Some(second);
            break;
        }
        marked.insert(second);
        b1 = blocks.get(first).immed_dom;
        b2 = blocks.get(second).immed_dom;
    }
    common
}

#[derive(Clone, Debug)]
pub struct PcodeOp {
    pub(crate) opcode: OpCode,
    pub(crate) flags: u32,
    pub(crate) addlflags: u32,
    pub(crate) start: SeqNum,
    pub(crate) parent: Option<BlockId>,
    pub(crate) links: [ListLinks<OpId>; 3],
    pub(crate) output: Option<VarnodeId>,
    pub(crate) inrefs: Vec<Option<VarnodeId>>,
}

impl LinkedNode<OpId> for PcodeOp {
    fn links(&self, slot: usize) -> &ListLinks<OpId> {
        &self.links[slot]
    }

    fn links_mut(&mut self, slot: usize) -> &mut ListLinks<OpId> {
        &mut self.links[slot]
    }
}

impl PcodeOp {
    pub const BASIC_LIST: usize = 0;
    pub const INSERT_LIST: usize = 1;
    pub const CODE_LIST: usize = 2;

    pub const STARTBASIC: u32 = 1;
    pub const BRANCH: u32 = 2;
    pub const CALL: u32 = 4;
    pub const RETURNS: u32 = 0x8;
    pub const NOCOLLAPSE: u32 = 0x10;
    pub const DEAD: u32 = 0x20;
    pub const MARKER: u32 = 0x40;
    pub const BOOLOUTPUT: u32 = 0x80;
    pub const BOOLEAN_FLIP: u32 = 0x100;
    pub const FALLTHRU_TRUE: u32 = 0x200;
    pub const INDIRECT_SOURCE: u32 = 0x400;
    pub const CODEREF: u32 = 0x800;
    pub const STARTMARK: u32 = 0x1000;
    pub const MARK: u32 = 0x2000;
    pub const COMMUTATIVE: u32 = 0x4000;
    pub const UNARY: u32 = 0x8000;
    pub const BINARY: u32 = 0x10000;
    pub const SPECIAL: u32 = 0x20000;
    pub const TERNARY: u32 = 0x40000;
    pub const RETURN_COPY: u32 = 0x80000;
    pub const NONPRINTING: u32 = 0x100000;
    pub const HALT: u32 = 0x200000;
    pub const BADINSTRUCTION: u32 = 0x400000;
    pub const UNIMPLEMENTED: u32 = 0x800000;
    pub const NORETURN: u32 = 0x1000000;
    pub const MISSING: u32 = 0x2000000;
    pub const SPACEBASE_PTR: u32 = 0x4000000;
    pub const INDIRECT_CREATION: u32 = 0x8000000;
    pub const CALCULATED_BOOL: u32 = 0x10000000;
    pub const HAS_CALLSPEC: u32 = 0x20000000;
    pub const PTRFLOW: u32 = 0x40000000;
    pub const INDIRECT_STORE: u32 = 0x80000000;

    pub const SPECIAL_PROP: u32 = 1;
    pub const SPECIAL_PRINT: u32 = 2;
    pub const MODIFIED: u32 = 4;
    pub const WARNING: u32 = 8;
    pub const INCIDENTAL_COPY: u32 = 0x10;
    pub const IS_CPOOL_TRANSFORMED: u32 = 0x20;
    pub const STOP_TYPE_PROPAGATION: u32 = 0x40;
    pub const HOLD_OUTPUT: u32 = 0x80;
    pub const CONCAT_ROOT: u32 = 0x100;
    pub const NO_INDIRECT_COLLAPSE: u32 = 0x200;
    pub const STORE_UNMAPPED: u32 = 0x400;
    pub const IMMED_COPY: u32 = 0x800;
    pub const STORE_ALIASUPDATE: u32 = 0x1000;

    pub fn new(size: i32, sq: &SeqNum) -> PcodeOp {
        PcodeOp {
            opcode: OpCode::Blank,
            flags: 0,
            addlflags: 0,
            start: sq.clone(),
            parent: None,
            links: [ListLinks::default(); 3],
            output: None,
            inrefs: vec![None; size as usize],
        }
    }

    pub fn set_opcode(&mut self, t_op: &dyn TypeOp) {
        self.flags &= !(PcodeOp::BRANCH
            | PcodeOp::CALL
            | PcodeOp::CODEREF
            | PcodeOp::COMMUTATIVE
            | PcodeOp::RETURNS
            | PcodeOp::NOCOLLAPSE
            | PcodeOp::MARKER
            | PcodeOp::BOOLOUTPUT
            | PcodeOp::UNARY
            | PcodeOp::BINARY
            | PcodeOp::TERNARY
            | PcodeOp::SPECIAL
            | PcodeOp::HAS_CALLSPEC
            | PcodeOp::RETURN_COPY);
        self.opcode = t_op.get_opcode();
        self.flags |= t_op.get_flags();
    }

    pub fn set_output(&mut self, vn: Option<VarnodeId>) {
        self.output = vn;
    }

    pub fn clear_input(&mut self, slot: i32) {
        self.inrefs[slot as usize] = None;
    }

    pub fn set_input(&mut self, vn: Option<VarnodeId>, slot: i32) {
        self.inrefs[slot as usize] = vn;
    }

    pub fn set_flag(&mut self, fl: u32) {
        self.flags |= fl;
    }

    pub fn clear_flag(&mut self, fl: u32) {
        self.flags &= !fl;
    }

    pub fn set_additional_flag(&mut self, fl: u32) {
        self.addlflags |= fl;
    }

    pub fn clear_additional_flag(&mut self, fl: u32) {
        self.addlflags &= !fl;
    }

    pub fn flip_flag(&mut self, fl: u32) {
        self.flags ^= fl;
    }

    pub fn set_num_inputs(&mut self, num: i32) {
        self.inrefs.clear();
        self.inrefs.resize(num as usize, None);
    }

    pub fn remove_input(&mut self, slot: i32) {
        self.inrefs.remove(slot as usize);
    }

    pub fn insert_input(&mut self, slot: i32) {
        self.inrefs.insert(slot as usize, None);
    }

    pub fn set_order(&mut self, ord: u32) {
        self.start.set_order(ord);
    }

    pub fn set_parent(&mut self, parent_block: Option<BlockId>) {
        self.parent = parent_block;
    }

    pub fn num_input(&self) -> i32 {
        self.inrefs.len() as i32
    }

    pub fn get_out(&self) -> Option<VarnodeId> {
        self.output
    }

    pub fn get_in(&self, slot: i32) -> VarnodeId {
        self.inrefs[slot as usize].expect("missing p-code op input")
    }

    pub fn get_in_option(&self, slot: i32) -> Option<VarnodeId> {
        usize::try_from(slot)
            .ok()
            .and_then(|index| self.inrefs.get(index).copied().flatten())
    }

    pub fn get_parent(&self) -> Option<BlockId> {
        self.parent
    }

    pub fn get_addr(&self) -> &Address {
        self.start.get_addr()
    }

    pub fn get_time(&self) -> u32 {
        self.start.get_time()
    }

    pub fn get_seq_num(&self) -> &SeqNum {
        &self.start
    }

    pub fn get_slot(&self, vn: VarnodeId) -> i32 {
        let count = self.inrefs.len();
        let mut index = 0;
        while index < count {
            if self.inrefs[index] == Some(vn) {
                break;
            }
            index += 1;
        }
        index as i32
    }

    pub fn get_repeat_slot(&self, this_op: OpId, vn: VarnodeId, first_slot: i32, descend: &[OpId], iter: usize) -> i32 {
        let mut count = 1;
        for reader in descend[..iter].iter() {
            if *reader == this_op {
                count += 1;
            }
        }
        if count == 1 {
            return first_slot;
        }
        let mut recount = 1;
        for index in (first_slot + 1) as usize..self.inrefs.len() {
            if self.inrefs[index] == Some(vn) {
                recount += 1;
                if recount == count {
                    return index as i32;
                }
            }
        }
        -1
    }

    pub fn get_eval_type(&self) -> u32 {
        self.flags & (PcodeOp::UNARY | PcodeOp::BINARY | PcodeOp::SPECIAL | PcodeOp::TERNARY)
    }

    pub fn get_halt_type(&self) -> u32 {
        self.flags
            & (PcodeOp::HALT | PcodeOp::BADINSTRUCTION | PcodeOp::UNIMPLEMENTED | PcodeOp::NORETURN | PcodeOp::MISSING)
    }

    pub fn is_dead(&self) -> bool {
        (self.flags & PcodeOp::DEAD) != 0
    }

    pub fn is_assignment(&self) -> bool {
        self.output.is_some()
    }

    pub fn is_call(&self) -> bool {
        (self.flags & PcodeOp::CALL) != 0
    }

    pub fn is_call_without_spec(&self) -> bool {
        (self.flags & (PcodeOp::CALL | PcodeOp::HAS_CALLSPEC)) == PcodeOp::CALL
    }

    pub fn is_marker(&self) -> bool {
        (self.flags & PcodeOp::MARKER) != 0
    }

    pub fn is_indirect_creation(&self) -> bool {
        (self.flags & PcodeOp::INDIRECT_CREATION) != 0
    }

    pub fn is_indirect_store(&self) -> bool {
        (self.flags & PcodeOp::INDIRECT_STORE) != 0
    }

    pub fn not_printed(&self) -> bool {
        (self.flags & (PcodeOp::MARKER | PcodeOp::NONPRINTING | PcodeOp::NORETURN)) != 0
    }

    pub fn is_bool_output(&self) -> bool {
        (self.flags & PcodeOp::BOOLOUTPUT) != 0
    }

    pub fn is_branch(&self) -> bool {
        (self.flags & PcodeOp::BRANCH) != 0
    }

    pub fn is_call_or_branch(&self) -> bool {
        (self.flags & (PcodeOp::BRANCH | PcodeOp::CALL)) != 0
    }

    pub fn is_flow_break(&self) -> bool {
        (self.flags & (PcodeOp::BRANCH | PcodeOp::RETURNS)) != 0
    }

    pub fn is_boolean_flip(&self) -> bool {
        (self.flags & PcodeOp::BOOLEAN_FLIP) != 0
    }

    pub fn is_fallthru_true(&self) -> bool {
        (self.flags & PcodeOp::FALLTHRU_TRUE) != 0
    }

    pub fn is_code_ref(&self) -> bool {
        (self.flags & PcodeOp::CODEREF) != 0
    }

    pub fn is_instruction_start(&self) -> bool {
        (self.flags & PcodeOp::STARTMARK) != 0
    }

    pub fn is_block_start(&self) -> bool {
        (self.flags & PcodeOp::STARTBASIC) != 0
    }

    pub fn is_modified(&self) -> bool {
        (self.addlflags & PcodeOp::MODIFIED) != 0
    }

    pub fn is_mark(&self) -> bool {
        (self.flags & PcodeOp::MARK) != 0
    }

    pub fn set_mark(&mut self) {
        self.flags |= PcodeOp::MARK;
    }

    pub fn is_warning(&self) -> bool {
        (self.addlflags & PcodeOp::WARNING) != 0
    }

    pub fn clear_mark(&mut self) {
        self.flags &= !PcodeOp::MARK;
    }

    pub fn is_indirect_source(&self) -> bool {
        (self.flags & PcodeOp::INDIRECT_SOURCE) != 0
    }

    pub fn set_indirect_source(&mut self) {
        self.flags |= PcodeOp::INDIRECT_SOURCE;
    }

    pub fn clear_indirect_source(&mut self) {
        self.flags &= !PcodeOp::INDIRECT_SOURCE;
    }

    pub fn is_ptr_flow(&self) -> bool {
        (self.flags & PcodeOp::PTRFLOW) != 0
    }

    pub fn set_ptr_flow(&mut self) {
        self.flags |= PcodeOp::PTRFLOW;
    }

    pub fn does_special_propagation(&self) -> bool {
        (self.addlflags & PcodeOp::SPECIAL_PROP) != 0
    }

    pub fn does_special_printing(&self) -> bool {
        (self.addlflags & PcodeOp::SPECIAL_PRINT) != 0
    }

    pub fn is_incidental_copy(&self) -> bool {
        (self.addlflags & PcodeOp::INCIDENTAL_COPY) != 0
    }

    pub fn is_calculated_bool(&self) -> bool {
        (self.flags & (PcodeOp::CALCULATED_BOOL | PcodeOp::BOOLOUTPUT)) != 0
    }

    pub fn is_cpool_transformed(&self) -> bool {
        (self.addlflags & PcodeOp::IS_CPOOL_TRANSFORMED) != 0
    }

    pub fn stops_type_propagation(&self) -> bool {
        (self.addlflags & PcodeOp::STOP_TYPE_PROPAGATION) != 0
    }

    pub fn set_stop_type_propagation(&mut self) {
        self.addlflags |= PcodeOp::STOP_TYPE_PROPAGATION;
    }

    pub fn clear_stop_type_propagation(&mut self) {
        self.addlflags &= !PcodeOp::STOP_TYPE_PROPAGATION;
    }

    pub fn hold_output(&self) -> bool {
        (self.addlflags & PcodeOp::HOLD_OUTPUT) != 0
    }

    pub fn set_hold_output(&mut self) {
        self.addlflags |= PcodeOp::HOLD_OUTPUT;
    }

    pub fn is_partial_root(&self) -> bool {
        (self.addlflags & PcodeOp::CONCAT_ROOT) != 0
    }

    pub fn set_partial_root(&mut self) {
        self.addlflags |= PcodeOp::CONCAT_ROOT;
    }

    pub fn is_return_copy(&self) -> bool {
        (self.flags & PcodeOp::RETURN_COPY) != 0
    }

    pub fn no_indirect_collapse(&self) -> bool {
        (self.addlflags & PcodeOp::NO_INDIRECT_COLLAPSE) != 0
    }

    pub fn set_no_indirect_collapse(&mut self) {
        self.addlflags |= PcodeOp::NO_INDIRECT_COLLAPSE;
    }

    pub fn is_store_unmapped(&self) -> bool {
        (self.addlflags & PcodeOp::STORE_UNMAPPED) != 0
    }

    pub fn set_store_unmapped(&mut self) {
        self.addlflags |= PcodeOp::STORE_UNMAPPED;
    }

    pub fn has_alias_update(&self) -> bool {
        (self.addlflags & PcodeOp::STORE_ALIASUPDATE) != 0
    }

    pub fn set_alias_update(&mut self) {
        self.addlflags |= PcodeOp::STORE_ALIASUPDATE;
    }

    pub fn uses_spacebase_ptr(&self) -> bool {
        (self.flags & PcodeOp::SPACEBASE_PTR) != 0
    }

    pub fn get_opcode<'glb>(&self, glb: &'glb Architecture) -> &'glb dyn TypeOp {
        glb.inst[self.opcode.index()]
            .as_deref()
            .expect("missing TypeOp for p-code opcode")
    }

    pub fn code(&self) -> OpCode {
        self.opcode
    }

    pub fn is_commutative(&self) -> bool {
        (self.flags & PcodeOp::COMMUTATIVE) != 0
    }

    pub fn get_op_from_const(addr: &Address) -> OpId {
        OpId(addr.get_offset() as u32)
    }
}

impl Funcdata {
    pub fn op_set_copy_immed(&mut self, op: OpId, slot: i32) {
        let parent = self.op(op).get_parent().expect("p-code op has no parent block");
        let inbl = self.block(parent).get_in(slot);
        let outedge = self.block(parent).get_in_rev_index(slot);
        self.block_set_immed_copy_edge(inbl, outedge);
        self.op_mut(op).addlflags |= PcodeOp::IMMED_COPY;
    }

    pub fn op_has_copy_immed(&self, op: OpId, slot: i32) -> bool {
        let pcode_op = self.op(op);
        if (pcode_op.addlflags & PcodeOp::IMMED_COPY) != 0 {
            let parent = pcode_op.get_parent().expect("p-code op has no parent block");
            let inbl = self.block(parent).get_in(slot);
            let outedge = self.block(parent).get_in_rev_index(slot);
            return self.block(inbl).has_immed_copy_edge(outedge);
        }
        false
    }

    pub fn op_is_collapsible(&self, op: OpId) -> bool {
        let pcode_op = self.op(op);
        if (pcode_op.flags & PcodeOp::NOCOLLAPSE) != 0 {
            return false;
        }
        if !pcode_op.is_assignment() {
            return false;
        }
        if pcode_op.inrefs.is_empty() {
            return false;
        }
        for slot in 0..pcode_op.num_input() {
            if !self.vn(pcode_op.get_in(slot)).is_constant() {
                return false;
            }
        }
        if self
            .vn(pcode_op.get_out().expect("assignment has no output"))
            .get_size()
            > 8
        {
            return false;
        }
        true
    }

    pub fn op_get_cse_hash(&self, op: OpId) -> u32 {
        let pcode_op = self.op(op);
        if (pcode_op.get_eval_type() & (PcodeOp::UNARY | PcodeOp::BINARY)) == 0 {
            return 0;
        }
        if pcode_op.code() == OpCode::Copy {
            return 0;
        }
        let output = pcode_op.get_out().expect("cse op has no output");
        let mut hash = ((self.vn(output).get_size() as u32) << 8) | (pcode_op.code() as u32);
        for slot in 0..pcode_op.num_input() {
            let vn = self.vn(pcode_op.get_in(slot));
            hash = hash.rotate_left(8);
            if vn.is_constant() {
                hash ^= vn.get_offset() as u32;
            } else {
                hash ^= vn.get_create_index();
            }
        }
        hash
    }

    pub fn op_is_cse_match(&self, op: OpId, other: OpId) -> bool {
        let first = self.op(op);
        let second = self.op(other);
        if (first.get_eval_type() & (PcodeOp::UNARY | PcodeOp::BINARY)) == 0 {
            return false;
        }
        if (second.get_eval_type() & (PcodeOp::UNARY | PcodeOp::BINARY)) == 0 {
            return false;
        }
        let first_out = first.get_out().expect("cse op has no output");
        let second_out = second.get_out().expect("cse op has no output");
        if self.vn(first_out).get_size() != self.vn(second_out).get_size() {
            return false;
        }
        if first.code() != second.code() {
            return false;
        }
        if first.code() == OpCode::Copy {
            return false;
        }
        if first.inrefs.len() != second.inrefs.len() {
            return false;
        }
        for slot in 0..first.num_input() {
            let vn1 = first.get_in(slot);
            let vn2 = second.get_in(slot);
            if vn1 == vn2 {
                continue;
            }
            let varnode1 = self.vn(vn1);
            let varnode2 = self.vn(vn2);
            if varnode1.is_constant() && varnode2.is_constant() && varnode1.get_offset() == varnode2.get_offset() {
                continue;
            }
            return false;
        }
        true
    }

    pub fn op_is_moveable(&self, op: OpId, point: OpId) -> bool {
        if op == point {
            return true;
        }
        let pcode_op = self.op(op);
        let point_op = self.op(point);
        let mut moving_load = false;
        if pcode_op.get_eval_type() == PcodeOp::SPECIAL {
            if pcode_op.code() == OpCode::Load {
                moving_load = true;
            } else {
                return false;
            }
        }
        if pcode_op.parent != point_op.parent {
            return false;
        }
        if let Some(output) = pcode_op.output {
            for read_op in self.vn(output).descend().iter() {
                let reader = self.op(*read_op);
                if reader.parent != pcode_op.parent {
                    continue;
                }
                if reader.start.get_order() <= point_op.start.get_order() {
                    return false;
                }
            }
        }
        let mut cross_calls = false;
        if pcode_op.get_eval_type() != PcodeOp::SPECIAL
            && let Some(output) = pcode_op.output
        {
            let out_vn = self.vn(output);
            if !out_vn.is_addr_tied() && !out_vn.is_persist() {
                let mut slot = 0;
                while slot < pcode_op.num_input() {
                    let vn = self.vn(pcode_op.get_in(slot));
                    if vn.is_addr_tied() || vn.is_persist() {
                        break;
                    }
                    slot += 1;
                }
                if slot == pcode_op.num_input() {
                    cross_calls = true;
                }
            }
        }
        let mut tied_list: Vec<VarnodeId> = Vec::new();
        for slot in 0..pcode_op.num_input() {
            let vn = pcode_op.get_in(slot);
            if self.vn(vn).is_addr_tied() {
                tied_list.push(vn);
            }
        }
        let output_tied = pcode_op.output.map(|output| self.vn(output).is_addr_tied());
        let mut biter = op;
        loop {
            biter = self
                .op(biter)
                .links(PcodeOp::BASIC_LIST)
                .next
                .expect("moveable test ran past the end of the block");
            let cur_op = self.op(biter);
            if cur_op.get_eval_type() == PcodeOp::SPECIAL {
                match cur_op.code() {
                    OpCode::Load => {
                        if output_tied == Some(true) {
                            return false;
                        }
                    }
                    OpCode::Store => {
                        if moving_load {
                            return false;
                        } else {
                            if !tied_list.is_empty() {
                                return false;
                            }
                            if output_tied == Some(true) {
                                return false;
                            }
                        }
                    }
                    OpCode::Indirect | OpCode::Segmentop | OpCode::Cpoolref => {}
                    OpCode::Call | OpCode::Callind | OpCode::New => {
                        if !cross_calls {
                            return false;
                        }
                    }
                    _ => return false,
                }
            }
            if let Some(cur_out) = cur_op.output {
                let cur_out_vn = self.vn(cur_out);
                if moving_load && cur_out_vn.is_addr_tied() {
                    return false;
                }
                for tied in tied_list.iter() {
                    let vn = self.vn(*tied);
                    if vn.overlap(cur_out_vn) >= 0 {
                        return false;
                    }
                    if cur_out_vn.overlap(vn) >= 0 {
                        return false;
                    }
                }
            }
            if biter == point {
                break;
            }
        }
        true
    }

    pub fn op_collapse(&self, op: OpId, marked_input: &mut bool, glb: &Architecture) -> Result<u64> {
        let pcode_op = self.op(op);
        let vn0 = self.vn(pcode_op.get_in(0));
        if vn0.get_symbol_entry().is_some() {
            *marked_input = true;
        }
        let top = pcode_op.get_opcode(glb);
        match pcode_op.get_eval_type() {
            PcodeOp::UNARY => {
                let out_size = self
                    .vn(pcode_op.get_out().expect("collapse op has no output"))
                    .get_size();
                return top.evaluate_unary(out_size, vn0.get_size(), vn0.get_offset());
            }
            PcodeOp::BINARY => {
                let vn1 = self.vn(pcode_op.get_in(1));
                if vn1.get_symbol_entry().is_some() {
                    *marked_input = true;
                }
                let out_size = self
                    .vn(pcode_op.get_out().expect("collapse op has no output"))
                    .get_size();
                return top.evaluate_binary(out_size, vn0.get_size(), vn0.get_offset(), vn1.get_offset());
            }
            _ => {}
        }
        Err(Error::Lowlevel("Invalid constant collapse".to_string()))
    }

    pub fn op_execute_simple(&self, op: OpId, input: &[u64], eval_error: &mut bool, glb: &Architecture) -> Result<u64> {
        let pcode_op = self.op(op);
        let eval_type = pcode_op.get_eval_type();
        let top = pcode_op.get_opcode(glb);
        let out_size = pcode_op.output.map(|output| self.vn(output).get_size()).unwrap_or(0);
        let in_size = pcode_op.inrefs[0].map(|vn| self.vn(vn).get_size()).unwrap_or(0);
        let res = if eval_type == PcodeOp::UNARY {
            top.evaluate_unary(out_size, in_size, input[0])
        } else if eval_type == PcodeOp::BINARY {
            top.evaluate_binary(out_size, in_size, input[0], input[1])
        } else if eval_type == PcodeOp::TERNARY {
            top.evaluate_ternary(out_size, in_size, input[0], input[1], input[2])
        } else {
            return Err(Error::Lowlevel(format!(
                "Cannot perform simple execution of {}",
                get_opname(pcode_op.code())
            )));
        };
        match res {
            Ok(value) => {
                *eval_error = false;
                Ok(value)
            }
            Err(Error::Evaluation(_)) => {
                *eval_error = true;
                Ok(0)
            }
            Err(err) => Err(err),
        }
    }

    pub fn op_collapse_constant_symbol(&mut self, op: OpId, new_const: VarnodeId, glb: &Architecture) -> Result<()> {
        let pcode_op = self.op(op);
        let copy_vn = match pcode_op.code() {
            OpCode::Subpiece => {
                if self.vn(pcode_op.get_in(1)).get_offset() != 0 {
                    return Ok(());
                }
                pcode_op.get_in(0)
            }
            OpCode::Copy | OpCode::IntZext | OpCode::IntNegate | OpCode::Int2comp => pcode_op.get_in(0),
            OpCode::IntLeft | OpCode::IntRight | OpCode::IntSright => pcode_op.get_in(0),
            OpCode::IntAdd | OpCode::IntMult | OpCode::IntAnd | OpCode::IntOr | OpCode::IntXor => {
                let first = pcode_op.get_in(0);
                if self.vn(first).get_symbol_entry().is_none() {
                    pcode_op.get_in(1)
                } else {
                    first
                }
            }
            _ => return Ok(()),
        };
        if self.vn(copy_vn).get_symbol_entry().is_none() {
            return Ok(());
        }
        self.vn_copy_symbol_if_valid(new_const, copy_vn, glb)
    }

    pub fn op_next_op(&self, op: OpId) -> Option<OpId> {
        list_next_op(&self.obank.ops, &self.blocks, op)
    }

    pub fn op_previous_op(&self, op: OpId) -> Option<OpId> {
        self.op(op).links(PcodeOp::BASIC_LIST).prev
    }

    pub fn op_target(&self, op: OpId) -> OpId {
        list_target(&self.obank.ops, op)
    }

    pub fn op_get_nz_mask_local(&self, op: OpId, cliploop: bool) -> u64 {
        let pcode_op = self.op(op);
        let size = self.vn(pcode_op.get_out().expect("op has no output")).get_size();
        let fullmask = calc_mask(size);
        let input_vn = |slot: i32| self.vn(pcode_op.get_in(slot));
        let resmask: u64;
        match pcode_op.code() {
            OpCode::IntEqual
            | OpCode::IntNotequal
            | OpCode::IntSless
            | OpCode::IntSlessequal
            | OpCode::IntLess
            | OpCode::IntLessequal
            | OpCode::IntCarry
            | OpCode::IntScarry
            | OpCode::IntSborrow
            | OpCode::BoolNegate
            | OpCode::BoolXor
            | OpCode::BoolAnd
            | OpCode::BoolOr
            | OpCode::FloatEqual
            | OpCode::FloatNotequal
            | OpCode::FloatLess
            | OpCode::FloatLessequal
            | OpCode::FloatNan => {
                resmask = 1;
            }
            OpCode::Copy | OpCode::IntZext => {
                resmask = input_vn(0).get_nz_mask();
            }
            OpCode::IntSext => {
                resmask = sign_extend_size(input_vn(0).get_nz_mask(), input_vn(0).get_size(), size);
            }
            OpCode::IntXor | OpCode::IntOr => {
                let mut mask = input_vn(0).get_nz_mask();
                if mask != fullmask {
                    mask |= input_vn(1).get_nz_mask();
                }
                resmask = mask;
            }
            OpCode::IntAnd => {
                let mut mask = input_vn(0).get_nz_mask();
                if mask != 0 {
                    mask &= input_vn(1).get_nz_mask();
                }
                resmask = mask;
            }
            OpCode::IntLeft => {
                if !input_vn(1).is_constant() {
                    resmask = fullmask;
                } else {
                    let sa = input_vn(1).get_offset() as i32;
                    resmask = pcode_left(input_vn(0).get_nz_mask(), sa) & fullmask;
                }
            }
            OpCode::IntRight => {
                if !input_vn(1).is_constant() {
                    resmask = fullmask;
                } else {
                    let sz1 = input_vn(0).get_size();
                    let sa = input_vn(1).get_offset() as i32;
                    let mut mask = pcode_right(input_vn(0).get_nz_mask(), sa);
                    if sz1 > 8 {
                        if sa >= 8 * sz1 {
                            mask = 0;
                        } else if sa >= 64 {
                            mask = calc_mask(sz1 - 8);
                            mask = mask.wrapping_shr((sa - 64) as u32);
                        } else {
                            let mut tmp: u64 = 0;
                            tmp = tmp.wrapping_sub(1);
                            tmp = tmp.wrapping_shl((64 - sa) as u32);
                            mask |= tmp;
                        }
                    }
                    resmask = mask;
                }
            }
            OpCode::IntSright => {
                if !input_vn(1).is_constant() || size > 8 {
                    resmask = fullmask;
                } else {
                    let sa = input_vn(1).get_offset() as i32;
                    let mut mask = input_vn(0).get_nz_mask();
                    if (mask & (fullmask ^ (fullmask >> 1))) == 0 {
                        mask = pcode_right(mask, sa);
                    } else {
                        mask = pcode_right(mask, sa);
                        mask |= fullmask.wrapping_shr(sa as u32) ^ fullmask;
                    }
                    resmask = mask;
                }
            }
            OpCode::IntDiv => {
                let val = input_vn(0).get_nz_mask();
                let mut mask = coveringmask(val);
                if input_vn(1).is_constant() {
                    let sa = mostsigbit_set(input_vn(1).get_nz_mask());
                    if sa != -1 {
                        mask >>= sa;
                    }
                }
                resmask = mask;
            }
            OpCode::IntRem => {
                let val = input_vn(1).get_nz_mask().wrapping_sub(1);
                resmask = coveringmask(val);
            }
            OpCode::Popcount => {
                let sz1 = popcount(input_vn(0).get_nz_mask());
                resmask = coveringmask(sz1 as u64) & fullmask;
            }
            OpCode::Lzcount => {
                resmask = coveringmask((input_vn(0).get_size() * 8) as u64) & fullmask;
            }
            OpCode::Subpiece => {
                let mut mask = input_vn(0).get_nz_mask();
                let sz1 = input_vn(1).get_offset() as i32;
                if input_vn(0).get_size() <= 8 {
                    if (sz1 as u32) < 8 {
                        mask >>= 8 * sz1;
                    } else {
                        mask = 0;
                    }
                } else if (sz1 as u32) < 8 {
                    mask >>= 8 * sz1;
                    if sz1 > 0 {
                        mask |= fullmask << (8 * (8 - sz1));
                    }
                } else {
                    mask = fullmask;
                }
                resmask = mask & fullmask;
            }
            OpCode::Piece => {
                let sa = input_vn(1).get_size();
                let mut mask = input_vn(0).get_nz_mask();
                mask = if (sa as u32) < 8 { mask << (8 * sa) } else { 0 };
                mask |= input_vn(1).get_nz_mask();
                resmask = mask;
            }
            OpCode::IntMult => {
                let val = input_vn(0).get_nz_mask();
                let mut mask = input_vn(1).get_nz_mask();
                if size > 8 {
                    mask = fullmask;
                } else {
                    let mut sz1 = mostsigbit_set(val);
                    let mut sz2 = mostsigbit_set(mask);
                    if sz1 == -1 || sz2 == -1 {
                        mask = 0;
                    } else {
                        let l1 = leastsigbit_set(val);
                        let l2 = leastsigbit_set(mask);
                        let sa = l1 + l2;
                        if sa >= 8 * size {
                            mask = 0;
                        } else {
                            sz1 = sz1 - l1 + 1;
                            sz2 = sz2 - l2 + 1;
                            let mut total = sz1 + sz2;
                            if sz1 == 1 || sz2 == 1 {
                                total -= 1;
                            }
                            mask = fullmask;
                            if total < 8 * size {
                                mask >>= 8 * size - total;
                            }
                            mask = (mask << sa) & fullmask;
                        }
                    }
                }
                resmask = mask;
            }
            OpCode::IntAdd => {
                let mut mask = input_vn(0).get_nz_mask();
                if mask != fullmask {
                    let othermask = input_vn(1).get_nz_mask();
                    if (othermask & mask) == 0 {
                        mask |= othermask;
                    } else {
                        mask |= othermask;
                        mask |= mask << 1;
                    }
                    mask &= fullmask;
                }
                resmask = mask;
            }
            OpCode::Multiequal => {
                if pcode_op.inrefs.is_empty() {
                    resmask = fullmask;
                } else {
                    let mut mask = 0;
                    if cliploop {
                        let parent = self.block(pcode_op.get_parent().expect("MULTIEQUAL has no parent block"));
                        for slot in 0..pcode_op.num_input() {
                            if parent.is_loop_in(slot) {
                                continue;
                            }
                            mask |= input_vn(slot).get_nz_mask();
                        }
                    } else {
                        for slot in 0..pcode_op.num_input() {
                            mask |= input_vn(slot).get_nz_mask();
                        }
                    }
                    resmask = mask;
                }
            }
            OpCode::Call | OpCode::Callind | OpCode::Cpoolref if pcode_op.is_calculated_bool() => {
                resmask = 1;
            }
            _ => {
                resmask = fullmask;
            }
        }
        resmask
    }

    pub fn op_compare_order(&self, op: OpId, bop: OpId) -> i32 {
        let parent = self.op(op).parent.expect("p-code op has no parent block");
        let other_parent = self.op(bop).parent.expect("p-code op has no parent block");
        if parent == other_parent {
            return if self.op(op).start.get_order() < self.op(bop).start.get_order() {
                -1
            } else {
                1
            };
        }
        let common = find_common_block(&self.blocks, parent, other_parent);
        if common == Some(parent) {
            return -1;
        }
        if common == Some(other_parent) {
            return 1;
        }
        0
    }

    pub fn op_verify_mult_neg_one(&self, op: OpId) -> bool {
        let pcode_op = self.op(op);
        if pcode_op.code() != OpCode::IntMult {
            return false;
        }
        let in1 = self.vn(pcode_op.get_in(1));
        if !in1.is_constant() {
            return false;
        }
        if in1.get_offset() != calc_mask(in1.get_size()) {
            return false;
        }
        true
    }

    pub fn op_print_raw(&self, op: OpId, out: &mut String, glb: &mut Architecture) {
        let opc = self.op(op).code();
        with_type_op(glb, opc, |top, glb| top.print_raw(out, op, self, glb));
    }

    pub fn op_get_op_name<'glb>(&self, op: OpId, glb: &'glb Architecture) -> &'glb str {
        self.op(op).get_opcode(glb).get_name()
    }

    pub fn op_print_debug(&self, op: OpId, out: &mut String, glb: &mut Architecture) {
        let _ = write!(out, "{}: ", self.op(op).get_seq_num());
        if self.op(op).is_dead() || self.op(op).get_parent().is_none() {
            out.push_str("**");
        } else {
            self.op_print_raw(op, out, glb);
        }
    }

    pub fn op_encode(&self, op: OpId, encoder: &mut dyn Encoder, glb: &Architecture) -> Result<()> {
        let pcode_op = self.op(op);
        encoder.open_element(ELEM_OP);
        encoder.write_signed_integer(ATTRIB_CODE, pcode_op.code() as i64);
        pcode_op.start.encode(encoder)?;
        match pcode_op.output {
            None => {
                encoder.open_element(ELEM_VOID);
                encoder.close_element(ELEM_VOID);
            }
            Some(output) => {
                encoder.open_element(ELEM_ADDR);
                encoder.write_unsigned_integer(ATTRIB_REF, self.vn(output).get_create_index() as u64);
                encoder.close_element(ELEM_ADDR);
            }
        }
        for slot in 0..pcode_op.inrefs.len() {
            let Some(vn) = pcode_op.inrefs[slot] else {
                encoder.open_element(ELEM_VOID);
                encoder.close_element(ELEM_VOID);
                continue;
            };
            let varnode = self.vn(vn);
            let space_type = varnode.get_space().map(|spc| spc.get_type());
            if space_type == Some(SpaceType::Iop) {
                if slot == 1 && pcode_op.code() == OpCode::Indirect {
                    let indop = PcodeOp::get_op_from_const(varnode.get_addr());
                    encoder.open_element(ELEM_IOP);
                    encoder.write_unsigned_integer(ATTRIB_VALUE, self.op(indop).get_seq_num().get_time() as u64);
                    encoder.close_element(ELEM_IOP);
                } else {
                    encoder.open_element(ELEM_VOID);
                    encoder.close_element(ELEM_VOID);
                }
            } else if space_type == Some(SpaceType::Constant) {
                if slot == 0 && (pcode_op.code() == OpCode::Store || pcode_op.code() == OpCode::Load) {
                    let spc = varnode
                        .get_space_from_const(&glb.manager)
                        .ok_or_else(|| Error::Lowlevel("invalid space constant in LOAD/STORE".to_string()))?;
                    encoder.open_element(ELEM_SPACEID);
                    encoder.write_space(ATTRIB_NAME, &spc);
                    encoder.close_element(ELEM_SPACEID);
                } else {
                    encoder.open_element(ELEM_ADDR);
                    encoder.write_unsigned_integer(ATTRIB_REF, varnode.get_create_index() as u64);
                    encoder.close_element(ELEM_ADDR);
                }
            } else {
                encoder.open_element(ELEM_ADDR);
                encoder.write_unsigned_integer(ATTRIB_REF, varnode.get_create_index() as u64);
                encoder.close_element(ELEM_ADDR);
            }
        }
        encoder.close_element(ELEM_OP);
        Ok(())
    }

    pub fn op_output_type_local(&mut self, op: OpId, glb: &mut Architecture) -> TypeId {
        let opc = self.op(op).code();
        with_type_op(glb, opc, |top, glb| top.get_output_local(op, self, glb))
            .expect("output data-type construction failed")
    }

    pub fn op_input_type_local(&mut self, op: OpId, slot: i32, glb: &mut Architecture) -> TypeId {
        let opc = self.op(op).code();
        with_type_op(glb, opc, |top, glb| top.get_input_local(op, slot, self, glb))
            .expect("input data-type construction failed")
    }
}

#[derive(Clone, Debug)]
pub struct PieceNode {
    pub(crate) piece_op: OpId,
    pub(crate) slot: i32,
    pub(crate) type_offset: i32,
    pub(crate) leaf: bool,
}

impl PieceNode {
    pub fn new(op: OpId, sl: i32, off: i32, leaf: bool) -> PieceNode {
        PieceNode {
            piece_op: op,
            slot: sl,
            type_offset: off,
            leaf,
        }
    }

    pub fn is_leaf(&self) -> bool {
        self.leaf
    }

    pub fn get_type_offset(&self) -> i32 {
        self.type_offset
    }

    pub fn get_slot(&self) -> i32 {
        self.slot
    }

    pub fn get_op(&self) -> OpId {
        self.piece_op
    }

    pub fn get_varnode(&self, data: &Funcdata) -> VarnodeId {
        data.op(self.piece_op).get_in(self.slot)
    }

    pub fn is_leaf_test(data: &Funcdata, root_vn: VarnodeId, vn: VarnodeId, rel_offset: i32) -> bool {
        let varnode = data.vn(vn);
        let root = data.vn(root_vn);
        if varnode.is_mapped() && root.get_symbol_entry() != varnode.get_symbol_entry() {
            return true;
        }
        if !varnode.is_written() {
            return true;
        }
        let def = varnode.get_def().expect("written varnode has no defining op");
        if data.op(def).code() != OpCode::Piece {
            return true;
        }
        if varnode.lone_descend().is_none() {
            return true;
        }
        if varnode.is_addr_tied() {
            let addr = root.get_addr().add(rel_offset as i64);
            if *varnode.get_addr() != addr {
                return true;
            }
        }
        false
    }

    pub fn find_root(data: &Funcdata, vn: VarnodeId) -> Result<VarnodeId> {
        let mut vn = vn;
        while data.vn(vn).is_proto_partial() || data.vn(vn).is_addr_tied() {
            let mut piece_op: Option<OpId> = None;
            for op in data.vn(vn).descend().iter() {
                let pcode_op = data.op(*op);
                if pcode_op.code() != OpCode::Piece {
                    continue;
                }
                let slot = pcode_op.get_slot(vn);
                let mut addr = data
                    .vn(pcode_op.get_out().expect("PIECE has no output"))
                    .get_addr()
                    .clone();
                let big_endian = addr.get_space().map(|spc| spc.is_big_endian()).unwrap_or(false);
                if big_endian == (slot == 1) {
                    addr = addr.add(data.vn(pcode_op.get_in(1 - slot)).get_size() as i64);
                }
                addr.renormalize(data.vn(vn).get_size())?;
                if addr == *data.vn(vn).get_addr() {
                    match piece_op {
                        Some(current) => {
                            if data.op_compare_order(*op, current) != 0 {
                                piece_op = Some(*op);
                            }
                        }
                        None => piece_op = Some(*op),
                    }
                }
            }
            let Some(found) = piece_op else {
                break;
            };
            vn = data.op(found).get_out().expect("PIECE has no output");
        }
        Ok(vn)
    }

    pub fn gather_pieces(
        data: &Funcdata,
        stack: &mut Vec<PieceNode>,
        root_vn: VarnodeId,
        op: OpId,
        base_offset: i32,
        root_offset: i32,
    ) {
        let big_endian = data
            .vn(root_vn)
            .get_space()
            .map(|spc| spc.is_big_endian())
            .unwrap_or(false);
        for slot in 0..2 {
            let vn = data.op(op).get_in(slot);
            let offset = if big_endian == (slot == 1) {
                base_offset + data.vn(data.op(op).get_in(1 - slot)).get_size()
            } else {
                base_offset
            };
            let res = PieceNode::is_leaf_test(data, root_vn, vn, offset - root_offset);
            stack.push(PieceNode::new(op, slot, offset, res));
            if !res {
                let def = data.vn(vn).get_def().expect("PIECE input has no defining op");
                PieceNode::gather_pieces(data, stack, root_vn, def, offset, root_offset);
            }
        }
    }
}

pub type PcodeOpTree = OrderedIndex<SeqKey, OpId>;

pub type OpTreeIter = Option<SeqKey>;

pub struct PcodeOpBank {
    pub(crate) ops: Arena<OpId, PcodeOp>,
    pub(crate) optree: PcodeOpTree,
    pub(crate) alttree: PcodeOpTree,
    pub(crate) deadlist: OpList,
    pub(crate) alivelist: OpList,
    pub(crate) storelist: OpList,
    pub(crate) loadlist: OpList,
    pub(crate) returnlist: OpList,
    pub(crate) useroplist: OpList,
    pub(crate) deadandgone: Vec<OpId>,
    pub(crate) uniqid: u32,
}

impl Default for PcodeOpBank {
    fn default() -> PcodeOpBank {
        PcodeOpBank::new()
    }
}

impl PcodeOpBank {
    pub fn new() -> PcodeOpBank {
        PcodeOpBank {
            ops: Arena::new(),
            optree: OrderedIndex::default(),
            alttree: OrderedIndex::default(),
            deadlist: OpList::new(PcodeOp::INSERT_LIST),
            alivelist: OpList::new(PcodeOp::INSERT_LIST),
            storelist: OpList::new(PcodeOp::CODE_LIST),
            loadlist: OpList::new(PcodeOp::CODE_LIST),
            returnlist: OpList::new(PcodeOp::CODE_LIST),
            useroplist: OpList::new(PcodeOp::CODE_LIST),
            deadandgone: Vec::new(),
            uniqid: 0,
        }
    }

    pub fn get(&self, op: OpId) -> &PcodeOp {
        self.ops.get(op)
    }

    pub fn get_mut(&mut self, op: OpId) -> &mut PcodeOp {
        self.ops.get_mut(op)
    }

    pub fn add_to_code_list(&mut self, op: OpId) {
        let list = match self.ops.get(op).code() {
            OpCode::Store => &mut self.storelist,
            OpCode::Load => &mut self.loadlist,
            OpCode::Return => &mut self.returnlist,
            OpCode::Callother => &mut self.useroplist,
            _ => return,
        };
        list.push_back(&mut self.ops, op);
    }

    pub fn remove_from_code_list(&mut self, op: OpId) {
        let list = match self.ops.get(op).code() {
            OpCode::Store => &mut self.storelist,
            OpCode::Load => &mut self.loadlist,
            OpCode::Return => &mut self.returnlist,
            OpCode::Callother => &mut self.useroplist,
            _ => return,
        };
        list.remove(&mut self.ops, op);
    }

    pub fn clear_code_lists(&mut self) {
        self.storelist.clear(&mut self.ops);
        self.loadlist.clear(&mut self.ops);
        self.returnlist.clear(&mut self.ops);
        self.useroplist.clear(&mut self.ops);
    }

    pub fn clear(&mut self) {
        self.ops.clear();
        self.optree.clear();
        self.alttree.clear();
        self.alivelist = OpList::new(PcodeOp::INSERT_LIST);
        self.deadlist = OpList::new(PcodeOp::INSERT_LIST);
        self.storelist = OpList::new(PcodeOp::CODE_LIST);
        self.loadlist = OpList::new(PcodeOp::CODE_LIST);
        self.returnlist = OpList::new(PcodeOp::CODE_LIST);
        self.useroplist = OpList::new(PcodeOp::CODE_LIST);
        self.deadandgone.clear();
        self.uniqid = 0;
    }

    pub fn set_uniq_id(&mut self, val: u32) {
        self.uniqid = val;
    }

    pub fn get_uniq_id(&self) -> u32 {
        self.uniqid
    }

    fn create_dead(&mut self, inputs: i32, sq: SeqNum, indirect: bool) -> OpId {
        let op = self.ops.alloc(PcodeOp::new(inputs, &sq));
        if indirect {
            self.alttree.insert(sq.ordering_key(), op);
        } else {
            self.optree.insert(sq.ordering_key(), op);
        }
        self.ops.get_mut(op).set_flag(PcodeOp::DEAD);
        self.deadlist.push_back(&mut self.ops, op);
        op
    }

    pub fn create(&mut self, inputs: i32, pc: &Address) -> OpId {
        let sq = SeqNum::new(pc.clone(), self.uniqid);
        if op_trace_enabled() {
            eprintln!("O {:x}:{}", pc.get_offset(), self.uniqid);
        }
        self.uniqid = self.uniqid.wrapping_add(1);
        self.create_dead(inputs, sq, false)
    }

    pub fn create_seq(&mut self, inputs: i32, sq: &SeqNum) -> OpId {
        if sq.get_time() >= self.uniqid {
            self.uniqid = sq.get_time().wrapping_add(1);
        }
        self.create_dead(inputs, sq.clone(), false)
    }

    pub fn create_indirect(&mut self, _inputs: i32, pc: &Address) -> OpId {
        let sq = SeqNum::new(pc.clone(), self.uniqid);
        if op_trace_enabled() {
            eprintln!("O {:x}:{} indirect", pc.get_offset(), self.uniqid);
        }
        self.uniqid = self.uniqid.wrapping_add(1);
        self.create_dead(2, sq, true)
    }

    pub fn destroy(&mut self, op: OpId) -> Result<()> {
        if !self.ops.get(op).is_dead() {
            return Err(Error::Lowlevel("Deleting integrated op".to_string()));
        }
        let sq = self.ops.get(op).get_seq_num().ordering_key();
        if self.ops.get(op).code() == OpCode::Indirect {
            self.alttree.remove(&sq);
        } else {
            self.optree.remove(&sq);
        }
        self.deadlist.remove(&mut self.ops, op);
        self.remove_from_code_list(op);
        self.deadandgone.push(op);
        Ok(())
    }

    pub fn destroy_dead(&mut self) {
        let mut iter = self.deadlist.front();
        while let Some(op) = iter {
            iter = self.ops.get(op).links(PcodeOp::INSERT_LIST).next;
            self.destroy(op).expect("dead list contains an op that is not dead");
        }
    }

    pub fn change_opcode(&mut self, op: OpId, newopc: &dyn TypeOp) {
        if self.ops.get(op).opcode != OpCode::Blank {
            self.remove_from_code_list(op);
            if self.ops.get(op).code() == OpCode::Indirect {
                let sq = self.ops.get(op).start.ordering_key();
                self.alttree.remove(&sq);
                self.optree.insert(sq, op);
            }
        }
        self.ops.get_mut(op).set_opcode(newopc);
        self.add_to_code_list(op);
    }

    pub fn mark_alive(&mut self, op: OpId) {
        self.deadlist.remove(&mut self.ops, op);
        self.ops.get_mut(op).clear_flag(PcodeOp::DEAD);
        self.alivelist.push_back(&mut self.ops, op);
    }

    pub fn mark_dead(&mut self, op: OpId) {
        self.alivelist.remove(&mut self.ops, op);
        self.ops.get_mut(op).set_flag(PcodeOp::DEAD);
        self.deadlist.push_back(&mut self.ops, op);
    }

    pub fn insert_after_dead(&mut self, op: OpId, prev: OpId) -> Result<()> {
        if !self.ops.get(op).is_dead() || !self.ops.get(prev).is_dead() {
            return Err(Error::Lowlevel("Dead move called on ops which aren't dead".to_string()));
        }
        self.deadlist.remove(&mut self.ops, op);
        self.deadlist.insert_after(&mut self.ops, prev, op);
        Ok(())
    }

    pub fn move_sequence_dead(&mut self, firstop: OpId, lastop: OpId, prev: OpId) {
        let enditer = self.ops.get(lastop).links(PcodeOp::INSERT_LIST).next;
        let previter = self.ops.get(prev).links(PcodeOp::INSERT_LIST).next;
        if previter != Some(firstop) {
            self.deadlist.splice_range(&mut self.ops, previter, firstop, enditer);
        }
    }

    pub fn mark_incidental_copy(&mut self, firstop: OpId, lastop: OpId) {
        let enditer = self.ops.get(lastop).links(PcodeOp::INSERT_LIST).next;
        let mut iter = Some(firstop);
        while iter != enditer {
            let op = iter.expect("incidental copy range is not contiguous");
            iter = self.ops.get(op).links(PcodeOp::INSERT_LIST).next;
            if self.ops.get(op).code() == OpCode::Copy {
                self.ops.get_mut(op).set_additional_flag(PcodeOp::INCIDENTAL_COPY);
            }
        }
    }

    pub fn empty(&self) -> bool {
        self.optree.is_empty()
    }

    pub fn target(&self, addr: &Address) -> Option<OpId> {
        let key = SeqKey::new(addr, 0);
        let (_, op) = self.optree.range((Bound::Included(&key), Bound::Unbounded)).next()?;
        Some(list_target(&self.ops, *op))
    }

    pub fn find_op(&self, num: &SeqNum) -> Option<OpId> {
        self.optree.get(&num.ordering_key()).copied()
    }

    pub fn find_last_op(&self, addr: &Address) -> Option<OpId> {
        let key = SeqKey::new(addr, u32::MAX);
        let (_, op) = self
            .optree
            .range((Bound::Unbounded, Bound::Included(&key)))
            .next_back()?;
        if self.ops.get(*op).get_addr() == addr {
            return Some(*op);
        }
        None
    }

    pub fn fallthru(&self, op: OpId, blocks: &Arena<BlockId, FlowBlock>) -> Option<OpId> {
        if self.ops.get(op).is_dead() {
            let following = self.ops.get(op).links(PcodeOp::INSERT_LIST).next;
            if let Some(retop) = following
                && !self.ops.get(retop).is_instruction_start()
            {
                return Some(retop);
            }
            let mut max = self.ops.get(op).get_seq_num().clone();
            let mut iter = op;
            while !self.ops.get(iter).is_instruction_start() {
                iter = self
                    .ops
                    .get(iter)
                    .links(PcodeOp::INSERT_LIST)
                    .prev
                    .expect("no instruction start before dead op");
            }
            let mut walk = Some(iter);
            while let Some(current) = walk {
                if current == op {
                    break;
                }
                if max < *self.ops.get(current).get_seq_num() {
                    max = self.ops.get(current).get_seq_num().clone();
                }
                walk = self.ops.get(current).links(PcodeOp::INSERT_LIST).next;
            }
            let (_, retop) = self
                .optree
                .range((Bound::Excluded(&max.ordering_key()), Bound::Unbounded))
                .next()?;
            return Some(*retop);
        }
        list_next_op(&self.ops, blocks, op)
    }

    pub fn tree_at(tree: &PcodeOpTree, iter: &OpTreeIter) -> Option<OpId> {
        iter.as_ref().and_then(|key| tree.get(key).copied())
    }

    pub fn tree_lower_bound(tree: &PcodeOpTree, key: &SeqKey) -> OpTreeIter {
        tree.range((Bound::Included(key), Bound::Unbounded))
            .next()
            .map(|(found, _)| *found)
    }

    pub fn tree_upper_bound(tree: &PcodeOpTree, key: &SeqKey) -> OpTreeIter {
        tree.range((Bound::Excluded(key), Bound::Unbounded))
            .next()
            .map(|(found, _)| *found)
    }

    pub fn tree_next(tree: &PcodeOpTree, iter: &OpTreeIter) -> OpTreeIter {
        let key = iter.as_ref()?;
        match tree.entry_from(key)? {
            (found, _, following) if found == *key => following,
            (found, _, _) => Some(found),
        }
    }

    pub fn tree_range(tree: &PcodeOpTree, begin: &OpTreeIter, end: &OpTreeIter) -> Vec<OpId> {
        let Some(start) = begin else {
            return Vec::new();
        };
        if let Some(key) = end
            && key < start
        {
            return Vec::new();
        }
        let upper = match end {
            Some(key) => Bound::Excluded(key),
            None => Bound::Unbounded,
        };
        tree.range((Bound::Included(start), upper)).map(|(_, id)| *id).collect()
    }

    pub fn begin_main(&self) -> OpTreeIter {
        self.optree.keys().next().copied()
    }

    pub fn end_main(&self) -> OpTreeIter {
        None
    }

    pub fn begin_main_addr(&self, addr: &Address) -> OpTreeIter {
        PcodeOpBank::tree_lower_bound(&self.optree, &SeqKey::new(addr, 0))
    }

    pub fn end_main_addr(&self, addr: &Address) -> OpTreeIter {
        PcodeOpBank::tree_upper_bound(&self.optree, &SeqKey::new(addr, u32::MAX))
    }

    pub fn begin_indirect(&self) -> OpTreeIter {
        self.alttree.keys().next().copied()
    }

    pub fn end_indirect(&self) -> OpTreeIter {
        None
    }

    pub fn begin_indirect_addr(&self, addr: &Address) -> OpTreeIter {
        PcodeOpBank::tree_lower_bound(&self.alttree, &SeqKey::new(addr, 0))
    }

    pub fn end_indirect_addr(&self, addr: &Address) -> OpTreeIter {
        PcodeOpBank::tree_upper_bound(&self.alttree, &SeqKey::new(addr, u32::MAX))
    }

    pub fn begin_alive(&self) -> Option<OpId> {
        self.alivelist.front()
    }

    pub fn end_alive(&self) -> Option<OpId> {
        None
    }

    pub fn begin_dead(&self) -> Option<OpId> {
        self.deadlist.front()
    }

    pub fn end_dead(&self) -> Option<OpId> {
        None
    }

    pub fn begin(&self, opc: OpCode) -> Option<OpId> {
        match opc {
            OpCode::Store => self.storelist.front(),
            OpCode::Load => self.loadlist.front(),
            OpCode::Return => self.returnlist.front(),
            OpCode::Callother => self.useroplist.front(),
            _ => None,
        }
    }

    pub fn end(&self, _opc: OpCode) -> Option<OpId> {
        None
    }

    pub fn code_list_ops(&self, opc: OpCode) -> Vec<OpId> {
        match opc {
            OpCode::Store => self.storelist.to_vec(&self.ops),
            OpCode::Load => self.loadlist.to_vec(&self.ops),
            OpCode::Return => self.returnlist.to_vec(&self.ops),
            OpCode::Callother => self.useroplist.to_vec(&self.ops),
            _ => Vec::new(),
        }
    }

    pub fn next_in_list(&self, op: OpId, slot: usize) -> Option<OpId> {
        self.ops.get(op).links(slot).next
    }

    pub fn alive_ops(&self) -> Vec<OpId> {
        self.alivelist.to_vec(&self.ops)
    }

    pub fn dead_ops(&self) -> Vec<OpId> {
        self.deadlist.to_vec(&self.ops)
    }
}

fn op_trace_enabled() -> bool {
    static STATE: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *STATE.get_or_init(|| std::env::var_os("GHIDRA_OP_TRACE").is_some())
}

#[cfg(test)]
mod tests {
    use std::sync::Arc;

    use super::*;
    use crate::space::AddrSpace;

    fn ram_address(offset: u64) -> Address {
        let spc = Arc::new(AddrSpace::new_processor("ram", false, 4, 1, 3, 0, 0, 0));
        Address::new(spc, offset)
    }

    #[test]
    fn bank_lists_and_lookup() {
        let mut bank = PcodeOpBank::new();
        let first = bank.create(1, &ram_address(0x100));
        let second = bank.create(2, &ram_address(0x100));
        let third = bank.create(0, &ram_address(0x104));
        bank.get_mut(first).set_flag(PcodeOp::STARTMARK);
        bank.get_mut(third).set_flag(PcodeOp::STARTMARK);
        assert_eq!(bank.dead_ops(), vec![first, second, third]);
        assert_eq!(bank.find_last_op(&ram_address(0x100)), Some(second));
        assert_eq!(bank.find_last_op(&ram_address(0x102)), None);
        assert_eq!(bank.target(&ram_address(0x101)), Some(third));
        assert_eq!(bank.fallthru(first, &Arena::new()), Some(second));
        assert_eq!(bank.fallthru(second, &Arena::new()), Some(third));
        bank.move_sequence_dead(third, third, first);
        assert_eq!(bank.dead_ops(), vec![first, third, second]);
        bank.mark_alive(third);
        assert_eq!(bank.alive_ops(), vec![third]);
        assert!(bank.destroy(third).is_err());
        bank.destroy_dead();
        assert_eq!(bank.dead_ops(), Vec::<OpId>::new());
        assert!(bank.find_op(&SeqNum::new(ram_address(0x100), 0)).is_none());
        assert_eq!(bank.deadandgone, vec![first, second]);
        bank.clear();
        assert!(bank.empty());
        assert_eq!(bank.get_uniq_id(), 0);
    }

    #[test]
    fn input_slot_editing() {
        let mut op = PcodeOp::new(2, &SeqNum::new(ram_address(0), 0));
        op.set_input(Some(VarnodeId(7)), 0);
        op.set_input(Some(VarnodeId(9)), 1);
        op.insert_input(1);
        assert_eq!(op.num_input(), 3);
        assert_eq!(op.get_in_option(1), None);
        assert_eq!(op.get_in(2), VarnodeId(9));
        op.remove_input(0);
        assert_eq!(op.get_slot(VarnodeId(9)), 1);
        op.set_input(Some(VarnodeId(9)), 0);
        let descend = [OpId(4), OpId(4)];
        assert_eq!(op.get_repeat_slot(OpId(4), VarnodeId(9), 0, &descend, 1), 1);
        assert_eq!(op.get_repeat_slot(OpId(4), VarnodeId(9), 0, &descend, 0), 0);
    }
}
