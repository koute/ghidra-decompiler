use crate::address::{Address, SeqNum, calc_int_max, calc_int_min, calc_mask, calc_uint_max};
use crate::architecture::Architecture;
use crate::block::BlockId;
use crate::error::{Error, Result};
use crate::expression::functional_equality_level;
use crate::flow::{
    ERROR_BADDATA, ERROR_OUTOFBOUNDS, ERROR_REINTERPRETED, ERROR_UNIMPLEMENTED, FLOW_FORINLINE, FlowInfo,
    POSSIBLE_UNREACHABLE,
};
use crate::funcdata::Funcdata;
use crate::jumptable::JumpTable;
use crate::op::{OpId, PcodeOp, find_common_block};
use crate::opcodes::{OpCode, get_booleanflip};
use crate::oplist::LinkedNode;
use crate::space::{AddrSpace, SpaceRef, SpaceType};
use crate::types::TypeId;
use crate::variable::HighId;
use crate::varnode::{Varnode, VarnodeId};

struct VarnodeSnapshot {
    size: i32,
    addr: Address,
    tp: TypeId,
    flags: u32,
}

struct OpSnapshot {
    code: OpCode,
    flags: u32,
    output: Option<VarnodeSnapshot>,
    inputs: Vec<VarnodeSnapshot>,
}

fn snapshot_varnode(source: &Funcdata, vn: VarnodeId) -> VarnodeSnapshot {
    let varnode = source.vn(vn);
    VarnodeSnapshot {
        size: varnode.get_size(),
        addr: varnode.get_addr().clone(),
        tp: varnode.get_type(),
        flags: varnode.get_flags(),
    }
}

fn snapshot_op(source: &Funcdata, op: OpId) -> OpSnapshot {
    let pcode_op = source.op(op);
    OpSnapshot {
        code: pcode_op.code(),
        flags: pcode_op.flags,
        output: pcode_op.get_out().map(|out| snapshot_varnode(source, out)),
        inputs: (0..pcode_op.num_input())
            .map(|slot| snapshot_varnode(source, pcode_op.get_in(slot)))
            .collect(),
    }
}

impl Funcdata {
    pub(crate) fn clone_varnode_parts(&mut self, size: i32, addr: &Address, tp: TypeId, flags: u32) -> VarnodeId {
        let newvn = self.vbank.create(size, addr, tp);
        let vflags = flags
            & (Varnode::ANNOTATION
                | Varnode::EXTERNREF
                | Varnode::READONLY
                | Varnode::PERSIST
                | Varnode::ADDRTIED
                | Varnode::ADDRFORCE
                | Varnode::INDIRECT_CREATION
                | Varnode::INCIDENTAL_COPY
                | Varnode::VOLATIL
                | Varnode::MAPPED);
        self.vn_set_flags(newvn, vflags);
        newvn
    }

    fn clone_op_snapshot(&mut self, snapshot: &OpSnapshot, seq: &SeqNum, glb: &mut Architecture) -> Result<OpId> {
        let newop = self.new_op_seq(snapshot.inputs.len() as i32, seq);
        self.op_set_opcode(newop, snapshot.code, glb);
        let fl = snapshot.flags & (PcodeOp::STARTMARK | PcodeOp::STARTBASIC);
        self.op_mut(newop).set_flag(fl);
        if let Some(out) = snapshot.output.as_ref() {
            let outvn = self.clone_varnode_parts(out.size, &out.addr, out.tp, out.flags);
            self.op_set_output(newop, outvn, glb)?;
        }
        for (slot, input) in snapshot.inputs.iter().enumerate() {
            let invn = self.clone_varnode_parts(input.size, &input.addr, input.tp, input.flags);
            self.op_set_input(newop, invn, slot as i32)?;
        }
        Ok(newop)
    }

    fn duplicate_constant(&mut self, vn: VarnodeId) -> VarnodeId {
        let (size, addr, tp, mapentry, flags) = {
            let varnode = self.vn(vn);
            (
                varnode.get_size(),
                varnode.get_addr().clone(),
                varnode.get_type(),
                varnode.get_symbol_entry(),
                varnode.get_flags(),
            )
        };
        let cvn = self.vbank.create(size, &addr, tp);
        if self.is_high_on() {
            let varnode = self.vn(cvn);
            if varnode.has_cover() {
                self.vbank.varnodes.get_mut(cvn).calc_cover(&mut self.highs);
            }
            if !self.vn(cvn).is_annotation() {
                self.high_create_unmapped(cvn);
            }
        }
        let varnode = self.vn_mut(cvn);
        varnode.tp = tp;
        varnode.mapentry = mapentry;
        varnode.flags &= !(Varnode::TYPELOCK | Varnode::NAMELOCK);
        varnode.flags |= (Varnode::TYPELOCK | Varnode::NAMELOCK) & flags;
        if let Some(high) = varnode.high {
            let high_data = self.high_mut(high);
            high_data.type_dirty();
            if mapentry.is_some() {
                high_data.symbol_dirty();
            }
        }
        cvn
    }

    pub fn op_set_opcode(&mut self, op: OpId, opc: OpCode, glb: &Architecture) {
        let top = glb.inst[opc.index()]
            .as_deref()
            .expect("missing TypeOp for p-code opcode");
        self.obank.change_opcode(op, top);
    }

    pub fn op_mark_halt(&mut self, op: OpId, flag: u32) -> Result<()> {
        if self.op(op).code() != OpCode::Return {
            return Err(Error::Lowlevel(
                "Only RETURN pcode ops can be marked as halt".to_string(),
            ));
        }
        let flag = flag
            & (PcodeOp::HALT | PcodeOp::BADINSTRUCTION | PcodeOp::UNIMPLEMENTED | PcodeOp::NORETURN | PcodeOp::MISSING);
        if flag == 0 {
            return Err(Error::Lowlevel("Bad halt flag".to_string()));
        }
        self.op_mut(op).set_flag(flag);
        Ok(())
    }

    pub fn op_unset_output(&mut self, op: OpId) -> Result<()> {
        let Some(vn) = self.op(op).get_out() else {
            return Ok(());
        };
        self.op_mut(op).set_output(None);
        self.vbank.make_free(vn, &self.obank.ops, &mut self.highs);
        self.vn_mut(vn).clear_cover();
        Ok(())
    }

    pub fn op_set_output(&mut self, op: OpId, vn: VarnodeId, glb: &mut Architecture) -> Result<()> {
        if Some(vn) == self.op(op).get_out() {
            return Ok(());
        }
        if self.op(op).get_out().is_some() {
            self.op_unset_output(op)?;
        }
        if let Some(def) = self.vn(vn).get_def() {
            self.op_unset_output(def)?;
        }
        let vn = self.vbank.set_def(vn, op, &mut self.obank.ops, &mut self.highs)?;
        self.set_varnode_properties(vn, glb)?;
        self.op_mut(op).set_output(Some(vn));
        Ok(())
    }

    pub fn op_unset_input(&mut self, op: OpId, slot: i32) {
        let vn = self.op(op).get_in(slot);
        self.vbank.varnodes.get_mut(vn).erase_descend(op, &mut self.highs);
        self.op_mut(op).clear_input(slot);
    }

    pub fn op_set_input(&mut self, op: OpId, vn: VarnodeId, slot: i32) -> Result<()> {
        if Some(vn) == self.op(op).get_in_option(slot) {
            return Ok(());
        }
        let mut vn = vn;
        let varnode = self.vn(vn);
        if varnode.is_constant() && !varnode.has_no_descend() && !varnode.is_spacebase() {
            vn = self.duplicate_constant(vn);
        }
        if self.op(op).get_in_option(slot).is_some() {
            self.op_unset_input(op, slot);
        }
        self.vbank.varnodes.get_mut(vn).add_descend(op, &mut self.highs)?;
        self.op_mut(op).set_input(Some(vn), slot);
        Ok(())
    }

    pub fn op_swap_input(&mut self, op: OpId, slot1: i32, slot2: i32) {
        let pcode_op = self.op_mut(op);
        let tmp = pcode_op.get_in_option(slot1);
        let other = pcode_op.get_in_option(slot2);
        pcode_op.set_input(other, slot1);
        pcode_op.set_input(tmp, slot2);
    }

    pub fn op_insert(&mut self, op: OpId, bl: BlockId, iter: Option<OpId>) {
        self.obank.mark_alive(op);
        self.block_insert_op(bl, iter, op);
    }

    pub fn op_uninsert(&mut self, op: OpId) {
        self.obank.mark_dead(op);
        let parent = self.op(op).get_parent().expect("p-code op has no parent block");
        self.block_remove_op(parent, op);
    }

    pub fn op_unlink(&mut self, op: OpId) -> Result<()> {
        self.op_unset_output(op)?;
        for slot in 0..self.op(op).num_input() {
            self.op_unset_input(op, slot);
        }
        if self.op(op).get_parent().is_some() {
            self.op_uninsert(op);
        }
        Ok(())
    }

    pub fn op_destroy(&mut self, op: OpId) -> Result<()> {
        if let Some(out) = self.op(op).get_out() {
            self.destroy_varnode(out)?;
        }
        for slot in 0..self.op(op).num_input() {
            if self.op(op).get_in_option(slot).is_some() {
                self.op_unset_input(op, slot);
            }
        }
        if let Some(parent) = self.op(op).get_parent() {
            self.obank.mark_dead(op);
            self.block_remove_op(parent, op);
        }
        Ok(())
    }

    pub fn op_destroy_recursive(&mut self, op: OpId, scratch: &mut Vec<OpId>) -> Result<()> {
        scratch.clear();
        scratch.push(op);
        let mut pos = 0;
        while pos < scratch.len() {
            let op = scratch[pos];
            pos += 1;
            for slot in 0..self.op(op).num_input() {
                let vn = self.vn(self.op(op).get_in(slot));
                if !vn.is_written() || vn.is_auto_live() {
                    continue;
                }
                if vn.lone_descend().is_none() {
                    continue;
                }
                let def_op = vn.get_def().expect("written varnode has no def");
                if self.op(def_op).is_call() || self.op(def_op).is_indirect_source() {
                    continue;
                }
                scratch.push(def_op);
            }
            self.op_destroy(op)?;
        }
        Ok(())
    }

    pub fn op_destroy_raw(&mut self, op: OpId) -> Result<()> {
        for slot in 0..self.op(op).num_input() {
            let vn = self.op(op).get_in(slot);
            self.destroy_varnode(vn)?;
        }
        if let Some(out) = self.op(op).get_out() {
            self.destroy_varnode(out)?;
        }
        self.obank.destroy(op)
    }

    pub fn op_set_all_input(&mut self, op: OpId, vvec: &[VarnodeId]) -> Result<()> {
        for slot in 0..self.op(op).num_input() {
            if self.op(op).get_in_option(slot).is_some() {
                self.op_unset_input(op, slot);
            }
        }
        self.op_mut(op).set_num_inputs(vvec.len() as i32);
        for (slot, vn) in vvec.iter().enumerate() {
            self.op_set_input(op, *vn, slot as i32)?;
        }
        Ok(())
    }

    pub fn op_remove_input(&mut self, op: OpId, slot: i32) {
        self.op_unset_input(op, slot);
        self.op_mut(op).remove_input(slot);
    }

    pub fn op_insert_input(&mut self, op: OpId, vn: VarnodeId, slot: i32) -> Result<()> {
        self.op_mut(op).insert_input(slot);
        self.op_set_input(op, vn, slot)
    }

    pub fn new_op(&mut self, inputs: i32, pc: &Address) -> OpId {
        self.obank.create(inputs, pc)
    }

    pub fn new_op_seq(&mut self, inputs: i32, sq: &SeqNum) -> OpId {
        self.obank.create_seq(inputs, sq)
    }

    pub fn new_indirect(&mut self, target: OpId, glb: &mut Architecture) -> Result<OpId> {
        let addr = self.op(target).get_addr().clone();
        let op = self.obank.create_indirect(2, &addr);
        self.op_set_opcode(op, OpCode::Indirect, glb);
        let iopvn = self.new_varnode_iop(target, glb);
        self.op_set_input(op, iopvn, 1)?;
        Ok(op)
    }

    pub fn op_insert_before(&mut self, op: OpId, follow: OpId) {
        let mut iter = follow;
        let parent = self.op(follow).get_parent().expect("p-code op has no parent block");
        if self.op(op).code() != OpCode::Indirect {
            while let Some(previousop) = self.op(iter).links(PcodeOp::BASIC_LIST).prev {
                if self.op(previousop).code() != OpCode::Indirect {
                    break;
                }
                iter = previousop;
            }
        }
        self.op_insert(op, parent, Some(iter));
    }

    pub fn op_insert_after(&mut self, op: OpId, prev: OpId) {
        let mut prev = prev;
        if self.op(prev).is_marker() && self.op(prev).code() == OpCode::Indirect {
            let invn = self.vn(self.op(prev).get_in(1));
            if invn.get_space().map(|spc| spc.get_type()) == Some(SpaceType::Iop) {
                let targ_op = PcodeOp::get_op_from_const(invn.get_addr());
                if !self.op(targ_op).is_dead() {
                    prev = targ_op;
                }
            }
        }
        let parent = self.op(prev).get_parent().expect("p-code op has no parent block");
        let mut iter = self.op(prev).links(PcodeOp::BASIC_LIST).next;
        if self.op(op).code() != OpCode::Multiequal {
            while let Some(nextop) = iter {
                if self.op(nextop).code() != OpCode::Multiequal {
                    break;
                }
                iter = self.op(nextop).links(PcodeOp::BASIC_LIST).next;
            }
        }
        self.op_insert(op, parent, iter);
    }

    pub fn op_insert_begin(&mut self, op: OpId, bl: BlockId) {
        let mut iter = self.block(bl).basic().op.front();
        if self.op(op).code() != OpCode::Multiequal {
            while let Some(current) = iter {
                if self.op(current).code() != OpCode::Multiequal {
                    break;
                }
                iter = self.op(current).links(PcodeOp::BASIC_LIST).next;
            }
        }
        self.op_insert(op, bl, iter);
    }

    pub fn op_insert_end(&mut self, op: OpId, bl: BlockId) {
        let mut iter = None;
        if let Some(last) = self.block(bl).basic().op.back()
            && self.op(last).is_flow_break()
        {
            iter = Some(last);
        }
        self.op_insert(op, bl, iter);
    }

    pub fn create_stack_ref(
        &mut self,
        spc: &SpaceRef,
        off: u64,
        op: OpId,
        stackptr: Option<VarnodeId>,
        insertafter: bool,
        glb: &mut Architecture,
    ) -> Result<VarnodeId> {
        let stackptr = match stackptr {
            Some(stackptr) => stackptr,
            None => self.new_spacebase_ptr(spc, glb)?,
        };
        let addrsize = self.vn(stackptr).get_size();
        let op_addr = self.op(op).get_addr().clone();
        let addop = self.new_op(2, &op_addr);
        self.op_set_opcode(addop, OpCode::IntAdd, glb);
        let mut addout = self.new_unique_out(addrsize, addop, glb)?;
        self.op_set_input(addop, stackptr, 0)?;
        let off = AddrSpace::byte_to_address(off, spc.get_word_size());
        let offvn = self.new_constant(addrsize, off, glb);
        self.op_set_input(addop, offvn, 1)?;
        if insertafter {
            self.op_insert_after(addop, op);
        } else {
            self.op_insert_before(addop, op);
        }
        let containerid = spc.get_contain().expect("space has no containing space");
        let segdef_size = glb
            .userops
            .get_segment_op(containerid.get_index())
            .and_then(|userop| userop.as_segment().map(|segment| segment.get_base_size()));
        if let Some(base_size) = segdef_size {
            let segop = self.new_op(3, &op_addr);
            self.op_set_opcode(segop, OpCode::Segmentop, glb);
            let segout = self.new_unique_out(containerid.get_addr_size() as i32, segop, glb)?;
            let spcvn = self.new_varnode_space(&containerid, glb);
            self.op_set_input(segop, spcvn, 0)?;
            let basevn = self.new_constant(base_size, 0, glb);
            self.op_set_input(segop, basevn, 1)?;
            self.op_set_input(segop, addout, 2)?;
            self.op_insert_after(segop, addop);
            addout = segout;
        }
        Ok(addout)
    }

    pub fn op_stack_load(
        &mut self,
        spc: &SpaceRef,
        off: u64,
        sz: u32,
        op: OpId,
        stackptr: Option<VarnodeId>,
        insertafter: bool,
        glb: &mut Architecture,
    ) -> Result<VarnodeId> {
        let addout = self.create_stack_ref(spc, off, op, stackptr, insertafter, glb)?;
        let op_addr = self.op(op).get_addr().clone();
        let loadop = self.new_op(2, &op_addr);
        self.op_set_opcode(loadop, OpCode::Load, glb);
        let container = spc.get_contain().expect("space has no containing space");
        let spcvn = self.new_varnode_space(&container, glb);
        self.op_set_input(loadop, spcvn, 0)?;
        self.op_set_input(loadop, addout, 1)?;
        let res = self.new_unique_out(sz as i32, loadop, glb)?;
        let def = self.vn(addout).get_def().expect("stack reference has no defining op");
        self.op_insert_after(loadop, def);
        Ok(res)
    }

    pub fn op_stack_store(
        &mut self,
        spc: &SpaceRef,
        off: u64,
        op: OpId,
        insertafter: bool,
        glb: &mut Architecture,
    ) -> Result<OpId> {
        let addout = self.create_stack_ref(spc, off, op, None, insertafter, glb)?;
        let op_addr = self.op(op).get_addr().clone();
        let storeop = self.new_op(3, &op_addr);
        self.op_set_opcode(storeop, OpCode::Store, glb);
        let container = spc.get_contain().expect("space has no containing space");
        let spcvn = self.new_varnode_space(&container, glb);
        self.op_set_input(storeop, spcvn, 0)?;
        self.op_set_input(storeop, addout, 1)?;
        let def = self.vn(addout).get_def().expect("stack reference has no defining op");
        self.op_insert_after(storeop, def);
        Ok(storeop)
    }

    pub fn op_bool_negate(
        &mut self,
        vn: VarnodeId,
        op: OpId,
        insertafter: bool,
        glb: &mut Architecture,
    ) -> Result<VarnodeId> {
        let op_addr = self.op(op).get_addr().clone();
        let negateop = self.new_op(1, &op_addr);
        self.op_set_opcode(negateop, OpCode::BoolNegate, glb);
        let resvn = self.new_unique_out(1, negateop, glb)?;
        self.op_set_input(negateop, vn, 0)?;
        if insertafter {
            self.op_insert_after(negateop, op);
        } else {
            self.op_insert_before(negateop, op);
        }
        Ok(resvn)
    }

    pub fn op_undo_ptradd(&mut self, op: OpId, finalize: bool, glb: &mut Architecture) -> Result<()> {
        let mult_vn = self.op(op).get_in(2);
        let mult_size = self.vn(mult_vn).get_offset() as i32;
        self.op_remove_input(op, 2);
        self.op_set_opcode(op, OpCode::IntAdd, glb);
        if mult_size == 1 {
            return Ok(());
        }
        let off_vn = self.op(op).get_in(1);
        if self.vn(off_vn).is_constant() {
            let off_size = self.vn(off_vn).get_size();
            let mut new_val = (mult_size as i64 as u64).wrapping_mul(self.vn(off_vn).get_offset());
            new_val &= calc_mask(off_size);
            let new_off_vn = self.new_constant(off_size, new_val, glb);
            if finalize {
                let ct = self.vn_get_type_read_facing(off_vn, op, glb);
                self.vn_update_type(new_off_vn, ct);
            }
            self.op_set_input(op, new_off_vn, 1)?;
            return Ok(());
        }
        let op_addr = self.op(op).get_addr().clone();
        let mult_op = self.new_op(2, &op_addr);
        self.op_set_opcode(mult_op, OpCode::IntMult, glb);
        let add_vn = self.new_unique_out(self.vn(off_vn).get_size(), mult_op, glb)?;
        if finalize {
            let ct = self.vn(mult_vn).get_type();
            self.vn_update_type(add_vn, ct);
            self.vn_set_flags(add_vn, Varnode::IMPLIED);
        }
        self.op_set_input(mult_op, off_vn, 0)?;
        self.op_set_input(mult_op, mult_vn, 1)?;
        self.op_set_input(op, add_vn, 1)?;
        self.op_insert_before(mult_op, op);
        Ok(())
    }

    pub fn clone_op(&mut self, op: OpId, seq: &SeqNum, glb: &mut Architecture) -> Result<OpId> {
        let snapshot = snapshot_op(self, op);
        self.clone_op_snapshot(&snapshot, seq, glb)
    }

    pub fn get_first_return_op(&self) -> Option<OpId> {
        let mut iter = self.obank.begin(OpCode::Return);
        while let Some(retop) = iter {
            iter = self.obank.next_in_list(retop, PcodeOp::CODE_LIST);
            let pcode_op = self.op(retop);
            if pcode_op.is_dead() {
                continue;
            }
            if pcode_op.get_halt_type() != 0 {
                continue;
            }
            return Some(retop);
        }
        None
    }

    pub fn new_op_before(
        &mut self,
        follow: OpId,
        opc: OpCode,
        in1: VarnodeId,
        in2: VarnodeId,
        in3: Option<VarnodeId>,
        glb: &mut Architecture,
    ) -> Result<OpId> {
        let sz = if in3.is_none() { 2 } else { 3 };
        let follow_addr = self.op(follow).get_addr().clone();
        let newop = self.new_op(sz, &follow_addr);
        self.op_set_opcode(newop, opc, glb);
        self.new_unique_out(self.vn(in1).get_size(), newop, glb)?;
        self.op_set_input(newop, in1, 0)?;
        self.op_set_input(newop, in2, 1)?;
        if let Some(in3) = in3 {
            self.op_set_input(newop, in3, 2)?;
        }
        self.op_insert_before(newop, follow);
        Ok(newop)
    }

    pub fn new_indirect_op(
        &mut self,
        indeffect: OpId,
        addr: &Address,
        sz: i32,
        extra_flags: u32,
        glb: &mut Architecture,
    ) -> Result<OpId> {
        let newin = self.new_varnode(sz, addr, None, glb)?;
        let newop = self.new_indirect(indeffect, glb)?;
        self.op_mut(newop).flags |= extra_flags;
        self.new_varnode_out(sz, addr, newop, glb)?;
        self.op_set_input(newop, newin, 0)?;
        self.op_insert_before(newop, indeffect);
        Ok(newop)
    }

    pub fn new_indirect_creation(
        &mut self,
        indeffect: OpId,
        addr: &Address,
        sz: i32,
        possibleout: bool,
        glb: &mut Architecture,
    ) -> Result<OpId> {
        let newin = self.new_constant(sz, 0, glb);
        let newop = self.new_indirect(indeffect, glb)?;
        self.op_mut(newop).flags |= PcodeOp::INDIRECT_CREATION;
        let newout = self.new_varnode_out(sz, addr, newop, glb)?;
        if !possibleout {
            self.vn_mut(newin).flags |= Varnode::INDIRECT_CREATION;
        }
        self.vn_mut(newout).flags |= Varnode::INDIRECT_CREATION;
        self.op_set_input(newop, newin, 0)?;
        self.op_insert_before(newop, indeffect);
        Ok(newop)
    }

    pub fn mark_indirect_creation(
        &mut self,
        indop: OpId,
        possible_output: bool,
        _glb: &mut Architecture,
    ) -> Result<()> {
        let outvn = self.op(indop).get_out().expect("INDIRECT has no output");
        let in0 = self.op(indop).get_in(0);
        self.op_mut(indop).flags |= PcodeOp::INDIRECT_CREATION;
        if !self.vn(in0).is_constant() {
            return Err(Error::Lowlevel("Indirect creation not properly formed".to_string()));
        }
        if !possible_output {
            self.vn_mut(in0).flags |= Varnode::INDIRECT_CREATION;
        }
        self.vn_mut(outvn).flags |= Varnode::INDIRECT_CREATION;
        Ok(())
    }

    pub fn follow_flow(&mut self, baddr: &Address, eaddr: &Address, glb: &mut Architecture) -> Result<()> {
        if !self.obank.empty() {
            if (self.flags & Funcdata::BLOCKS_GENERATED) == 0 {
                return Err(Error::Lowlevel("Function loaded for inlining".to_string()));
            }
            return Ok(());
        }
        let fl = glb.flowoptions;
        let mut flow = FlowInfo::new(self);
        flow.set_range(baddr, eaddr);
        flow.set_flags(fl);
        flow.set_maximum_instructions(glb.max_instructions);
        flow.generate_ops(self, glb)?;
        self.size = flow.get_size();
        flow.generate_blocks(self, glb)?;
        self.flags |= Funcdata::BLOCKS_GENERATED;
        self.switch_over_jump_tables(&flow, glb)?;
        if flow.has_unimplemented() {
            self.flags |= Funcdata::UNIMPLEMENTED_PRESENT;
        }
        if flow.has_bad_data() {
            self.flags |= Funcdata::BADDATA_PRESENT;
        }
        Ok(())
    }

    pub fn truncated_flow(&mut self, fd: &Funcdata, flow: &FlowInfo, glb: &mut Architecture) -> Result<()> {
        if !self.obank.empty() {
            return Err(Error::Lowlevel(
                "Trying to do truncated flow on pre-existing pcode".to_string(),
            ));
        }
        for op in fd.obank.dead_ops() {
            let snapshot = snapshot_op(fd, op);
            let seq = fd.op(op).get_seq_num().clone();
            self.clone_op_snapshot(&snapshot, &seq, glb)?;
        }
        self.obank.set_uniq_id(fd.obank.get_uniq_id());
        for oldspec_id in fd.qlst.iter() {
            let oldspec = fd.call_spec(*oldspec_id);
            let old_seq = fd.op(oldspec.get_op()).get_seq_num().clone();
            let newop = self.find_op(&old_seq).expect("cloned call op is missing");
            let newspec = oldspec.clone_spec(newop, self)?;
            let newspec_id = self.callspecs.alloc(newspec);
            let invn0 = self.op(newop).get_in(0);
            if self.vn(invn0).get_space().map(|spc| spc.get_type()) == Some(SpaceType::Fspec) {
                let newvn0 = self.new_varnode_call_specs(newspec_id, glb);
                self.op_set_input(newop, newvn0, 0)?;
                self.delete_varnode(invn0)?;
            }
            self.qlst.push(newspec_id);
        }
        for jt_id in fd.jumpvec.iter() {
            let jt = fd.jump_table(*jt_id);
            let Some(indop) = jt.get_indirect_op() else {
                continue;
            };
            let ind_seq = fd.op(indop).get_seq_num().clone();
            let Some(newop) = self.find_op(&ind_seq) else {
                return Err(Error::Lowlevel(
                    "Could not trace jumptable across partial clone".to_string(),
                ));
            };
            let mut jtclone = JumpTable::from_table(jt);
            jtclone.set_indirect_op(self, newop);
            let jtclone_id = self.jumptables.alloc(jtclone);
            self.jumpvec.push(jtclone_id);
        }
        let mut partialflow = FlowInfo::new_clone(self, flow);
        if partialflow.has_inject() {
            partialflow.inject_pcode(self, glb)?;
        }
        partialflow.clear_flags(!POSSIBLE_UNREACHABLE);
        partialflow.generate_blocks(self, glb)?;
        self.flags |= Funcdata::BLOCKS_GENERATED;
        Ok(())
    }

    pub fn inline_flow(
        &mut self,
        inlinefd: &mut Funcdata,
        flow: &mut FlowInfo,
        callop: OpId,
        glb: &mut Architecture,
    ) -> Result<i32> {
        glb.clear_analysis(inlinefd);
        let mut inlineflow = FlowInfo::new(inlinefd);
        inlinefd.obank.set_uniq_id(self.obank.get_uniq_id());
        let spc = self.baseaddr.get_space().cloned();
        let baddr = Address::from_parts(spc.clone(), 0);
        let eaddr = Address::from_parts(spc, u64::MAX);
        inlineflow.set_range(&baddr, &eaddr);
        inlineflow
            .set_flags(ERROR_OUTOFBOUNDS | ERROR_UNIMPLEMENTED | ERROR_BADDATA | ERROR_REINTERPRETED | FLOW_FORINLINE);
        inlineflow.forward_recursion(flow);
        inlineflow.generate_ops(inlinefd, glb)?;
        let res;
        if inlineflow.check_ez_model(inlinefd) {
            res = 0;
            let before = self.obank.deadlist.back();
            let calladdr = self.op(callop).get_addr().clone();
            flow.inline_ez_clone(&inlineflow, inlinefd, &calladdr, self, glb)?;
            let first = match before {
                Some(op) => self.obank.next_in_list(op, PcodeOp::INSERT_LIST),
                None => self.obank.deadlist.front(),
            };
            if let Some(firstop) = first {
                let lastop = self
                    .obank
                    .deadlist
                    .back()
                    .expect("dead list is empty after inline clone");
                self.obank.move_sequence_dead(firstop, lastop, callop);
                if self.op(callop).is_block_start() {
                    self.op_mut(firstop).set_flag(PcodeOp::STARTBASIC);
                    flow.update_target(callop, firstop, self);
                } else {
                    self.op_mut(firstop).clear_flag(PcodeOp::STARTBASIC);
                }
            }
            self.op_destroy_raw(callop)?;
        } else {
            let mut retaddr = Address::invalid();
            if !flow.test_hard_inline_restrictions(inlinefd, callop, &mut retaddr, self) {
                return Ok(-1);
            }
            res = 1;
            for jt_id in inlinefd.jumpvec.iter() {
                let jtclone = JumpTable::from_table(inlinefd.jump_table(*jt_id));
                let jtclone_id = self.jumptables.alloc(jtclone);
                self.jumpvec.push(jtclone_id);
            }
            flow.inline_clone(&inlineflow, inlinefd, &retaddr, self, glb)?;
            while self.op(callop).num_input() > 1 {
                let last = self.op(callop).num_input() - 1;
                self.op_remove_input(callop, last);
            }
            self.op_set_opcode(callop, OpCode::Branch, glb);
            let inline_addr = inlinefd.get_address().clone();
            let inlineaddr = self.new_code_ref(&inline_addr, glb);
            self.op_set_input(callop, inlineaddr, 0)?;
        }
        self.obank.set_uniq_id(inlinefd.obank.get_uniq_id());
        Ok(res)
    }

    pub fn find_primary_branch(
        &self,
        addr: &Address,
        find_branch: bool,
        find_call: bool,
        find_callother: bool,
        find_return: bool,
    ) -> Option<OpId> {
        let begin = self.begin_op_main_addr(addr);
        let end = self.end_op_main_addr(addr);
        for op in crate::op::PcodeOpBank::tree_range(&self.obank.optree, &begin, &end) {
            let pcode_op = self.op(op);
            if pcode_op.is_call_or_branch() || pcode_op.is_flow_break() {
                let opc = pcode_op.code();
                if find_branch
                    && (opc == OpCode::Branch || opc == OpCode::Cbranch)
                    && !self.vn(pcode_op.get_in(0)).is_constant()
                {
                    return Some(op);
                }
                if find_branch && opc == OpCode::Branchind {
                    return Some(op);
                }
                if find_call && (opc == OpCode::Call || opc == OpCode::Callind) {
                    return Some(op);
                }
                if find_return && opc == OpCode::Return {
                    return Some(op);
                }
                if find_callother && opc == OpCode::Callother {
                    return Some(op);
                }
            }
        }
        None
    }

    pub fn list_ops(&self, res: &mut Vec<OpId>, addr: &Address) {
        let begin = self.obank.begin_main_addr(addr);
        let end = self.obank.end_main_addr(addr);
        for op in crate::op::PcodeOpBank::tree_range(&self.obank.optree, &begin, &end) {
            if !self.op(op).is_dead() {
                res.push(op);
            }
        }
        let begin = self.obank.begin_indirect_addr(addr);
        let end = self.obank.end_indirect_addr(addr);
        for op in crate::op::PcodeOpBank::tree_range(&self.obank.alttree, &begin, &end) {
            if !self.op(op).is_dead() {
                res.push(op);
            }
        }
    }

    pub fn replace_lessequal(&mut self, op: OpId, glb: &mut Architecture) -> Result<bool> {
        let (vn, diff, slot) = if self.vn(self.op(op).get_in(0)).is_constant() {
            (self.op(op).get_in(0), -1i64, 0)
        } else if self.vn(self.op(op).get_in(1)).is_constant() {
            (self.op(op).get_in(1), 1i64, 1)
        } else {
            return Ok(false);
        };
        let val = self.vn(vn).get_offset();
        let size = self.vn(vn).get_size();
        if self.op(op).code() == OpCode::IntSlessequal {
            if diff == -1 && val == calc_int_min(size) {
                return Ok(false);
            }
            if diff == 1 && val == calc_int_max(size) {
                return Ok(false);
            }
            self.op_set_opcode(op, OpCode::IntSless, glb);
        } else {
            if diff == -1 && val == 0 {
                return Ok(false);
            }
            if diff == 1 && val == calc_uint_max(size) {
                return Ok(false);
            }
            self.op_set_opcode(op, OpCode::IntLess, glb);
        }
        let res = val.wrapping_add(diff as u64) & calc_mask(size);
        let newvn = self.new_constant(size, res, glb);
        self.vn_copy_symbol(newvn, vn, glb)?;
        self.op_set_input(op, newvn, slot)?;
        Ok(true)
    }

    fn distribute_term(
        &mut self,
        op: OpId,
        vn: VarnodeId,
        coeff: u64,
        sz: i32,
        glb: &mut Architecture,
    ) -> Result<VarnodeId> {
        if self.vn(vn).is_constant() {
            let val = coeff.wrapping_mul(self.vn(vn).get_offset()) & calc_mask(sz);
            return Ok(self.new_constant(sz, val, glb));
        }
        let op_addr = self.op(op).get_addr().clone();
        let newop = self.new_op(2, &op_addr);
        self.op_set_opcode(newop, OpCode::IntMult, glb);
        let newvn = self.new_unique_out(sz, newop, glb)?;
        self.op_set_input(newop, vn, 0)?;
        let newcvn = self.new_constant(sz, coeff, glb);
        self.op_set_input(newop, newcvn, 1)?;
        self.op_insert_before(newop, op);
        Ok(newvn)
    }

    pub fn distribute_int_mult_add(&mut self, op: OpId, glb: &mut Architecture) -> Result<bool> {
        let addop = self
            .vn(self.op(op).get_in(0))
            .get_def()
            .expect("distributed INT_MULT input is not written");
        let vn0 = self.op(addop).get_in(0);
        let vn1 = self.op(addop).get_in(1);
        if self.vn(vn0).is_free() && !self.vn(vn0).is_constant() {
            return Ok(false);
        }
        if self.vn(vn1).is_free() && !self.vn(vn1).is_constant() {
            return Ok(false);
        }
        let coeff = self.vn(self.op(op).get_in(1)).get_offset();
        let sz = self
            .vn(self.op(op).get_out().expect("INT_MULT has no output"))
            .get_size();
        let newvn0 = self.distribute_term(op, vn0, coeff, sz, glb)?;
        let newvn1 = self.distribute_term(op, vn1, coeff, sz, glb)?;
        self.op_set_input(op, newvn0, 0)?;
        self.op_set_input(op, newvn1, 1)?;
        self.op_set_opcode(op, OpCode::IntAdd, glb);
        Ok(true)
    }

    pub fn collapse_int_mult_mult(&mut self, vn: VarnodeId, glb: &mut Architecture) -> Result<bool> {
        if !self.vn(vn).is_written() {
            return Ok(false);
        }
        let op = self.vn(vn).get_def().expect("written varnode has no def");
        if self.op(op).code() != OpCode::IntMult {
            return Ok(false);
        }
        let const_vn_first = self.op(op).get_in(1);
        if !self.vn(const_vn_first).is_constant() {
            return Ok(false);
        }
        let first_in = self.op(op).get_in(0);
        if !self.vn(first_in).is_written() {
            return Ok(false);
        }
        let other_mult_op = self.vn(first_in).get_def().expect("written varnode has no def");
        if self.op(other_mult_op).code() != OpCode::IntMult {
            return Ok(false);
        }
        let const_vn_second = self.op(other_mult_op).get_in(1);
        if !self.vn(const_vn_second).is_constant() {
            return Ok(false);
        }
        let invn = self.op(other_mult_op).get_in(0);
        if self.vn(invn).is_free() {
            return Ok(false);
        }
        let sz = self.vn(invn).get_size();
        let val = self
            .vn(const_vn_first)
            .get_offset()
            .wrapping_mul(self.vn(const_vn_second).get_offset())
            & calc_mask(sz);
        let newvn = self.new_constant(sz, val, glb);
        self.op_set_input(op, newvn, 1)?;
        self.op_set_input(op, invn, 0)?;
        Ok(true)
    }

    pub fn build_copy_temp(&mut self, vn: VarnodeId, point: OpId, glb: &mut Architecture) -> Result<VarnodeId> {
        let mut other_op: Option<OpId> = None;
        for op in self.vn(vn).descend().iter() {
            let pcode_op = self.op(*op);
            if pcode_op.code() != OpCode::Copy {
                continue;
            }
            let outvn = self.vn(pcode_op.get_out().expect("COPY has no output"));
            if outvn.get_space().map(|spc| spc.get_type()) == Some(SpaceType::Internal) {
                if outvn.is_type_lock() {
                    continue;
                }
                other_op = Some(*op);
                break;
            }
        }
        let mut used_copy: Option<OpId> = None;
        if let Some(other) = other_op {
            let point_parent = self.op(point).get_parent().expect("p-code op has no parent block");
            let other_parent = self.op(other).get_parent().expect("p-code op has no parent block");
            if point_parent == other_parent {
                if self.op(point).get_seq_num().get_order() < self.op(other).get_seq_num().get_order() {
                    used_copy = None;
                } else {
                    used_copy = Some(other);
                }
            } else {
                let common = find_common_block(&self.blocks, point_parent, other_parent)
                    .expect("blocks have no common dominator");
                if common == point_parent {
                    used_copy = None;
                } else if common == other_parent {
                    used_copy = Some(other);
                } else {
                    let stop = self.block(common).get_stop();
                    let copy = self.new_op(1, &stop);
                    self.op_set_opcode(copy, OpCode::Copy, glb);
                    self.new_unique_out(self.vn(vn).get_size(), copy, glb)?;
                    self.op_set_input(copy, vn, 0)?;
                    self.op_insert_end(copy, common);
                    used_copy = Some(copy);
                }
            }
        }
        let used_copy = match used_copy {
            Some(copy) => copy,
            None => {
                let point_addr = self.op(point).get_addr().clone();
                let copy = self.new_op(1, &point_addr);
                self.op_set_opcode(copy, OpCode::Copy, glb);
                self.new_unique_out(self.vn(vn).get_size(), copy, glb)?;
                self.op_set_input(copy, vn, 0)?;
                self.op_insert_before(copy, point);
                copy
            }
        };
        if let Some(other) = other_op
            && other != used_copy
        {
            let other_out = self.op(other).get_out().expect("COPY has no output");
            let used_out = self.op(used_copy).get_out().expect("COPY has no output");
            self.total_replace(other_out, used_out)?;
            self.op_destroy(other)?;
        }
        Ok(self.op(used_copy).get_out().expect("COPY has no output"))
    }

    pub fn op_flip_in_place_test(&self, op: OpId, fliplist: &mut Vec<OpId>, allow_op_removal: bool) -> i32 {
        let pcode_op = self.op(op);
        match pcode_op.code() {
            OpCode::Cbranch => {
                let vn = self.vn(pcode_op.get_in(1));
                if vn.lone_descend() != Some(op) {
                    return 2;
                }
                if !vn.is_written() {
                    return 2;
                }
                let mut subtest1 = self.op_flip_in_place_test(
                    vn.get_def().expect("written varnode has no def"),
                    fliplist,
                    allow_op_removal,
                );
                if subtest1 != 2 && pcode_op.is_boolean_flip() {
                    subtest1 = 1 - subtest1;
                }
                subtest1
            }
            OpCode::IntEqual | OpCode::FloatEqual => {
                fliplist.push(op);
                1
            }
            OpCode::BoolNegate => {
                if !allow_op_removal {
                    return 2;
                }
                fliplist.push(op);
                0
            }
            OpCode::IntNotequal | OpCode::FloatNotequal => {
                fliplist.push(op);
                0
            }
            OpCode::IntSless | OpCode::IntLess => {
                let vn = self.vn(pcode_op.get_in(0));
                fliplist.push(op);
                if !vn.is_constant() {
                    return 1;
                }
                0
            }
            OpCode::IntSlessequal | OpCode::IntLessequal => {
                let vn = self.vn(pcode_op.get_in(1));
                fliplist.push(op);
                if vn.is_constant() {
                    return 1;
                }
                0
            }
            OpCode::BoolOr | OpCode::BoolAnd => {
                let vn = self.vn(pcode_op.get_in(0));
                if vn.lone_descend() != Some(op) {
                    return 2;
                }
                if !vn.is_written() {
                    return 2;
                }
                let subtest1 = self.op_flip_in_place_test(
                    vn.get_def().expect("written varnode has no def"),
                    fliplist,
                    allow_op_removal,
                );
                if subtest1 == 2 {
                    return 2;
                }
                let vn = self.vn(pcode_op.get_in(1));
                if vn.lone_descend() != Some(op) {
                    return 2;
                }
                if !vn.is_written() {
                    return 2;
                }
                let subtest2 = self.op_flip_in_place_test(
                    vn.get_def().expect("written varnode has no def"),
                    fliplist,
                    allow_op_removal,
                );
                if subtest2 == 2 {
                    return 2;
                }
                fliplist.push(op);
                subtest1
            }
            _ => 2,
        }
    }

    pub fn op_flip_in_place_execute(&mut self, fliplist: &[OpId], glb: &mut Architecture) -> Result<()> {
        for op in fliplist.iter().copied() {
            let flip = get_booleanflip(self.op(op).code());
            match flip {
                Some((OpCode::Copy, _)) => {
                    let vn = self.op(op).get_in(0);
                    let out = self.op(op).get_out().expect("BOOL_NEGATE has no output");
                    let otherop = self
                        .vn(out)
                        .lone_descend()
                        .expect("BOOL_NEGATE output has no lone descendant");
                    let slot = self.op(otherop).get_slot(out);
                    self.op_set_input(otherop, vn, slot)?;
                    self.op_destroy(op)?;
                }
                None => {
                    if self.op(op).code() == OpCode::BoolAnd {
                        self.op_set_opcode(op, OpCode::BoolOr, glb);
                    } else if self.op(op).code() == OpCode::BoolOr {
                        self.op_set_opcode(op, OpCode::BoolAnd, glb);
                    } else {
                        return Err(Error::Lowlevel("Bad flipInPlace op".to_string()));
                    }
                }
                Some((opc, flipyes)) => {
                    self.op_set_opcode(op, opc, glb);
                    if flipyes {
                        self.op_swap_input(op, 0, 1);
                        if opc == OpCode::IntLessequal || opc == OpCode::IntSlessequal {
                            self.replace_lessequal(op, glb)?;
                        }
                    }
                }
            }
        }
        Ok(())
    }

    pub fn op_normalize_flip(&mut self, cbranch: OpId, glb: &mut Architecture) -> Result<bool> {
        let bool_vn = self.op(cbranch).get_in(1);
        if !self.vn(bool_vn).is_written() {
            return Ok(false);
        }
        if self.vn(bool_vn).lone_descend() != Some(cbranch) {
            return Ok(false);
        }
        let cond_op = self.vn(bool_vn).get_def().expect("written varnode has no def");
        let Some((opc, flipyes)) = get_booleanflip(self.op(cond_op).code()) else {
            return Ok(false);
        };
        self.op_set_opcode(cond_op, opc, glb);
        if flipyes {
            self.op_swap_input(cond_op, 0, 1);
        }
        self.op_mut(cbranch).flip_flag(PcodeOp::BOOLEAN_FLIP);
        if opc == OpCode::IntLessequal || opc == OpCode::IntSlessequal {
            self.replace_lessequal(cond_op, glb)?;
        }
        Ok(true)
    }

    pub fn op_collapse_indirects_for_copy(&mut self, copy_op: OpId, glb: &mut Architecture) -> Result<()> {
        while let Some(op) = self.op(copy_op).links(PcodeOp::BASIC_LIST).prev {
            if self.op(op).code() != OpCode::Indirect {
                break;
            }
            let vn1 = self.op(copy_op).get_out().expect("COPY has no output");
            let vn2 = self.op(op).get_out().expect("INDIRECT has no output");
            let res = self.vn(vn1).characterize_overlap(self.vn(vn2));
            if res > 0 {
                let vn1_big_endian = self.vn(vn1).get_addr().is_big_endian();
                let vn2_big_endian = self.vn(vn2).get_addr().is_big_endian();
                let (vn1_off, vn1_size) = (self.vn(vn1).get_offset(), self.vn(vn1).get_size());
                let (vn2_off, vn2_size) = (self.vn(vn2).get_offset(), self.vn(vn2).get_size());
                let op_addr = self.op(op).get_addr().clone();
                if res != 2 && self.vn(vn1).contains(self.vn(vn2)) == 0 {
                    let trunc = if vn1_big_endian {
                        vn1_off
                            .wrapping_add(vn1_size as u64)
                            .wrapping_sub(vn2_off.wrapping_add(vn2_size as u64))
                    } else {
                        vn2_off.wrapping_sub(vn1_off)
                    };
                    self.op_uninsert(op);
                    self.op_set_input(op, vn1, 0)?;
                    let truncvn = self.new_constant(4, trunc, glb);
                    self.op_set_input(op, truncvn, 1)?;
                    self.op_set_opcode(op, OpCode::Subpiece, glb);
                    self.op_insert_after(op, copy_op);
                    continue;
                }
                if res != 2 {
                    let invn = self.op(op).get_in(0);
                    let mut insert_point = copy_op;
                    let mut bytes_before = 0i32;
                    if vn2_off < vn1_off {
                        bytes_before = vn1_off.wrapping_sub(vn2_off) as i32;
                    }
                    let vn2end = vn2_off.wrapping_add(vn2_size as u64).wrapping_sub(1);
                    let vn1end = vn1_off.wrapping_add(vn1_size as u64).wrapping_sub(1);
                    let mut bytes_after = 0i32;
                    if vn2end > vn1end {
                        bytes_after = vn2end.wrapping_sub(vn1end) as i32;
                    }
                    let overlap = vn2_size - bytes_before - bytes_after;
                    let mut front_vn: Option<VarnodeId> = None;
                    let mut back_vn: Option<VarnodeId> = None;
                    let front_slot = if vn2_big_endian { 0 } else { 1 };
                    let vn2_addr = self.vn(vn2).get_addr().clone();
                    if bytes_before != 0 {
                        let byte_off = if vn2_big_endian { vn2_size - bytes_before } else { 0 };
                        let sub_before = self.new_op(2, &op_addr);
                        self.op_set_opcode(sub_before, OpCode::Subpiece, glb);
                        front_vn = Some(self.new_varnode_out(bytes_after, &vn2_addr, sub_before, glb)?);
                        self.op_set_input(sub_before, invn, 0)?;
                        let offvn = self.new_constant(4, byte_off as u64, glb);
                        self.op_set_input(sub_before, offvn, 1)?;
                        self.op_insert_after(sub_before, insert_point);
                        insert_point = sub_before;
                    }
                    if bytes_after != 0 {
                        let byte_off = if vn2_big_endian { 0 } else { vn2_size - bytes_after };
                        let sub_after = self.new_op(2, &op_addr);
                        self.op_set_opcode(sub_after, OpCode::Subpiece, glb);
                        let addr = vn2_addr.add((vn2_size - bytes_after) as i64);
                        back_vn = Some(self.new_varnode_out(bytes_after, &addr, sub_after, glb)?);
                        self.op_set_input(sub_after, invn, 0)?;
                        let offvn = self.new_constant(4, byte_off as u64, glb);
                        self.op_set_input(sub_after, offvn, 1)?;
                        self.op_insert_after(sub_after, insert_point);
                        insert_point = sub_after;
                    }
                    let other_piece = if overlap != vn1_size {
                        let byte_off = if bytes_after == 0 {
                            if vn1_big_endian { vn1_size - overlap } else { 0 }
                        } else if vn1_big_endian {
                            0
                        } else {
                            vn1_size - overlap
                        };
                        let sub_middle = self.new_op(2, &op_addr);
                        self.op_set_opcode(sub_middle, OpCode::Subpiece, glb);
                        let addr = vn2_addr.add(bytes_before as i64);
                        let piece = self.new_varnode_out(overlap, &addr, sub_middle, glb)?;
                        self.op_set_input(sub_middle, vn1, 0)?;
                        let offvn = self.new_constant(4, byte_off as u64, glb);
                        self.op_set_input(sub_middle, offvn, 1)?;
                        self.op_insert_after(sub_middle, insert_point);
                        insert_point = sub_middle;
                        piece
                    } else {
                        vn1
                    };
                    if bytes_before == 0 {
                        front_vn = Some(other_piece);
                    } else if bytes_after == 0 {
                        back_vn = Some(other_piece);
                    } else {
                        let front = front_vn.expect("front piece was not built");
                        let concat = self.new_op(2, &op_addr);
                        self.op_set_opcode(concat, OpCode::Piece, glb);
                        let concat_size = self.vn(front).get_size() + self.vn(other_piece).get_size();
                        let new_vn = self.new_varnode_out(concat_size, &vn2_addr, concat, glb)?;
                        self.op_set_input(concat, front, front_slot)?;
                        self.op_set_input(concat, other_piece, 1 - front_slot)?;
                        self.op_insert_after(concat, insert_point);
                        insert_point = concat;
                        front_vn = Some(new_vn);
                    }
                    self.op_uninsert(op);
                    self.op_set_opcode(op, OpCode::Piece, glb);
                    self.op_set_input(op, front_vn.expect("front piece was not built"), front_slot)?;
                    self.op_set_input(op, back_vn.expect("back piece was not built"), 1 - front_slot)?;
                    self.op_insert_after(op, insert_point);
                    continue;
                }
                self.op_uninsert(op);
                self.op_set_input(op, vn1, 0)?;
                self.op_remove_input(op, 1);
                self.op_set_opcode(op, OpCode::Copy, glb);
                self.op_insert_after(op, copy_op);
            } else {
                let invn = self.op(op).get_in(0);
                self.total_replace(vn2, invn)?;
                self.op_destroy(op)?;
            }
        }
        Ok(())
    }

    pub fn op_collapse_indirects_for_alias(&mut self, effect_op: OpId) -> Result<()> {
        self.op_mut(effect_op).clear_additional_flag(PcodeOp::STORE_ALIASUPDATE);
        let Some(mut iter) = self.op(effect_op).links(PcodeOp::BASIC_LIST).prev else {
            return Ok(());
        };
        let use_guard = self.op(effect_op).uses_spacebase_ptr() && self.op(effect_op).code() == OpCode::Store;
        loop {
            let op = iter;
            if self.op(op).code() != OpCode::Indirect {
                break;
            }
            let out = self.op(op).get_out().expect("INDIRECT has no output");
            let mut should_destroy = false;
            if self.vn(out).has_no_local_alias()
                && !self.op(op).is_indirect_creation()
                && !self.op(op).no_indirect_collapse()
            {
                should_destroy = true;
            } else if use_guard
                && let Some(guard) = self.get_store_guard(effect_op)
                && !guard.is_guarded(self.vn(out).get_addr())
            {
                should_destroy = true;
            }
            let previous = self.op(op).links(PcodeOp::BASIC_LIST).prev;
            if should_destroy {
                let invn = self.op(op).get_in(0);
                self.total_replace(out, invn)?;
                self.op_destroy(op)?;
                match previous {
                    None => break,
                    Some(prev) => iter = prev,
                }
            } else {
                match previous {
                    None => break,
                    Some(prev) => iter = prev,
                }
            }
        }
        Ok(())
    }

    pub fn cse_find_in_block(&self, op: OpId, vn: VarnodeId, bl: BlockId, earliest: Option<OpId>) -> Option<OpId> {
        for res in self.vn(vn).descend().iter().copied() {
            if res == op {
                continue;
            }
            if self.op(res).get_parent() != Some(bl) {
                continue;
            }
            if let Some(earliest) = earliest
                && self.op(earliest).get_seq_num().get_order() < self.op(res).get_seq_num().get_order()
            {
                continue;
            }
            let outvn1 = self.op(op).get_out().expect("cse op has no output");
            let Some(outvn2) = self.op(res).get_out() else {
                continue;
            };
            let mut buf1 = [None; 2];
            let mut buf2 = [None; 2];
            if functional_equality_level(outvn1, outvn2, &mut buf1, &mut buf2, self) == 0 {
                return Some(res);
            }
        }
        None
    }

    pub fn cse_elimination(&mut self, op1: OpId, op2: OpId, glb: &mut Architecture) -> Result<Option<OpId>> {
        let parent1 = self.op(op1).get_parent().expect("p-code op has no parent block");
        let parent2 = self.op(op2).get_parent().expect("p-code op has no parent block");
        let replace = if parent1 == parent2 {
            if self.op(op1).get_seq_num().get_order() < self.op(op2).get_seq_num().get_order() {
                op1
            } else {
                op2
            }
        } else {
            let common = find_common_block(&self.blocks, parent1, parent2).expect("blocks have no common dominator");
            if common == parent1 {
                op1
            } else if common == parent2 {
                op2
            } else {
                let stop = self.block(common).get_stop();
                let replace = self.new_op(self.op(op1).num_input(), &stop);
                self.op_set_opcode(replace, self.op(op1).code(), glb);
                let out1 = self.op(op1).get_out().expect("cse op has no output");
                let (out_size, out_addr) = (self.vn(out1).get_size(), self.vn(out1).get_addr().clone());
                self.new_varnode_out(out_size, &out_addr, replace, glb)?;
                for slot in 0..self.op(op1).num_input() {
                    let input = self.op(op1).get_in(slot);
                    if self.vn(input).is_constant() {
                        let (size, offset) = (self.vn(input).get_size(), self.vn(input).get_offset());
                        let cvn = self.new_constant(size, offset, glb);
                        self.op_set_input(replace, cvn, slot)?;
                    } else {
                        self.op_set_input(replace, input, slot)?;
                    }
                }
                self.op_insert_end(replace, common);
                replace
            }
        };
        let replace_out = self.op(replace).get_out().expect("cse op has no output");
        if replace != op1 {
            let out1 = self.op(op1).get_out().expect("cse op has no output");
            self.total_replace(out1, replace_out)?;
            self.op_destroy(op1)?;
        }
        if replace != op2 {
            let out2 = self.op(op2).get_out().expect("cse op has no output");
            self.total_replace(out2, replace_out)?;
            self.op_destroy(op2)?;
        }
        Ok(Some(replace))
    }

    pub fn cse_eliminate_list(
        &mut self,
        list: &mut [(u32, OpId)],
        outlist: &mut Vec<VarnodeId>,
        glb: &mut Architecture,
    ) -> Result<()> {
        if list.is_empty() {
            return Ok(());
        }
        list.sort_by_key(|entry| entry.0);
        for index in 1..list.len() {
            let (hash1, op1) = list[index - 1];
            let (hash2, op2) = list[index];
            if hash1 != hash2 || op1 == op2 {
                continue;
            }
            if self.op(op1).is_dead() || self.op(op2).is_dead() || !self.op_is_cse_match(op1, op2) {
                continue;
            }
            let outvn1 = self.op(op1).get_out();
            let outvn2 = self.op(op2).get_out();
            if outvn1.is_none_or(|vn| self.is_heritaged(vn)) && outvn2.is_none_or(|vn| self.is_heritaged(vn)) {
                let resop = self
                    .cse_elimination(op1, op2, glb)?
                    .expect("cse elimination produced no op");
                outlist.push(self.op(resop).get_out().expect("cse op has no output"));
            }
        }
        Ok(())
    }

    pub fn move_respecting_cover(&mut self, op: OpId, last_op: OpId) -> bool {
        if op == last_op {
            return true;
        }
        if self.op(op).is_call() {
            return false;
        }
        let mut prev_op: Option<OpId> = None;
        if self.op(op).code() == OpCode::Cast {
            let vn = self.op(op).get_in(0);
            if !self.vn(vn).is_explicit() {
                if !self.vn(vn).is_written() {
                    return false;
                }
                let def = self.vn(vn).get_def().expect("written varnode has no def");
                if self.op(def).is_call() {
                    return false;
                }
                if self.op_previous_op(op) != Some(def) {
                    return false;
                }
                prev_op = Some(def);
            }
        }
        let rootvn = self.op(op).get_out().expect("moved op has no output");
        let mut high_list: Vec<HighId> = Vec::new();
        let type_val = self.high_mark_expression(rootvn, &mut high_list);
        let mut cur_op = op;
        loop {
            let next_op = self.op_next_op(cur_op).expect("no op follows in flow");
            let opc = self.op(next_op).code();
            if opc != OpCode::Copy && opc != OpCode::Cast {
                break;
            }
            if rootvn == self.op(next_op).get_in(0) {
                break;
            }
            let copy_vn = self.op(next_op).get_out().expect("COPY has no output");
            let copy_high = self
                .vn(copy_vn)
                .get_high_option()
                .expect("Requesting non-existent high-level");
            if self.high(copy_high).is_mark() {
                break;
            }
            if type_val != 0 && self.vn(copy_vn).is_addr_tied() {
                break;
            }
            cur_op = next_op;
            if cur_op == last_op {
                break;
            }
        }
        for high in high_list.iter() {
            self.high_mut(*high).clear_mark();
        }
        if cur_op == last_op {
            self.op_uninsert(op);
            self.op_insert_after(op, last_op);
            if let Some(prev) = prev_op {
                self.op_uninsert(prev);
                self.op_insert_after(prev, last_op);
            }
            return true;
        }
        false
    }
}
