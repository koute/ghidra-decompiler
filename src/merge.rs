use crate::stdsort::std_sort;

use crate::address::Address;
use crate::architecture::Architecture;
use crate::block::BlockId;
use crate::cover::{Cover, PcodeOpSet, PcodeOpSetBase};
use crate::database::Database;
use crate::error::{Error, Result};
use crate::expression::PcodeOpNode;
use crate::funcdata::Funcdata;
use crate::op::{OpId, PcodeOp, PieceNode};
use crate::opcodes::OpCode;
use crate::space::SpaceType;
use crate::types::{TypeFactory, TypeId, TypeMetatype};
use crate::variable::{HighId, HighIntersectTest, VariablePiece};
use crate::varnode::{LocIter, Varnode, VarnodeId};

#[derive(Copy, Clone, Debug)]
pub struct BlockVarnode {
    index: i32,
    vn: VarnodeId,
}

impl BlockVarnode {
    pub fn set(varnode: VarnodeId, data: &Funcdata) -> BlockVarnode {
        let index = match data.vn(varnode).get_def() {
            None => 0,
            Some(op) => {
                let parent = data.op(op).get_parent().expect("defining op without parent block");
                data.block(parent).get_index()
            }
        };
        BlockVarnode { index, vn: varnode }
    }

    pub fn less_than(&self, op2: &BlockVarnode) -> bool {
        self.index < op2.index
    }

    pub fn get_varnode(&self) -> VarnodeId {
        self.vn
    }

    pub fn get_index(&self) -> i32 {
        self.index
    }

    pub fn find_front(blocknum: i32, list: &[BlockVarnode]) -> i32 {
        let mut min: i32 = 0;
        let mut max: i32 = list.len() as i32 - 1;
        while min < max {
            let cur = (min + max) / 2;
            let curblock = list[cur as usize].get_index();
            if curblock >= blocknum {
                max = cur;
            } else {
                min = cur + 1;
            }
        }
        if min > max {
            return -1;
        }
        if list[min as usize].get_index() != blocknum {
            return -1;
        }
        min
    }
}

#[derive(Clone, Debug, Default)]
pub struct StackAffectingOps {
    pub base: PcodeOpSetBase,
}

impl StackAffectingOps {
    pub fn new() -> StackAffectingOps {
        StackAffectingOps {
            base: PcodeOpSetBase::new(),
        }
    }
}

impl PcodeOpSet for StackAffectingOps {
    fn base(&self) -> &PcodeOpSetBase {
        &self.base
    }

    fn base_mut(&mut self) -> &mut PcodeOpSetBase {
        &mut self.base
    }

    fn populate(&mut self, data: &Funcdata) {
        for index in 0..data.num_calls() {
            let op = data.call_spec(data.get_call_specs(index)).get_op();
            self.add_op(op);
        }
        for guard in data.get_store_guards() {
            if guard.is_valid(OpCode::Store, data) {
                self.add_op(guard.get_op().expect("store guard without op"));
            }
        }
        self.finalize(data);
    }

    fn affects_test(&self, op: OpId, vn: VarnodeId, data: &Funcdata) -> bool {
        if data.op(op).code() == OpCode::Store {
            return match data.get_store_guard(op) {
                None => true,
                Some(load_guard) => load_guard.is_guarded(data.vn(vn).get_addr()),
            };
        }
        true
    }
}

pub struct Merge {
    stack_affecting_ops: StackAffectingOps,
    test_cache: HighIntersectTest,
    copy_trims: Vec<OpId>,
    proto_partial: Vec<OpId>,
}

impl Default for Merge {
    fn default() -> Merge {
        Merge::new()
    }
}

fn symbol_table(glb: &Architecture) -> &Database {
    glb.symboltab.as_deref().expect("missing symbol table")
}

fn type_factory(glb: &Architecture) -> &TypeFactory {
    glb.types.as_deref().expect("missing type factory")
}

fn refresh_cover(data: &mut Funcdata, vn: VarnodeId) {
    data.vn_update_cover(vn);
}

fn cover_of(data: &Funcdata, vn: VarnodeId) -> &Cover {
    data.vn(vn).get_cover_raw().expect("missing varnode cover")
}

fn high_of(data: &Funcdata, vn: VarnodeId) -> Result<HighId> {
    data.vn(vn).get_high()
}

fn piece_of(data: &Funcdata, high: HighId) -> Option<&VariablePiece> {
    data.high(high).piece.as_ref()
}

fn vn_set_flags(data: &mut Funcdata, vn: VarnodeId, flags: u32) {
    let Funcdata { vbank, highs, .. } = data;
    vbank.varnodes.get_mut(vn).set_flags(flags, highs);
}

fn vn_make_explicit(data: &mut Funcdata, vn: VarnodeId) {
    let Funcdata { vbank, highs, .. } = data;
    let varnode = vbank.varnodes.get_mut(vn);
    varnode.clear_implied(highs);
    varnode.set_explicit(highs);
}

impl Merge {
    pub fn new() -> Merge {
        Merge {
            stack_affecting_ops: StackAffectingOps::new(),
            test_cache: HighIntersectTest::new(),
            copy_trims: Vec::new(),
            proto_partial: Vec::new(),
        }
    }

    fn cache_update_high(data: &mut Funcdata, high: HighId) -> bool {
        let mut cache = std::mem::take(&mut data.covermerge.test_cache);
        let result = cache.update_high(data, high);
        data.covermerge.test_cache = cache;
        result
    }

    fn cache_intersection(data: &mut Funcdata, first: HighId, second: HighId) -> Result<bool> {
        let mut cache = std::mem::take(&mut data.covermerge.test_cache);
        let mut affecting = std::mem::take(&mut data.covermerge.stack_affecting_ops);
        let result = cache.intersection(data, &mut affecting, first, second);
        data.covermerge.test_cache = cache;
        data.covermerge.stack_affecting_ops = affecting;
        result
    }

    fn merge_test_required(data: &mut Funcdata, glb: &Architecture, high_out: HighId, high_in: HighId) -> Result<bool> {
        if high_in == high_out {
            return Ok(true);
        }

        if data.high_is_type_lock(high_in, glb)
            && data.high_is_type_lock(high_out, glb)
            && data.high_get_type(high_in, glb) != data.high_get_type(high_out, glb)
        {
            return Ok(false);
        }

        if data.high_is_addr_tied(high_out) && data.high_is_addr_tied(high_in) {
            let tied_in = data.high_get_tied_varnode(high_in)?;
            let tied_out = data.high_get_tied_varnode(high_out)?;
            if data.vn(tied_in).get_addr() != data.vn(tied_out).get_addr() {
                return Ok(false);
            }
        }

        if data.high_is_input(high_in) {
            if data.high_is_persist(high_out) {
                return Ok(false);
            }
            if data.high_is_addr_tied(high_out) && !data.high_is_addr_tied(high_in) {
                return Ok(false);
            }
        } else if data.high_is_extra_out(high_in) {
            return Ok(false);
        }
        if data.high_is_input(high_out) {
            if data.high_is_persist(high_in) {
                return Ok(false);
            }
            if data.high_is_addr_tied(high_in) && !data.high_is_addr_tied(high_out) {
                return Ok(false);
            }
        } else if data.high_is_extra_out(high_out) {
            return Ok(false);
        }

        if data.high_is_proto_partial(high_in) {
            if data.high_is_proto_partial(high_out) {
                return Ok(false);
            }
            if data.high_is_input(high_out) {
                return Ok(false);
            }
            if data.high_is_addr_tied(high_out) {
                return Ok(false);
            }
            if data.high_is_persist(high_out) {
                return Ok(false);
            }
        }
        if data.high_is_proto_partial(high_out) {
            if data.high_is_input(high_in) {
                return Ok(false);
            }
            if data.high_is_addr_tied(high_in) {
                return Ok(false);
            }
            if data.high_is_persist(high_in) {
                return Ok(false);
            }
        }
        if let (Some(piece_in), Some(piece_out)) = (piece_of(data, high_in), piece_of(data, high_out)) {
            let group_in = piece_in.get_group();
            let group_out = piece_out.get_group();
            if group_in == group_out {
                return Ok(false);
            }
            if piece_in.get_size() != data.groups[group_in].get_size()
                && piece_out.get_size() != data.groups[group_out].get_size()
            {
                return Ok(false);
            }
        }

        let symbol_in = data.high_get_symbol(high_in, glb);
        let symbol_out = data.high_get_symbol(high_out, glb);
        if let (Some(symbol_in), Some(symbol_out)) = (symbol_in, symbol_out) {
            if symbol_in != symbol_out {
                return Ok(false);
            }
            if data.high(high_in).get_symbol_offset() != data.high(high_out).get_symbol_offset() {
                return Ok(false);
            }
        }
        Ok(true)
    }

    fn merge_test_adjacent(data: &mut Funcdata, glb: &Architecture, high_out: HighId, high_in: HighId) -> Result<bool> {
        if !Merge::merge_test_required(data, glb, high_out, high_in)? {
            return Ok(false);
        }

        if data.high_is_name_lock(high_in) && data.high_is_name_lock(high_out) {
            return Ok(false);
        }

        if data.high_get_type(high_out, glb) != data.high_get_type(high_in, glb) {
            return Ok(false);
        }
        if data.high_is_input(high_out) {
            let vn = data.high_get_input_varnode(high_out)?;
            if data.vn(vn).is_illegal_input() && !data.vn(vn).is_indirect_only() {
                return Ok(false);
            }
        }
        if data.high_is_input(high_in) {
            let vn = data.high_get_input_varnode(high_in)?;
            if data.vn(vn).is_illegal_input() && !data.vn(vn).is_indirect_only() {
                return Ok(false);
            }
        }
        if let Some(symbol) = data.high_get_symbol(high_in, glb)
            && symbol_table(glb).symbol(symbol).is_isolated()
        {
            return Ok(false);
        }
        if let Some(symbol) = data.high_get_symbol(high_out, glb)
            && symbol_table(glb).symbol(symbol).is_isolated()
        {
            return Ok(false);
        }

        if piece_of(data, high_out).is_some() && piece_of(data, high_in).is_some() {
            return Ok(false);
        }
        Ok(true)
    }

    fn merge_test_speculative(
        data: &mut Funcdata,
        glb: &Architecture,
        high_out: HighId,
        high_in: HighId,
    ) -> Result<bool> {
        if !Merge::merge_test_adjacent(data, glb, high_out, high_in)? {
            return Ok(false);
        }

        if data.high_is_persist(high_out) {
            return Ok(false);
        }
        if data.high_is_persist(high_in) {
            return Ok(false);
        }
        if data.high_is_input(high_out) {
            return Ok(false);
        }
        if data.high_is_input(high_in) {
            return Ok(false);
        }
        if data.high_is_addr_tied(high_out) {
            return Ok(false);
        }
        if data.high_is_addr_tied(high_in) {
            return Ok(false);
        }
        Ok(true)
    }

    fn merge_test_must(data: &mut Funcdata, vn: VarnodeId) -> Result<()> {
        let varnode = data.vn(vn);
        if varnode.has_cover() && !varnode.is_implied() {
            return Ok(());
        }
        Err(Error::Lowlevel("Cannot force merge of range".to_string()))
    }

    fn merge_test_basic(data: &mut Funcdata, vn: Option<VarnodeId>) -> bool {
        let Some(vn) = vn else {
            return false;
        };
        let varnode = data.vn(vn);
        if !varnode.has_cover() {
            return false;
        }
        if varnode.is_implied() {
            return false;
        }
        if varnode.is_proto_partial() {
            return false;
        }
        if varnode.is_spacebase() {
            return false;
        }
        true
    }

    fn find_single_copy(data: &mut Funcdata, high: HighId, singlelist: &mut Vec<VarnodeId>) -> Result<()> {
        for index in 0..data.high(high).num_instances() {
            let vn = data.high(high).get_instance(index);
            if !data.vn(vn).is_written() {
                continue;
            }
            let op = data.vn(vn).get_def().expect("written varnode without defining op");
            if data.op(op).code() != OpCode::Copy {
                continue;
            }
            if high_of(data, data.op(op).get_in(0))? == high {
                continue;
            }
            singlelist.push(vn);
        }
        Ok(())
    }

    fn compare_high_by_block(data: &Funcdata, first_high: HighId, second_high: HighId) -> bool {
        let result = data
            .high(first_high)
            .get_cover()
            .compare_to(data.high(second_high).get_cover());
        if result == 0 {
            let v1 = data.high(first_high).get_instance(0);
            let v2 = data.high(second_high).get_instance(0);
            if data.vn(v1).get_addr() == data.vn(v2).get_addr() {
                let def1 = data.vn(v1).get_def();
                let def2 = data.vn(v2).get_def();
                return match (def1, def2) {
                    (None, second) => second.is_some(),
                    (Some(_), None) => false,
                    (Some(first), Some(second)) => data.op(first).get_addr() < data.op(second).get_addr(),
                };
            }
            return data.vn(v1).get_addr() < data.vn(v2).get_addr();
        }
        result < 0
    }

    fn compare_copy_by_in_varnode(data: &Funcdata, op1: OpId, op2: OpId) -> bool {
        let in_vn1 = data.op(op1).get_in(0);
        let in_vn2 = data.op(op2).get_in(0);
        if in_vn1 != in_vn2 {
            return data.vn(in_vn1).get_create_index() < data.vn(in_vn2).get_create_index();
        }
        let index1 = data
            .block(data.op(op1).get_parent().expect("op without parent block"))
            .get_index();
        let index2 = data
            .block(data.op(op2).get_parent().expect("op without parent block"))
            .get_index();
        if index1 != index2 {
            return index1 < index2;
        }
        data.op(op1).get_seq_num().get_order() < data.op(op2).get_seq_num().get_order()
    }

    fn shadowed_varnode(data: &mut Funcdata, vn: VarnodeId) -> Result<bool> {
        let high = high_of(data, vn)?;
        let num = data.high(high).num_instances();
        for index in 0..num {
            let othervn = data.high(high).get_instance(index);
            if othervn == vn {
                continue;
            }
            refresh_cover(data, vn);
            refresh_cover(data, othervn);
            if cover_of(data, vn).intersect(cover_of(data, othervn), data) == 2 {
                return Ok(true);
            }
        }
        Ok(false)
    }

    fn find_all_into_copies(
        data: &mut Funcdata,
        high: HighId,
        copy_ins: &mut Vec<OpId>,
        filter_temps: bool,
    ) -> Result<()> {
        for index in 0..data.high(high).num_instances() {
            let vn = data.high(high).get_instance(index);
            if !data.vn(vn).is_written() {
                continue;
            }
            let op = data.vn(vn).get_def().expect("written varnode without defining op");
            if data.op(op).code() != OpCode::Copy {
                continue;
            }
            if high_of(data, data.op(op).get_in(0))? == high {
                continue;
            }
            if filter_temps {
                let out = data.op(op).get_out().expect("copy without output");
                let space_type = data.vn(out).get_space().map(|spc| spc.get_type());
                if space_type != Some(SpaceType::Internal) {
                    continue;
                }
            }
            copy_ins.push(op);
        }
        let reader: &Funcdata = data;
        std_sort(copy_ins, |first, second| {
            Merge::compare_copy_by_in_varnode(reader, *first, *second)
        });
        Ok(())
    }

    fn collect_inputs(data: &mut Funcdata, high: HighId, oplist: &mut Vec<PcodeOpNode>, op: OpId) -> Result<()> {
        let group = piece_of(data, high).map(|piece| piece.get_group());
        let mut current = op;
        loop {
            for slot in 0..data.op(current).num_input() {
                let vn = data.op(current).get_in(slot);
                if data.vn(vn).is_annotation() {
                    continue;
                }
                let test_high = high_of(data, vn)?;
                let same_group = match piece_of(data, test_high) {
                    Some(piece) => Some(piece.get_group()) == group,
                    None => false,
                };
                if test_high == high || same_group {
                    oplist.push(PcodeOpNode::new(current, slot));
                }
            }
            match data.op_previous_op(current) {
                Some(previous) if data.op(previous).code() == OpCode::Indirect => current = previous,
                _ => break,
            }
        }
        Ok(())
    }

    fn allocate_copy_trim(
        data: &mut Funcdata,
        glb: &mut Architecture,
        in_vn: VarnodeId,
        addr: &Address,
        trim_op: OpId,
    ) -> Result<OpId> {
        let copy_op = data.new_op(1, addr);
        data.op_set_opcode(copy_op, OpCode::Copy, glb);
        let ct = data.vn(in_vn).get_type();
        if type_factory(glb).get(ct).needs_resolution() {
            if data.vn(in_vn).is_written() {
                let def = data.vn(in_vn).get_def().expect("written varnode without defining op");
                let field_num = data.inherit_union_field(ct, copy_op, -1, def, -1, glb);
                data.force_facing_type(ct, field_num, copy_op, 0, glb);
            } else {
                let slot = data.op(trim_op).get_slot(in_vn);
                let field_num = data
                    .get_union_field(ct, trim_op, slot, glb)
                    .map(|res_union| res_union.get_field_num())
                    .unwrap_or(-1);
                data.force_facing_type(ct, field_num, copy_op, 0, glb);
            }
        }
        let size = data.vn(in_vn).get_size();
        let out_vn = data.new_unique(size, Some(ct), glb);
        data.op_set_output(copy_op, out_vn, glb)?;
        data.op_set_input(copy_op, in_vn, 0)?;
        data.covermerge.copy_trims.push(copy_op);
        Ok(copy_op)
    }

    fn snip_reads(data: &mut Funcdata, glb: &mut Architecture, vn: VarnodeId, markedop: &mut [OpId]) -> Result<()> {
        if markedop.is_empty() {
            return Ok(());
        }

        let bl: BlockId;
        let pc: Address;
        let afterop: Option<OpId>;
        if data.vn(vn).is_input() {
            bl = data.block(data.get_basic_blocks()).get_block(0);
            pc = data.block(bl).get_start();
            afterop = None;
        } else {
            let def = data.vn(vn).get_def().expect("written varnode without defining op");
            bl = data.op(def).get_parent().expect("op without parent block");
            pc = data.op(def).get_addr().clone();
            if data.op(def).code() == OpCode::Indirect {
                afterop = Some(PcodeOp::get_op_from_const(data.vn(data.op(def).get_in(1)).get_addr()));
            } else {
                afterop = Some(def);
            }
        }
        let copyop = Merge::allocate_copy_trim(data, glb, vn, &pc, markedop[0])?;
        match afterop {
            None => data.op_insert_begin(copyop, bl),
            Some(after) => data.op_insert_after(copyop, after),
        }

        let copy_out = data.op(copyop).get_out().expect("copy without output");
        for op in markedop.iter() {
            let slot = data.op(*op).get_slot(vn);
            data.op_set_input(*op, copy_out, slot)?;
        }
        Ok(())
    }

    fn snip_output_interference(data: &mut Funcdata, glb: &mut Architecture, indop: OpId) -> Result<bool> {
        let op = PcodeOp::get_op_from_const(data.vn(data.op(indop).get_in(1)).get_addr());
        let mut correctable: Vec<PcodeOpNode> = Vec::new();
        let out_high = high_of(data, data.op(indop).get_out().expect("indirect without output"))?;
        Merge::collect_inputs(data, out_high, &mut correctable, op)?;
        if correctable.is_empty() {
            return Ok(false);
        }

        {
            let reader: &Funcdata = data;
            std_sort(&mut correctable, |first, second| {
                PcodeOpNode::compare_by_high(first, second, reader)
            });
        }
        let mut snipop: Option<OpId> = None;
        let mut cur_high: Option<HighId> = None;
        for node in correctable.iter() {
            let insertop = node.op.expect("edge without op");
            let slot = node.slot;
            let vn = data.op(insertop).get_in(slot);
            let vn_high = high_of(data, vn)?;
            if Some(vn_high) != cur_high {
                let addr = data.op(insertop).get_addr().clone();
                let newop = Merge::allocate_copy_trim(data, glb, vn, &addr, insertop)?;
                data.op_insert_before(newop, insertop);
                snipop = Some(newop);
                cur_high = Some(vn_high);
            }
            let snip_out = data
                .op(snipop.expect("missing snip op"))
                .get_out()
                .expect("copy without output");
            data.op_set_input(insertop, snip_out, slot)?;
        }
        Ok(true)
    }

    fn eliminate_intersect(
        data: &mut Funcdata,
        glb: &mut Architecture,
        vn: VarnodeId,
        blocksort: &[BlockVarnode],
    ) -> Result<()> {
        let mut markedop: Vec<OpId> = Vec::new();
        let descendants: Vec<OpId> = data.vn(vn).descend().to_vec();

        for op in descendants {
            let mut insertop = false;
            let mut single = Cover::new();
            single.add_def_point(vn, data);
            single.add_ref_point(op, vn, data);
            let blocknums: Vec<i32> = single.blocks().keys().copied().collect();
            for blocknum in blocknums {
                let mut slot = BlockVarnode::find_front(blocknum, blocksort);
                if slot == -1 {
                    continue;
                }
                while (slot as usize) < blocksort.len() {
                    if blocksort[slot as usize].get_index() != blocknum {
                        break;
                    }
                    let vn2 = blocksort[slot as usize].get_varnode();
                    slot += 1;
                    if vn2 == vn {
                        continue;
                    }
                    let boundtype = single.contain_varnode_def(vn2, data);
                    if boundtype == 0 {
                        continue;
                    }
                    let overlaptype = data.vn(vn).characterize_overlap(data.vn(vn2));
                    if overlaptype == 0 {
                        continue;
                    }
                    if overlaptype == 1 {
                        let off = data.vn(vn).get_offset().wrapping_sub(data.vn(vn2).get_offset()) as i32;
                        if data.vn_partial_copy_shadow(vn, vn2, off) {
                            continue;
                        }
                    }
                    if boundtype == 2 {
                        match data.vn(vn2).get_def() {
                            None => match data.vn(vn).get_def() {
                                None => {
                                    if vn < vn2 {
                                        continue;
                                    }
                                }
                                Some(_) => continue,
                            },
                            Some(def2) => {
                                if let Some(def1) = data.vn(vn).get_def()
                                    && data.op(def2).get_seq_num().get_order() < data.op(def1).get_seq_num().get_order()
                                {
                                    continue;
                                }
                            }
                        }
                    } else if boundtype == 3 {
                        if !data.vn(vn2).is_addr_force() {
                            continue;
                        }
                        if !data.vn(vn2).is_written() {
                            continue;
                        }
                        let indop = data.vn(vn2).get_def().expect("written varnode without defining op");
                        if data.op(indop).code() != OpCode::Indirect {
                            continue;
                        }
                        if op != PcodeOp::get_op_from_const(data.vn(data.op(indop).get_in(1)).get_addr()) {
                            continue;
                        }
                        let ind_in = data.op(indop).get_in(0);
                        if overlaptype != 1 {
                            if data.vn_copy_shadow(vn, ind_in) {
                                continue;
                            }
                        } else {
                            let off = data.vn(vn).get_offset().wrapping_sub(data.vn(vn2).get_offset()) as i32;
                            if data.vn_partial_copy_shadow(vn, ind_in, off) {
                                continue;
                            }
                        }
                    }
                    insertop = true;
                    break;
                }
                if insertop {
                    break;
                }
            }
            if insertop {
                markedop.push(op);
            }
        }
        Merge::snip_reads(data, glb, vn, &mut markedop)
    }

    fn unify_address(data: &mut Funcdata, glb: &mut Architecture, varnodes: &[VarnodeId]) -> Result<()> {
        let mut isectlist: Vec<VarnodeId> = Vec::new();
        for vn in varnodes {
            if data.vn(*vn).is_free() {
                continue;
            }
            isectlist.push(*vn);
        }
        let mut blocksort: Vec<BlockVarnode> = isectlist.iter().map(|vn| BlockVarnode::set(*vn, data)).collect();
        blocksort.sort_by_key(|entry| entry.get_index());

        for vn in isectlist.iter() {
            Merge::eliminate_intersect(data, glb, *vn, &blocksort)?;
        }
        Ok(())
    }

    fn trim_op_output(data: &mut Funcdata, glb: &mut Architecture, op: OpId) -> Result<()> {
        let afterop = if data.op(op).code() == OpCode::Indirect {
            PcodeOp::get_op_from_const(data.vn(data.op(op).get_in(1)).get_addr())
        } else {
            op
        };
        let vn = data.op(op).get_out().expect("op without output");
        let mut ct = data.vn(vn).get_type();
        let addr = data.op(op).get_addr().clone();
        let copyop = data.new_op(1, &addr);
        data.op_set_opcode(copyop, OpCode::Copy, glb);
        if type_factory(glb).get(ct).needs_resolution() {
            let field_num = data.inherit_union_field(ct, copyop, -1, op, -1, glb);
            data.force_facing_type(ct, field_num, copyop, 0, glb);
            if type_factory(glb).get(ct).get_metatype() == TypeMetatype::PartialUnion {
                ct = data.vn_get_type_def_facing(vn, glb);
            }
        }
        let size = data.vn(vn).get_size();
        let uniq = data.new_unique(size, Some(ct), glb);
        data.op_set_output(op, uniq, glb)?;
        data.op_set_output(copyop, vn, glb)?;
        data.op_set_input(copyop, uniq, 0)?;
        data.op_insert_after(copyop, afterop);
        Ok(())
    }

    fn trim_op_input(data: &mut Funcdata, glb: &mut Architecture, op: OpId, slot: i32) -> Result<()> {
        let parent = data.op(op).get_parent().expect("op without parent block");
        let pc = if data.op(op).code() == OpCode::Multiequal {
            let bb = data.block(parent).get_in(slot);
            data.block(bb).get_stop()
        } else {
            data.op(op).get_addr().clone()
        };
        let vn = data.op(op).get_in(slot);
        let copyop = Merge::allocate_copy_trim(data, glb, vn, &pc, op)?;
        let copy_out = data.op(copyop).get_out().expect("copy without output");
        data.op_set_input(op, copy_out, slot)?;
        if data.op(op).code() == OpCode::Multiequal {
            let bb = data.block(parent).get_in(slot);
            data.op_insert_end(copyop, bb);
        } else {
            data.op_insert_before(copyop, op);
        }
        Ok(())
    }

    fn merge_range_must(data: &mut Funcdata, varnodes: &[VarnodeId]) -> Result<()> {
        let first = varnodes[0];
        Merge::merge_test_must(data, first)?;
        let high = high_of(data, first)?;
        for vn in &varnodes[1..] {
            let vn_high = high_of(data, *vn)?;
            if vn_high == high {
                continue;
            }
            Merge::merge_test_must(data, *vn)?;
            if !Merge::merge(data, high, vn_high, false)? {
                return Err(Error::Lowlevel("Forced merge caused intersection".to_string()));
            }
        }
        Ok(())
    }

    fn out_high(data: &Funcdata, op: OpId) -> Result<HighId> {
        high_of(data, data.op(op).get_out().expect("op without output"))
    }

    fn in_high(data: &Funcdata, op: OpId, slot: i32) -> Result<HighId> {
        high_of(data, data.op(op).get_in(slot))
    }

    fn merge_op(data: &mut Funcdata, glb: &mut Architecture, op: OpId) -> Result<()> {
        let mut testlist: Vec<HighId> = Vec::new();
        let max = if data.op(op).code() == OpCode::Indirect {
            1
        } else {
            data.op(op).num_input()
        };
        let high_out = Merge::out_high(data, op)?;
        for index in 0..max {
            let high_in = Merge::in_high(data, op, index)?;
            if !Merge::merge_test_required(data, glb, high_out, high_in)? {
                Merge::trim_op_input(data, glb, op, index)?;
                continue;
            }
            for prior in 0..index {
                let prior_high = Merge::in_high(data, op, prior)?;
                if !Merge::merge_test_required(data, glb, prior_high, high_in)? {
                    Merge::trim_op_input(data, glb, op, index)?;
                    break;
                }
            }
        }
        Merge::merge_test(data, high_out, &mut testlist)?;
        let mut index = 0;
        while index < max {
            let high_in = Merge::in_high(data, op, index)?;
            if !Merge::merge_test(data, high_in, &mut testlist)? {
                break;
            }
            index += 1;
        }

        if index != max {
            let mut nexttrim = 0;
            while nexttrim < max {
                Merge::trim_op_input(data, glb, op, nexttrim)?;
                testlist.clear();
                Merge::merge_test(data, high_out, &mut testlist)?;
                index = 0;
                while index < max {
                    let high_in = Merge::in_high(data, op, index)?;
                    if !Merge::merge_test(data, high_in, &mut testlist)? {
                        break;
                    }
                    index += 1;
                }
                if index == max {
                    break;
                }
                nexttrim += 1;
            }
            if nexttrim == max {
                Merge::trim_op_output(data, glb, op)?;
            }
        }

        for index in 0..max {
            let current_out = Merge::out_high(data, op)?;
            let current_in = Merge::in_high(data, op, index)?;
            if !Merge::merge_test_required(data, glb, current_out, current_in)? {
                return Err(Error::Lowlevel(
                    "Non-cover related merge restriction violated, despite trims".to_string(),
                ));
            }
            let current_out = Merge::out_high(data, op)?;
            let current_in = Merge::in_high(data, op, index)?;
            if !Merge::merge(data, current_out, current_in, false)? {
                return Err(Error::Lowlevel(format!(
                    "Unable to force merge of op at {}",
                    data.op(op).get_seq_num()
                )));
            }
        }
        Ok(())
    }

    fn merge_indirect(data: &mut Funcdata, glb: &mut Architecture, indop: OpId) -> Result<()> {
        let outvn = data.op(indop).get_out().expect("indirect without output");
        if !data.vn(outvn).is_addr_force() {
            return Merge::merge_op(data, glb, indop);
        }

        let invn0 = data.op(indop).get_in(0);
        let out_high = high_of(data, outvn)?;
        let in_high = high_of(data, invn0)?;
        if Merge::merge_test_required(data, glb, out_high, in_high)? && Merge::merge(data, in_high, out_high, false)? {
            return Ok(());
        }
        if Merge::snip_output_interference(data, glb, indop)? {
            let out_high = high_of(data, outvn)?;
            let in_high = high_of(data, invn0)?;
            if Merge::merge_test_required(data, glb, out_high, in_high)?
                && Merge::merge(data, in_high, out_high, false)?
            {
                return Ok(());
            }
        }

        let addr = data.op(indop).get_addr().clone();
        let newop = Merge::allocate_copy_trim(data, glb, invn0, &addr, indop)?;
        if let Some(entry) = data.vn(outvn).get_symbol_entry() {
            let symbol = symbol_table(glb).entry(entry).get_symbol();
            let symbol_type = symbol_table(glb)
                .symbol(symbol)
                .get_type()
                .expect("symbol without data-type");
            if type_factory(glb).get(symbol_type).needs_resolution() {
                data.inherit_union_field(symbol_type, newop, -1, indop, -1, glb);
            }
        }
        let new_out = data.op(newop).get_out().expect("copy without output");
        data.op_set_input(indop, new_out, 0)?;
        data.op_insert_before(newop, indop);
        let out_high = high_of(data, outvn)?;
        let in_high = Merge::in_high(data, indop, 0)?;
        if !Merge::merge_test_required(data, glb, out_high, in_high)? || !Merge::merge(data, in_high, out_high, false)?
        {
            return Err(Error::Lowlevel("Unable to merge address forced indirect".to_string()));
        }
        Ok(())
    }

    fn merge_linear(data: &mut Funcdata, glb: &Architecture, highvec: &mut [HighId]) -> Result<()> {
        let mut highstack: Vec<HighId> = Vec::new();

        if highvec.len() <= 1 {
            return Ok(());
        }
        for high in highvec.iter() {
            Merge::cache_update_high(data, *high);
        }
        {
            let reader: &Funcdata = data;
            std_sort(highvec, |first, second| {
                Merge::compare_high_by_block(reader, *first, *second)
            });
        }
        for high in highvec.iter() {
            let mut merged = false;
            for outer in highstack.iter() {
                if Merge::merge_test_speculative(data, glb, *outer, *high)? && Merge::merge(data, *outer, *high, true)?
                {
                    merged = true;
                    break;
                }
            }
            if !merged {
                highstack.push(*high);
            }
        }
        Ok(())
    }

    fn merge(data: &mut Funcdata, high1: HighId, high2: HighId, isspeculative: bool) -> Result<bool> {
        if high1 == high2 {
            return Ok(true);
        }
        if Merge::cache_intersection(data, high1, high2)? {
            return Ok(false);
        }

        let mut cache = std::mem::take(&mut data.covermerge.test_cache);
        let result = data.high_merge(high1, high2, Some(&mut cache), isspeculative);
        data.covermerge.test_cache = cache;
        result?;
        data.high_update_cover(high1);

        Ok(true)
    }

    fn check_copy_pair(data: &mut Funcdata, high: HighId, dom_op: OpId, sub_op: OpId) -> Result<bool> {
        let dom_block = data.op(dom_op).get_parent().expect("op without parent block");
        let sub_block = data.op(sub_op).get_parent().expect("op without parent block");
        if !data.block_dominates(dom_block, sub_block) {
            return Ok(false);
        }
        let mut range = Cover::new();
        range.add_def_point(data.op(dom_op).get_out().expect("copy without output"), data);
        range.add_ref_point(sub_op, data.op(sub_op).get_in(0), data);
        let in_vn = data.op(dom_op).get_in(0);
        for index in 0..data.high(high).num_instances() {
            let vn = data.high(high).get_instance(index);
            if !data.vn(vn).is_written() {
                continue;
            }
            let op = data.vn(vn).get_def().expect("written varnode without defining op");
            if data.op(op).code() == OpCode::Copy && data.op(op).get_in(0) == in_vn {
                continue;
            }
            if range.contain(op, 1, data) {
                return Ok(false);
            }
        }
        Ok(true)
    }

    fn build_dominant_copy(
        data: &mut Funcdata,
        glb: &mut Architecture,
        high: HighId,
        copy: &mut [OpId],
        pos: i32,
        size: i32,
    ) -> Result<()> {
        let pos = pos as usize;
        let size = size as usize;
        let block_set: Vec<BlockId> = (0..size)
            .map(|index| {
                data.op(copy[pos + index])
                    .get_parent()
                    .expect("op without parent block")
            })
            .collect();
        let dom_bl = data
            .block_find_common_block_set(&block_set)
            .expect("no common dominating block");
        let mut dom_copy = copy[pos];
        let root_vn = data.op(dom_copy).get_in(0);
        let mut dom_vn = data.op(dom_copy).get_out().expect("copy without output");
        let dom_copy_is_new = if Some(dom_bl) == data.op(dom_copy).get_parent() {
            false
        } else {
            let old_copy = dom_copy;
            let stop = data.block(dom_bl).get_stop();
            dom_copy = data.new_op(1, &stop);
            data.op_set_opcode(dom_copy, OpCode::Copy, glb);
            let mut ct = data.vn(root_vn).get_type();
            if type_factory(glb).get(ct).needs_resolution() {
                let field_num = data
                    .get_union_field(ct, old_copy, 0, glb)
                    .map(|res_union| res_union.get_field_num())
                    .unwrap_or(-1);
                data.force_facing_type(ct, field_num, dom_copy, 0, glb);
                data.force_facing_type(ct, field_num, dom_copy, -1, glb);
                if type_factory(glb).get(ct).get_metatype() == TypeMetatype::PartialUnion {
                    ct = data.vn_get_type_read_facing(root_vn, old_copy, glb);
                }
            }
            let root_size = data.vn(root_vn).get_size();
            dom_vn = data.new_unique(root_size, Some(ct), glb);
            data.op_set_output(dom_copy, dom_vn, glb)?;
            data.op_set_input(dom_copy, root_vn, 0)?;
            data.op_insert_end(dom_copy, dom_bl);
            true
        };
        let mut b_cover = Cover::new();
        for index in 0..data.high(high).num_instances() {
            let vn = data.high(high).get_instance(index);
            if data.vn(vn).is_written() {
                let op = data.vn(vn).get_def().expect("written varnode without defining op");
                if data.op(op).code() == OpCode::Copy && data.vn_copy_shadow(data.op(op).get_in(0), root_vn) {
                    continue;
                }
            }
            refresh_cover(data, vn);
            b_cover.merge(cover_of(data, vn), data);
        }

        let mut count = size;
        for index in 0..size {
            let op = copy[pos + index];
            if op == dom_copy {
                continue;
            }
            let out_vn = data.op(op).get_out().expect("copy without output");
            let mut a_cover = Cover::new();
            a_cover.add_def_point(dom_vn, data);
            let readers: Vec<OpId> = data.vn(out_vn).descend().to_vec();
            for reader in readers {
                a_cover.add_ref_point(reader, out_vn, data);
            }
            if b_cover.intersect(&a_cover, data) > 1 {
                count -= 1;
                data.op_mut(op).set_mark();
            }
        }

        if count <= 1 {
            for index in 0..size {
                data.op_mut(copy[pos + index]).set_mark();
            }
            count = 0;
            if dom_copy_is_new {
                data.op_destroy(dom_copy)?;
            }
        }
        for index in 0..size {
            let op = copy[pos + index];
            if data.op(op).is_mark() {
                data.op_mut(op).clear_mark();
            } else {
                let out_vn = data.op(op).get_out().expect("copy without output");
                if out_vn != dom_vn {
                    let out_high = high_of(data, out_vn)?;
                    data.high_remove(out_high, out_vn);
                    data.total_replace(out_vn, dom_vn)?;
                    data.op_destroy(op)?;
                }
            }
        }
        if count > 0 && dom_copy_is_new {
            let dom_high = high_of(data, dom_vn)?;
            data.high_merge(high, dom_high, None, true)?;
        }
        Ok(())
    }

    fn mark_redundant_copies(data: &mut Funcdata, high: HighId, copy: &mut [OpId], pos: i32, size: i32) -> Result<()> {
        let mut index = size - 1;
        while index > 0 {
            let sub_op = copy[(pos + index) as usize];
            if !data.op(sub_op).is_dead() {
                let mut prior = index - 1;
                while prior >= 0 {
                    let dom_op = copy[(pos + prior) as usize];
                    if !data.op(dom_op).is_dead() && Merge::check_copy_pair(data, high, dom_op, sub_op)? {
                        data.op_mark_non_printing(sub_op);
                        break;
                    }
                    prior -= 1;
                }
            }
            index -= 1;
        }
        Ok(())
    }

    fn copy_group_size(data: &Funcdata, copy_ins: &[OpId], pos: usize) -> usize {
        let in_vn = data.op(copy_ins[pos]).get_in(0);
        let mut group_size = 1;
        while pos + group_size < copy_ins.len() {
            let next_vn = data.op(copy_ins[pos + group_size]).get_in(0);
            if next_vn != in_vn {
                break;
            }
            group_size += 1;
        }
        group_size
    }

    fn process_high_dominant_copy(data: &mut Funcdata, glb: &mut Architecture, high: HighId) -> Result<()> {
        let mut copy_ins: Vec<OpId> = Vec::new();

        Merge::find_all_into_copies(data, high, &mut copy_ins, true)?;
        if copy_ins.len() < 2 {
            return Ok(());
        }
        let mut pos = 0;
        while pos < copy_ins.len() {
            let group_size = Merge::copy_group_size(data, &copy_ins, pos);
            if group_size > 1 {
                Merge::build_dominant_copy(data, glb, high, &mut copy_ins, pos as i32, group_size as i32)?;
            }
            pos += group_size;
        }
        Ok(())
    }

    fn process_high_redundant_copy(data: &mut Funcdata, high: HighId) -> Result<()> {
        let mut copy_ins: Vec<OpId> = Vec::new();

        Merge::find_all_into_copies(data, high, &mut copy_ins, false)?;
        if copy_ins.len() < 2 {
            return Ok(());
        }
        let mut pos = 0;
        while pos < copy_ins.len() {
            let group_size = Merge::copy_group_size(data, &copy_ins, pos);
            if group_size > 1 {
                Merge::mark_redundant_copies(data, high, &mut copy_ins, pos as i32, group_size as i32)?;
            }
            pos += group_size;
        }
        Ok(())
    }

    fn group_partial_root(data: &mut Funcdata, glb: &Architecture, vn: VarnodeId) -> Result<()> {
        let high = high_of(data, vn)?;
        if data.high(high).num_instances() != 1 {
            return Ok(());
        }
        let mut pieces: Vec<PieceNode> = Vec::new();

        let base_offset = match data.vn(vn).get_symbol_entry() {
            Some(entry) => symbol_table(glb).entry(entry).get_offset(),
            None => 0,
        };

        let def = data.vn(vn).get_def().expect("partial root without defining op");
        PieceNode::gather_pieces(data, &mut pieces, vn, def, base_offset, base_offset);
        let mut throw_out = false;
        for piece in pieces.iter() {
            let node_vn = piece.get_varnode(data);
            let node_high = high_of(data, node_vn)?;
            if !data.vn(node_vn).is_proto_partial() || data.high(node_high).num_instances() != 1 {
                throw_out = true;
                break;
            }
        }
        if throw_out {
            for piece in pieces.iter() {
                let node_vn = piece.get_varnode(data);
                data.vn_mut(node_vn).clear_proto_partial();
            }
        } else {
            for piece in pieces.iter() {
                let node_vn = piece.get_varnode(data);
                let node_high = high_of(data, node_vn)?;
                data.high_group_with(node_high, piece.get_type_offset() - base_offset, high)?;
            }
        }
        Ok(())
    }

    pub fn clear(&mut self) {
        self.test_cache.clear();
        self.copy_trims.clear();
        self.proto_partial.clear();
        self.stack_affecting_ops.clear();
    }

    pub fn mark_implied(data: &mut Funcdata, vn: VarnodeId) {
        {
            let Funcdata { vbank, highs, .. } = &mut *data;
            vbank.varnodes.get_mut(vn).set_implied(highs);
        }
        let op = data.vn(vn).get_def().expect("implied varnode without defining op");
        for slot in 0..data.op(op).num_input() {
            let defvn = data.op(op).get_in(slot);
            if !data.vn(defvn).has_cover() {
                continue;
            }
            vn_set_flags(data, defvn, Varnode::COVERDIRTY);
        }
    }

    pub fn inflate_test(data: &mut Funcdata, inflate_vn: VarnodeId, high: HighId) -> Result<bool> {
        let ahigh = high_of(data, inflate_vn)?;

        Merge::cache_update_high(data, high);
        let high_cover = data.high(high).internal_cover.clone();

        for index in 0..data.high(ahigh).num_instances() {
            let instance = data.high(ahigh).get_instance(index);
            if data.vn_copy_shadow(instance, inflate_vn) {
                continue;
            }
            refresh_cover(data, instance);
            if cover_of(data, instance).intersect(&high_cover, data) == 2 {
                return Ok(true);
            }
        }
        if piece_of(data, ahigh).is_some() {
            VariablePiece::update_intersections(data, ahigh);
            let piece = piece_of(data, ahigh).expect("piece removed during intersection update");
            let piece_offset = piece.get_offset();
            let intersections: Vec<HighId> = (0..piece.num_intersection())
                .map(|index| piece.get_intersection(index))
                .collect();
            for other_high in intersections {
                let other_offset = piece_of(data, other_high)
                    .expect("intersecting high without piece")
                    .get_offset();
                let off = other_offset - piece_offset;
                for index in 0..data.high(other_high).num_instances() {
                    let instance = data.high(other_high).get_instance(index);
                    if data.vn_partial_copy_shadow(instance, inflate_vn, off) {
                        continue;
                    }
                    refresh_cover(data, instance);
                    if cover_of(data, instance).intersect(&high_cover, data) == 2 {
                        return Ok(true);
                    }
                }
            }
        }
        Ok(false)
    }

    pub fn merge_test(data: &mut Funcdata, high: HighId, tmplist: &mut Vec<HighId>) -> Result<bool> {
        if !data.high_has_cover(high) {
            return Ok(false);
        }

        for other in tmplist.iter() {
            if Merge::cache_intersection(data, *other, high)? {
                return Ok(false);
            }
        }
        tmplist.push(high);
        Ok(true)
    }

    pub fn merge_opcode(data: &mut Funcdata, glb: &Architecture, opc: OpCode) -> Result<()> {
        let bblocks = data.get_basic_blocks();
        for index in 0..data.block(bblocks).get_size() {
            let bl = data.block(bblocks).get_block(index);
            let ops = data.block(bl).get_op_list().to_vec(&data.obank.ops);
            for op in ops {
                if data.op(op).code() != opc {
                    continue;
                }
                let vn1 = data.op(op).get_out();
                if !Merge::merge_test_basic(data, vn1) {
                    continue;
                }
                let vn1 = vn1.expect("op without output");
                for slot in 0..data.op(op).num_input() {
                    let vn2 = data.op(op).get_in(slot);
                    if !Merge::merge_test_basic(data, Some(vn2)) {
                        continue;
                    }
                    let high1 = high_of(data, vn1)?;
                    let high2 = high_of(data, vn2)?;
                    if Merge::merge_test_required(data, glb, high1, high2)? {
                        Merge::merge(data, high1, high2, false)?;
                    }
                }
            }
        }
        Ok(())
    }

    pub fn merge_by_datatype(data: &mut Funcdata, glb: &Architecture, varnodes: &[VarnodeId]) -> Result<()> {
        let mut highvec: Vec<HighId> = Vec::new();
        let mut highlist: Vec<HighId> = Vec::new();

        for vn in varnodes {
            if data.vn(*vn).is_free() {
                continue;
            }
            let high = high_of(data, *vn)?;
            if data.high(high).is_mark() {
                continue;
            }
            if !Merge::merge_test_basic(data, Some(*vn)) {
                continue;
            }
            data.high_mut(high).set_mark();
            highlist.push(high);
        }
        for high in highlist.iter() {
            data.high_mut(*high).clear_mark();
        }

        while !highlist.is_empty() {
            highvec.clear();
            let high = highlist.remove(0);
            let ct: TypeId = data.high_get_type(high, glb);
            highvec.push(high);
            let mut position = 0;
            while position < highlist.len() {
                let candidate = highlist[position];
                if ct == data.high_get_type(candidate, glb) {
                    highvec.push(candidate);
                    highlist.remove(position);
                } else {
                    position += 1;
                }
            }
            Merge::merge_linear(data, glb, &mut highvec)?;
        }
        Ok(())
    }

    pub fn merge_addr_tied(data: &mut Funcdata, glb: &mut Architecture) -> Result<()> {
        let mut bounds: Vec<LocIter> = Vec::new();
        let mut startiter = data.begin_loc();
        while let Some(start_vn) = data.vbank.loc_at(&startiter) {
            let spc = data.vn(start_vn).get_space().expect("varnode without space").clone();
            let space_type = spc.get_type();
            if space_type != SpaceType::Processor && space_type != SpaceType::Spacebase {
                startiter = data.end_loc_space(&spc, glb);
                continue;
            }
            let finaliter = data.end_loc_space(&spc, glb);
            while startiter != finaliter {
                let vn = data.vbank.loc_at(&startiter).expect("location iterator out of range");
                if data.vn(vn).is_free() {
                    let size = data.vn(vn).get_size();
                    let addr = data.vn(vn).get_addr().clone();
                    startiter = data.end_loc_flags(size, &addr, 0);
                    continue;
                }
                bounds.clear();
                let flags = data.overlap_loc(&startiter, &mut bounds);
                let max = bounds.len() - 1;
                if (flags & Varnode::ADDRTIED) != 0 {
                    let whole = data.vbank.loc_range(&startiter, &bounds[max]);
                    Merge::unify_address(data, glb, &whole)?;
                    let mut index = 0;
                    while index < max {
                        let range = data.vbank.loc_range(&bounds[index], &bounds[index + 1]);
                        Merge::merge_range_must(data, &range)?;
                        index += 2;
                    }
                    if max > 2 {
                        let vn1 = data.vbank.loc_at(&bounds[0]).expect("location iterator out of range");
                        let mut index = 2;
                        while index < max {
                            let vn2 = data
                                .vbank
                                .loc_at(&bounds[index])
                                .expect("location iterator out of range");
                            let off = data.vn(vn2).get_offset().wrapping_sub(data.vn(vn1).get_offset()) as i32;
                            let high2 = high_of(data, vn2)?;
                            let high1 = high_of(data, vn1)?;
                            data.high_group_with(high2, off, high1)?;
                            index += 2;
                        }
                    }
                }
                startiter = bounds[max];
            }
        }
        Ok(())
    }

    pub fn merge_marker(data: &mut Funcdata, glb: &mut Architecture) -> Result<()> {
        let mut current = data.begin_op_alive();
        while let Some(op) = current {
            if data.op(op).is_marker() && !data.op(op).is_indirect_creation() {
                if data.op(op).code() == OpCode::Indirect {
                    Merge::merge_indirect(data, glb, op)?;
                } else {
                    Merge::merge_op(data, glb, op)?;
                }
            }
            current = data.obank.next_in_list(op, PcodeOp::INSERT_LIST);
        }
        Ok(())
    }

    pub fn group_partials(data: &mut Funcdata, glb: &Architecture) -> Result<()> {
        let mut index = 0;
        while index < data.covermerge.proto_partial.len() {
            let op = data.covermerge.proto_partial[index];
            index += 1;
            if data.op(op).is_dead() {
                continue;
            }
            if !data.op(op).is_partial_root() {
                continue;
            }
            let out = data.op(op).get_out().expect("partial root without output");
            Merge::group_partial_root(data, glb, out)?;
        }
        Ok(())
    }

    pub fn merge_adjacent(data: &mut Funcdata, glb: &mut Architecture) -> Result<()> {
        let mut current = data.begin_op_alive();
        while let Some(op) = current {
            current = data.obank.next_in_list(op, PcodeOp::INSERT_LIST);
            if data.op(op).is_call() {
                continue;
            }
            let vn1 = data.op(op).get_out();
            if !Merge::merge_test_basic(data, vn1) {
                continue;
            }
            let vn1 = vn1.expect("op without output");
            let high_out = high_of(data, vn1)?;
            let ct = data.op_output_type_local(op, glb);
            for slot in 0..data.op(op).num_input() {
                if ct != data.op_input_type_local(op, slot, glb) {
                    continue;
                }
                let vn2 = data.op(op).get_in(slot);
                if !Merge::merge_test_basic(data, Some(vn2)) {
                    continue;
                }
                if data.vn(vn1).get_size() != data.vn(vn2).get_size() {
                    continue;
                }
                if data.vn(vn2).get_def().is_none() && !data.vn(vn2).is_input() {
                    continue;
                }
                let high_in = high_of(data, vn2)?;
                if !Merge::merge_test_adjacent(data, glb, high_out, high_in)? {
                    continue;
                }

                if !Merge::cache_intersection(data, high_in, high_out)? {
                    Merge::merge(data, high_out, high_in, true)?;
                }
            }
        }
        Ok(())
    }

    pub fn merge_multi_entry(data: &mut Funcdata, glb: &mut Architecture) -> Result<()> {
        let localmap = data.get_scope_local().expect("function without local scope");
        let symbols: Vec<_> = symbol_table(glb).scope(localmap).begin_multi_entry().collect();
        for symbol in symbols {
            let mut merge_list: Vec<VarnodeId> = Vec::new();
            let num_entries = symbol_table(glb).symbol(symbol).num_entries();
            let mut merge_count = 0;
            let mut skip_count = 0;
            let mut conflict_count = 0;
            for index in 0..num_entries {
                let prev_size = merge_list.len();
                let database = symbol_table(glb);
                let entry = database.symbol(symbol).get_map_entry_index(index);
                let symbol_type = database.symbol(symbol).get_type().expect("symbol without data-type");
                if database.entry(entry).get_size() != type_factory(glb).get(symbol_type).get_size() {
                    continue;
                }
                data.find_linked_varnodes(entry, &mut merge_list, glb);
                if merge_list.len() == prev_size {
                    skip_count += 1;
                }
            }
            if merge_list.is_empty() {
                continue;
            }
            let high = high_of(data, merge_list[0])?;
            Merge::cache_update_high(data, high);
            for vn in merge_list.iter() {
                let new_high = high_of(data, *vn)?;
                if new_high == high {
                    continue;
                }
                Merge::cache_update_high(data, new_high);
                if !Merge::merge_test_required(data, glb, high, new_high)?
                    || !Merge::merge(data, high, new_high, false)?
                {
                    glb.symboltab
                        .as_deref_mut()
                        .expect("missing symbol table")
                        .symbol_mut(symbol)
                        .set_merge_problems();
                    data.high_mut(new_high).set_unmerged();
                    conflict_count += 1;
                    continue;
                }
                merge_count += 1;
            }
            if skip_count != 0 || conflict_count != 0 {
                let mut message = String::from("Unable to");
                if merge_count != 0 {
                    message.push_str(" fully");
                }
                message.push_str(" merge symbol: ");
                message.push_str(symbol_table(glb).symbol(symbol).get_name());
                if skip_count > 0 {
                    message.push_str(" -- Some instance varnodes not found.");
                }
                if conflict_count > 0 {
                    message.push_str(" -- Some merges are forbidden");
                }
                data.warning_header(&message, glb);
            }
        }
        Ok(())
    }

    pub fn hide_shadows(data: &mut Funcdata, high: HighId) -> Result<bool> {
        let mut singlelist: Vec<VarnodeId> = Vec::new();
        let mut res = false;

        Merge::find_single_copy(data, high, &mut singlelist)?;
        if singlelist.len() <= 1 {
            return Ok(false);
        }
        let mut entries: Vec<Option<VarnodeId>> = singlelist.into_iter().map(Some).collect();
        for first in 0..entries.len() - 1 {
            let Some(vn1) = entries[first] else {
                continue;
            };
            for second in first + 1..entries.len() {
                let Some(vn2) = entries[second] else {
                    continue;
                };
                if !data.vn_copy_shadow(vn1, vn2) {
                    continue;
                }
                refresh_cover(data, vn2);
                if cover_of(data, vn2).contain_varnode_def(vn1, data) == 1 {
                    let def1 = data.vn(vn1).get_def().expect("written varnode without defining op");
                    data.op_set_input(def1, vn2, 0)?;
                    res = true;
                    break;
                }
                refresh_cover(data, vn1);
                if cover_of(data, vn1).contain_varnode_def(vn2, data) == 1 {
                    let def2 = data.vn(vn2).get_def().expect("written varnode without defining op");
                    data.op_set_input(def2, vn1, 0)?;
                    entries[second] = None;
                    res = true;
                }
            }
        }
        Ok(res)
    }

    pub fn process_copy_trims(data: &mut Funcdata, glb: &mut Architecture) -> Result<()> {
        let mut multi_copy: Vec<HighId> = Vec::new();

        let copy_trims = std::mem::take(&mut data.covermerge.copy_trims);
        for op in copy_trims.iter() {
            let high = Merge::out_high(data, *op)?;
            if !data.high(high).has_copy_in1() {
                multi_copy.push(high);
                data.high_mut(high).set_copy_in1();
            } else {
                data.high_mut(high).set_copy_in2();
            }
        }
        for high in multi_copy {
            if data.high(high).has_copy_in2() {
                Merge::process_high_dominant_copy(data, glb, high)?;
            }
            data.high_mut(high).clear_copy_ins();
        }
        Ok(())
    }

    pub fn mark_internal_copies(data: &mut Funcdata) -> Result<()> {
        let mut multi_copy: Vec<HighId> = Vec::new();

        let mut current = data.begin_op_alive();
        while let Some(op) = current {
            match data.op(op).code() {
                OpCode::Copy => {
                    let v1 = data.op(op).get_out().expect("copy without output");
                    let h1 = high_of(data, v1)?;
                    if h1 == Merge::in_high(data, op, 0)? {
                        data.op_mark_non_printing(op);
                    } else {
                        if !data.high(h1).has_copy_in1() {
                            data.high_mut(h1).set_copy_in1();
                            multi_copy.push(h1);
                        } else {
                            data.high_mut(h1).set_copy_in2();
                        }
                        if data.vn(v1).has_no_descend() && Merge::shadowed_varnode(data, v1)? {
                            data.op_mark_non_printing(op);
                        }
                    }
                }
                OpCode::Piece => 'piece: {
                    let v1 = data.op(op).get_out().expect("piece without output");
                    let v2 = data.op(op).get_in(0);
                    let v3 = data.op(op).get_in(1);
                    let (h1, h2, h3) = (high_of(data, v1)?, high_of(data, v2)?, high_of(data, v3)?);
                    let (Some(p1), Some(p2), Some(p3)) = (piece_of(data, h1), piece_of(data, h2), piece_of(data, h3))
                    else {
                        break 'piece;
                    };
                    if p1.get_group() != p2.get_group() {
                        break 'piece;
                    }
                    if p1.get_group() != p3.get_group() {
                        break 'piece;
                    }
                    let big_endian = data.vn(v1).get_space().expect("varnode without space").is_big_endian();
                    if big_endian {
                        if p2.get_offset() != p1.get_offset() {
                            break 'piece;
                        }
                        if p3.get_offset() != p1.get_offset() + data.vn(v2).get_size() {
                            break 'piece;
                        }
                    } else {
                        if p3.get_offset() != p1.get_offset() {
                            break 'piece;
                        }
                        if p2.get_offset() != p1.get_offset() + data.vn(v3).get_size() {
                            break 'piece;
                        }
                    }
                    data.op_mark_non_printing(op);
                    if data.vn(v2).is_implied() {
                        vn_make_explicit(data, v2);
                    }
                    if data.vn(v3).is_implied() {
                        vn_make_explicit(data, v3);
                    }
                }
                OpCode::Subpiece => 'subpiece: {
                    let v1 = data.op(op).get_out().expect("subpiece without output");
                    let v2 = data.op(op).get_in(0);
                    let (h1, h2) = (high_of(data, v1)?, high_of(data, v2)?);
                    let (Some(p1), Some(p2)) = (piece_of(data, h1), piece_of(data, h2)) else {
                        break 'subpiece;
                    };
                    if p1.get_group() != p2.get_group() {
                        break 'subpiece;
                    }
                    let val = data.vn(data.op(op).get_in(1)).get_offset() as i32;
                    let big_endian = data.vn(v1).get_space().expect("varnode without space").is_big_endian();
                    if big_endian {
                        if p2.get_offset() + (data.vn(v2).get_size() - data.vn(v1).get_size() - val) != p1.get_offset()
                        {
                            break 'subpiece;
                        }
                    } else if p2.get_offset() + val != p1.get_offset() {
                        break 'subpiece;
                    }
                    data.op_mark_non_printing(op);
                    if data.vn(v2).is_implied() {
                        vn_make_explicit(data, v2);
                    }
                }
                _ => {}
            }
            current = data.obank.next_in_list(op, PcodeOp::INSERT_LIST);
        }
        for high in multi_copy {
            if data.high(high).has_copy_in2() {
                Merge::process_high_redundant_copy(data, high)?;
            }
            data.high_mut(high).clear_copy_ins();
        }
        Ok(())
    }

    pub fn register_proto_partial_root(data: &mut Funcdata, vn: VarnodeId) {
        let def = data.vn(vn).get_def().expect("partial root without defining op");
        data.covermerge.proto_partial.push(def);
    }

    pub fn verify_high_covers(data: &mut Funcdata) -> Result<()> {
        let varnodes = data.vbank.loc_range(&data.begin_loc(), &data.end_loc());
        for vn in varnodes {
            if data.vn(vn).has_cover() {
                let high = high_of(data, vn)?;
                if !data.high(high).has_copy_in1() {
                    data.high_mut(high).set_copy_in1();
                    data.high_verify_cover(high)?;
                }
            }
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn entry(index: i32, id: u32) -> BlockVarnode {
        BlockVarnode {
            index,
            vn: VarnodeId(id),
        }
    }

    #[test]
    fn find_front_locates_first_entry_of_block() {
        let list = vec![entry(0, 1), entry(2, 2), entry(2, 3), entry(2, 4), entry(5, 5)];
        assert_eq!(BlockVarnode::find_front(0, &list), 0);
        assert_eq!(BlockVarnode::find_front(2, &list), 1);
        assert_eq!(BlockVarnode::find_front(5, &list), 4);
        assert_eq!(BlockVarnode::find_front(1, &list), -1);
        assert_eq!(BlockVarnode::find_front(3, &list), -1);
        assert_eq!(BlockVarnode::find_front(9, &list), -1);
    }

    #[test]
    fn find_front_on_empty_list() {
        assert_eq!(BlockVarnode::find_front(0, &[]), -1);
    }
}
