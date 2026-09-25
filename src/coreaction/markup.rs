use crate::stdsort::std_sort;
use std::collections::{BTreeMap, VecDeque};

use crate::action::{Action, ActionBase, ActionGroupList, RULE_ONCEPERFUNC, RULE_REPEATAPPLY};
use crate::address::{Address, calc_mask, coveringmask, leastsigbit_set, minimalmask};
use crate::architecture::Architecture;
use crate::block::BlockId;
use crate::cast::CastStrategy;
use crate::database::Database;
use crate::error::Result;
use crate::expression::{PcodeOpNode, functional_equality};
use crate::fspec::{CallSpecId, ProtoParameter};
use crate::funcdata::Funcdata;
use crate::merge::Merge;
use crate::op::{OpId, PcodeOp, PieceNode};
use crate::opcodes::OpCode;
use crate::space::{AddrSpace, SpaceType};
use crate::typeop::with_type_op;
use crate::types::{Datatype, TypeId, TypeMetatype};
use crate::unionresolve::ResolvedUnion;
use crate::variable::HighId;
use crate::varnode::VarnodeId;

use super::{
    basic_next, loc_step_until, space_type_of, symbol_table, symbol_table_mut, type_factory, type_factory_mut,
};

fn capitalized_opcode_name(glb: &Architecture, opc: OpCode) -> String {
    let name = glb.inst[opc.index()]
        .as_ref()
        .expect("no TypeOp registered for opcode")
        .get_name()
        .to_string();
    let mut chars = name.chars();
    match chars.next() {
        Some(first) => first.to_ascii_uppercase().to_string() + chars.as_str(),
        None => name,
    }
}

#[derive(Clone, Copy, Debug)]
pub struct OpStackElement {
    pub vn: VarnodeId,
    pub slot: i32,
    pub slotback: i32,
}

impl OpStackElement {
    pub fn new(vn: VarnodeId, data: &Funcdata) -> OpStackElement {
        let mut slot = 0;
        let mut slotback = 0;
        if data.vn(vn).is_written() {
            let def = data.vn(vn).get_def().expect("written varnode has no defining op");
            let opc = data.op(def).code();
            if opc == OpCode::Load {
                slot = 1;
                slotback = 2;
            } else if opc == OpCode::Ptradd {
                slotback = 1;
            } else if opc == OpCode::Segmentop {
                slot = 2;
                slotback = 3;
            } else {
                slotback = data.op(def).num_input();
            }
        }
        OpStackElement { vn, slot, slotback }
    }
}

#[derive(Clone, Copy, Debug)]
pub struct DescTreeElement {
    pub vn: VarnodeId,
    pub desciter: usize,
}

impl DescTreeElement {
    pub fn new(vn: VarnodeId) -> DescTreeElement {
        DescTreeElement { vn, desciter: 0 }
    }
}

#[derive(Clone, Debug)]
pub struct OpRecommend {
    pub ct: Option<TypeId>,
    pub namerec: String,
}

#[derive(Clone, Debug)]
pub struct ConstPoint {
    pub vn: VarnodeId,
    pub const_vn: Option<VarnodeId>,
    pub value: u64,
    pub const_block: BlockId,
    pub in_slot: i32,
    pub block_is_dom: bool,
}

impl ConstPoint {
    pub fn new(
        vn: VarnodeId,
        const_vn: VarnodeId,
        bl: BlockId,
        slot: i32,
        is_dom: bool,
        data: &Funcdata,
    ) -> ConstPoint {
        ConstPoint {
            vn,
            const_vn: Some(const_vn),
            value: data.vn(const_vn).get_offset(),
            const_block: bl,
            in_slot: slot,
            block_is_dom: is_dom,
        }
    }

    pub fn from_value(vn: VarnodeId, val: u64, bl: BlockId, slot: i32, is_dom: bool) -> ConstPoint {
        ConstPoint {
            vn,
            const_vn: None,
            value: val,
            const_block: bl,
            in_slot: slot,
            block_is_dom: is_dom,
        }
    }
}

pub struct ActionSetCasts {
    pub base: ActionBase,
}

impl ActionSetCasts {
    pub fn new(group: &str) -> ActionSetCasts {
        ActionSetCasts {
            base: ActionBase::new(RULE_ONCEPERFUNC, "setcasts", group),
        }
    }

    pub fn check_pointer_issues(op: OpId, vn: VarnodeId, data: &mut Funcdata, glb: &mut Architecture) -> Result<()> {
        if data.op(op).does_special_printing() {
            return Ok(());
        }
        let ptrvn = data.op(op).get_in(1);
        let ptrtype = data.vn_get_high_type_read_facing(ptrvn, op, glb)?;
        let valsize = data.vn(vn).get_size();
        let ptrdt = type_factory(glb).get(ptrtype);
        let is_ptr = ptrdt.get_metatype() == TypeMetatype::Ptr;
        if !is_ptr || type_factory(glb).get(ptrdt.get_ptr_to()).get_size() != valsize {
            let name = capitalized_opcode_name(glb, data.op(op).code());
            let addr = data.op(op).get_addr().clone();
            data.warning(&format!("{} size is inaccurate", name), &addr, glb);
        }
        let ptrdt = type_factory(glb).get(ptrtype);
        if ptrdt.get_metatype() == TypeMetatype::Ptr
            && let Some(spc) = ptrdt.get_space().cloned()
        {
            let op_spc = data
                .vn(data.op(op).get_in(0))
                .get_space_from_const(&glb.manager)
                .expect("LOAD/STORE space operand is invalid");
            let contain_matches = spc.get_contain().map(|contain| contain.get_index()) == Some(op_spc.get_index());
            if op_spc.get_index() != spc.get_index() && !contain_matches {
                let name = capitalized_opcode_name(glb, data.op(op).code());
                let message = format!(
                    "{} refers to '{}' but pointer attribute is '{}'",
                    name,
                    op_spc.get_name(),
                    spc.get_name()
                );
                let addr = data.op(op).get_addr().clone();
                data.warning(&message, &addr, glb);
            }
        }
        Ok(())
    }

    pub fn test_struct_offset0(
        glb: &mut Architecture,
        reqtype: TypeId,
        curtype: TypeId,
        cast_strategy: &dyn CastStrategy,
    ) -> bool {
        let types = type_factory(glb);
        if types.get(curtype).get_metatype() != TypeMetatype::Ptr {
            return false;
        }
        let high_ptr_to = types.get(curtype).get_ptr_to();
        let mut reqtype = reqtype;
        let mut curtype: TypeId;
        let high_dt = types.get(high_ptr_to);
        if high_dt.get_metatype() == TypeMetatype::Struct {
            if high_dt.num_depend(types) == 0 {
                return false;
            }
            let first = &high_dt.get_fields()[0];
            if first.offset != 0 {
                return false;
            }
            reqtype = types.get(reqtype).get_ptr_to();
            curtype = first.tp;
            if types.get(reqtype).get_metatype() == TypeMetatype::Array {
                reqtype = types.get(reqtype).get_base();
            }
            if types.get(curtype).get_metatype() == TypeMetatype::Array {
                curtype = types.get(curtype).get_base();
            }
        } else if high_dt.get_metatype() == TypeMetatype::Array {
            reqtype = types.get(reqtype).get_ptr_to();
            curtype = high_dt.get_base();
        } else {
            return false;
        }
        if types.get(reqtype).get_metatype() == TypeMetatype::Void {
            return false;
        }
        cast_strategy
            .cast_standard(reqtype, curtype, true, true, type_factory_mut(glb))
            .is_none()
    }

    pub fn try_resolution_adjustment(
        dt: TypeId,
        op: OpId,
        slot: i32,
        data: &mut Funcdata,
        glb: &mut Architecture,
    ) -> Result<bool> {
        if type_factory(glb).get(dt).needs_resolution() {
            return Ok(false);
        }
        let vn = if slot < 0 {
            data.op(op).get_out().expect("op has no output")
        } else {
            data.op(op).get_in(slot)
        };
        let high = data.vn(vn).get_high()?;
        let cur_type = data.high_get_type(high, glb);
        let cur_dt = type_factory(glb).get(cur_type);
        if !cur_dt.needs_resolution() {
            return Ok(false);
        }
        if slot < 0 && cur_dt.get_metatype() == TypeMetatype::Ptr {
            return Ok(false);
        }
        let field_num = cur_dt.find_compatible_resolve(dt, type_factory(glb));
        if field_num < 0 {
            return Ok(false);
        }
        let resolve = ResolvedUnion::new_field(cur_type, field_num, type_factory_mut(glb))?;
        if !data.set_union_field(cur_type, op, slot, &resolve, glb) {
            return Ok(false);
        }
        if slot >= 0 && type_factory(glb).get(cur_type).get_metatype() == TypeMetatype::Ptr && data.vn(vn).is_written()
        {
            let def = data.vn(vn).get_def().expect("written varnode has no defining op");
            if data.op(def).code() != OpCode::Ptrsub || data.vn(data.op(def).get_in(0)).get_type() != cur_type {
                let ptrsub = ActionSetCasts::insert_ptrsub_zero(op, slot, resolve.get_datatype(), data, glb)?;
                data.set_union_field(cur_type, ptrsub, -1, &resolve, glb);
            }
        }
        Ok(true)
    }

    pub fn try_resolution_copy(op: OpId, data: &mut Funcdata, glb: &mut Architecture) -> Result<bool> {
        let outvn = match data.op(op).get_out() {
            Some(outvn) => outvn,
            None => return Ok(false),
        };
        let outhigh = data.vn(outvn).get_high()?;
        let out_type = data.high_get_type(outhigh, glb);
        let inhigh = data.vn(data.op(op).get_in(0)).get_high()?;
        let in_type = data.high_get_type(inhigh, glb);
        let types = type_factory(glb);
        let in_needs = types.get(in_type).needs_resolution();
        let out_needs = types.get(out_type).needs_resolution();
        if !in_needs && !out_needs {
            return Ok(false);
        }
        let mut in_resolve = -1;
        let mut out_resolve = -1;
        if in_needs {
            in_resolve = types.get(in_type).find_compatible_resolve(out_type, types);
            if in_resolve < 0 {
                return Ok(false);
            }
        }
        if out_needs && types.get(out_type).get_metatype() != TypeMetatype::Ptr {
            if in_resolve >= 0 {
                let depend = types
                    .get(in_type)
                    .get_depend(in_resolve, types)
                    .expect("union field is missing");
                out_resolve = types.get(out_type).find_compatible_resolve(depend, types);
            } else {
                out_resolve = types.get(out_type).find_compatible_resolve(in_type, types);
            }
            if out_resolve < 0 {
                return Ok(false);
            }
        }
        if in_resolve >= 0 {
            let resolve = ResolvedUnion::new_field(in_type, in_resolve, type_factory_mut(glb))?;
            if !data.set_union_field(in_type, op, 0, &resolve, glb) {
                return Ok(false);
            }
        }
        if out_resolve >= 0 {
            let resolve = ResolvedUnion::new_field(out_type, out_resolve, type_factory_mut(glb))?;
            if !data.set_union_field(out_type, op, -1, &resolve, glb) {
                return Ok(false);
            }
        }
        Ok(true)
    }

    pub fn is_op_identical(glb: &Architecture, ct1: TypeId, ct2: TypeId) -> bool {
        let types = type_factory(glb);
        let mut ct1 = ct1;
        let mut ct2 = ct2;
        while types.get(ct1).get_metatype() == TypeMetatype::Ptr && types.get(ct2).get_metatype() == TypeMetatype::Ptr {
            ct1 = types.get(ct1).get_ptr_to();
            ct2 = types.get(ct2).get_ptr_to();
        }
        while let Some(next) = types.get(ct1).get_typedef() {
            ct1 = next;
        }
        while let Some(next) = types.get(ct2).get_typedef() {
            ct2 = next;
        }
        ct1 == ct2
    }

    pub fn resolve_union(
        op: OpId,
        slot: i32,
        data: &mut Funcdata,
        glb: &mut Architecture,
        cast_strategy: &mut dyn CastStrategy,
    ) -> Result<i32> {
        let vn = data.op(op).get_in(slot);
        if data.vn(vn).is_annotation() {
            return Ok(0);
        }
        let high = data.vn(vn).get_high()?;
        let dt = data.high_get_type(high, glb);
        if !type_factory(glb).get(dt).needs_resolution() {
            return Ok(0);
        }
        let mut res_union = data.get_union_field(dt, op, slot, glb).cloned();
        if res_union.is_none() {
            Datatype::resolve_in_flow(dt, op, slot, data, glb)?;
            res_union = data.get_union_field(dt, op, slot, glb).cloned();
        }
        if let Some(res_union) = res_union
            && res_union.get_field_num() >= 0
        {
            if type_factory(glb).get(dt).get_metatype() == TypeMetatype::Ptr {
                let reqtype = data.vn_get_type_read_facing(vn, op, glb);
                if cast_strategy
                    .cast_standard(reqtype, res_union.get_datatype(), true, true, type_factory_mut(glb))
                    .is_some()
                {
                    return Ok(0);
                }
                let ptrsub = ActionSetCasts::insert_ptrsub_zero(op, slot, reqtype, data, glb)?;
                data.set_union_field(dt, ptrsub, -1, &res_union, glb);
            } else if data.vn(vn).is_implied() {
                if data.vn(vn).is_written() {
                    let def = data.vn(vn).get_def().expect("written varnode has no defining op");
                    let write_res = data.get_union_field(dt, def, -1, glb).cloned();
                    if let Some(write_res) = write_res
                        && write_res.get_field_num() == res_union.get_field_num()
                    {
                        return Ok(0);
                    }
                }
                data.vn_mut(vn).set_implied_field();
            }
            return Ok(1);
        }
        Ok(0)
    }

    pub fn cast_output(
        op: OpId,
        data: &mut Funcdata,
        glb: &mut Architecture,
        cast_strategy: &mut dyn CastStrategy,
    ) -> Result<i32> {
        let mut force = false;
        let opc_code = data.op(op).code();
        let tokenct = with_type_op(glb, opc_code, |top, glb| {
            top.get_output_token(op, cast_strategy, data, glb)
        })?;
        let outvn = data.op(op).get_out().expect("op has no output");
        let outhigh = data.vn(outvn).get_high()?;
        let out_high_type = data.high_get_type(outhigh, glb);
        if tokenct == out_high_type {
            if type_factory(glb).get(tokenct).needs_resolution() {
                let resolve = ResolvedUnion::new(tokenct, type_factory(glb));
                data.set_union_field(tokenct, op, -1, &resolve, glb);
            }
            return Ok(0);
        }
        let mut out_high_resolve = data.vn_get_high_type_def_facing(outvn, glb)?;
        if data.vn(outvn).is_implied() {
            if data.vn(outvn).is_type_lock() {
                let out_op = data.vn(outvn).lone_descend();
                let is_return = match out_op {
                    Some(out_op) => data.op(out_op).code() == OpCode::Return,
                    None => false,
                };
                if !is_return {
                    force = !ActionSetCasts::is_op_identical(glb, out_high_resolve, tokenct);
                }
            } else if type_factory(glb).get(out_high_resolve).get_metatype() != TypeMetatype::Ptr {
                data.vn_update_type(outvn, tokenct);
                out_high_resolve = data.vn_get_high_type_def_facing(outvn, glb)?;
            } else if type_factory(glb).get(tokenct).get_metatype() == TypeMetatype::Ptr {
                let outct = type_factory(glb).get(out_high_resolve).get_ptr_to();
                let meta = type_factory(glb).get(outct).get_metatype();
                if meta != TypeMetatype::Array && meta != TypeMetatype::Struct && meta != TypeMetatype::Union {
                    data.vn_update_type(outvn, tokenct);
                    out_high_resolve = data.vn_get_high_type_def_facing(outvn, glb)?;
                }
            }
        }
        let mut opc = OpCode::Cast;
        if !force {
            let outct = out_high_resolve;
            if type_factory(glb).get(outct).get_metatype() == TypeMetatype::Ptr
                && ActionSetCasts::test_struct_offset0(glb, outct, tokenct, cast_strategy)
            {
                opc = OpCode::Ptrsub;
            } else {
                let ct = cast_strategy.cast_standard(outct, tokenct, false, true, type_factory_mut(glb));
                if ct.is_none() {
                    return Ok(0);
                }
            }
            if ActionSetCasts::try_resolution_adjustment(tokenct, op, -1, data, glb)? {
                return Ok(0);
            }
        }
        let outsize = data.vn(outvn).get_size();
        let vn = data.new_unique(outsize, None, glb);
        data.vn_update_type(vn, tokenct);
        data.vbank.get_mut(vn).set_implied(&mut data.highs);
        let opaddr = data.op(op).get_addr().clone();
        let newop = data.new_op(if opc != OpCode::Cast { 2 } else { 1 }, &opaddr);
        data.op_set_opcode(newop, opc, glb);
        data.op_set_output(newop, outvn, glb)?;
        data.op_set_input(newop, vn, 0)?;
        if opc != OpCode::Cast {
            let zero = data.new_constant(4, 0, glb);
            data.op_set_input(newop, zero, 1)?;
        }
        data.op_set_output(op, vn, glb)?;
        data.op_insert_after(newop, op);
        if type_factory(glb).get(tokenct).needs_resolution() {
            data.force_facing_type(tokenct, -1, newop, 0, glb);
        }
        if type_factory(glb).get(out_high_type).needs_resolution() {
            data.inherit_union_field(out_high_type, newop, -1, op, -1, glb);
        }
        Ok(1)
    }

    pub fn cast_input(
        op: OpId,
        slot: i32,
        data: &mut Funcdata,
        glb: &mut Architecture,
        cast_strategy: &mut dyn CastStrategy,
    ) -> Result<i32> {
        let opc_code = data.op(op).code();
        let ct = {
            let strategy: &dyn CastStrategy = cast_strategy;
            with_type_op(glb, opc_code, |top, glb| {
                top.get_input_cast(op, slot, strategy, data, glb)
            })?
        };
        let ct = match ct {
            Some(ct) => ct,
            None => {
                let res_unsigned = cast_strategy.mark_explicit_unsigned(op, slot, data, glb)?;
                let res_sized = cast_strategy.mark_explicit_long_size(op, slot, data, glb)?;
                if res_unsigned || res_sized {
                    return Ok(1);
                }
                return Ok(0);
            }
        };
        let vn = data.op(op).get_in(slot);
        let mut vnin = vn;
        let vn_is_cast = match data.vn(vn).get_def() {
            Some(def) => data.vn(vn).is_written() && data.op(def).code() == OpCode::Cast,
            None => false,
        };
        if vn_is_cast {
            if data.vn(vn).is_implied() {
                if data.vn(vn).lone_descend() == Some(op) {
                    data.vn_update_type(vn, ct);
                    if data.vn(vn).get_type() == ct {
                        return Ok(1);
                    }
                }
                let def = data.vn(vn).get_def().expect("written varnode has no defining op");
                vnin = data.op(def).get_in(0);
                if ct == data.vn(vnin).get_type() {
                    data.op_set_input(op, vnin, slot)?;
                    return Ok(1);
                }
            }
        } else if data.vn(vn).is_constant() {
            data.vn_update_type(vn, ct);
            if data.vn(vn).get_type() == ct {
                return Ok(1);
            }
        } else if type_factory(glb).get(ct).get_metatype() == TypeMetatype::Ptr && {
            let readtype = data.vn_get_high_type_read_facing(vn, op, glb)?;
            ActionSetCasts::test_struct_offset0(glb, ct, readtype, cast_strategy)
        } {
            let newop = ActionSetCasts::insert_ptrsub_zero(op, slot, ct, data, glb)?;
            let high = data.vn(vn).get_high()?;
            let hightype = data.high_get_type(high, glb);
            if type_factory(glb).get(hightype).needs_resolution() {
                data.inherit_union_field(hightype, newop, 0, op, slot, glb);
            }
            return Ok(1);
        } else if data.op(op).code() != OpCode::Copy {
            if ActionSetCasts::try_resolution_adjustment(ct, op, slot, data, glb)? {
                return Ok(1);
            }
        } else if ActionSetCasts::try_resolution_copy(op, data, glb)? {
            return Ok(1);
        }
        let opaddr = data.op(op).get_addr().clone();
        let newop = data.new_op(1, &opaddr);
        let insize = data.vn(vnin).get_size();
        let vnout = data.new_unique_out(insize, newop, glb)?;
        data.vn_update_type(vnout, ct);
        data.vbank.get_mut(vnout).set_implied(&mut data.highs);
        data.op_set_opcode(newop, OpCode::Cast, glb);
        data.op_set_input(newop, vnin, 0)?;
        data.op_set_input(op, vnout, slot)?;
        data.op_insert_before(newop, op);
        if type_factory(glb).get(ct).needs_resolution() {
            data.force_facing_type(ct, -1, newop, -1, glb);
        }
        let high = data.vn(vn).get_high()?;
        let hightype = data.high_get_type(high, glb);
        if type_factory(glb).get(hightype).needs_resolution() {
            data.inherit_union_field(hightype, newop, 0, op, slot, glb);
        }
        Ok(1)
    }

    pub fn insert_ptrsub_zero(
        op: OpId,
        slot: i32,
        ct: TypeId,
        data: &mut Funcdata,
        glb: &mut Architecture,
    ) -> Result<OpId> {
        let vn = data.op(op).get_in(slot);
        let opaddr = data.op(op).get_addr().clone();
        let newop = data.new_op(2, &opaddr);
        let size = data.vn(vn).get_size();
        let vnout = data.new_unique_out(size, newop, glb)?;
        data.vn_update_type(vnout, ct);
        data.vbank.get_mut(vnout).set_implied(&mut data.highs);
        data.op_set_opcode(newop, OpCode::Ptrsub, glb);
        data.op_set_input(newop, vn, 0)?;
        let zero = data.new_constant(4, 0, glb);
        data.op_set_input(newop, zero, 1)?;
        data.op_set_input(op, vnout, slot)?;
        data.op_insert_before(newop, op);
        Ok(newop)
    }

    fn process_ops(
        &mut self,
        data: &mut Funcdata,
        glb: &mut Architecture,
        cast_strategy: &mut dyn CastStrategy,
    ) -> Result<()> {
        let size = data.block(data.bblocks).get_size();
        for index in 0..size {
            let bb = data.block(data.bblocks).get_block(index);
            let mut iter = data.block(bb).get_op_list().front();
            while let Some(op) = iter {
                if data.op(op).not_printed() {
                    iter = basic_next(data, op);
                    continue;
                }
                let opc = data.op(op).code();
                if opc == OpCode::Cast {
                    iter = basic_next(data, op);
                    continue;
                }
                if opc == OpCode::Ptradd {
                    let size = data.vn(data.op(op).get_in(2)).get_offset() as i32;
                    let ct = data.vn_get_high_type_read_facing(data.op(op).get_in(0), op, glb)?;
                    let ctdt = type_factory(glb).get(ct);
                    let fits = ctdt.get_metatype() == TypeMetatype::Ptr
                        && type_factory(glb).get(ctdt.get_ptr_to()).get_align_size() as i64
                            == AddrSpace::address_to_byte_int(size as i64, ctdt.get_word_size());
                    if !fits {
                        data.op_undo_ptradd(op, true, glb)?;
                    }
                } else if opc == OpCode::Ptrsub {
                    let readtype = data.vn_get_type_read_facing(data.op(op).get_in(0), op, glb);
                    let offset = data.vn(data.op(op).get_in(1)).get_offset();
                    if !type_factory(glb)
                        .get(readtype)
                        .is_ptrsub_matching(offset as i64, 0, 0, glb)
                    {
                        if offset == 0 {
                            data.op_remove_input(op, 1);
                            data.op_set_opcode(op, OpCode::Copy, glb);
                        } else {
                            data.op_set_opcode(op, OpCode::IntAdd, glb);
                        }
                    }
                }
                let mut slot = 0;
                while slot < data.op(op).num_input() {
                    self.base.count += ActionSetCasts::resolve_union(op, slot, data, glb, cast_strategy)?;
                    slot += 1;
                }
                let vn = data.op(op).get_out();
                if let Some(vn) = vn {
                    let high = data.vn(vn).get_high()?;
                    let out_high_type = data.high_get_type(high, glb);
                    if type_factory(glb).get(out_high_type).needs_resolution() {
                        Datatype::resolve_in_flow(out_high_type, op, -1, data, glb)?;
                    }
                }
                let mut slot = 0;
                while slot < data.op(op).num_input() {
                    self.base.count += ActionSetCasts::cast_input(op, slot, data, glb, cast_strategy)?;
                    slot += 1;
                }
                if opc == OpCode::Load {
                    let outvn = data.op(op).get_out().expect("LOAD has no output");
                    ActionSetCasts::check_pointer_issues(op, outvn, data, glb)?;
                } else if opc == OpCode::Store {
                    let valvn = data.op(op).get_in(2);
                    ActionSetCasts::check_pointer_issues(op, valvn, data, glb)?;
                }
                if vn.is_some() {
                    self.base.count += ActionSetCasts::cast_output(op, data, glb, cast_strategy)?;
                }
                iter = basic_next(data, op);
            }
        }
        Ok(())
    }
}

impl Action for ActionSetCasts {
    fn base(&self) -> &ActionBase {
        &self.base
    }

    fn base_mut(&mut self) -> &mut ActionBase {
        &mut self.base
    }

    fn clone_action(&self, grouplist: &ActionGroupList) -> Option<Box<dyn Action>> {
        if !grouplist.contains(self.get_group()) {
            return None;
        }
        Some(Box::new(ActionSetCasts::new(self.get_group())))
    }

    fn apply(&mut self, data: &mut Funcdata, glb: &mut Architecture) -> Result<i32> {
        data.start_cast_phase();
        let print = glb.print;
        let mut cast_strategy = glb.printlist[print]
            .as_mut()
            .expect("missing print language")
            .base_mut()
            .cast_strategy
            .take()
            .expect("print language has no cast strategy");
        let result = self.process_ops(data, glb, cast_strategy.as_mut());
        glb.printlist[print]
            .as_mut()
            .expect("missing print language")
            .base_mut()
            .cast_strategy = Some(cast_strategy);
        result?;
        Ok(0)
    }
}

pub struct ActionNameVars {
    pub base: ActionBase,
}

impl ActionNameVars {
    pub fn new(group: &str) -> ActionNameVars {
        ActionNameVars {
            base: ActionBase::new(RULE_ONCEPERFUNC, "namevars", group),
        }
    }

    pub fn make_rec(
        param: &ProtoParameter,
        vn: VarnodeId,
        recmap: &mut BTreeMap<HighId, OpRecommend>,
        data: &mut Funcdata,
        glb: &mut Architecture,
    ) -> Result<()> {
        if !param.is_name_locked(glb) {
            return Ok(());
        }
        if param.is_name_undefined(glb) {
            return Ok(());
        }
        if data.vn(vn).get_size() != param.get_size(glb) {
            return Ok(());
        }
        let mut vn = vn;
        let mut ct = Some(param.get_type(glb));
        if data.vn(vn).is_implied() && data.vn(vn).is_written() {
            let castop = data.vn(vn).get_def().expect("written varnode has no defining op");
            if data.op(castop).code() == OpCode::Cast {
                vn = data.op(castop).get_in(0);
                ct = None;
            }
        }
        let high = data.vn(vn).get_high()?;
        if data.high_is_addr_tied(high) {
            return Ok(());
        }
        let name = param.get_name(glb).to_string();
        if name.starts_with("param_") {
            return Ok(());
        }
        if let Some(rec) = recmap.get_mut(&high) {
            let ct = match ct {
                Some(ct) => ct,
                None => return Ok(()),
            };
            if let Some(oldtype) = rec.ct {
                let types = type_factory(glb);
                if types.get(oldtype).type_order(types.get(ct), types) <= 0 {
                    return Ok(());
                }
            }
            rec.ct = Some(ct);
            rec.namerec = name;
        } else {
            recmap.insert(high, OpRecommend { ct, namerec: name });
        }
        Ok(())
    }

    pub fn look_for_bad_jump_tables(data: &mut Funcdata, glb: &mut Architecture) -> Result<()> {
        let numfunc = data.num_calls();
        let localmap = data.get_scope_local().expect("function has no local scope");
        for index in 0..numfunc {
            let fc = data.get_call_specs(index);
            if !data.call_spec(fc).is_bad_jump_table() {
                continue;
            }
            let op = data.call_spec(fc).get_op();
            let mut vn = data.op(op).get_in(0);
            if data.vn(vn).is_implied() && data.vn(vn).is_written() {
                let castop = data.vn(vn).get_def().expect("written varnode has no defining op");
                if data.op(castop).code() == OpCode::Cast {
                    vn = data.op(castop).get_in(0);
                }
            }
            if data.vn(vn).is_free() {
                continue;
            }
            let high = data.vn(vn).get_high()?;
            let sym = match data.high_get_symbol(high, glb) {
                Some(sym) => sym,
                None => continue,
            };
            let db = symbol_table_mut(glb);
            if db.symbol(sym).is_name_locked() {
                continue;
            }
            let scope = db.symbol(sym).get_scope();
            if scope != localmap {
                continue;
            }
            let newname = db.scope_make_name_unique(localmap, "UNRECOVERED_JUMPTABLE")?;
            db.scope_rename_symbol(scope, sym, &newname)?;
        }
        Ok(())
    }

    pub fn look_for_func_param_names(data: &mut Funcdata, glb: &mut Architecture, varlist: &[VarnodeId]) -> Result<()> {
        let numfunc = data.num_calls();
        if numfunc == 0 {
            return Ok(());
        }
        let mut recmap: BTreeMap<HighId, OpRecommend> = BTreeMap::new();
        let localmap = data.get_scope_local().expect("function has no local scope");
        for index in 0..numfunc {
            let fc = data.get_call_specs(index);
            if !data.call_spec_mut(fc).is_input_locked(glb) {
                continue;
            }
            let op = data.call_spec(fc).get_op();
            let mut numparam = data.call_spec(fc).num_params(glb);
            if numparam >= data.op(op).num_input() {
                numparam = data.op(op).num_input() - 1;
            }
            for paramindex in 0..numparam {
                let param = data
                    .call_spec_mut(fc)
                    .get_param(paramindex, glb)
                    .expect("parameter is missing")
                    .clone();
                let vn = data.op(op).get_in(paramindex + 1);
                ActionNameVars::make_rec(&param, vn, &mut recmap, data, glb)?;
            }
        }
        if recmap.is_empty() {
            return Ok(());
        }
        for &vn in varlist.iter() {
            if data.vn(vn).is_free() {
                continue;
            }
            if data.vn(vn).is_input() {
                continue;
            }
            let high = data.vn(vn).get_high()?;
            if data.high(high).get_num_merge_classes() > 1 {
                continue;
            }
            let sym = match data.high_get_symbol(high, glb) {
                Some(sym) => sym,
                None => continue,
            };
            let db = symbol_table_mut(glb);
            if !db.symbol(sym).is_name_undefined() {
                continue;
            }
            if let Some(rec) = recmap.get(&high) {
                let scope = db.symbol(sym).get_scope();
                let newname = db.scope_make_name_unique(localmap, &rec.namerec)?;
                db.scope_rename_symbol(scope, sym, &newname)?;
            }
        }
        Ok(())
    }

    pub fn link_spacebase_symbol(
        vn: VarnodeId,
        data: &mut Funcdata,
        glb: &mut Architecture,
        namerec: &mut Vec<VarnodeId>,
    ) -> Result<()> {
        if !data.vn(vn).is_constant() && !data.vn(vn).is_input() {
            return Ok(());
        }
        let descend = data.vn(vn).descend().to_vec();
        for op in descend {
            if data.op(op).code() != OpCode::Ptrsub {
                continue;
            }
            let off_vn = data.op(op).get_in(1);
            let sym = data.link_symbol_reference(off_vn, glb)?;
            if let Some(sym) = sym
                && symbol_table(glb).symbol(sym).is_name_undefined()
            {
                namerec.push(off_vn);
            }
        }
        Ok(())
    }

    pub fn link_symbols(data: &mut Funcdata, glb: &mut Architecture, namerec: &mut Vec<VarnodeId>) -> Result<()> {
        let const_space = glb.manager.get_constant_space().expect("missing constant space");
        let enditer = data.end_loc_space(&const_space, glb);
        let mut iter = data.begin_loc_space(&const_space);
        while let Some((curvn, next)) = loc_step_until(data, &iter, &enditer) {
            iter = next;
            if data.vn(curvn).get_symbol_entry().is_some() {
                data.link_symbol(curvn, glb)?;
            } else if data.vn(curvn).is_spacebase() {
                ActionNameVars::link_spacebase_symbol(curvn, data, glb, namerec)?;
            }
        }
        let numspaces = glb.manager.num_spaces();
        for index in 0..numspaces {
            let spc = match glb.manager.get_space(index) {
                Some(spc) => spc,
                None => continue,
            };
            if spc.get_index() == const_space.get_index() {
                continue;
            }
            let enditer = data.end_loc_space(&spc, glb);
            let mut iter = data.begin_loc_space(&spc);
            while let Some((curvn, next)) = loc_step_until(data, &iter, &enditer) {
                iter = next;
                if data.vn(curvn).is_free() {
                    continue;
                }
                if data.vn(curvn).is_spacebase() {
                    ActionNameVars::link_spacebase_symbol(curvn, data, glb, namerec)?;
                }
                let curhigh = data.vn(curvn).get_high()?;
                let vn = data.high_get_name_representative(curhigh);
                if vn != curvn {
                    continue;
                }
                let high = data.vn(vn).get_high()?;
                if !data.high_has_name(high)? {
                    continue;
                }
                let sym = data.link_symbol(vn, glb)?;
                if let Some(sym) = sym {
                    if symbol_table(glb).symbol(sym).is_name_undefined() && data.high(high).get_symbol_offset() < 0 {
                        namerec.push(vn);
                    }
                    if symbol_table(glb).symbol(sym).is_size_type_locked() {
                        let symtype = symbol_table(glb)
                            .symbol(sym)
                            .get_type()
                            .expect("symbol has no data-type");
                        if data.vn(vn).get_size() == type_factory(glb).get(symtype).get_size() {
                            let hightype = data.high_get_type(high, glb);
                            let scope = symbol_table(glb).symbol(sym).get_scope();
                            let types = glb.types.as_deref().expect("missing type factory");
                            let db = glb.symboltab.as_deref_mut().expect("missing symbol table");
                            db.scope_override_size_lock_type(scope, sym, hightype, types)?;
                        }
                    }
                    let scope = symbol_table(glb).symbol(sym).get_scope();
                    if data.vn(vn).is_addr_tied() && !symbol_table(glb).scope(scope).is_global() {
                        data.high_finalize_datatype(high, glb)?;
                    }
                }
            }
        }
        Ok(())
    }
}

impl Action for ActionNameVars {
    fn base(&self) -> &ActionBase {
        &self.base
    }

    fn base_mut(&mut self) -> &mut ActionBase {
        &mut self.base
    }

    fn clone_action(&self, grouplist: &ActionGroupList) -> Option<Box<dyn Action>> {
        if !grouplist.contains(self.get_group()) {
            return None;
        }
        Some(Box::new(ActionNameVars::new(self.get_group())))
    }

    fn apply(&mut self, data: &mut Funcdata, glb: &mut Architecture) -> Result<i32> {
        let mut namerec: Vec<VarnodeId> = Vec::new();
        ActionNameVars::link_symbols(data, glb, &mut namerec)?;
        let localmap = data.get_scope_local().expect("function has no local scope");
        Database::local_recover_name_recommendations_for_symbols(glb, data, localmap)?;
        ActionNameVars::look_for_bad_jump_tables(data, glb)?;
        ActionNameVars::look_for_func_param_names(data, glb, &namerec)?;
        let mut base = 1;
        for &vn in namerec.iter() {
            let high = data.vn(vn).get_high()?;
            let sym = data.high_get_symbol(high, glb).expect("named high has no symbol");
            if symbol_table(glb).symbol(sym).is_name_undefined() {
                let scope = symbol_table(glb).symbol(sym).get_scope();
                let newname =
                    Database::scope_build_default_name(glb, Some(&mut *data), scope, sym, &mut base, Some(vn))?;
                symbol_table_mut(glb).scope_rename_symbol(scope, sym, &newname)?;
            }
        }
        Database::scope_assign_default_names(glb, Some(data), localmap, &mut base)?;
        Ok(0)
    }
}

pub struct ActionMarkExplicit {
    pub base: ActionBase,
}

impl ActionMarkExplicit {
    pub fn new(group: &str) -> ActionMarkExplicit {
        ActionMarkExplicit {
            base: ActionBase::new(RULE_ONCEPERFUNC, "markexplicit", group),
        }
    }

    pub fn base_explicit(data: &mut Funcdata, _glb: &mut Architecture, vn: VarnodeId, maxref: i32) -> Result<i32> {
        let mut maxref = maxref;
        let def = match data.vn(vn).get_def() {
            Some(def) => def,
            None => return Ok(-1),
        };
        if data.op(def).is_marker() {
            return Ok(-1);
        }
        if data.op(def).is_call() {
            if data.op(def).code() == OpCode::New && data.op(def).num_input() == 1 {
                return Ok(-2);
            }
            return Ok(-1);
        }
        if let Some(high) = data.vn(vn).get_high_option()
            && data.high(high).num_instances() > 1
        {
            return Ok(-1);
        }
        if data.vn(vn).is_addr_tied() {
            if data.op(def).code() == OpCode::Subpiece {
                let vin = data.op(def).get_in(0);
                if data.vn(vin).is_addr_tied() {
                    let overlap = data.vn(vn).overlap_join(data.vn(vin))?;
                    if overlap as i64 as u64 == data.vn(data.op(def).get_in(1)).get_offset() {
                        return Ok(-1);
                    }
                }
            }
            let use_op = match data.vn(vn).lone_descend() {
                Some(use_op) => use_op,
                None => return Ok(-1),
            };
            if data.op(use_op).code() == OpCode::IntZext {
                let vnout = data.op(use_op).get_out().expect("INT_ZEXT has no output");
                if !data.vn(vnout).is_addr_tied() || data.vn(vnout).contains(data.vn(vn)) != 0 {
                    return Ok(-1);
                }
            } else if data.op(use_op).code() == OpCode::Piece {
                let root_vn = PieceNode::find_root(data, vn)?;
                if vn == root_vn {
                    return Ok(-1);
                }
                let rootdef = data.vn(root_vn).get_def().expect("PIECE root has no defining op");
                if data.op(rootdef).is_partial_root() {
                    return Ok(-1);
                }
            } else {
                return Ok(-1);
            }
        } else if data.vn(vn).is_mapped() {
            return Ok(-1);
        } else if data.vn(vn).is_proto_partial() {
            return Ok(-1);
        } else if data.op(def).code() == OpCode::Piece && data.vn(data.op(def).get_in(0)).is_proto_partial() {
            return Ok(-1);
        }
        if data.vn(vn).has_no_descend() {
            return Ok(-1);
        }
        if data.op(def).code() == OpCode::Insert {
            let defout = data.op(def).get_out().expect("INSERT has no output");
            match data.vn(defout).lone_descend() {
                Some(store_op) if data.op(store_op).code() == OpCode::Store => {}
                _ => return Ok(-1),
            }
        }
        if data.op(def).code() == OpCode::Ptrsub {
            let basevn = data.op(def).get_in(0);
            if data.vn(basevn).is_spacebase() && (data.vn(basevn).is_constant() || data.vn(basevn).is_input()) {
                maxref = 1000000;
            }
        }
        let mut desccount = 0;
        for &op in data.vn(vn).descend() {
            if data.op(op).is_marker() {
                return Ok(-1);
            }
            desccount += 1;
            if desccount > maxref {
                return Ok(-1);
            }
        }
        Ok(desccount)
    }

    pub fn multiple_interaction(data: &mut Funcdata, _glb: &mut Architecture, multlist: &mut [VarnodeId]) -> i32 {
        let mut purgelist: Vec<VarnodeId> = Vec::new();
        for &vn in multlist.iter() {
            let op = data
                .vn(vn)
                .get_def()
                .expect("multiple descendant varnode has no defining op");
            let opc = data.op(op).code();
            if data.op(op).is_bool_output() || opc == OpCode::IntZext || opc == OpCode::IntSext || opc == OpCode::Ptradd
            {
                let mut maxparam = 2;
                if data.op(op).num_input() < maxparam {
                    maxparam = data.op(op).num_input();
                }
                for slot in 0..maxparam {
                    let topvn = data.op(op).get_in(slot);
                    if data.vn(topvn).is_mark() {
                        let mut topopc = OpCode::Copy;
                        if data.vn(topvn).is_written() {
                            let topdef = data.vn(topvn).get_def().expect("written varnode has no defining op");
                            if data.op(topdef).is_bool_output() {
                                continue;
                            }
                            topopc = data.op(topdef).code();
                        }
                        if opc == OpCode::Ptradd {
                            if topopc == OpCode::Ptradd {
                                purgelist.push(topvn);
                            }
                        } else {
                            purgelist.push(topvn);
                        }
                    }
                }
            }
        }
        for &vn in purgelist.iter() {
            data.vbank.get_mut(vn).set_explicit(&mut data.highs);
            data.vbank.get_mut(vn).clear_implied(&mut data.highs);
            data.vn_mut(vn).clear_mark();
        }
        purgelist.len() as i32
    }

    pub fn process_multiplier(data: &mut Funcdata, _glb: &mut Architecture, vn: VarnodeId, max: i32) {
        let mut opstack: Vec<OpStackElement> = Vec::new();
        let mut finalcount = 0;
        opstack.push(OpStackElement::new(vn, data));
        loop {
            let top = *opstack.last().expect("expression stack is empty");
            let vncur = top.vn;
            let isaterm = data.vn(vncur).is_explicit() || !data.vn(vncur).is_written();
            if isaterm || top.slotback <= top.slot {
                if isaterm && !data.vn(vncur).is_spacebase() {
                    finalcount += 1;
                }
                if finalcount > max {
                    data.vbank.get_mut(vn).set_explicit(&mut data.highs);
                    data.vbank.get_mut(vn).clear_implied(&mut data.highs);
                    return;
                }
                opstack.pop();
            } else {
                let op = data.vn(vncur).get_def().expect("written varnode has no defining op");
                let slot = top.slot;
                opstack.last_mut().expect("expression stack is empty").slot += 1;
                let newvn = data.op(op).get_in(slot);
                if data.vn(newvn).is_mark() {
                    data.vbank.get_mut(vn).set_explicit(&mut data.highs);
                    data.vbank.get_mut(vn).clear_implied(&mut data.highs);
                }
                opstack.push(OpStackElement::new(newvn, data));
            }
            if opstack.is_empty() {
                break;
            }
        }
    }

    pub fn check_new_to_constructor(data: &mut Funcdata, _glb: &mut Architecture, vn: VarnodeId) {
        let op = data.vn(vn).get_def().expect("NEW output has no defining op");
        let bb = data.op(op).get_parent();
        let mut firstuse: Option<OpId> = None;
        for &curop in data.vn(vn).descend() {
            if data.op(curop).get_parent() != bb {
                continue;
            }
            match firstuse {
                None => firstuse = Some(curop),
                Some(first) => {
                    if data.op(curop).get_seq_num().get_order() < data.op(first).get_seq_num().get_order() {
                        firstuse = Some(curop);
                    } else if data.op(curop).code() == OpCode::Callind {
                        let ptr = data.op(curop).get_in(0);
                        if data.vn(ptr).is_written() && data.vn(ptr).get_def() == Some(first) {
                            firstuse = Some(curop);
                        }
                    }
                }
            }
        }
        let firstuse = match firstuse {
            Some(firstuse) => firstuse,
            None => return,
        };
        if !data.op(firstuse).is_call() {
            return;
        }
        if data.op(firstuse).get_out().is_some() {
            return;
        }
        if data.op(firstuse).num_input() < 2 {
            return;
        }
        if data.op(firstuse).get_in(1) != vn {
            return;
        }
        data.op_mark_special_print(firstuse);
        data.op_mark_non_printing(op);
    }
}

impl Action for ActionMarkExplicit {
    fn base(&self) -> &ActionBase {
        &self.base
    }

    fn base_mut(&mut self) -> &mut ActionBase {
        &mut self.base
    }

    fn clone_action(&self, grouplist: &ActionGroupList) -> Option<Box<dyn Action>> {
        if !grouplist.contains(self.get_group()) {
            return None;
        }
        Some(Box::new(ActionMarkExplicit::new(self.get_group())))
    }

    fn apply(&mut self, data: &mut Funcdata, glb: &mut Architecture) -> Result<i32> {
        let mut multlist: Vec<VarnodeId> = Vec::new();
        let maxref = glb.max_implied_ref;
        let enditer = data.begin_def_flags(0)?;
        let begin = data.begin_def();
        for vn in data.vbank.def_range(&begin, &enditer) {
            let desccount = ActionMarkExplicit::base_explicit(data, glb, vn, maxref)?;
            if desccount < 0 {
                data.vbank.get_mut(vn).set_explicit(&mut data.highs);
                self.base.count += 1;
                if desccount < -1 {
                    ActionMarkExplicit::check_new_to_constructor(data, glb, vn);
                }
            } else if desccount > 1 {
                data.vn_mut(vn).set_mark();
                multlist.push(vn);
            }
        }
        self.base.count += ActionMarkExplicit::multiple_interaction(data, glb, &mut multlist);
        let maxdup = glb.max_term_duplication;
        for &vn in multlist.iter() {
            if data.vn(vn).is_mark() {
                ActionMarkExplicit::process_multiplier(data, glb, vn, maxdup);
            }
        }
        for &vn in multlist.iter() {
            data.vn_mut(vn).clear_mark();
        }
        Ok(0)
    }
}

pub struct ActionMarkImplied {
    pub base: ActionBase,
}

impl ActionMarkImplied {
    pub fn new(group: &str) -> ActionMarkImplied {
        ActionMarkImplied {
            base: ActionBase::new(RULE_ONCEPERFUNC, "markimplied", group),
        }
    }

    pub fn is_possible_alias_step(data: &Funcdata, vn1: VarnodeId, vn2: VarnodeId) -> bool {
        let var = [vn1, vn2];
        for index in 0..2 {
            let vncur = var[index];
            if !data.vn(vncur).is_written() {
                continue;
            }
            let op = data.vn(vncur).get_def().expect("written varnode has no defining op");
            let opc = data.op(op).code();
            if opc != OpCode::IntAdd && opc != OpCode::Ptrsub && opc != OpCode::Ptradd && opc != OpCode::IntXor {
                continue;
            }
            if var[1 - index] != data.op(op).get_in(0) {
                continue;
            }
            if data.vn(data.op(op).get_in(1)).is_constant() {
                return false;
            }
        }
        true
    }

    pub fn is_possible_alias(data: &Funcdata, vn1: VarnodeId, vn2: VarnodeId, depth: i32) -> bool {
        if vn1 == vn2 {
            return true;
        }
        if !data.vn(vn1).is_written() || !data.vn(vn2).is_written() {
            if data.vn(vn1).is_constant() && data.vn(vn2).is_constant() {
                return data.vn(vn1).get_offset() == data.vn(vn2).get_offset();
            }
            return ActionMarkImplied::is_possible_alias_step(data, vn1, vn2);
        }
        if !ActionMarkImplied::is_possible_alias_step(data, vn1, vn2) {
            return false;
        }
        let op1 = data.vn(vn1).get_def().expect("written varnode has no defining op");
        let op2 = data.vn(vn2).get_def().expect("written varnode has no defining op");
        let mut opc1 = data.op(op1).code();
        let mut opc2 = data.op(op2).code();
        let mut mult1: i32 = 1;
        let mut mult2: i32 = 1;
        if opc1 == OpCode::Ptrsub {
            opc1 = OpCode::IntAdd;
        } else if opc1 == OpCode::Ptradd {
            opc1 = OpCode::IntAdd;
            mult1 = data.vn(data.op(op1).get_in(2)).get_offset() as i32;
        }
        if opc2 == OpCode::Ptrsub {
            opc2 = OpCode::IntAdd;
        } else if opc2 == OpCode::Ptradd {
            opc2 = OpCode::IntAdd;
            mult2 = data.vn(data.op(op2).get_in(2)).get_offset() as i32;
        }
        if opc1 != opc2 {
            return true;
        }
        if depth == 0 {
            return true;
        }
        let depth = depth - 1;
        match opc1 {
            OpCode::Copy | OpCode::IntZext | OpCode::IntSext | OpCode::Int2comp | OpCode::IntNegate => {
                return ActionMarkImplied::is_possible_alias(
                    data,
                    data.op(op1).get_in(0),
                    data.op(op2).get_in(0),
                    depth,
                );
            }
            OpCode::IntAdd => {
                let cvn1 = data.op(op1).get_in(1);
                let cvn2 = data.op(op2).get_in(1);
                let in10 = data.op(op1).get_in(0);
                let in20 = data.op(op2).get_in(0);
                if data.vn(cvn1).is_constant() && data.vn(cvn2).is_constant() {
                    let val1 = (mult1 as i64 as u64).wrapping_mul(data.vn(cvn1).get_offset());
                    let val2 = (mult2 as i64 as u64).wrapping_mul(data.vn(cvn2).get_offset());
                    if val1 == val2 {
                        return ActionMarkImplied::is_possible_alias(data, in10, in20, depth);
                    }
                    return !functional_equality(in10, in20, data);
                }
                if mult1 != mult2 {
                    return true;
                }
                if functional_equality(in10, in20, data) {
                    return ActionMarkImplied::is_possible_alias(data, cvn1, cvn2, depth);
                }
                if functional_equality(cvn1, cvn2, data) {
                    return ActionMarkImplied::is_possible_alias(data, in10, in20, depth);
                }
                if functional_equality(in10, cvn2, data) {
                    return ActionMarkImplied::is_possible_alias(data, cvn1, in20, depth);
                }
                if functional_equality(cvn1, in20, data) {
                    return ActionMarkImplied::is_possible_alias(data, in10, cvn2, depth);
                }
            }
            _ => {}
        }
        true
    }

    pub fn check_implied_cover(data: &mut Funcdata, _glb: &mut Architecture, vn: VarnodeId) -> Result<bool> {
        let op = data.vn(vn).get_def().expect("implied candidate has no defining op");
        if data.op(op).code() == OpCode::Load {
            let mut oiter = data.begin_op(OpCode::Store);
            while let Some(storeop) = oiter {
                oiter = data.obank.next_in_list(storeop, PcodeOp::CODE_LIST);
                if data.op(storeop).is_dead() {
                    continue;
                }
                data.vn_update_cover(vn);
                let crosses = data
                    .vn(vn)
                    .get_cover_raw()
                    .expect("varnode has no cover")
                    .contain(storeop, 2, data);
                if crosses
                    && data.vn(data.op(storeop).get_in(0)).get_offset() == data.vn(data.op(op).get_in(0)).get_offset()
                    && ActionMarkImplied::is_possible_alias(data, data.op(storeop).get_in(1), data.op(op).get_in(1), 2)
                {
                    return Ok(false);
                }
            }
        }
        if data.op(op).is_call() || data.op(op).code() == OpCode::Load {
            for index in 0..data.num_calls() {
                let callop = data.call_spec(data.get_call_specs(index)).get_op();
                data.vn_update_cover(vn);
                if data
                    .vn(vn)
                    .get_cover_raw()
                    .expect("varnode has no cover")
                    .contain(callop, 2, data)
                {
                    return Ok(false);
                }
            }
        }
        for slot in 0..data.op(op).num_input() {
            let defvn = data.op(op).get_in(slot);
            if data.vn(defvn).is_constant() {
                continue;
            }
            let high = data.vn(vn).get_high()?;
            if Merge::inflate_test(data, defvn, high)? {
                return Ok(false);
            }
        }
        Ok(true)
    }
}

impl Action for ActionMarkImplied {
    fn base(&self) -> &ActionBase {
        &self.base
    }

    fn base_mut(&mut self) -> &mut ActionBase {
        &mut self.base
    }

    fn clone_action(&self, grouplist: &ActionGroupList) -> Option<Box<dyn Action>> {
        if !grouplist.contains(self.get_group()) {
            return None;
        }
        Some(Box::new(ActionMarkImplied::new(self.get_group())))
    }

    fn apply(&mut self, data: &mut Funcdata, glb: &mut Architecture) -> Result<i32> {
        let mut varstack: Vec<DescTreeElement> = Vec::new();
        let begin = data.begin_loc();
        let end = data.end_loc();
        for vn in data.vbank.loc_range(&begin, &end) {
            if data.vn(vn).is_free() {
                continue;
            }
            if data.vn(vn).is_explicit() {
                continue;
            }
            if data.vn(vn).is_implied() {
                continue;
            }
            varstack.push(DescTreeElement::new(vn));
            loop {
                let top = *varstack.last().expect("varnode stack is empty");
                let vncur = top.vn;
                if top.desciter == data.vn(vncur).descend().len() {
                    self.base.count += 1;
                    if !ActionMarkImplied::check_implied_cover(data, glb, vncur)? {
                        data.vbank.get_mut(vncur).set_explicit(&mut data.highs);
                    } else {
                        Merge::mark_implied(data, vncur);
                    }
                    varstack.pop();
                } else {
                    let descop = data.vn(vncur).descend()[top.desciter];
                    varstack.last_mut().expect("varnode stack is empty").desciter += 1;
                    if let Some(outvn) = data.op(descop).get_out()
                        && !data.vn(outvn).is_explicit()
                        && !data.vn(outvn).is_implied()
                    {
                        varstack.push(DescTreeElement::new(outvn));
                    }
                }
                if varstack.is_empty() {
                    break;
                }
            }
        }
        Ok(0)
    }
}

pub struct ActionUnreachable {
    pub base: ActionBase,
}

impl ActionUnreachable {
    pub fn new(group: &str) -> ActionUnreachable {
        ActionUnreachable {
            base: ActionBase::new(0, "unreachable", group),
        }
    }
}

impl Action for ActionUnreachable {
    fn base(&self) -> &ActionBase {
        &self.base
    }

    fn base_mut(&mut self) -> &mut ActionBase {
        &mut self.base
    }

    fn clone_action(&self, grouplist: &ActionGroupList) -> Option<Box<dyn Action>> {
        if !grouplist.contains(self.get_group()) {
            return None;
        }
        Some(Box::new(ActionUnreachable::new(self.get_group())))
    }

    fn apply(&mut self, data: &mut Funcdata, glb: &mut Architecture) -> Result<i32> {
        if data.remove_unreachable_blocks(true, false, glb)? {
            self.base.count += 1;
        }
        Ok(0)
    }
}

pub struct ActionDoNothing {
    pub base: ActionBase,
}

impl ActionDoNothing {
    pub fn new(group: &str) -> ActionDoNothing {
        ActionDoNothing {
            base: ActionBase::new(RULE_REPEATAPPLY, "donothing", group),
        }
    }
}

impl Action for ActionDoNothing {
    fn base(&self) -> &ActionBase {
        &self.base
    }

    fn base_mut(&mut self) -> &mut ActionBase {
        &mut self.base
    }

    fn clone_action(&self, grouplist: &ActionGroupList) -> Option<Box<dyn Action>> {
        if !grouplist.contains(self.get_group()) {
            return None;
        }
        Some(Box::new(ActionDoNothing::new(self.get_group())))
    }

    fn apply(&mut self, data: &mut Funcdata, glb: &mut Architecture) -> Result<i32> {
        let mut index = 0;
        while index < data.block(data.bblocks).get_size() {
            let bb = data.block(data.bblocks).get_block(index);
            index += 1;
            data.block_mut(bb).clear_delayed_donothing();
            if !data.block_is_do_nothing(bb) {
                continue;
            }
            if data.block(bb).size_out() == 1 && data.block(bb).get_out(0) == bb {
                if !data.block(bb).is_donothing_loop() {
                    data.block_mut(bb).set_donothing_loop();
                    let start = data.block(bb).get_start();
                    data.warning("Do nothing block with infinite loop", &start, glb);
                }
            } else if data.block_unblocked_multi(bb, 0) {
                if data.is_normalization_on() || data.block_has_no_immediate_copy(bb, 0) {
                    data.remove_do_nothing_block(bb, glb)?;
                    self.base.count += 1;
                    return Ok(0);
                } else {
                    data.block_mut(bb).set_delayed_donothing();
                }
            }
        }
        Ok(0)
    }
}

pub struct ActionLateDoNothing {
    pub base: ActionBase,
}

impl ActionLateDoNothing {
    pub fn new(group: &str) -> ActionLateDoNothing {
        ActionLateDoNothing {
            base: ActionBase::new(0, "latedonothing", group),
        }
    }

    pub fn removing_creates_redundancy(data: &Funcdata, bl: BlockId) -> bool {
        let outbl = data.block(bl).get_out(0);
        for index in 0..data.block(bl).size_in() {
            let inbl = data.block(bl).get_in(index);
            if data.block(inbl).size_out() == 1 {
                continue;
            }
            let mut count = 0;
            while count < data.block(inbl).size_out() {
                let curbl = data.block(inbl).get_out(count);
                if curbl != bl && curbl != outbl {
                    break;
                }
                count += 1;
            }
            if count == data.block(inbl).size_out() {
                return true;
            }
        }
        false
    }
}

impl Action for ActionLateDoNothing {
    fn base(&self) -> &ActionBase {
        &self.base
    }

    fn base_mut(&mut self) -> &mut ActionBase {
        &mut self.base
    }

    fn clone_action(&self, grouplist: &ActionGroupList) -> Option<Box<dyn Action>> {
        if !grouplist.contains(self.get_group()) {
            return None;
        }
        Some(Box::new(ActionLateDoNothing::new(self.get_group())))
    }

    fn apply(&mut self, data: &mut Funcdata, glb: &mut Architecture) -> Result<i32> {
        let mut remove_list: Vec<BlockId> = Vec::new();
        for index in 0..data.block(data.bblocks).get_size() {
            let bb = data.block(data.bblocks).get_block(index);
            if !data.block(bb).is_delayed_donothing() {
                continue;
            }
            if !data.block_is_do_nothing(bb) {
                continue;
            }
            if ActionLateDoNothing::removing_creates_redundancy(data, bb) {
                continue;
            }
            if data.block(bb).size_out() == 1 && data.block(bb).get_out(0) == bb {
                if !data.block(bb).is_donothing_loop() {
                    data.block_mut(bb).set_donothing_loop();
                    let start = data.block(bb).get_start();
                    data.warning("Do nothing block with infinite loop", &start, glb);
                }
            } else if data.block_unblocked_multi(bb, 0) {
                remove_list.push(bb);
            }
        }
        for &bb in remove_list.iter() {
            data.remove_do_nothing_block(bb, glb)?;
            self.base.count += 1;
        }
        Ok(0)
    }
}

pub struct ActionRedundBranch {
    pub base: ActionBase,
}

impl ActionRedundBranch {
    pub fn new(group: &str) -> ActionRedundBranch {
        ActionRedundBranch {
            base: ActionBase::new(0, "redundbranch", group),
        }
    }
}

impl Action for ActionRedundBranch {
    fn base(&self) -> &ActionBase {
        &self.base
    }

    fn base_mut(&mut self) -> &mut ActionBase {
        &mut self.base
    }

    fn clone_action(&self, grouplist: &ActionGroupList) -> Option<Box<dyn Action>> {
        if !grouplist.contains(self.get_group()) {
            return None;
        }
        Some(Box::new(ActionRedundBranch::new(self.get_group())))
    }

    fn apply(&mut self, data: &mut Funcdata, glb: &mut Architecture) -> Result<i32> {
        let mut index: i32 = 0;
        while index < data.block(data.bblocks).get_size() {
            let bb = data.block(data.bblocks).get_block(index);
            index += 1;
            if data.block(bb).size_out() == 0 {
                continue;
            }
            let bl = data.block(bb).get_out(0);
            if data.block(bb).size_out() == 1 {
                if data.block(bl).size_in() == 1 && !data.block(bl).is_entry_point() && !data.block(bb).is_switch_out()
                {
                    data.splice_block_basic(bb, glb)?;
                    self.base.count += 1;
                    index = 0;
                }
                continue;
            }
            let mut slot = 1;
            while slot < data.block(bb).size_out() {
                if data.block(bb).get_out(slot) != bl {
                    break;
                }
                slot += 1;
            }
            if slot != data.block(bb).size_out() {
                continue;
            }
            data.remove_branch(bb, 1, glb)?;
            self.base.count += 1;
        }
        Ok(0)
    }
}

pub struct ActionDeterminedBranch {
    pub base: ActionBase,
}

impl ActionDeterminedBranch {
    pub fn new(group: &str) -> ActionDeterminedBranch {
        ActionDeterminedBranch {
            base: ActionBase::new(0, "determinedbranch", group),
        }
    }
}

impl Action for ActionDeterminedBranch {
    fn base(&self) -> &ActionBase {
        &self.base
    }

    fn base_mut(&mut self) -> &mut ActionBase {
        &mut self.base
    }

    fn clone_action(&self, grouplist: &ActionGroupList) -> Option<Box<dyn Action>> {
        if !grouplist.contains(self.get_group()) {
            return None;
        }
        Some(Box::new(ActionDeterminedBranch::new(self.get_group())))
    }

    fn apply(&mut self, data: &mut Funcdata, glb: &mut Architecture) -> Result<i32> {
        let mut index = 0;
        while index < data.block(data.bblocks).get_size() {
            let bb = data.block(data.bblocks).get_block(index);
            index += 1;
            let cbranch = match data.block_last_op(bb) {
                Some(cbranch) => cbranch,
                None => continue,
            };
            if data.op(cbranch).code() != OpCode::Cbranch {
                continue;
            }
            let condvn = data.op(cbranch).get_in(1);
            if !data.vn(condvn).is_constant() {
                continue;
            }
            let val = data.vn(condvn).get_offset();
            let num = if (val != 0) != data.op(cbranch).is_boolean_flip() {
                0
            } else {
                1
            };
            data.remove_branch(bb, num, glb)?;
            self.base.count += 1;
        }
        Ok(0)
    }
}

pub struct ActionDeadCode {
    pub base: ActionBase,
}

impl ActionDeadCode {
    pub fn new(group: &str) -> ActionDeadCode {
        ActionDeadCode {
            base: ActionBase::new(0, "deadcode", group),
        }
    }

    pub fn push_consumed(data: &mut Funcdata, val: u64, vn: VarnodeId, worklist: &mut Vec<VarnodeId>) {
        let newval = (val | data.vn(vn).get_consume()) & calc_mask(data.vn(vn).get_size());
        if newval == data.vn(vn).get_consume() && data.vn(vn).is_consume_vacuous() {
            return;
        }
        data.vn_mut(vn).set_consume_vacuous();
        if !data.vn(vn).is_consume_list() {
            data.vn_mut(vn).set_consume_list();
            if data.vn(vn).is_written() {
                worklist.push(vn);
            }
        }
        data.vn_mut(vn).set_consume(newval);
    }

    pub fn propagate_consumed(data: &mut Funcdata, _glb: &mut Architecture, worklist: &mut Vec<VarnodeId>) {
        let vn = worklist.pop().expect("consume worklist is empty");
        let outc = data.vn(vn).get_consume();
        data.vn_mut(vn).clear_consume_list();
        let op = data.vn(vn).get_def().expect("consumed varnode has no defining op");
        let in0 = data.op(op).get_in_option(0);
        let in1 = data.op(op).get_in_option(1);
        let first_consume: u64;
        let second_consume: u64;
        match data.op(op).code() {
            OpCode::IntMult => {
                let in0 = in0.expect("op input is missing");
                let in1 = in1.expect("op input is missing");
                second_consume = coveringmask(outc);
                if data.vn(in1).is_constant() {
                    let least_set = leastsigbit_set(data.vn(in1).get_offset());
                    if least_set >= 0 {
                        first_consume = (calc_mask(data.vn(vn).get_size()) >> least_set) & second_consume;
                    } else {
                        first_consume = 0;
                    }
                } else {
                    first_consume = second_consume;
                }
                ActionDeadCode::push_consumed(data, first_consume, in0, worklist);
                ActionDeadCode::push_consumed(data, second_consume, in1, worklist);
            }
            OpCode::IntAdd | OpCode::IntSub => {
                first_consume = coveringmask(outc);
                ActionDeadCode::push_consumed(data, first_consume, in0.expect("op input is missing"), worklist);
                ActionDeadCode::push_consumed(data, first_consume, in1.expect("op input is missing"), worklist);
            }
            OpCode::Subpiece => {
                let in0 = in0.expect("op input is missing");
                let in1 = in1.expect("op input is missing");
                let size = data.vn(in1).get_offset() as i32;
                let mut value = if size >= 8 {
                    0
                } else {
                    outc.wrapping_shl((size * 8) as u32)
                };
                if value == 0 && outc != 0 && data.vn(in0).get_size() > 8 {
                    value = !0u64;
                    value ^= value >> 1;
                }
                second_consume = if outc == 0 { 0 } else { !0u64 };
                ActionDeadCode::push_consumed(data, value, in0, worklist);
                ActionDeadCode::push_consumed(data, second_consume, in1, worklist);
            }
            OpCode::Piece => {
                let in0 = in0.expect("op input is missing");
                let in1 = in1.expect("op input is missing");
                let size = data.vn(in1).get_size();
                let value;
                let low;
                if data.vn(vn).get_size() > 8 {
                    if size >= 8 {
                        value = !0u64;
                        low = outc;
                    } else {
                        value = outc.wrapping_shr((size * 8) as u32) ^ (!0u64).wrapping_shl((8 * (8 - size)) as u32);
                        low = outc ^ value.wrapping_shl((size * 8) as u32);
                    }
                } else {
                    value = outc.wrapping_shr((size * 8) as u32);
                    low = outc ^ value.wrapping_shl((size * 8) as u32);
                }
                ActionDeadCode::push_consumed(data, value, in0, worklist);
                ActionDeadCode::push_consumed(data, low, in1, worklist);
            }
            OpCode::Indirect => {
                let in0 = in0.expect("op input is missing");
                let in1 = in1.expect("op input is missing");
                ActionDeadCode::push_consumed(data, outc, in0, worklist);
                if space_type_of(data, in1) == Some(SpaceType::Iop) {
                    let indop = PcodeOp::get_op_from_const(data.vn(in1).get_addr());
                    if !data.op(indop).is_dead() {
                        if data.op(indop).code() == OpCode::Copy {
                            let indout = data.op(indop).get_out().expect("COPY has no output");
                            let opout = data.op(op).get_out().expect("INDIRECT has no output");
                            if data.vn(indout).characterize_overlap(data.vn(opout)) > 0 {
                                ActionDeadCode::push_consumed(data, !0u64, indout, worklist);
                                data.op_mut(indop).set_indirect_source();
                            }
                        } else {
                            data.op_mut(indop).set_indirect_source();
                        }
                    }
                }
            }
            OpCode::Copy | OpCode::IntNegate => {
                ActionDeadCode::push_consumed(data, outc, in0.expect("op input is missing"), worklist);
            }
            OpCode::IntXor | OpCode::IntOr => {
                ActionDeadCode::push_consumed(data, outc, in0.expect("op input is missing"), worklist);
                ActionDeadCode::push_consumed(data, outc, in1.expect("op input is missing"), worklist);
            }
            OpCode::IntAnd => {
                let in0 = in0.expect("op input is missing");
                let in1 = in1.expect("op input is missing");
                if data.vn(in1).is_constant() {
                    let val = data.vn(in1).get_offset();
                    ActionDeadCode::push_consumed(data, outc & val, in0, worklist);
                    ActionDeadCode::push_consumed(data, outc, in1, worklist);
                } else {
                    ActionDeadCode::push_consumed(data, outc, in0, worklist);
                    ActionDeadCode::push_consumed(data, outc, in1, worklist);
                }
            }
            OpCode::Multiequal => {
                for slot in 0..data.op(op).num_input() {
                    let invn = data.op(op).get_in(slot);
                    ActionDeadCode::push_consumed(data, outc, invn, worklist);
                }
            }
            OpCode::IntZext => {
                ActionDeadCode::push_consumed(data, outc, in0.expect("op input is missing"), worklist);
            }
            OpCode::IntSext => {
                let in0 = in0.expect("op input is missing");
                second_consume = calc_mask(data.vn(in0).get_size());
                let mut value = outc & second_consume;
                if outc > second_consume {
                    value |= second_consume ^ (second_consume >> 1);
                }
                ActionDeadCode::push_consumed(data, value, in0, worklist);
            }
            OpCode::IntLeft => {
                let in0 = in0.expect("op input is missing");
                let in1 = in1.expect("op input is missing");
                if data.vn(in1).is_constant() {
                    let mut size = data.vn(vn).get_size();
                    let sa = data.vn(in1).get_offset() as i32;
                    let mut value;
                    if size > 8 {
                        if sa >= 64 {
                            value = !0u64;
                        } else if sa == 0 {
                            value = outc;
                        } else {
                            value = outc.wrapping_shr(sa as u32) ^ (!0u64).wrapping_shl((64 - sa) as u32);
                        }
                        size = 8 * size - sa;
                        if size < 64 {
                            let mask = (!0u64).wrapping_shl(size as u32);
                            value &= !mask;
                        }
                    } else {
                        value = outc.wrapping_shr(sa as u32);
                    }
                    second_consume = if outc == 0 { 0 } else { !0u64 };
                    ActionDeadCode::push_consumed(data, value, in0, worklist);
                    ActionDeadCode::push_consumed(data, second_consume, in1, worklist);
                } else {
                    first_consume = if outc == 0 { 0 } else { !0u64 };
                    ActionDeadCode::push_consumed(data, first_consume, in0, worklist);
                    ActionDeadCode::push_consumed(data, first_consume, in1, worklist);
                }
            }
            OpCode::IntRight => {
                let in0 = in0.expect("op input is missing");
                let in1 = in1.expect("op input is missing");
                if data.vn(in1).is_constant() {
                    let sa = data.vn(in1).get_offset() as i32;
                    let value = if sa >= 64 { 0 } else { outc.wrapping_shl(sa as u32) };
                    second_consume = if outc == 0 { 0 } else { !0u64 };
                    ActionDeadCode::push_consumed(data, value, in0, worklist);
                    ActionDeadCode::push_consumed(data, second_consume, in1, worklist);
                } else {
                    first_consume = if outc == 0 { 0 } else { !0u64 };
                    ActionDeadCode::push_consumed(data, first_consume, in0, worklist);
                    ActionDeadCode::push_consumed(data, first_consume, in1, worklist);
                }
            }
            OpCode::IntLess | OpCode::IntLessequal | OpCode::IntEqual | OpCode::IntNotequal => {
                let in0 = in0.expect("op input is missing");
                let in1 = in1.expect("op input is missing");
                first_consume = if outc == 0 {
                    0
                } else {
                    data.vn(in0).get_nz_mask() | data.vn(in1).get_nz_mask()
                };
                ActionDeadCode::push_consumed(data, first_consume, in0, worklist);
                ActionDeadCode::push_consumed(data, first_consume, in1, worklist);
            }
            OpCode::Insert => {
                let in0 = in0.expect("op input is missing");
                let in1 = in1.expect("op input is missing");
                let in2 = data.op(op).get_in(2);
                let in3 = data.op(op).get_in(3);
                let mut value: u64 = 1;
                value = value.wrapping_shl(data.vn(in3).get_offset() as i32 as u32);
                value = value.wrapping_sub(1);
                ActionDeadCode::push_consumed(data, value, in1, worklist);
                value = value.wrapping_shl(data.vn(in2).get_offset() as i32 as u32);
                ActionDeadCode::push_consumed(data, outc & !value, in0, worklist);
                second_consume = if outc == 0 { 0 } else { !0u64 };
                ActionDeadCode::push_consumed(data, second_consume, in2, worklist);
                ActionDeadCode::push_consumed(data, second_consume, in3, worklist);
            }
            OpCode::Zpull | OpCode::Spull => {
                let in0 = in0.expect("op input is missing");
                let in1 = in1.expect("op input is missing");
                let in2 = data.op(op).get_in(2);
                let mut value: u64 = 1;
                value = value.wrapping_shl(data.vn(in2).get_offset() as i32 as u32);
                value = value.wrapping_sub(1);
                value &= outc;
                value = value.wrapping_shl(data.vn(in1).get_offset() as i32 as u32);
                ActionDeadCode::push_consumed(data, value, in0, worklist);
                second_consume = if outc == 0 { 0 } else { !0u64 };
                ActionDeadCode::push_consumed(data, second_consume, in1, worklist);
                ActionDeadCode::push_consumed(data, second_consume, in2, worklist);
            }
            OpCode::Popcount | OpCode::Lzcount => {
                let in0 = in0.expect("op input is missing");
                let mut value = (16 * data.vn(in0).get_size() - 1) as i64 as u64;
                value &= outc;
                second_consume = if value == 0 { 0 } else { !0u64 };
                ActionDeadCode::push_consumed(data, second_consume, in0, worklist);
            }
            OpCode::Call | OpCode::Callind => {}
            OpCode::FloatInt2float => {
                let in0 = in0.expect("op input is missing");
                let mut value = 0;
                if outc != 0 {
                    value = coveringmask(data.vn(in0).get_nz_mask());
                }
                ActionDeadCode::push_consumed(data, value, in0, worklist);
            }
            _ => {
                first_consume = if outc == 0 { 0 } else { !0u64 };
                for slot in 0..data.op(op).num_input() {
                    let invn = data.op(op).get_in(slot);
                    ActionDeadCode::push_consumed(data, first_consume, invn, worklist);
                }
            }
        }
    }

    pub fn never_consumed(vn: VarnodeId, data: &mut Funcdata, glb: &mut Architecture) -> Result<bool> {
        if data.vn(vn).get_size() > 8 {
            return Ok(false);
        }
        while let Some(&op) = data.vn(vn).descend().first() {
            let slot = data.op(op).get_slot(vn);
            let size = data.vn(vn).get_size();
            let zero = data.new_constant(size, 0, glb);
            data.op_set_input(op, zero, slot)?;
        }
        let op = data.vn(vn).get_def().expect("unconsumed varnode has no defining op");
        if data.op(op).is_call() {
            data.op_unset_output(op)?;
        } else {
            data.op_destroy(op)?;
        }
        Ok(true)
    }

    pub fn mark_consumed_parameters(
        fc: CallSpecId,
        data: &mut Funcdata,
        glb: &mut Architecture,
        worklist: &mut Vec<VarnodeId>,
    ) {
        let call_op = data.call_spec(fc).get_op();
        let target = data.op(call_op).get_in(0);
        ActionDeadCode::push_consumed(data, !0u64, target, worklist);
        if data.call_spec_mut(fc).is_input_locked(glb) || data.call_spec(fc).is_input_active() {
            for slot in 1..data.op(call_op).num_input() {
                let invn = data.op(call_op).get_in(slot);
                ActionDeadCode::push_consumed(data, !0u64, invn, worklist);
            }
            return;
        }
        for slot in 1..data.op(call_op).num_input() {
            let vn = data.op(call_op).get_in(slot);
            let mut consume_val = if data.vn(vn).is_auto_live() {
                !0u64
            } else {
                minimalmask(data.vn(vn).get_nz_mask())
            };
            let bytes_consumed = data.call_spec(fc).get_input_bytes_consumed(slot);
            if bytes_consumed != 0 {
                consume_val &= calc_mask(bytes_consumed);
            }
            ActionDeadCode::push_consumed(data, consume_val, vn, worklist);
        }
    }

    pub fn gather_consumed_return(data: &mut Funcdata, glb: &mut Architecture) -> u64 {
        if data.get_func_proto().is_output_locked(glb) || data.get_active_output().is_some() {
            return !0u64;
        }
        let mut consume_val: u64 = 0;
        let mut iter = data.begin_op(OpCode::Return);
        while let Some(return_op) = iter {
            iter = data.obank.next_in_list(return_op, PcodeOp::CODE_LIST);
            if data.op(return_op).is_dead() {
                continue;
            }
            if data.op(return_op).num_input() > 1 {
                let vn = data.op(return_op).get_in(1);
                consume_val |= minimalmask(data.vn(vn).get_nz_mask());
            }
        }
        let val = data.get_func_proto().get_return_bytes_consumed();
        if val != 0 {
            consume_val &= calc_mask(val);
        }
        consume_val
    }

    pub fn last_chance_load(data: &mut Funcdata, _glb: &mut Architecture, worklist: &mut Vec<VarnodeId>) -> bool {
        if data.get_heritage_pass() > 1 {
            return false;
        }
        if data.is_jumptable_recovery_on() {
            return false;
        }
        let mut res = false;
        let mut iter = data.begin_op(OpCode::Load);
        while let Some(op) = iter {
            iter = data.obank.next_in_list(op, PcodeOp::CODE_LIST);
            if data.op(op).is_dead() {
                continue;
            }
            let vn = data.op(op).get_out().expect("LOAD has no output");
            if data.vn(vn).is_consume_vacuous() {
                continue;
            }
            if data.vn_is_eventual_constant(data.op(op).get_in(1), 3, 1) {
                ActionDeadCode::push_consumed(data, !0u64, vn, worklist);
                data.vn_mut(vn).set_auto_live_hold();
                res = true;
            }
        }
        res
    }
}

impl Action for ActionDeadCode {
    fn base(&self) -> &ActionBase {
        &self.base
    }

    fn base_mut(&mut self) -> &mut ActionBase {
        &mut self.base
    }

    fn clone_action(&self, grouplist: &ActionGroupList) -> Option<Box<dyn Action>> {
        if !grouplist.contains(self.get_group()) {
            return None;
        }
        Some(Box::new(ActionDeadCode::new(self.get_group())))
    }

    fn apply(&mut self, data: &mut Funcdata, glb: &mut Architecture) -> Result<i32> {
        let mut worklist: Vec<VarnodeId> = Vec::new();
        let begin = data.begin_loc();
        let end = data.end_loc();
        for vn in data.vbank.loc_range(&begin, &end) {
            data.vn_mut(vn).clear_consume_list();
            data.vn_mut(vn).clear_consume_vacuous();
            data.vn_mut(vn).set_consume(0);
            if data.vn(vn).is_addr_force() && !data.vn(vn).is_direct_write() {
                data.vbank.get_mut(vn).clear_addr_force(&mut data.highs);
            }
        }
        let numspaces = glb.manager.num_spaces();
        for index in 0..numspaces {
            let spc = match glb.manager.get_space(index) {
                Some(spc) => spc,
                None => continue,
            };
            if !spc.does_deadcode() {
                continue;
            }
            if data.dead_removal_allowed(&spc) {
                continue;
            }
            let begin = data.begin_loc_space(&spc);
            let end = data.end_loc_space(&spc, glb);
            for vn in data.vbank.loc_range(&begin, &end) {
                ActionDeadCode::push_consumed(data, !0u64, vn, &mut worklist);
            }
        }
        let return_consume = ActionDeadCode::gather_consumed_return(data, glb);
        let mut iter = data.begin_op_alive();
        while let Some(op) = iter {
            iter = data.obank.next_in_list(op, PcodeOp::INSERT_LIST);
            data.op_mut(op).clear_indirect_source();
            if data.op(op).is_call() {
                if data.op(op).is_call_without_spec() {
                    for slot in 0..data.op(op).num_input() {
                        let invn = data.op(op).get_in(slot);
                        ActionDeadCode::push_consumed(data, !0u64, invn, &mut worklist);
                    }
                }
                if !data.op(op).is_assignment() {
                    continue;
                }
                if data.op(op).hold_output() {
                    let outvn = data.op(op).get_out().expect("call has no output");
                    ActionDeadCode::push_consumed(data, !0u64, outvn, &mut worklist);
                }
            } else if !data.op(op).is_assignment() {
                let opc = data.op(op).code();
                if opc == OpCode::Return {
                    let invn = data.op(op).get_in(0);
                    ActionDeadCode::push_consumed(data, !0u64, invn, &mut worklist);
                    for slot in 1..data.op(op).num_input() {
                        let invn = data.op(op).get_in(slot);
                        ActionDeadCode::push_consumed(data, return_consume, invn, &mut worklist);
                    }
                } else if opc == OpCode::Branchind {
                    let mask = match data.find_jump_table(op) {
                        Some(jt) => data.jump_table(jt).get_switch_var_consume(),
                        None => !0u64,
                    };
                    let invn = data.op(op).get_in(0);
                    ActionDeadCode::push_consumed(data, mask, invn, &mut worklist);
                } else {
                    for slot in 0..data.op(op).num_input() {
                        let invn = data.op(op).get_in(slot);
                        ActionDeadCode::push_consumed(data, !0u64, invn, &mut worklist);
                    }
                }
                continue;
            } else {
                for slot in 0..data.op(op).num_input() {
                    let vn = data.op(op).get_in(slot);
                    if data.vn(vn).is_auto_live() {
                        ActionDeadCode::push_consumed(data, !0u64, vn, &mut worklist);
                    }
                }
            }
            let vn = data.op(op).get_out().expect("assignment has no output");
            if data.vn(vn).is_auto_live() {
                ActionDeadCode::push_consumed(data, !0u64, vn, &mut worklist);
            }
        }
        let mut index = 0;
        while index < data.num_calls() {
            let fc = data.get_call_specs(index);
            index += 1;
            ActionDeadCode::mark_consumed_parameters(fc, data, glb, &mut worklist);
        }
        while !worklist.is_empty() {
            ActionDeadCode::propagate_consumed(data, glb, &mut worklist);
        }
        if ActionDeadCode::last_chance_load(data, glb, &mut worklist) {
            while !worklist.is_empty() {
                ActionDeadCode::propagate_consumed(data, glb, &mut worklist);
            }
        }
        for index in 0..numspaces {
            let spc = match glb.manager.get_space(index) {
                Some(spc) => spc,
                None => continue,
            };
            if !spc.does_deadcode() {
                continue;
            }
            if !data.dead_removal_allowed(&spc) {
                continue;
            }
            let endviter = data.end_loc_space(&spc, glb);
            let mut viter = data.begin_loc_space(&spc);
            let mut changecount = 0;
            while let Some((vn, next)) = loc_step_until(data, &viter, &endviter) {
                viter = next;
                if !data.vn(vn).is_written() {
                    continue;
                }
                let vacflag = data.vn(vn).is_consume_vacuous();
                data.vn_mut(vn).clear_consume_list();
                data.vn_mut(vn).clear_consume_vacuous();
                if !vacflag {
                    let op = data.vn(vn).get_def().expect("written varnode has no defining op");
                    changecount += 1;
                    if data.op(op).is_call() {
                        data.op_unset_output(op)?;
                    } else {
                        data.op_destroy(op)?;
                    }
                } else if data.vn(vn).get_consume() == 0 && ActionDeadCode::never_consumed(vn, data, glb)? {
                    changecount += 1;
                }
            }
            if changecount != 0 {
                data.seen_deadcode(&spc);
            }
        }
        data.clear_dead_varnodes()?;
        data.clear_dead_ops();
        Ok(0)
    }
}

pub struct ActionConditionalConst {
    pub base: ActionBase,
}

impl ActionConditionalConst {
    pub fn new(group: &str) -> ActionConditionalConst {
        ActionConditionalConst {
            base: ActionBase::new(0, "condconst", group),
        }
    }

    pub fn clear_marks(data: &mut Funcdata, op_list: &[OpId]) {
        for &op in op_list.iter() {
            data.op_mut(op).clear_mark();
        }
    }

    fn sort_edges(data: &Funcdata, edges: &mut [PcodeOpNode]) {
        std_sort(edges, |first, second| first.less_than(second, data));
    }

    fn contains_edge(data: &Funcdata, edges: &[PcodeOpNode], edge: &PcodeOpNode) -> bool {
        let pos = edges.partition_point(|elem| elem.less_than(edge, data));
        pos < edges.len() && !edge.less_than(&edges[pos], data)
    }

    pub fn collect_reachable(
        data: &mut Funcdata,
        vn: VarnodeId,
        phi_node_edges: &mut [PcodeOpNode],
        reachable: &mut Vec<OpId>,
    ) {
        ActionConditionalConst::sort_edges(data, phi_node_edges);
        let mut count = 0;
        let mut vn = vn;
        if data.vn(vn).is_written() {
            let op = data.vn(vn).get_def().expect("written varnode has no defining op");
            if data.op(op).code() == OpCode::Multiequal {
                data.op_mut(op).set_mark();
                reachable.push(op);
            }
        }
        loop {
            let descend = data.vn(vn).descend().to_vec();
            for op in descend {
                if data.op(op).is_mark() {
                    continue;
                }
                let opc = data.op(op).code();
                if opc == OpCode::Multiequal {
                    let mut tmp_op = PcodeOpNode::new(op, 0);
                    while tmp_op.slot < data.op(op).num_input() {
                        if data.op(op).get_in(tmp_op.slot) == vn
                            && !ActionConditionalConst::contains_edge(data, phi_node_edges, &tmp_op)
                        {
                            break;
                        }
                        tmp_op.slot += 1;
                    }
                    if tmp_op.slot == data.op(op).num_input() {
                        continue;
                    }
                } else if opc != OpCode::Copy && opc != OpCode::Indirect {
                    continue;
                }
                reachable.push(op);
                data.op_mut(op).set_mark();
            }
            if count >= reachable.len() {
                break;
            }
            vn = data.op(reachable[count]).get_out().expect("reachable op has no output");
            count += 1;
        }
    }

    pub fn flow_to_alternate_path(data: &mut Funcdata, op: OpId) -> bool {
        if data.op(op).is_mark() {
            return true;
        }
        let mut mark_set: Vec<VarnodeId> = Vec::new();
        let vn = data.op(op).get_out().expect("MULTIEQUAL has no output");
        mark_set.push(vn);
        data.vn_mut(vn).set_mark();
        let mut count = 0;
        let mut found_path = false;
        while count < mark_set.len() {
            let vn = mark_set[count];
            count += 1;
            let descend = data.vn(vn).descend().to_vec();
            for next_op in descend {
                let opc = data.op(next_op).code();
                if opc == OpCode::Multiequal {
                    if data.op(next_op).is_mark() {
                        found_path = true;
                        break;
                    }
                } else if opc != OpCode::Copy && opc != OpCode::Indirect {
                    continue;
                }
                let out_vn = data.op(next_op).get_out().expect("op has no output");
                if data.vn(out_vn).is_mark() {
                    continue;
                }
                data.vn_mut(out_vn).set_mark();
                mark_set.push(out_vn);
            }
            if found_path {
                break;
            }
        }
        for &vn in mark_set.iter() {
            data.vn_mut(vn).clear_mark();
        }
        found_path
    }

    pub fn flow_together(data: &mut Funcdata, edges: &[PcodeOpNode], index: i32, result: &mut [i32]) -> bool {
        let mut reachable: Vec<OpId> = Vec::new();
        let mut excise: Vec<PcodeOpNode> = Vec::new();
        let edge_op = edges[index as usize].op.expect("edge without op");
        let outvn = data.op(edge_op).get_out().expect("MULTIEQUAL has no output");
        ActionConditionalConst::collect_reachable(data, outvn, &mut excise, &mut reachable);
        let mut res = false;
        for other in 0..edges.len() {
            if other == index as usize {
                continue;
            }
            if result[other] == 0 {
                continue;
            }
            if data.op(edges[other].op.expect("edge without op")).is_mark() {
                result[index as usize] = 2;
                result[other] = 2;
                res = true;
            }
        }
        ActionConditionalConst::clear_marks(data, &reachable);
        res
    }

    pub fn place_copy(
        op: OpId,
        bl: BlockId,
        const_vn: VarnodeId,
        data: &mut Funcdata,
        glb: &mut Architecture,
    ) -> Result<VarnodeId> {
        let last_op = data.block_last_op(bl);
        let iter: Option<OpId>;
        let addr: Address;
        match last_op {
            None => {
                iter = None;
                addr = data.op(op).get_addr().clone();
            }
            Some(last) => {
                if data.op(last).is_branch() {
                    iter = Some(last);
                } else {
                    iter = None;
                }
                addr = data.op(last).get_addr().clone();
            }
        }
        let copy_op = data.new_op(1, &addr);
        data.op_set_opcode(copy_op, OpCode::Copy, glb);
        let size = data.vn(const_vn).get_size();
        let out_vn = data.new_unique_out(size, copy_op, glb)?;
        data.op_set_input(copy_op, const_vn, 0)?;
        data.op_insert(copy_op, bl, iter);
        Ok(out_vn)
    }

    pub fn find_const_compare(
        data: &Funcdata,
        points: &mut VecDeque<ConstPoint>,
        bool_vn: VarnodeId,
        bl: BlockId,
        block_dom: &[bool; 2],
        flip_edge: bool,
    ) {
        let mut bool_vn = bool_vn;
        let mut flip_edge = flip_edge;
        if !data.vn(bool_vn).is_written() {
            return;
        }
        let mut comp_op = data.vn(bool_vn).get_def().expect("written varnode has no defining op");
        let mut opc = data.op(comp_op).code();
        if opc == OpCode::BoolNegate {
            flip_edge = !flip_edge;
            bool_vn = data.op(comp_op).get_in(0);
            if !data.vn(bool_vn).is_written() {
                return;
            }
            comp_op = data.vn(bool_vn).get_def().expect("written varnode has no defining op");
            opc = data.op(comp_op).code();
        }
        let mut const_edge: i32 = if opc == OpCode::IntEqual {
            1
        } else if opc == OpCode::IntNotequal {
            0
        } else {
            return;
        };
        let mut var_vn = data.op(comp_op).get_in(0);
        let mut const_vn = data.op(comp_op).get_in(1);
        if !data.vn(const_vn).is_constant() {
            if !data.vn(var_vn).is_constant() {
                return;
            }
            std::mem::swap(&mut const_vn, &mut var_vn);
        }
        if data.vn(var_vn).lone_descend().is_some() {
            return;
        }
        if flip_edge {
            const_edge = 1 - const_edge;
        }
        points.push_back(ConstPoint::new(
            var_vn,
            const_vn,
            data.block(bl).get_out(const_edge),
            data.block(bl).get_out_rev_index(const_edge),
            block_dom[const_edge as usize],
            data,
        ));
    }

    pub fn push_constant(
        data: &Funcdata,
        glb: &Architecture,
        points: &mut VecDeque<ConstPoint>,
        op: OpId,
    ) -> Result<()> {
        if (data.op(op).get_eval_type() & PcodeOp::SPECIAL) != 0 {
            return Ok(());
        }
        let is_float = glb.inst[data.op(op).code().index()]
            .as_ref()
            .expect("no TypeOp registered for opcode")
            .is_floating_point_op();
        if is_float {
            return Ok(());
        }
        let outvn = data.op(op).get_out().expect("op has no output");
        if data.vn(outvn).get_size() > 8 {
            return Ok(());
        }
        let front = points.front().expect("constant point list is empty").clone();
        let slot = data.op(op).get_slot(front.vn);
        let mut input: [u64; 3] = [0; 3];
        for index in 0..data.op(op).num_input() {
            if index == slot {
                input[index as usize] = front.value;
            } else {
                let in_vn = data.op(op).get_in(index);
                if data.vn(in_vn).get_size() > 8 {
                    return Ok(());
                }
                if data.vn(in_vn).is_constant() {
                    input[index as usize] = data.vn(in_vn).get_offset();
                } else {
                    return Ok(());
                }
            }
        }
        let mut eval_error = false;
        let numinput = data.op(op).num_input() as usize;
        let outval = data.op_execute_simple(op, &input[..numinput], &mut eval_error, glb)?;
        if eval_error {
            return Ok(());
        }
        points.push_back(ConstPoint::from_value(
            outvn,
            outval,
            front.const_block,
            front.in_slot,
            front.block_is_dom,
        ));
        Ok(())
    }

    pub fn place_multiple_constants(
        phi_node_edges: &mut [PcodeOpNode],
        marks: &mut [i32],
        const_vn: VarnodeId,
        data: &mut Funcdata,
        glb: &mut Architecture,
    ) -> Result<()> {
        let mut blocks: Vec<BlockId> = Vec::new();
        let mut op: Option<OpId> = None;
        for index in 0..phi_node_edges.len() {
            if marks[index] != 2 {
                continue;
            }
            let edge_op = phi_node_edges[index].op.expect("edge without op");
            op = Some(edge_op);
            let bl = data.op(edge_op).get_parent().expect("op is not in a basic block");
            let bl = data.block(bl).get_in(phi_node_edges[index].slot);
            blocks.push(bl);
        }
        let root_block = data
            .block_find_common_block_set(&blocks)
            .expect("no common block for MULTIEQUAL edges");
        let out_vn = ActionConditionalConst::place_copy(
            op.expect("no MULTIEQUAL flows together"),
            root_block,
            const_vn,
            data,
            glb,
        )?;
        for index in 0..phi_node_edges.len() {
            if marks[index] != 2 {
                continue;
            }
            let edge_op = phi_node_edges[index].op.expect("edge without op");
            data.op_set_input(edge_op, out_vn, phi_node_edges[index].slot)?;
        }
        Ok(())
    }

    pub fn handle_phi_nodes(
        &mut self,
        var_vn: VarnodeId,
        const_vn: VarnodeId,
        phi_node_edges: &mut [PcodeOpNode],
        data: &mut Funcdata,
        glb: &mut Architecture,
    ) -> Result<()> {
        let mut alternate_flow: Vec<OpId> = Vec::new();
        let mut results: Vec<i32> = vec![0; phi_node_edges.len()];
        ActionConditionalConst::collect_reachable(data, var_vn, phi_node_edges, &mut alternate_flow);
        let mut alternate = 0;
        for index in 0..phi_node_edges.len() {
            let edge_op = phi_node_edges[index].op.expect("edge without op");
            if !ActionConditionalConst::flow_to_alternate_path(data, edge_op) {
                results[index] = 1;
                alternate += 1;
            }
        }
        ActionConditionalConst::clear_marks(data, &alternate_flow);
        let mut has_flow_together = false;
        if alternate > 1 {
            for index in 0..results.len() {
                if results[index] == 0 {
                    continue;
                }
                if ActionConditionalConst::flow_together(data, phi_node_edges, index as i32, &mut results) {
                    has_flow_together = true;
                }
            }
        }
        for index in 0..phi_node_edges.len() {
            if results[index] != 1 {
                continue;
            }
            let op = phi_node_edges[index].op.expect("edge without op");
            let slot = phi_node_edges[index].slot;
            let parent = data.op(op).get_parent().expect("op is not in a basic block");
            let bl = data.block(parent).get_in(slot);
            let out_vn = ActionConditionalConst::place_copy(op, bl, const_vn, data, glb)?;
            data.op_set_input(op, out_vn, slot)?;
            self.base.count += 1;
        }
        if has_flow_together {
            ActionConditionalConst::place_multiple_constants(phi_node_edges, &mut results, const_vn, data, glb)?;
            self.base.count += 1;
        }
        Ok(())
    }

    pub fn test_alternate_path(&mut self, data: &mut Funcdata, vn: VarnodeId, op: OpId, slot: i32, depth: i32) -> bool {
        for index in 0..data.op(op).num_input() {
            if index == slot {
                continue;
            }
            let in_vn = data.op(op).get_in(index);
            if in_vn == vn {
                return true;
            }
            if data.vn(in_vn).is_written() {
                let cur_op = data.vn(in_vn).get_def().expect("written varnode has no defining op");
                let opc = data.op(cur_op).code();
                if opc == OpCode::IntAdd || opc == OpCode::Ptrsub || opc == OpCode::Ptradd {
                    if data.op(cur_op).get_in(0) == vn || data.op(cur_op).get_in(1) == vn {
                        return true;
                    }
                } else if opc == OpCode::Multiequal {
                    if depth == 0 {
                        continue;
                    }
                    if self.test_alternate_path(data, vn, cur_op, -1, depth - 1) {
                        return true;
                    }
                }
            }
        }
        false
    }

    pub fn propagate_constant(
        &mut self,
        points: &mut VecDeque<ConstPoint>,
        use_multiequal: bool,
        data: &mut Funcdata,
        glb: &mut Architecture,
    ) -> Result<()> {
        let mut phi_node_edges: Vec<PcodeOpNode> = Vec::new();
        while let Some(point) = points.front().cloned() {
            let var_vn = point.vn;
            let mut const_vn = point.const_vn;
            let const_block = point.const_block;
            let descend = data.vn(var_vn).descend().to_vec();
            let mut iter = 0;
            while iter < descend.len() {
                let op = descend[iter];
                while iter < descend.len() && descend[iter] == op {
                    iter += 1;
                }
                let opc = data.op(op).code();
                if opc == OpCode::Indirect {
                    continue;
                } else if opc == OpCode::Multiequal {
                    if !use_multiequal {
                        continue;
                    }
                    let opout = data.op(op).get_out().expect("MULTIEQUAL has no output");
                    if data.vn(var_vn).is_addr_tied() && data.vn(var_vn).get_addr() == data.vn(opout).get_addr() {
                        continue;
                    }
                    let bl = data.op(op).get_parent().expect("op is not in a basic block");
                    if bl == const_block {
                        if data.op(op).get_in(point.in_slot) == var_vn {
                            if point.value > 1 {
                                continue;
                            }
                            if data.vn(opout).is_addr_tied() {
                                continue;
                            }
                            if self.test_alternate_path(data, var_vn, op, point.in_slot, 2) {
                                continue;
                            }
                            phi_node_edges.push(PcodeOpNode::new(op, point.in_slot));
                        }
                    } else if point.block_is_dom {
                        for slot in 0..data.op(op).num_input() {
                            if data.op(op).get_in(slot) == var_vn {
                                let inbl = data.block(bl).get_in(slot);
                                if data.block_dominates(const_block, inbl) {
                                    phi_node_edges.push(PcodeOpNode::new(op, slot));
                                }
                            }
                        }
                    }
                    continue;
                } else if opc == OpCode::Copy {
                    let opout = data.op(op).get_out().expect("COPY has no output");
                    let follow_op = match data.vn(opout).lone_descend() {
                        Some(follow_op) => follow_op,
                        None => continue,
                    };
                    if data.op(follow_op).is_marker() {
                        continue;
                    }
                    if data.op(follow_op).code() == OpCode::Copy {
                        continue;
                    }
                }
                if !point.block_is_dom {
                    continue;
                }
                let opparent = data.op(op).get_parent().expect("op is not in a basic block");
                if data.block_dominates(const_block, opparent) {
                    let constant = match const_vn {
                        Some(constant) => constant,
                        None => {
                            let size = data.vn(var_vn).get_size();
                            let constant = data.new_constant(size, point.value, glb);
                            const_vn = Some(constant);
                            constant
                        }
                    };
                    if opc == OpCode::Return {
                        let opaddr = data.op(op).get_addr().clone();
                        let copy_before_ret = data.new_op(1, &opaddr);
                        data.op_set_opcode(copy_before_ret, OpCode::Copy, glb);
                        data.op_set_input(copy_before_ret, constant, 0)?;
                        let size = data.vn(var_vn).get_size();
                        let varaddr = data.vn(var_vn).get_addr().clone();
                        data.new_varnode_out(size, &varaddr, copy_before_ret, glb)?;
                        let copyout = data.op(copy_before_ret).get_out().expect("COPY has no output");
                        data.op_set_input(op, copyout, 1)?;
                        data.op_insert_before(copy_before_ret, op);
                    } else {
                        let slot = data.op(op).get_slot(var_vn);
                        data.op_set_input(op, constant, slot)?;
                    }
                    self.base.count += 1;
                } else {
                    ActionConditionalConst::push_constant(data, glb, points, op)?;
                }
            }
            if !phi_node_edges.is_empty() {
                let constant = match const_vn {
                    Some(constant) => constant,
                    None => {
                        let size = data.vn(var_vn).get_size();
                        data.new_constant(size, point.value, glb)
                    }
                };
                self.handle_phi_nodes(var_vn, constant, &mut phi_node_edges, data, glb)?;
                phi_node_edges.clear();
            }
            points.pop_front();
        }
        Ok(())
    }
}

impl Action for ActionConditionalConst {
    fn base(&self) -> &ActionBase {
        &self.base
    }

    fn base_mut(&mut self) -> &mut ActionBase {
        &mut self.base
    }

    fn clone_action(&self, grouplist: &ActionGroupList) -> Option<Box<dyn Action>> {
        if !grouplist.contains(self.get_group()) {
            return None;
        }
        Some(Box::new(ActionConditionalConst::new(self.get_group())))
    }

    fn apply(&mut self, data: &mut Funcdata, glb: &mut Architecture) -> Result<i32> {
        let mut use_multiequal = true;
        if let Some(stack_space) = glb.manager.get_stack_space() {
            let num_passes = data.num_heritage_passes(&stack_space)?;
            if num_passes <= 0 {
                use_multiequal = false;
            }
        }
        let mut block_dom: [bool; 2] = [false, false];
        let mut points: VecDeque<ConstPoint> = VecDeque::new();
        let mut index = 0;
        while index < data.block(data.bblocks).get_size() {
            let bl = data.block(data.bblocks).get_block(index);
            index += 1;
            let c_branch = match data.block_last_op(bl) {
                Some(c_branch) => c_branch,
                None => continue,
            };
            if data.op(c_branch).code() != OpCode::Cbranch {
                continue;
            }
            let bool_vn = data.op(c_branch).get_in(1);
            let out0 = data.block(bl).get_out(0);
            let out1 = data.block(bl).get_out(1);
            block_dom[0] = data.block_restricted_by_conditional(out0, bl);
            block_dom[1] = data.block_restricted_by_conditional(out1, bl);
            let flip_edge = data.op(c_branch).is_boolean_flip();
            if data.vn(bool_vn).lone_descend().is_none() {
                points.push_back(ConstPoint::from_value(
                    bool_vn,
                    if flip_edge { 1 } else { 0 },
                    data.block(bl).get_false_out(),
                    data.block(bl).get_out_rev_index(0),
                    block_dom[0],
                ));
                points.push_back(ConstPoint::from_value(
                    bool_vn,
                    if flip_edge { 0 } else { 1 },
                    data.block(bl).get_true_out(),
                    data.block(bl).get_out_rev_index(1),
                    block_dom[1],
                ));
            }
            ActionConditionalConst::find_const_compare(data, &mut points, bool_vn, bl, &block_dom, flip_edge);
            self.propagate_constant(&mut points, use_multiequal, data, glb)?;
        }
        Ok(0)
    }
}
