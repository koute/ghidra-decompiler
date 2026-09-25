use crate::action::{ActionGroupList, Rule, RuleBase};
use crate::address::{Address, calc_mask, leastsigbit_set, sign_extend_size};
use crate::architecture::Architecture;
use crate::cpool::CPoolRecord;
use crate::database::Database;
use crate::error::{Error, Result};
use crate::fspec::FuncCallSpecs;
use crate::funcdata::Funcdata;
use crate::op::OpId;
use crate::opcodes::OpCode;
use crate::space::{AddrSpace, SpaceRef, same_space};
use crate::varnode::VarnodeId;

pub struct RuleIdentityEl {
    pub base: RuleBase,
}

impl RuleIdentityEl {
    pub fn new(group: &str) -> RuleIdentityEl {
        RuleIdentityEl {
            base: RuleBase::new(group, 0, "identityel"),
        }
    }
}

impl Rule for RuleIdentityEl {
    fn base(&self) -> &RuleBase {
        &self.base
    }

    fn base_mut(&mut self) -> &mut RuleBase {
        &mut self.base
    }

    fn clone_rule(&self, grouplist: &ActionGroupList) -> Option<Box<dyn Rule>> {
        if !grouplist.contains(self.get_group()) {
            return None;
        }
        Some(Box::new(RuleIdentityEl::new(self.get_group())))
    }

    fn get_op_list(&self, oplist: &mut Vec<OpCode>) {
        oplist.extend_from_slice(&[
            OpCode::IntAdd,
            OpCode::IntXor,
            OpCode::IntOr,
            OpCode::BoolXor,
            OpCode::BoolOr,
            OpCode::IntMult,
        ]);
    }

    fn apply_op(&mut self, op: OpId, data: &mut Funcdata, glb: &mut Architecture) -> Result<i32> {
        let constvn = data.op(op).get_in(1);
        if !data.vn(constvn).is_constant() {
            return Ok(0);
        }
        let val = data.vn(constvn).get_offset();
        if val == 0 && data.op(op).code() != OpCode::IntMult {
            data.op_set_opcode(op, OpCode::Copy, glb);
            data.op_remove_input(op, 1);
            return Ok(1);
        }
        if data.op(op).code() != OpCode::IntMult {
            return Ok(0);
        }
        if val == 1 {
            data.op_set_opcode(op, OpCode::Copy, glb);
            data.op_remove_input(op, 1);
            return Ok(1);
        }
        if val == 0 {
            data.op_set_opcode(op, OpCode::Copy, glb);
            data.op_remove_input(op, 0);
            return Ok(1);
        }
        Ok(0)
    }
}

pub struct RuleShift2Mult {
    pub base: RuleBase,
}

impl RuleShift2Mult {
    pub fn new(group: &str) -> RuleShift2Mult {
        RuleShift2Mult {
            base: RuleBase::new(group, 0, "shift2mult"),
        }
    }
}

impl Rule for RuleShift2Mult {
    fn base(&self) -> &RuleBase {
        &self.base
    }

    fn base_mut(&mut self) -> &mut RuleBase {
        &mut self.base
    }

    fn clone_rule(&self, grouplist: &ActionGroupList) -> Option<Box<dyn Rule>> {
        if !grouplist.contains(self.get_group()) {
            return None;
        }
        Some(Box::new(RuleShift2Mult::new(self.get_group())))
    }

    fn get_op_list(&self, oplist: &mut Vec<OpCode>) {
        oplist.push(OpCode::IntLeft);
    }

    fn apply_op(&mut self, op: OpId, data: &mut Funcdata, glb: &mut Architecture) -> Result<i32> {
        let vn = data.op(op).get_out().expect("op without output");
        let constvn = data.op(op).get_in(1);
        if !data.vn(constvn).is_constant() {
            return Ok(0);
        }
        let val = data.vn(constvn).get_offset() as i32;
        if val >= 32 {
            return Ok(0);
        }
        let mut flag = false;
        let mut arithop = data.vn(data.op(op).get_in(0)).get_def();
        let descendants: Vec<OpId> = data.vn(vn).descend().to_vec();
        let mut position = 0usize;
        loop {
            if let Some(candidate) = arithop {
                let opc = data.op(candidate).code();
                if opc == OpCode::IntAdd || opc == OpCode::IntSub || opc == OpCode::IntMult {
                    flag = true;
                    break;
                }
            }
            if position == descendants.len() {
                break;
            }
            arithop = Some(descendants[position]);
            position += 1;
        }
        if !flag {
            return Ok(0);
        }
        let size = data.vn(vn).get_size();
        let newconst = data.new_constant(size, 1u64.wrapping_shl(val as u32), glb);
        data.op_set_input(op, newconst, 1)?;
        data.op_set_opcode(op, OpCode::IntMult, glb);
        Ok(1)
    }
}

pub struct RuleShiftPiece {
    pub base: RuleBase,
}

impl RuleShiftPiece {
    pub fn new(group: &str) -> RuleShiftPiece {
        RuleShiftPiece {
            base: RuleBase::new(group, 0, "shiftpiece"),
        }
    }

    pub fn mult_power_of2(op: OpId, data: &Funcdata) -> i32 {
        let opc = data.op(op).code();
        if opc != OpCode::IntLeft && opc != OpCode::IntMult {
            return -1;
        }
        let cvn = data.op(op).get_in(1);
        if !data.vn(cvn).is_constant() {
            return -1;
        }
        let val = data.vn(cvn).get_offset();
        if opc == OpCode::IntLeft {
            return val as i32;
        }
        let shift_amount = leastsigbit_set(val);
        if shift_amount >= 0 && val.wrapping_shr(shift_amount as u32) == 1 {
            return shift_amount;
        }
        -1
    }
}

impl Rule for RuleShiftPiece {
    fn base(&self) -> &RuleBase {
        &self.base
    }

    fn base_mut(&mut self) -> &mut RuleBase {
        &mut self.base
    }

    fn clone_rule(&self, grouplist: &ActionGroupList) -> Option<Box<dyn Rule>> {
        if !grouplist.contains(self.get_group()) {
            return None;
        }
        Some(Box::new(RuleShiftPiece::new(self.get_group())))
    }

    fn get_op_list(&self, oplist: &mut Vec<OpCode>) {
        oplist.push(OpCode::IntOr);
        oplist.push(OpCode::IntXor);
        oplist.push(OpCode::IntAdd);
    }

    fn apply_op(&mut self, op: OpId, data: &mut Funcdata, glb: &mut Architecture) -> Result<i32> {
        let vn1 = data.op(op).get_in(0);
        if !data.vn(vn1).is_written() {
            return Ok(0);
        }
        let vn2 = data.op(op).get_in(1);
        if !data.vn(vn2).is_written() {
            return Ok(0);
        }
        let mut shiftop = data.vn(vn1).get_def().expect("written varnode without defining op");
        let mut zextloop = data.vn(vn2).get_def().expect("written varnode without defining op");
        let mut shift_amount = RuleShiftPiece::mult_power_of2(shiftop, data);
        if shift_amount < 0 {
            shift_amount = RuleShiftPiece::mult_power_of2(zextloop, data);
            if shift_amount < 0 {
                return Ok(0);
            }
            std::mem::swap(&mut shiftop, &mut zextloop);
        }
        let hivn = data.op(shiftop).get_in(0);
        if !data.vn(hivn).is_written() {
            return Ok(0);
        }
        let zexthiop = data.vn(hivn).get_def().expect("written varnode without defining op");
        if data.op(zexthiop).code() != OpCode::IntZext && data.op(zexthiop).code() != OpCode::IntSext {
            return Ok(0);
        }
        let vn1 = data.op(zexthiop).get_in(0);
        if data.vn(vn1).is_constant() {
            if data.vn(vn1).get_size() < 8 {
                return Ok(0);
            }
        } else if data.vn(vn1).is_free() {
            return Ok(0);
        }
        let concatsize = shift_amount.wrapping_add(8 * data.vn(vn1).get_size());
        let outsize = data.vn(data.op(op).get_out().expect("op without output")).get_size();
        if outsize * 8 < concatsize {
            return Ok(0);
        }
        if data.op(zextloop).code() != OpCode::IntZext {
            if !data.vn(vn1).is_written() {
                return Ok(0);
            }
            let r_shift_op = data.vn(vn1).get_def().expect("written varnode without defining op");
            if data.op(r_shift_op).code() != OpCode::IntSright {
                return Ok(0);
            }
            if !data.vn(data.op(r_shift_op).get_in(1)).is_constant() {
                return Ok(0);
            }
            let vn2 = data.op(r_shift_op).get_in(0);
            if !data.vn(vn2).is_written() {
                return Ok(0);
            }
            let subop = data.vn(vn2).get_def().expect("written varnode without defining op");
            if data.op(subop).code() != OpCode::Subpiece {
                return Ok(0);
            }
            if data.vn(data.op(subop).get_in(1)).get_offset() != 0 {
                return Ok(0);
            }
            let big_vn = data.op(zextloop).get_out().expect("op without output");
            if data.op(subop).get_in(0) != big_vn {
                return Ok(0);
            }
            let rsa = data.vn(data.op(r_shift_op).get_in(1)).get_offset() as i32;
            if rsa != data.vn(vn2).get_size() * 8 - 1 {
                return Ok(0);
            }
            if data.vn(big_vn).get_nz_mask().wrapping_shr(shift_amount as u32) != 0 {
                return Ok(0);
            }
            if shift_amount != 8 * data.vn(vn2).get_size() {
                return Ok(0);
            }
            data.op_set_opcode(op, OpCode::IntSext, glb);
            data.op_set_input(op, vn2, 0)?;
            data.op_remove_input(op, 1);
            return Ok(1);
        }
        let vn2 = data.op(zextloop).get_in(0);
        if data.vn(vn2).is_free() {
            return Ok(0);
        }
        if shift_amount != 8 * data.vn(vn2).get_size() {
            return Ok(0);
        }
        if concatsize == outsize * 8 {
            data.op_set_opcode(op, OpCode::Piece, glb);
            data.op_set_input(op, vn1, 0)?;
            data.op_set_input(op, vn2, 1)?;
        } else {
            let addr = data.op(op).get_addr().clone();
            let newop = data.new_op(2, &addr);
            let newout = data.new_unique_out(concatsize / 8, newop, glb)?;
            data.op_set_opcode(newop, OpCode::Piece, glb);
            data.op_set_input(newop, vn1, 0)?;
            data.op_set_input(newop, vn2, 1)?;
            data.op_insert_before(newop, op);
            let extopc = data.op(zexthiop).code();
            data.op_set_opcode(op, extopc, glb);
            data.op_remove_input(op, 1);
            data.op_set_input(op, newout, 0)?;
        }
        Ok(1)
    }
}

pub struct RuleCollapseConstants {
    pub base: RuleBase,
}

impl RuleCollapseConstants {
    pub fn new(group: &str) -> RuleCollapseConstants {
        RuleCollapseConstants {
            base: RuleBase::new(group, 0, "collapseconstants"),
        }
    }
}

impl Rule for RuleCollapseConstants {
    fn base(&self) -> &RuleBase {
        &self.base
    }

    fn base_mut(&mut self) -> &mut RuleBase {
        &mut self.base
    }

    fn clone_rule(&self, grouplist: &ActionGroupList) -> Option<Box<dyn Rule>> {
        if !grouplist.contains(self.get_group()) {
            return None;
        }
        Some(Box::new(RuleCollapseConstants::new(self.get_group())))
    }

    fn get_op_list(&self, oplist: &mut Vec<OpCode>) {
        oplist.extend_from_slice(&[
            OpCode::IntEqual,
            OpCode::IntNotequal,
            OpCode::IntSless,
            OpCode::IntSlessequal,
            OpCode::IntLess,
            OpCode::IntLessequal,
            OpCode::IntZext,
            OpCode::IntSext,
            OpCode::IntAdd,
            OpCode::IntSub,
            OpCode::IntCarry,
            OpCode::IntScarry,
            OpCode::IntSborrow,
            OpCode::Int2comp,
            OpCode::IntNegate,
            OpCode::IntXor,
            OpCode::IntAnd,
            OpCode::IntOr,
            OpCode::IntLeft,
            OpCode::IntRight,
            OpCode::IntSright,
            OpCode::IntMult,
            OpCode::IntDiv,
            OpCode::IntSdiv,
            OpCode::IntRem,
            OpCode::IntSrem,
            OpCode::BoolNegate,
            OpCode::BoolXor,
            OpCode::BoolAnd,
            OpCode::BoolOr,
            OpCode::FloatEqual,
            OpCode::FloatNotequal,
            OpCode::FloatLess,
            OpCode::FloatLessequal,
            OpCode::FloatNan,
            OpCode::FloatAdd,
            OpCode::FloatDiv,
            OpCode::FloatMult,
            OpCode::FloatSub,
            OpCode::FloatNeg,
            OpCode::FloatAbs,
            OpCode::FloatSqrt,
            OpCode::FloatInt2float,
            OpCode::FloatFloat2float,
            OpCode::FloatTrunc,
            OpCode::FloatCeil,
            OpCode::FloatFloor,
            OpCode::FloatRound,
            OpCode::Piece,
            OpCode::Subpiece,
            OpCode::Popcount,
            OpCode::Lzcount,
        ]);
    }

    fn apply_op(&mut self, op: OpId, data: &mut Funcdata, glb: &mut Architecture) -> Result<i32> {
        if !data.op_is_collapsible(op) {
            return Ok(0);
        }
        let mut marked_input = false;
        let collapsed = data.op_collapse(op, &mut marked_input, glb)?;
        let newval = glb.manager.get_constant(collapsed);
        let size = data.vn(data.op(op).get_out().expect("op without output")).get_size();
        let vn = data.new_varnode(size, &newval, None, glb)?;
        if marked_input {
            data.op_collapse_constant_symbol(op, vn, glb)?;
        }
        let mut slot = data.op(op).num_input() - 1;
        while slot > 0 {
            data.op_remove_input(op, slot);
            slot -= 1;
        }
        data.op_set_input(op, vn, 0)?;
        data.op_set_opcode(op, OpCode::Copy, glb);
        Ok(1)
    }
}

pub struct RuleTransformCpool {
    pub base: RuleBase,
}

impl RuleTransformCpool {
    pub fn new(group: &str) -> RuleTransformCpool {
        RuleTransformCpool {
            base: RuleBase::new(group, 0, "transformcpool"),
        }
    }
}

impl Rule for RuleTransformCpool {
    fn base(&self) -> &RuleBase {
        &self.base
    }

    fn base_mut(&mut self) -> &mut RuleBase {
        &mut self.base
    }

    fn clone_rule(&self, grouplist: &ActionGroupList) -> Option<Box<dyn Rule>> {
        if !grouplist.contains(self.get_group()) {
            return None;
        }
        Some(Box::new(RuleTransformCpool::new(self.get_group())))
    }

    fn get_op_list(&self, oplist: &mut Vec<OpCode>) {
        oplist.push(OpCode::Cpoolref);
    }

    fn apply_op(&mut self, op: OpId, data: &mut Funcdata, glb: &mut Architecture) -> Result<i32> {
        if data.op(op).is_cpool_transformed() {
            return Ok(0);
        }
        data.op_mark_cpool_transformed(op);
        let refs: Vec<u64> = (1..data.op(op).num_input())
            .map(|slot| data.vn(data.op(op).get_in(slot)).get_offset())
            .collect();
        let record = glb
            .cpool
            .as_ref()
            .expect("missing constant pool")
            .get_record(&refs)
            .map(|rec| (rec.get_tag(), rec.get_value(), rec.get_type()));
        if let Some((tag, value, tp)) = record {
            if tag == CPoolRecord::INSTANCE_OF {
                data.op_mark_calculated_bool(op);
            } else if tag == CPoolRecord::PRIMITIVE {
                let size = data.vn(data.op(op).get_out().expect("op without output")).get_size();
                let cvn = data.new_constant(size, value & calc_mask(size), glb);
                data.vn_update_type_locked(
                    cvn,
                    tp.expect("primitive constant pool record without type"),
                    true,
                    true,
                    glb,
                );
                while data.op(op).num_input() > 1 {
                    let last = data.op(op).num_input() - 1;
                    data.op_remove_input(op, last);
                }
                data.op_set_opcode(op, OpCode::Copy, glb);
                data.op_set_input(op, cvn, 0)?;
                return Ok(1);
            }
            let tagvn = data.new_constant(4, tag as u64, glb);
            let slot = data.op(op).num_input();
            data.op_insert_input(op, tagvn, slot)?;
        }
        Ok(1)
    }
}

pub struct RulePropagateCopy {
    pub base: RuleBase,
}

impl RulePropagateCopy {
    pub fn new(group: &str) -> RulePropagateCopy {
        RulePropagateCopy {
            base: RuleBase::new(group, 0, "propagatecopy"),
        }
    }
}

impl Rule for RulePropagateCopy {
    fn base(&self) -> &RuleBase {
        &self.base
    }

    fn base_mut(&mut self) -> &mut RuleBase {
        &mut self.base
    }

    fn clone_rule(&self, grouplist: &ActionGroupList) -> Option<Box<dyn Rule>> {
        if !grouplist.contains(self.get_group()) {
            return None;
        }
        Some(Box::new(RulePropagateCopy::new(self.get_group())))
    }

    fn get_op_list(&self, oplist: &mut Vec<OpCode>) {
        oplist.push(OpCode::Copy);
    }

    fn apply_op(&mut self, op: OpId, data: &mut Funcdata, _glb: &mut Architecture) -> Result<i32> {
        let vn = data.op(op).get_out().expect("op without output");
        let invn = data.op(op).get_in(0);
        if invn == vn {
            return Err(Error::Lowlevel("Self-defined varnode".to_string()));
        }
        if !data.vn(invn).is_heritage_known() {
            return Ok(0);
        }
        let descendants: Vec<OpId> = data.vn(vn).descend().to_vec();
        let mut count = 0;
        for other_op in descendants {
            if data.op(other_op).is_return_copy() {
                continue;
            }
            for slot in 0..data.op(other_op).num_input() {
                if vn != data.op(other_op).get_in(slot) {
                    continue;
                }
                if data.op(other_op).is_marker() {
                    if data.vn(invn).is_constant() {
                        continue;
                    }
                    if data.vn(vn).is_addr_force() {
                        continue;
                    }
                    if data.vn(invn).is_addr_tied() {
                        let other_out = data.op(other_op).get_out().expect("op without output");
                        if data.vn(other_out).is_addr_tied()
                            && data.vn(other_out).get_addr() != data.vn(invn).get_addr()
                        {
                            continue;
                        }
                    }
                    if data.op(other_op).code() == OpCode::Multiequal {
                        let other_parent = data.op(other_op).get_parent().expect("op without parent block");
                        if data.op(op).get_parent() == Some(data.block(other_parent).get_in(slot)) {
                            data.op_set_copy_immed(other_op, slot);
                        }
                    }
                }
                data.op_set_input(other_op, invn, slot)?;
                count += 1;
                break;
            }
        }
        Ok(count)
    }
}

pub struct Rule2Comp2Mult {
    pub base: RuleBase,
}

impl Rule2Comp2Mult {
    pub fn new(group: &str) -> Rule2Comp2Mult {
        Rule2Comp2Mult {
            base: RuleBase::new(group, 0, "2comp2mult"),
        }
    }
}

impl Rule for Rule2Comp2Mult {
    fn base(&self) -> &RuleBase {
        &self.base
    }

    fn base_mut(&mut self) -> &mut RuleBase {
        &mut self.base
    }

    fn clone_rule(&self, grouplist: &ActionGroupList) -> Option<Box<dyn Rule>> {
        if !grouplist.contains(self.get_group()) {
            return None;
        }
        Some(Box::new(Rule2Comp2Mult::new(self.get_group())))
    }

    fn get_op_list(&self, oplist: &mut Vec<OpCode>) {
        oplist.push(OpCode::Int2comp);
    }

    fn apply_op(&mut self, op: OpId, data: &mut Funcdata, glb: &mut Architecture) -> Result<i32> {
        data.op_set_opcode(op, OpCode::IntMult, glb);
        let size = data.vn(data.op(op).get_in(0)).get_size();
        let negone = data.new_constant(size, calc_mask(size), glb);
        data.op_insert_input(op, negone, 1)?;
        Ok(1)
    }
}

pub struct RuleCarryElim {
    pub base: RuleBase,
}

impl RuleCarryElim {
    pub fn new(group: &str) -> RuleCarryElim {
        RuleCarryElim {
            base: RuleBase::new(group, 0, "carryelim"),
        }
    }
}

impl Rule for RuleCarryElim {
    fn base(&self) -> &RuleBase {
        &self.base
    }

    fn base_mut(&mut self) -> &mut RuleBase {
        &mut self.base
    }

    fn clone_rule(&self, grouplist: &ActionGroupList) -> Option<Box<dyn Rule>> {
        if !grouplist.contains(self.get_group()) {
            return None;
        }
        Some(Box::new(RuleCarryElim::new(self.get_group())))
    }

    fn get_op_list(&self, oplist: &mut Vec<OpCode>) {
        oplist.push(OpCode::IntCarry);
    }

    fn apply_op(&mut self, op: OpId, data: &mut Funcdata, glb: &mut Architecture) -> Result<i32> {
        let vn2 = data.op(op).get_in(1);
        if !data.vn(vn2).is_constant() {
            return Ok(0);
        }
        let vn1 = data.op(op).get_in(0);
        if data.vn(vn1).is_free() {
            return Ok(0);
        }
        let mut off = data.vn(vn2).get_offset();
        if off == 0 {
            data.op_remove_input(op, 1);
            let falsevn = data.new_constant(1, 0, glb);
            data.op_set_input(op, falsevn, 0)?;
            data.op_set_opcode(op, OpCode::Copy, glb);
            return Ok(1);
        }
        off = off.wrapping_neg() & calc_mask(data.vn(vn2).get_size());
        data.op_set_opcode(op, OpCode::IntLessequal, glb);
        data.op_set_input(op, vn1, 1)?;
        let size = data.vn(vn1).get_size();
        let newconst = data.new_constant(size, off, glb);
        data.op_set_input(op, newconst, 0)?;
        Ok(1)
    }
}

pub struct RuleSub2Add {
    pub base: RuleBase,
}

impl RuleSub2Add {
    pub fn new(group: &str) -> RuleSub2Add {
        RuleSub2Add {
            base: RuleBase::new(group, 0, "sub2add"),
        }
    }
}

impl Rule for RuleSub2Add {
    fn base(&self) -> &RuleBase {
        &self.base
    }

    fn base_mut(&mut self) -> &mut RuleBase {
        &mut self.base
    }

    fn clone_rule(&self, grouplist: &ActionGroupList) -> Option<Box<dyn Rule>> {
        if !grouplist.contains(self.get_group()) {
            return None;
        }
        Some(Box::new(RuleSub2Add::new(self.get_group())))
    }

    fn get_op_list(&self, oplist: &mut Vec<OpCode>) {
        oplist.push(OpCode::IntSub);
    }

    fn apply_op(&mut self, op: OpId, data: &mut Funcdata, glb: &mut Architecture) -> Result<i32> {
        let vn = data.op(op).get_in(1);
        let addr = data.op(op).get_addr().clone();
        let newop = data.new_op(2, &addr);
        data.op_set_opcode(newop, OpCode::IntMult, glb);
        let size = data.vn(vn).get_size();
        let newvn = data.new_unique_out(size, newop, glb)?;
        data.op_set_input(op, newvn, 1)?;
        data.op_set_input(newop, vn, 0)?;
        let negone = data.new_constant(size, calc_mask(size), glb);
        data.op_set_input(newop, negone, 1)?;
        data.op_set_opcode(op, OpCode::IntAdd, glb);
        data.op_insert_before(newop, op);
        Ok(1)
    }
}

pub struct RuleXorCollapse {
    pub base: RuleBase,
}

impl RuleXorCollapse {
    pub fn new(group: &str) -> RuleXorCollapse {
        RuleXorCollapse {
            base: RuleBase::new(group, 0, "xorcollapse"),
        }
    }
}

impl Rule for RuleXorCollapse {
    fn base(&self) -> &RuleBase {
        &self.base
    }

    fn base_mut(&mut self) -> &mut RuleBase {
        &mut self.base
    }

    fn clone_rule(&self, grouplist: &ActionGroupList) -> Option<Box<dyn Rule>> {
        if !grouplist.contains(self.get_group()) {
            return None;
        }
        Some(Box::new(RuleXorCollapse::new(self.get_group())))
    }

    fn get_op_list(&self, oplist: &mut Vec<OpCode>) {
        oplist.push(OpCode::IntEqual);
        oplist.push(OpCode::IntNotequal);
    }

    fn apply_op(&mut self, op: OpId, data: &mut Funcdata, glb: &mut Architecture) -> Result<i32> {
        let cmpconst = data.op(op).get_in(1);
        if !data.vn(cmpconst).is_constant() {
            return Ok(0);
        }
        let invn = data.op(op).get_in(0);
        let Some(xorop) = data.vn(invn).get_def() else {
            return Ok(0);
        };
        if data.op(xorop).code() != OpCode::IntXor {
            return Ok(0);
        }
        if data.vn(invn).lone_descend().is_none() {
            return Ok(0);
        }
        let coeff1 = data.vn(cmpconst).get_offset();
        let xorvn = data.op(xorop).get_in(1);
        let xorbase = data.op(xorop).get_in(0);
        if data.vn(xorbase).is_free() {
            return Ok(0);
        }
        if !data.vn(xorvn).is_constant() {
            if coeff1 != 0 {
                return Ok(0);
            }
            if data.vn(xorvn).is_free() {
                return Ok(0);
            }
            data.op_set_input(op, xorvn, 1)?;
            data.op_set_input(op, xorbase, 0)?;
            return Ok(1);
        }
        let coeff2 = data.vn(xorvn).get_offset();
        if coeff2 == 0 {
            return Ok(0);
        }
        let size = data.vn(cmpconst).get_size();
        let constvn = data.new_constant(size, coeff1 ^ coeff2, glb);
        data.vn_copy_symbol_if_valid(constvn, xorvn, glb)?;
        data.op_set_input(op, constvn, 1)?;
        data.op_set_input(op, xorbase, 0)?;
        Ok(1)
    }
}

pub struct RuleAddMultCollapse {
    pub base: RuleBase,
}

impl RuleAddMultCollapse {
    pub fn new(group: &str) -> RuleAddMultCollapse {
        RuleAddMultCollapse {
            base: RuleBase::new(group, 0, "addmultcollapse"),
        }
    }
}

impl Rule for RuleAddMultCollapse {
    fn base(&self) -> &RuleBase {
        &self.base
    }

    fn base_mut(&mut self) -> &mut RuleBase {
        &mut self.base
    }

    fn clone_rule(&self, grouplist: &ActionGroupList) -> Option<Box<dyn Rule>> {
        if !grouplist.contains(self.get_group()) {
            return None;
        }
        Some(Box::new(RuleAddMultCollapse::new(self.get_group())))
    }

    fn get_op_list(&self, oplist: &mut Vec<OpCode>) {
        oplist.extend_from_slice(&[OpCode::IntAdd, OpCode::IntMult]);
    }

    fn apply_op(&mut self, op: OpId, data: &mut Funcdata, glb: &mut Architecture) -> Result<i32> {
        let opc = data.op(op).code();
        let const0 = data.op(op).get_in(1);
        if !data.vn(const0).is_constant() {
            return Ok(0);
        }
        let sub = data.op(op).get_in(0);
        if !data.vn(sub).is_written() {
            return Ok(0);
        }
        let subop = data.vn(sub).get_def().expect("written varnode without defining op");
        if data.op(subop).code() != opc {
            return Ok(0);
        }
        let const1 = data.op(subop).get_in(1);
        let size0 = data.vn(const0).get_size();
        if !data.vn(const1).is_constant() {
            if opc != OpCode::IntAdd {
                return Ok(0);
            }
            for slot in 0..2 {
                let othervn = data.op(subop).get_in(slot);
                if data.vn(othervn).is_constant() {
                    continue;
                }
                if data.vn(othervn).is_free() {
                    continue;
                }
                let sub2 = data.op(subop).get_in(1 - slot);
                if !data.vn(sub2).is_written() {
                    continue;
                }
                let baseop = data.vn(sub2).get_def().expect("written varnode without defining op");
                if data.op(baseop).code() != OpCode::IntAdd {
                    continue;
                }
                let const1 = data.op(baseop).get_in(1);
                if !data.vn(const1).is_constant() {
                    continue;
                }
                let basevn = data.op(baseop).get_in(0);
                if !data.vn(basevn).is_spacebase() {
                    continue;
                }
                if !data.vn(basevn).is_input() {
                    continue;
                }
                let val = data.op(op).get_opcode(glb).evaluate_binary(
                    size0,
                    size0,
                    data.vn(const0).get_offset(),
                    data.vn(const1).get_offset(),
                )?;
                let newvn = data.new_constant(size0, val, glb);
                if data.vn(const0).get_symbol_entry().is_some() {
                    data.vn_copy_symbol_if_valid(newvn, const0, glb)?;
                } else if data.vn(const1).get_symbol_entry().is_some() {
                    data.vn_copy_symbol_if_valid(newvn, const1, glb)?;
                }
                let addr = data.op(op).get_addr().clone();
                let newop = data.new_op(2, &addr);
                data.op_set_opcode(newop, OpCode::IntAdd, glb);
                let newout = data.new_unique_out(size0, newop, glb)?;
                data.op_set_input(newop, basevn, 0)?;
                data.op_set_input(newop, newvn, 1)?;
                data.op_insert_before(newop, op);
                data.op_set_input(op, newout, 0)?;
                data.op_set_input(op, othervn, 1)?;
                return Ok(1);
            }
            return Ok(0);
        }
        let sub2 = data.op(subop).get_in(0);
        if data.vn(sub2).is_free() {
            return Ok(0);
        }
        let val = data.op(op).get_opcode(glb).evaluate_binary(
            size0,
            size0,
            data.vn(const0).get_offset(),
            data.vn(const1).get_offset(),
        )?;
        let newvn = data.new_constant(size0, val, glb);
        if data.vn(const0).get_symbol_entry().is_some() {
            data.vn_copy_symbol_if_valid(newvn, const0, glb)?;
        } else if data.vn(const1).get_symbol_entry().is_some() {
            data.vn_copy_symbol_if_valid(newvn, const1, glb)?;
        }
        data.op_set_input(op, newvn, 1)?;
        data.op_set_input(op, sub2, 0)?;
        Ok(1)
    }
}

pub struct RuleLoadVarnode {
    pub base: RuleBase,
}

impl RuleLoadVarnode {
    pub fn new(group: &str) -> RuleLoadVarnode {
        RuleLoadVarnode {
            base: RuleBase::new(group, 0, "loadvarnode"),
        }
    }

    pub fn correct_spacebase(
        glb: &Architecture,
        vn: VarnodeId,
        spc: Option<SpaceRef>,
        data: &Funcdata,
    ) -> Result<Option<SpaceRef>> {
        if !data.vn(vn).is_spacebase() {
            return Ok(None);
        }
        if data.vn(vn).is_constant() {
            return Ok(spc);
        }
        if !data.vn(vn).is_input() {
            return Ok(None);
        }
        let assoc = glb.get_space_by_spacebase(data.vn(vn).get_addr(), data.vn(vn).get_size())?;
        if !same_space(&assoc.get_contain(), &spc) {
            return Ok(None);
        }
        Ok(Some(assoc))
    }

    pub fn vn_spacebase(
        glb: &Architecture,
        vn: VarnodeId,
        val: &mut u64,
        spc: Option<SpaceRef>,
        data: &Funcdata,
    ) -> Result<Option<SpaceRef>> {
        let retspace = RuleLoadVarnode::correct_spacebase(glb, vn, spc.clone(), data)?;
        if retspace.is_some() {
            *val = 0;
            return Ok(retspace);
        }
        if !data.vn(vn).is_written() {
            return Ok(None);
        }
        let op = data.vn(vn).get_def().expect("written varnode without defining op");
        if data.op(op).code() != OpCode::IntAdd {
            return Ok(None);
        }
        let vn1 = data.op(op).get_in(0);
        let vn2 = data.op(op).get_in(1);
        let retspace = RuleLoadVarnode::correct_spacebase(glb, vn1, spc.clone(), data)?;
        if retspace.is_some() {
            if data.vn(vn2).is_constant() {
                *val = data.vn(vn2).get_offset();
                return Ok(retspace);
            }
            return Ok(None);
        }
        let retspace = RuleLoadVarnode::correct_spacebase(glb, vn2, spc, data)?;
        if retspace.is_some() && data.vn(vn1).is_constant() {
            *val = data.vn(vn1).get_offset();
            return Ok(retspace);
        }
        Ok(None)
    }

    pub fn check_spacebase(
        glb: &Architecture,
        op: OpId,
        offoff: &mut u64,
        data: &Funcdata,
    ) -> Result<Option<SpaceRef>> {
        let mut offvn = data.op(op).get_in(1);
        let loadspace = data.vn(data.op(op).get_in(0)).get_space_from_const(&glb.manager);
        let segment_def = if data.vn(offvn).is_written() {
            data.vn(offvn)
                .get_def()
                .filter(|def| data.op(*def).code() == OpCode::Segmentop)
        } else {
            None
        };
        if let Some(segop) = segment_def {
            offvn = data.op(segop).get_in(2);
            if data.vn(offvn).is_constant() {
                return Ok(None);
            }
        } else if data.vn(offvn).is_constant() {
            *offoff = data.vn(offvn).get_offset();
            return Ok(loadspace);
        }
        RuleLoadVarnode::vn_spacebase(glb, offvn, offoff, loadspace, data)
    }
}

impl Rule for RuleLoadVarnode {
    fn base(&self) -> &RuleBase {
        &self.base
    }

    fn base_mut(&mut self) -> &mut RuleBase {
        &mut self.base
    }

    fn clone_rule(&self, grouplist: &ActionGroupList) -> Option<Box<dyn Rule>> {
        if !grouplist.contains(self.get_group()) {
            return None;
        }
        Some(Box::new(RuleLoadVarnode::new(self.get_group())))
    }

    fn get_op_list(&self, oplist: &mut Vec<OpCode>) {
        oplist.push(OpCode::Load);
    }

    fn apply_op(&mut self, op: OpId, data: &mut Funcdata, glb: &mut Architecture) -> Result<i32> {
        let mut offoff: u64 = 0;
        let Some(baseoff) = RuleLoadVarnode::check_spacebase(glb, op, &mut offoff, data)? else {
            return Ok(0);
        };
        let refvn = data.op(op).get_out().expect("op without output");
        let size = data.vn(refvn).get_size();
        offoff = AddrSpace::address_to_byte(offoff, baseoff.get_word_size());
        let newvn = data.new_varnode_space_offset(size, &baseoff, offoff, glb)?;
        data.op_set_input(op, newvn, 0)?;
        data.op_remove_input(op, 1);
        data.op_set_opcode(op, OpCode::Copy, glb);
        if data.vn(refvn).is_spacebase_placeholder() {
            data.vn_mut(refvn).clear_spacebase_placeholder();
            if let Some(place_op) = data.vn(refvn).lone_descend()
                && let Some(fc) = data.get_call_specs_op(place_op)
            {
                FuncCallSpecs::resolve_spacebase_relative(data, fc, refvn, glb)?;
            }
        }
        Ok(1)
    }
}

pub struct RuleStoreVarnode {
    pub base: RuleBase,
}

impl RuleStoreVarnode {
    pub fn new(group: &str) -> RuleStoreVarnode {
        RuleStoreVarnode {
            base: RuleBase::new(group, 0, "storevarnode"),
        }
    }
}

impl Rule for RuleStoreVarnode {
    fn base(&self) -> &RuleBase {
        &self.base
    }

    fn base_mut(&mut self) -> &mut RuleBase {
        &mut self.base
    }

    fn clone_rule(&self, grouplist: &ActionGroupList) -> Option<Box<dyn Rule>> {
        if !grouplist.contains(self.get_group()) {
            return None;
        }
        Some(Box::new(RuleStoreVarnode::new(self.get_group())))
    }

    fn get_op_list(&self, oplist: &mut Vec<OpCode>) {
        oplist.push(OpCode::Store);
    }

    fn apply_op(&mut self, op: OpId, data: &mut Funcdata, glb: &mut Architecture) -> Result<i32> {
        let mut offoff: u64 = 0;
        let Some(baseoff) = RuleLoadVarnode::check_spacebase(glb, op, &mut offoff, data)? else {
            return Ok(0);
        };
        let size = data.vn(data.op(op).get_in(2)).get_size();
        offoff = AddrSpace::address_to_byte(offoff, baseoff.get_word_size());
        let addr = Address::new(baseoff.clone(), offoff);
        let newout = data.new_varnode_out(size, &addr, op, glb)?;
        data.vn_mut(newout).set_stack_store();
        data.op_remove_input(op, 1);
        data.op_remove_input(op, 0);
        data.op_set_opcode(op, OpCode::Copy, glb);
        if data.op(op).is_store_unmapped() {
            let scope = data.get_scope_local().expect("function without local scope");
            Database::local_mark_not_mapped(glb, data, scope, &baseoff, offoff, size, false);
        }
        data.op_collapse_indirects_for_copy(op, glb)?;
        Ok(1)
    }
}

pub struct RuleSubExtComm {
    pub base: RuleBase,
}

impl RuleSubExtComm {
    pub fn new(group: &str) -> RuleSubExtComm {
        RuleSubExtComm {
            base: RuleBase::new(group, 0, "subextcomm"),
        }
    }
}

impl Rule for RuleSubExtComm {
    fn base(&self) -> &RuleBase {
        &self.base
    }

    fn base_mut(&mut self) -> &mut RuleBase {
        &mut self.base
    }

    fn clone_rule(&self, grouplist: &ActionGroupList) -> Option<Box<dyn Rule>> {
        if !grouplist.contains(self.get_group()) {
            return None;
        }
        Some(Box::new(RuleSubExtComm::new(self.get_group())))
    }

    fn get_op_list(&self, oplist: &mut Vec<OpCode>) {
        oplist.push(OpCode::Subpiece);
    }

    fn apply_op(&mut self, op: OpId, data: &mut Funcdata, glb: &mut Architecture) -> Result<i32> {
        let base = data.op(op).get_in(0);
        if !data.vn(base).is_written() {
            return Ok(0);
        }
        let extop = data.vn(base).get_def().expect("written varnode without defining op");
        let extopc = data.op(extop).code();
        if extopc != OpCode::IntZext && extopc != OpCode::IntSext {
            return Ok(0);
        }
        let invn = data.op(extop).get_in(0);
        if data.vn(invn).is_free() {
            return Ok(0);
        }
        let subcut = data.vn(data.op(op).get_in(1)).get_offset() as i32;
        let outsize = data.vn(data.op(op).get_out().expect("op without output")).get_size();
        let insize = data.vn(invn).get_size();
        if outsize + subcut <= insize {
            data.op_set_input(op, invn, 0)?;
            if insize == outsize {
                data.op_remove_input(op, 1);
                data.op_set_opcode(op, OpCode::Copy, glb);
            }
            return Ok(1);
        }
        if subcut >= insize {
            return Ok(0);
        }
        let newvn = if subcut != 0 {
            let addr = data.op(op).get_addr().clone();
            let newop = data.new_op(2, &addr);
            data.op_set_opcode(newop, OpCode::Subpiece, glb);
            let newvn = data.new_unique_out(insize - subcut, newop, glb)?;
            let constsize = data.vn(data.op(op).get_in(1)).get_size();
            let cutvn = data.new_constant(constsize, subcut as u64, glb);
            data.op_set_input(newop, cutvn, 1)?;
            data.op_set_input(newop, invn, 0)?;
            data.op_insert_before(newop, op);
            newvn
        } else {
            invn
        };
        data.op_remove_input(op, 1);
        data.op_set_opcode(op, extopc, glb);
        data.op_set_input(op, newvn, 0)?;
        Ok(1)
    }
}

pub struct RuleSubCommute {
    pub base: RuleBase,
}

impl RuleSubCommute {
    pub fn new(group: &str) -> RuleSubCommute {
        RuleSubCommute {
            base: RuleBase::new(group, 0, "subcommute"),
        }
    }

    pub fn shorten_extension(
        ext_op: OpId,
        max_size: i32,
        data: &mut Funcdata,
        glb: &mut Architecture,
    ) -> Result<VarnodeId> {
        let orig_out = data.op(ext_op).get_out().expect("op without output");
        let mut addr = data.vn(orig_out).get_addr().clone();
        if addr.is_big_endian() {
            addr = addr.add((data.vn(orig_out).get_size() - max_size) as i64);
        }
        data.op_unset_output(ext_op)?;
        data.new_varnode_out(max_size, &addr, ext_op, glb)
    }

    pub fn cancel_extensions(
        longform: OpId,
        sub_op: OpId,
        ext0_in: VarnodeId,
        ext1_in: VarnodeId,
        data: &mut Funcdata,
        glb: &mut Architecture,
    ) -> Result<bool> {
        let mut ext0_in = ext0_in;
        let mut ext1_in = ext1_in;
        let outvn = data.op(longform).get_out().expect("op without output");
        if data.vn(outvn).lone_descend() != Some(sub_op) {
            return Ok(false);
        }
        let size0 = data.vn(ext0_in).get_size();
        let size1 = data.vn(ext1_in).get_size();
        let max_size: i32;
        if size0 == size1 {
            max_size = size0;
            if data.vn(ext0_in).is_free() && !data.vn(ext0_in).is_constant() {
                return Ok(false);
            }
            if data.vn(ext1_in).is_free() && !data.vn(ext1_in).is_constant() {
                return Ok(false);
            }
        } else if size0 < size1 {
            max_size = size1;
            if data.vn(ext1_in).is_free() && !data.vn(ext1_in).is_constant() {
                return Ok(false);
            }
            let longin = data.op(longform).get_in(0);
            if data.vn(longin).lone_descend() != Some(longform) {
                return Ok(false);
            }
            let extdef = data.vn(longin).get_def().expect("written varnode without defining op");
            ext0_in = RuleSubCommute::shorten_extension(extdef, max_size, data, glb)?;
        } else {
            max_size = size0;
            if data.vn(ext0_in).is_free() && !data.vn(ext0_in).is_constant() {
                return Ok(false);
            }
            let longin = data.op(longform).get_in(1);
            if data.vn(longin).lone_descend() != Some(longform) {
                return Ok(false);
            }
            let extdef = data.vn(longin).get_def().expect("written varnode without defining op");
            ext1_in = RuleSubCommute::shorten_extension(extdef, max_size, data, glb)?;
        }
        data.op_unset_output(longform)?;
        let outvn = data.new_unique_out(max_size, longform, glb)?;
        data.op_set_input(longform, ext0_in, 0)?;
        data.op_set_input(longform, ext1_in, 1)?;
        data.op_set_input(sub_op, outvn, 0)?;
        Ok(true)
    }
}

impl Rule for RuleSubCommute {
    fn base(&self) -> &RuleBase {
        &self.base
    }

    fn base_mut(&mut self) -> &mut RuleBase {
        &mut self.base
    }

    fn clone_rule(&self, grouplist: &ActionGroupList) -> Option<Box<dyn Rule>> {
        if !grouplist.contains(self.get_group()) {
            return None;
        }
        Some(Box::new(RuleSubCommute::new(self.get_group())))
    }

    fn get_op_list(&self, oplist: &mut Vec<OpCode>) {
        oplist.push(OpCode::Subpiece);
    }

    fn apply_op(&mut self, op: OpId, data: &mut Funcdata, glb: &mut Architecture) -> Result<i32> {
        let base = data.op(op).get_in(0);
        if !data.vn(base).is_written() {
            return Ok(0);
        }
        let offset = data.vn(data.op(op).get_in(1)).get_offset() as i32;
        let outvn = data.op(op).get_out().expect("op without output");
        if data.vn(outvn).is_precis_lo() || data.vn(outvn).is_precis_hi() {
            return Ok(0);
        }
        let insize = data.vn(base).get_size();
        let outsize = data.vn(outvn).get_size();
        let longform = data.vn(base).get_def().expect("written varnode without defining op");
        let mut skip_slot: i32 = -1;
        match data.op(longform).code() {
            OpCode::IntLeft => {
                skip_slot = 1;
                if offset != 0 {
                    return Ok(0);
                }
                let longin = data.op(longform).get_in(0);
                if data.vn(longin).is_written() {
                    let opc = data
                        .op(data.vn(longin).get_def().expect("written varnode without defining op"))
                        .code();
                    if opc != OpCode::IntZext && opc != OpCode::Piece {
                        return Ok(0);
                    }
                } else {
                    return Ok(0);
                }
            }
            OpCode::IntRem | OpCode::IntDiv => {
                if offset != 0 {
                    return Ok(0);
                }
                let longin0 = data.op(longform).get_in(0);
                if !data.vn(longin0).is_written() {
                    return Ok(0);
                }
                let zext0 = data.vn(longin0).get_def().expect("written varnode without defining op");
                if data.op(zext0).code() != OpCode::IntZext {
                    return Ok(0);
                }
                let zext0_in = data.op(zext0).get_in(0);
                let longin1 = data.op(longform).get_in(1);
                if data.vn(longin1).is_written() {
                    let zext1 = data.vn(longin1).get_def().expect("written varnode without defining op");
                    if data.op(zext1).code() != OpCode::IntZext {
                        return Ok(0);
                    }
                    let zext1_in = data.op(zext1).get_in(0);
                    if data.vn(zext1_in).get_size() > outsize || data.vn(zext0_in).get_size() > outsize {
                        if RuleSubCommute::cancel_extensions(longform, op, zext0_in, zext1_in, data, glb)? {
                            return Ok(1);
                        }
                        return Ok(0);
                    }
                } else if data.vn(longin1).is_constant() && data.vn(zext0_in).get_size() <= outsize {
                    let val = data.vn(longin1).get_offset();
                    let smallval = val & calc_mask(outsize);
                    if val != smallval {
                        return Ok(0);
                    }
                } else {
                    return Ok(0);
                }
            }
            OpCode::IntSrem | OpCode::IntSdiv => {
                if offset != 0 {
                    return Ok(0);
                }
                let longin0 = data.op(longform).get_in(0);
                if !data.vn(longin0).is_written() {
                    return Ok(0);
                }
                let sext0 = data.vn(longin0).get_def().expect("written varnode without defining op");
                if data.op(sext0).code() != OpCode::IntSext {
                    return Ok(0);
                }
                let sext0_in = data.op(sext0).get_in(0);
                let longin1 = data.op(longform).get_in(1);
                if data.vn(longin1).is_written() {
                    let sext1 = data.vn(longin1).get_def().expect("written varnode without defining op");
                    if data.op(sext1).code() != OpCode::IntSext {
                        return Ok(0);
                    }
                    let sext1_in = data.op(sext1).get_in(0);
                    if data.vn(sext1_in).get_size() > outsize || data.vn(sext0_in).get_size() > outsize {
                        if RuleSubCommute::cancel_extensions(longform, op, sext0_in, sext1_in, data, glb)? {
                            return Ok(1);
                        }
                        return Ok(0);
                    }
                } else if data.vn(longin1).is_constant() && data.vn(sext0_in).get_size() <= outsize {
                    let val = data.vn(longin1).get_offset();
                    let mut smallval = val & calc_mask(outsize);
                    smallval = sign_extend_size(smallval, outsize, insize);
                    if val != smallval {
                        return Ok(0);
                    }
                } else {
                    return Ok(0);
                }
            }
            OpCode::IntAdd => {
                if offset != 0 {
                    return Ok(0);
                }
                if data.vn(data.op(longform).get_in(0)).is_spacebase() {
                    return Ok(0);
                }
            }
            OpCode::IntMult => {
                if offset != 0 {
                    return Ok(0);
                }
            }
            OpCode::IntNegate | OpCode::IntXor | OpCode::IntAnd | OpCode::IntOr => {}
            _ => return Ok(0),
        }
        if data.vn(base).lone_descend() != Some(op) {
            return Ok(0);
        }
        if offset == 0
            && let Some(nextop) = data.vn(outvn).lone_descend()
            && data.op(nextop).code() == OpCode::IntZext
            && data
                .vn(data.op(nextop).get_out().expect("op without output"))
                .get_size()
                == insize
        {
            return Ok(0);
        }
        let mut last_in: Option<VarnodeId> = None;
        let mut new_vn: Option<VarnodeId> = None;
        for slot in 0..data.op(longform).num_input() {
            let vn = data.op(longform).get_in(slot);
            if slot != skip_slot {
                if last_in != Some(vn) || new_vn.is_none() {
                    let addr = data.op(op).get_addr().clone();
                    let newsub = data.new_op(2, &addr);
                    data.op_set_opcode(newsub, OpCode::Subpiece, glb);
                    let created = data.new_unique_out(outsize, newsub, glb)?;
                    new_vn = Some(created);
                    data.op_set_input(longform, created, slot)?;
                    data.op_set_input(newsub, vn, 0)?;
                    let offsetvn = data.new_constant(4, offset as u64, glb);
                    data.op_set_input(newsub, offsetvn, 1)?;
                    data.op_insert_before(newsub, longform);
                } else {
                    data.op_set_input(longform, new_vn.expect("missing commuted SUBPIECE output"), slot)?;
                }
            }
            last_in = Some(vn);
        }
        data.op_set_output(longform, outvn, glb)?;
        data.op_destroy(op)?;
        Ok(1)
    }
}

pub struct RuleConcatCommute {
    pub base: RuleBase,
}

impl RuleConcatCommute {
    pub fn new(group: &str) -> RuleConcatCommute {
        RuleConcatCommute {
            base: RuleBase::new(group, 0, "concatcommute"),
        }
    }
}

impl Rule for RuleConcatCommute {
    fn base(&self) -> &RuleBase {
        &self.base
    }

    fn base_mut(&mut self) -> &mut RuleBase {
        &mut self.base
    }

    fn clone_rule(&self, grouplist: &ActionGroupList) -> Option<Box<dyn Rule>> {
        if !grouplist.contains(self.get_group()) {
            return None;
        }
        Some(Box::new(RuleConcatCommute::new(self.get_group())))
    }

    fn get_op_list(&self, oplist: &mut Vec<OpCode>) {
        oplist.push(OpCode::Piece);
    }

    fn apply_op(&mut self, op: OpId, data: &mut Funcdata, glb: &mut Architecture) -> Result<i32> {
        let outsz = data.vn(data.op(op).get_out().expect("op without output")).get_size();
        if outsz > 8 {
            return Ok(0);
        }
        for slot in 0..2 {
            let vn = data.op(op).get_in(slot);
            if !data.vn(vn).is_written() {
                continue;
            }
            let logicop = data.vn(vn).get_def().expect("written varnode without defining op");
            let opc = data.op(logicop).code();
            let hi: VarnodeId;
            let lo: VarnodeId;
            let mut val: u64;
            if opc == OpCode::IntOr || opc == OpCode::IntXor {
                if !data.vn(data.op(logicop).get_in(1)).is_constant() {
                    continue;
                }
                val = data.vn(data.op(logicop).get_in(1)).get_offset();
                if slot == 0 {
                    hi = data.op(logicop).get_in(0);
                    lo = data.op(op).get_in(1);
                    val = val.wrapping_shl((8 * data.vn(lo).get_size()) as u32);
                } else {
                    hi = data.op(op).get_in(0);
                    lo = data.op(logicop).get_in(0);
                }
            } else if opc == OpCode::IntAnd {
                if !data.vn(data.op(logicop).get_in(1)).is_constant() {
                    continue;
                }
                val = data.vn(data.op(logicop).get_in(1)).get_offset();
                if slot == 0 {
                    hi = data.op(logicop).get_in(0);
                    lo = data.op(op).get_in(1);
                    val = val.wrapping_shl((8 * data.vn(lo).get_size()) as u32);
                    val |= calc_mask(data.vn(lo).get_size());
                } else {
                    hi = data.op(op).get_in(0);
                    lo = data.op(logicop).get_in(0);
                    val |= calc_mask(data.vn(hi).get_size()).wrapping_shl((8 * data.vn(lo).get_size()) as u32);
                }
            } else {
                continue;
            }
            if data.vn(hi).is_free() {
                continue;
            }
            if data.vn(lo).is_free() {
                continue;
            }
            let addr = data.op(op).get_addr().clone();
            let newconcat = data.new_op(2, &addr);
            data.op_set_opcode(newconcat, OpCode::Piece, glb);
            let newvn = data.new_unique_out(outsz, newconcat, glb)?;
            data.op_set_input(newconcat, hi, 0)?;
            data.op_set_input(newconcat, lo, 1)?;
            data.op_insert_before(newconcat, op);
            data.op_set_opcode(op, opc, glb);
            data.op_set_input(op, newvn, 0)?;
            let newsize = data.vn(newvn).get_size();
            let newconst = data.new_constant(newsize, val, glb);
            data.op_set_input(op, newconst, 1)?;
            return Ok(1);
        }
        Ok(0)
    }
}

pub struct RuleConcatZext {
    pub base: RuleBase,
}

impl RuleConcatZext {
    pub fn new(group: &str) -> RuleConcatZext {
        RuleConcatZext {
            base: RuleBase::new(group, 0, "concatzext"),
        }
    }
}

impl Rule for RuleConcatZext {
    fn base(&self) -> &RuleBase {
        &self.base
    }

    fn base_mut(&mut self) -> &mut RuleBase {
        &mut self.base
    }

    fn clone_rule(&self, grouplist: &ActionGroupList) -> Option<Box<dyn Rule>> {
        if !grouplist.contains(self.get_group()) {
            return None;
        }
        Some(Box::new(RuleConcatZext::new(self.get_group())))
    }

    fn get_op_list(&self, oplist: &mut Vec<OpCode>) {
        oplist.push(OpCode::Piece);
    }

    fn apply_op(&mut self, op: OpId, data: &mut Funcdata, glb: &mut Architecture) -> Result<i32> {
        let hi = data.op(op).get_in(0);
        if !data.vn(hi).is_written() {
            return Ok(0);
        }
        let zextop = data.vn(hi).get_def().expect("written varnode without defining op");
        if data.op(zextop).code() != OpCode::IntZext {
            return Ok(0);
        }
        let hi = data.op(zextop).get_in(0);
        let lo = data.op(op).get_in(1);
        if data.vn(hi).is_free() {
            return Ok(0);
        }
        if data.vn(lo).is_free() {
            return Ok(0);
        }
        let addr = data.op(op).get_addr().clone();
        let newconcat = data.new_op(2, &addr);
        data.op_set_opcode(newconcat, OpCode::Piece, glb);
        let newsize = data.vn(hi).get_size() + data.vn(lo).get_size();
        let newvn = data.new_unique_out(newsize, newconcat, glb)?;
        data.op_set_input(newconcat, hi, 0)?;
        data.op_set_input(newconcat, lo, 1)?;
        data.op_insert_before(newconcat, op);
        data.op_remove_input(op, 1);
        data.op_set_input(op, newvn, 0)?;
        data.op_set_opcode(op, OpCode::IntZext, glb);
        Ok(1)
    }
}

pub struct RuleZextCommute {
    pub base: RuleBase,
}

impl RuleZextCommute {
    pub fn new(group: &str) -> RuleZextCommute {
        RuleZextCommute {
            base: RuleBase::new(group, 0, "zextcommute"),
        }
    }
}

impl Rule for RuleZextCommute {
    fn base(&self) -> &RuleBase {
        &self.base
    }

    fn base_mut(&mut self) -> &mut RuleBase {
        &mut self.base
    }

    fn clone_rule(&self, grouplist: &ActionGroupList) -> Option<Box<dyn Rule>> {
        if !grouplist.contains(self.get_group()) {
            return None;
        }
        Some(Box::new(RuleZextCommute::new(self.get_group())))
    }

    fn get_op_list(&self, oplist: &mut Vec<OpCode>) {
        oplist.push(OpCode::IntRight);
    }

    fn apply_op(&mut self, op: OpId, data: &mut Funcdata, glb: &mut Architecture) -> Result<i32> {
        let zextvn = data.op(op).get_in(0);
        if !data.vn(zextvn).is_written() {
            return Ok(0);
        }
        let zextop = data.vn(zextvn).get_def().expect("written varnode without defining op");
        if data.op(zextop).code() != OpCode::IntZext {
            return Ok(0);
        }
        let zextin = data.op(zextop).get_in(0);
        if data.vn(zextin).is_free() {
            return Ok(0);
        }
        let savn = data.op(op).get_in(1);
        if !data.vn(savn).is_constant() && data.vn(savn).is_free() {
            return Ok(0);
        }
        let addr = data.op(op).get_addr().clone();
        let newop = data.new_op(2, &addr);
        data.op_set_opcode(newop, OpCode::IntRight, glb);
        let insize = data.vn(zextin).get_size();
        let newout = data.new_unique_out(insize, newop, glb)?;
        data.op_remove_input(op, 1);
        data.op_set_input(op, newout, 0)?;
        data.op_set_opcode(op, OpCode::IntZext, glb);
        data.op_set_input(newop, zextin, 0)?;
        data.op_set_input(newop, savn, 1)?;
        data.op_insert_before(newop, op);
        Ok(1)
    }
}

pub struct RuleZextShiftZext {
    pub base: RuleBase,
}

impl RuleZextShiftZext {
    pub fn new(group: &str) -> RuleZextShiftZext {
        RuleZextShiftZext {
            base: RuleBase::new(group, 0, "zextshiftzext"),
        }
    }
}

impl Rule for RuleZextShiftZext {
    fn base(&self) -> &RuleBase {
        &self.base
    }

    fn base_mut(&mut self) -> &mut RuleBase {
        &mut self.base
    }

    fn clone_rule(&self, grouplist: &ActionGroupList) -> Option<Box<dyn Rule>> {
        if !grouplist.contains(self.get_group()) {
            return None;
        }
        Some(Box::new(RuleZextShiftZext::new(self.get_group())))
    }

    fn get_op_list(&self, oplist: &mut Vec<OpCode>) {
        oplist.push(OpCode::IntZext);
    }

    fn apply_op(&mut self, op: OpId, data: &mut Funcdata, glb: &mut Architecture) -> Result<i32> {
        let invn = data.op(op).get_in(0);
        if !data.vn(invn).is_written() {
            return Ok(0);
        }
        let shiftop = data.vn(invn).get_def().expect("written varnode without defining op");
        if data.op(shiftop).code() == OpCode::IntZext {
            let vn = data.op(shiftop).get_in(0);
            if data.vn(vn).is_free() && !data.vn(vn).is_constant() {
                return Ok(0);
            }
            if data.vn(invn).lone_descend() != Some(op) {
                return Ok(0);
            }
            data.op_set_input(op, vn, 0)?;
            return Ok(1);
        }
        if data.op(shiftop).code() != OpCode::IntLeft {
            return Ok(0);
        }
        if !data.vn(data.op(shiftop).get_in(1)).is_constant() {
            return Ok(0);
        }
        let shiftin = data.op(shiftop).get_in(0);
        if !data.vn(shiftin).is_written() {
            return Ok(0);
        }
        let zext2op = data.vn(shiftin).get_def().expect("written varnode without defining op");
        if data.op(zext2op).code() != OpCode::IntZext {
            return Ok(0);
        }
        let rootvn = data.op(zext2op).get_in(0);
        if data.vn(rootvn).is_free() {
            return Ok(0);
        }
        let shift_amount = data.vn(data.op(shiftop).get_in(1)).get_offset();
        let zext2size = data
            .vn(data.op(zext2op).get_out().expect("op without output"))
            .get_size();
        let limit = ((zext2size - data.vn(rootvn).get_size()) as u64).wrapping_mul(8);
        if shift_amount > limit {
            return Ok(0);
        }
        let addr = data.op(op).get_addr().clone();
        let newop = data.new_op(1, &addr);
        data.op_set_opcode(newop, OpCode::IntZext, glb);
        let outsize = data.vn(data.op(op).get_out().expect("op without output")).get_size();
        let outvn = data.new_unique_out(outsize, newop, glb)?;
        data.op_set_input(newop, rootvn, 0)?;
        data.op_set_opcode(op, OpCode::IntLeft, glb);
        data.op_set_input(op, outvn, 0)?;
        let amountvn = data.new_constant(4, shift_amount, glb);
        data.op_insert_input(op, amountvn, 1)?;
        data.op_insert_before(newop, op);
        Ok(1)
    }
}

pub struct RuleShiftAnd {
    pub base: RuleBase,
}

impl RuleShiftAnd {
    pub fn new(group: &str) -> RuleShiftAnd {
        RuleShiftAnd {
            base: RuleBase::new(group, 0, "shiftand"),
        }
    }
}

impl Rule for RuleShiftAnd {
    fn base(&self) -> &RuleBase {
        &self.base
    }

    fn base_mut(&mut self) -> &mut RuleBase {
        &mut self.base
    }

    fn clone_rule(&self, grouplist: &ActionGroupList) -> Option<Box<dyn Rule>> {
        if !grouplist.contains(self.get_group()) {
            return None;
        }
        Some(Box::new(RuleShiftAnd::new(self.get_group())))
    }

    fn get_op_list(&self, oplist: &mut Vec<OpCode>) {
        oplist.push(OpCode::IntRight);
        oplist.push(OpCode::IntLeft);
        oplist.push(OpCode::IntMult);
    }

    fn apply_op(&mut self, op: OpId, data: &mut Funcdata, _glb: &mut Architecture) -> Result<i32> {
        let cvn = data.op(op).get_in(1);
        if !data.vn(cvn).is_constant() {
            return Ok(0);
        }
        let shiftin = data.op(op).get_in(0);
        if !data.vn(shiftin).is_written() {
            return Ok(0);
        }
        let andop = data.vn(shiftin).get_def().expect("written varnode without defining op");
        if data.op(andop).code() != OpCode::IntAnd {
            return Ok(0);
        }
        let maskvn = data.op(andop).get_in(1);
        if !data.vn(maskvn).is_constant() {
            return Ok(0);
        }
        let mut mask = data.vn(maskvn).get_offset();
        let invn = data.op(andop).get_in(0);
        if data.vn(invn).is_free() {
            return Ok(0);
        }
        let mut opc = data.op(op).code();
        let shift_amount: i32;
        if opc == OpCode::IntRight || opc == OpCode::IntLeft {
            shift_amount = data.vn(cvn).get_offset() as i32;
        } else {
            shift_amount = leastsigbit_set(data.vn(cvn).get_offset());
            if shift_amount <= 0 {
                return Ok(0);
            }
            let testval = 1u64.wrapping_shl(shift_amount as u32);
            if testval != data.vn(cvn).get_offset() {
                return Ok(0);
            }
            opc = OpCode::IntLeft;
        }
        let mut nzm = data.vn(invn).get_nz_mask();
        let fullmask = calc_mask(data.vn(invn).get_size());
        if opc == OpCode::IntRight {
            nzm = nzm.wrapping_shr(shift_amount as u32);
            mask = mask.wrapping_shr(shift_amount as u32);
        } else {
            nzm = nzm.wrapping_shl(shift_amount as u32);
            mask = mask.wrapping_shl(shift_amount as u32);
            nzm &= fullmask;
            mask &= fullmask;
        }
        if (mask & nzm) != nzm {
            return Ok(0);
        }
        data.op_set_input(op, invn, 0)?;
        Ok(1)
    }
}

pub struct RuleConcatZero {
    pub base: RuleBase,
}

impl RuleConcatZero {
    pub fn new(group: &str) -> RuleConcatZero {
        RuleConcatZero {
            base: RuleBase::new(group, 0, "concatzero"),
        }
    }
}

impl Rule for RuleConcatZero {
    fn base(&self) -> &RuleBase {
        &self.base
    }

    fn base_mut(&mut self) -> &mut RuleBase {
        &mut self.base
    }

    fn clone_rule(&self, grouplist: &ActionGroupList) -> Option<Box<dyn Rule>> {
        if !grouplist.contains(self.get_group()) {
            return None;
        }
        Some(Box::new(RuleConcatZero::new(self.get_group())))
    }

    fn get_op_list(&self, oplist: &mut Vec<OpCode>) {
        oplist.push(OpCode::Piece);
    }

    fn apply_op(&mut self, op: OpId, data: &mut Funcdata, glb: &mut Architecture) -> Result<i32> {
        let lowvn = data.op(op).get_in(1);
        if !data.vn(lowvn).is_constant() {
            return Ok(0);
        }
        if data.vn(lowvn).get_offset() != 0 {
            return Ok(0);
        }
        let shift_amount = 8 * data.vn(lowvn).get_size();
        let highvn = data.op(op).get_in(0);
        if data.vn(highvn).is_constant() && data.vn(highvn).get_offset() == 0 {
            return Ok(0);
        }
        let addr = data.op(op).get_addr().clone();
        let newop = data.new_op(1, &addr);
        let outsize = data.vn(data.op(op).get_out().expect("op without output")).get_size();
        let outvn = data.new_unique_out(outsize, newop, glb)?;
        data.op_set_opcode(newop, OpCode::IntZext, glb);
        data.op_set_opcode(op, OpCode::IntLeft, glb);
        data.op_set_input(op, outvn, 0)?;
        let amountvn = data.new_constant(4, shift_amount as u64, glb);
        data.op_set_input(op, amountvn, 1)?;
        data.op_set_input(newop, highvn, 0)?;
        data.op_insert_before(newop, op);
        Ok(1)
    }
}

pub struct RuleConcatLeftShift {
    pub base: RuleBase,
}

impl RuleConcatLeftShift {
    pub fn new(group: &str) -> RuleConcatLeftShift {
        RuleConcatLeftShift {
            base: RuleBase::new(group, 0, "concatleftshift"),
        }
    }
}

impl Rule for RuleConcatLeftShift {
    fn base(&self) -> &RuleBase {
        &self.base
    }

    fn base_mut(&mut self) -> &mut RuleBase {
        &mut self.base
    }

    fn clone_rule(&self, grouplist: &ActionGroupList) -> Option<Box<dyn Rule>> {
        if !grouplist.contains(self.get_group()) {
            return None;
        }
        Some(Box::new(RuleConcatLeftShift::new(self.get_group())))
    }

    fn get_op_list(&self, oplist: &mut Vec<OpCode>) {
        oplist.push(OpCode::Piece);
    }

    fn apply_op(&mut self, op: OpId, data: &mut Funcdata, glb: &mut Architecture) -> Result<i32> {
        let vn2 = data.op(op).get_in(1);
        if !data.vn(vn2).is_written() {
            return Ok(0);
        }
        let shiftop = data.vn(vn2).get_def().expect("written varnode without defining op");
        if data.op(shiftop).code() != OpCode::IntLeft {
            return Ok(0);
        }
        if !data.vn(data.op(shiftop).get_in(1)).is_constant() {
            return Ok(0);
        }
        let mut shift_amount = data.vn(data.op(shiftop).get_in(1)).get_offset() as i32;
        if (shift_amount & 7) != 0 {
            return Ok(0);
        }
        let tmpvn = data.op(shiftop).get_in(0);
        if !data.vn(tmpvn).is_written() {
            return Ok(0);
        }
        let zextop = data.vn(tmpvn).get_def().expect("written varnode without defining op");
        if data.op(zextop).code() != OpCode::IntZext {
            return Ok(0);
        }
        let lowvn = data.op(zextop).get_in(0);
        if data.vn(lowvn).is_free() {
            return Ok(0);
        }
        let vn1 = data.op(op).get_in(0);
        if data.vn(vn1).is_free() {
            return Ok(0);
        }
        shift_amount /= 8;
        if shift_amount + data.vn(lowvn).get_size() != data.vn(tmpvn).get_size() {
            return Ok(0);
        }
        let addr = data.op(op).get_addr().clone();
        let newop = data.new_op(2, &addr);
        data.op_set_opcode(newop, OpCode::Piece, glb);
        let newsize = data.vn(vn1).get_size() + data.vn(lowvn).get_size();
        let newout = data.new_unique_out(newsize, newop, glb)?;
        data.op_set_input(newop, vn1, 0)?;
        data.op_set_input(newop, lowvn, 1)?;
        data.op_insert_before(newop, op);
        data.op_set_input(op, newout, 0)?;
        let outsize = data.vn(data.op(op).get_out().expect("op without output")).get_size();
        let zero = data.new_constant(outsize - newsize, 0, glb);
        data.op_set_input(op, zero, 1)?;
        Ok(1)
    }
}

pub struct RuleSubZext {
    pub base: RuleBase,
}

impl RuleSubZext {
    pub fn new(group: &str) -> RuleSubZext {
        RuleSubZext {
            base: RuleBase::new(group, 0, "subzext"),
        }
    }
}

impl Rule for RuleSubZext {
    fn base(&self) -> &RuleBase {
        &self.base
    }

    fn base_mut(&mut self) -> &mut RuleBase {
        &mut self.base
    }

    fn clone_rule(&self, grouplist: &ActionGroupList) -> Option<Box<dyn Rule>> {
        if !grouplist.contains(self.get_group()) {
            return None;
        }
        Some(Box::new(RuleSubZext::new(self.get_group())))
    }

    fn get_op_list(&self, oplist: &mut Vec<OpCode>) {
        oplist.push(OpCode::IntZext);
    }

    fn apply_op(&mut self, op: OpId, data: &mut Funcdata, glb: &mut Architecture) -> Result<i32> {
        let subvn = data.op(op).get_in(0);
        if !data.vn(subvn).is_written() {
            return Ok(0);
        }
        let subop = data.vn(subvn).get_def().expect("written varnode without defining op");
        let outsize = data.vn(data.op(op).get_out().expect("op without output")).get_size();
        if data.op(subop).code() == OpCode::Subpiece {
            let basevn = data.op(subop).get_in(0);
            if data.vn(basevn).is_free() {
                return Ok(0);
            }
            let basesize = data.vn(basevn).get_size();
            if basesize != outsize {
                return Ok(0);
            }
            if basesize > 8 {
                return Ok(0);
            }
            let cutvn = data.op(subop).get_in(1);
            if data.vn(cutvn).get_offset() != 0 {
                if data.vn(subvn).lone_descend() != Some(op) {
                    return Ok(0);
                }
                let newvn = data.new_unique(basesize, None, glb);
                let right_val = data.vn(cutvn).get_offset().wrapping_mul(8);
                data.op_set_input(op, newvn, 0)?;
                data.op_set_opcode(subop, OpCode::IntRight, glb);
                let cutsize = data.vn(cutvn).get_size();
                let shiftvn = data.new_constant(cutsize, right_val, glb);
                data.op_set_input(subop, shiftvn, 1)?;
                data.op_set_output(subop, newvn, glb)?;
            } else {
                data.op_set_input(op, basevn, 0)?;
            }
            let val = calc_mask(data.vn(subvn).get_size());
            let constvn = data.new_constant(basesize, val, glb);
            data.op_set_opcode(op, OpCode::IntAnd, glb);
            data.op_insert_input(op, constvn, 1)?;
            return Ok(1);
        } else if data.op(subop).code() == OpCode::IntRight {
            let shiftop = subop;
            if !data.vn(data.op(shiftop).get_in(1)).is_constant() {
                return Ok(0);
            }
            let midvn = data.op(shiftop).get_in(0);
            if !data.vn(midvn).is_written() {
                return Ok(0);
            }
            let subop = data.vn(midvn).get_def().expect("written varnode without defining op");
            if data.op(subop).code() != OpCode::Subpiece {
                return Ok(0);
            }
            let basevn = data.op(subop).get_in(0);
            if data.vn(basevn).is_free() {
                return Ok(0);
            }
            let basesize = data.vn(basevn).get_size();
            if basesize != outsize {
                return Ok(0);
            }
            if data.vn(midvn).lone_descend() != Some(shiftop) {
                return Ok(0);
            }
            if data.vn(subvn).lone_descend() != Some(op) {
                return Ok(0);
            }
            let mut val = calc_mask(data.vn(midvn).get_size());
            let mut shift_amount = data.vn(data.op(shiftop).get_in(1)).get_offset();
            val = val.wrapping_shr(shift_amount as u32);
            shift_amount = shift_amount.wrapping_add(data.vn(data.op(subop).get_in(1)).get_offset().wrapping_mul(8));
            let newvn = data.new_unique(basesize, None, glb);
            data.op_set_input(op, newvn, 0)?;
            data.op_set_input(shiftop, basevn, 0)?;
            let amountsize = data.vn(data.op(shiftop).get_in(1)).get_size();
            let amountvn = data.new_constant(amountsize, shift_amount, glb);
            data.op_set_input(shiftop, amountvn, 1)?;
            data.op_set_output(shiftop, newvn, glb)?;
            let constvn = data.new_constant(basesize, val, glb);
            data.op_set_opcode(op, OpCode::IntAnd, glb);
            data.op_insert_input(op, constvn, 1)?;
            return Ok(1);
        }
        Ok(0)
    }
}

pub struct RuleSubCancel {
    pub base: RuleBase,
}

impl RuleSubCancel {
    pub fn new(group: &str) -> RuleSubCancel {
        RuleSubCancel {
            base: RuleBase::new(group, 0, "subcancel"),
        }
    }
}

impl Rule for RuleSubCancel {
    fn base(&self) -> &RuleBase {
        &self.base
    }

    fn base_mut(&mut self) -> &mut RuleBase {
        &mut self.base
    }

    fn clone_rule(&self, grouplist: &ActionGroupList) -> Option<Box<dyn Rule>> {
        if !grouplist.contains(self.get_group()) {
            return None;
        }
        Some(Box::new(RuleSubCancel::new(self.get_group())))
    }

    fn get_op_list(&self, oplist: &mut Vec<OpCode>) {
        oplist.push(OpCode::Subpiece);
    }

    fn apply_op(&mut self, op: OpId, data: &mut Funcdata, glb: &mut Architecture) -> Result<i32> {
        let base = data.op(op).get_in(0);
        if !data.vn(base).is_written() {
            return Ok(0);
        }
        let extop = data.vn(base).get_def().expect("written varnode without defining op");
        let mut opc = data.op(extop).code();
        if opc != OpCode::IntZext && opc != OpCode::IntSext && opc != OpCode::IntAnd {
            return Ok(0);
        }
        let offset = data.vn(data.op(op).get_in(1)).get_offset() as i32;
        let outsize = data.vn(data.op(op).get_out().expect("op without output")).get_size();
        if opc == OpCode::IntAnd {
            let cvn = data.op(extop).get_in(1);
            if offset == 0 && data.vn(cvn).is_constant() && data.vn(cvn).get_offset() == calc_mask(outsize) {
                let thruvn = data.op(extop).get_in(0);
                if !data.vn(thruvn).is_free() {
                    data.op_set_input(op, thruvn, 0)?;
                    return Ok(1);
                }
            }
            return Ok(0);
        }
        let insize = data.vn(base).get_size();
        let farinsize = data.vn(data.op(extop).get_in(0)).get_size();
        let mut thruvn: VarnodeId;
        if offset == 0 {
            thruvn = data.op(extop).get_in(0);
            if data.vn(thruvn).is_free() {
                if data.vn(thruvn).is_constant() && insize > 8 && outsize == farinsize {
                    opc = OpCode::Copy;
                    let thrusize = data.vn(thruvn).get_size();
                    let thruoffset = data.vn(thruvn).get_offset();
                    thruvn = data.new_constant(thrusize, thruoffset, glb);
                } else {
                    return Ok(0);
                }
            } else if outsize == farinsize {
                opc = OpCode::Copy;
            } else if outsize < farinsize {
                opc = OpCode::Subpiece;
            }
        } else if opc == OpCode::IntZext && farinsize <= offset {
            opc = OpCode::Copy;
            thruvn = data.new_constant(outsize, 0, glb);
        } else {
            return Ok(0);
        }
        data.op_set_opcode(op, opc, glb);
        data.op_set_input(op, thruvn, 0)?;
        if opc != OpCode::Subpiece {
            data.op_remove_input(op, 1);
        }
        Ok(1)
    }
}

pub struct RuleShiftSub {
    pub base: RuleBase,
}

impl RuleShiftSub {
    pub fn new(group: &str) -> RuleShiftSub {
        RuleShiftSub {
            base: RuleBase::new(group, 0, "shiftsub"),
        }
    }
}

impl Rule for RuleShiftSub {
    fn base(&self) -> &RuleBase {
        &self.base
    }

    fn base_mut(&mut self) -> &mut RuleBase {
        &mut self.base
    }

    fn clone_rule(&self, grouplist: &ActionGroupList) -> Option<Box<dyn Rule>> {
        if !grouplist.contains(self.get_group()) {
            return None;
        }
        Some(Box::new(RuleShiftSub::new(self.get_group())))
    }

    fn get_op_list(&self, oplist: &mut Vec<OpCode>) {
        oplist.push(OpCode::Subpiece);
    }

    fn apply_op(&mut self, op: OpId, data: &mut Funcdata, glb: &mut Architecture) -> Result<i32> {
        let invn = data.op(op).get_in(0);
        if !data.vn(invn).is_written() {
            return Ok(0);
        }
        let shiftop = data.vn(invn).get_def().expect("written varnode without defining op");
        if data.op(shiftop).code() != OpCode::IntLeft {
            return Ok(0);
        }
        let savn = data.op(shiftop).get_in(1);
        if !data.vn(savn).is_constant() {
            return Ok(0);
        }
        let amount = data.vn(savn).get_offset() as i32;
        if (amount & 7) != 0 {
            return Ok(0);
        }
        let mut cut = data.vn(data.op(op).get_in(1)).get_offset() as i32;
        let vn = data.op(shiftop).get_in(0);
        if data.vn(vn).is_free() {
            return Ok(0);
        }
        let insize = data.vn(vn).get_size();
        let outsize = data.vn(data.op(op).get_out().expect("op without output")).get_size();
        cut -= amount / 8;
        if cut < 0 || cut + outsize > insize {
            return Ok(0);
        }
        data.op_set_input(op, vn, 0)?;
        let constsize = data.vn(data.op(op).get_in(1)).get_size();
        let newconst = data.new_constant(constsize, cut as u64, glb);
        data.op_set_input(op, newconst, 1)?;
        Ok(1)
    }
}
