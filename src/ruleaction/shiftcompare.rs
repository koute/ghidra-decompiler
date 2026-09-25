use crate::action::{ActionGroupList, Rule, RuleBase};
use crate::address::{calc_mask, leastsigbit_set, signbit_negative};
use crate::architecture::Architecture;
use crate::error::Result;
use crate::expression::{AddExpression, BooleanMatch, functional_equality};
use crate::funcdata::Funcdata;
use crate::op::OpId;
use crate::opcodes::OpCode;
use crate::varnode::VarnodeId;

pub struct RuleDoubleSub {
    pub base: RuleBase,
}

impl RuleDoubleSub {
    pub fn new(group: &str) -> RuleDoubleSub {
        RuleDoubleSub {
            base: RuleBase::new(group, 0, "doublesub"),
        }
    }
}

impl Rule for RuleDoubleSub {
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
        Some(Box::new(RuleDoubleSub::new(self.get_group())))
    }

    fn get_op_list(&self, oplist: &mut Vec<OpCode>) {
        oplist.push(OpCode::Subpiece);
    }

    fn apply_op(&mut self, op: OpId, data: &mut Funcdata, glb: &mut Architecture) -> Result<i32> {
        let vn = data.op(op).get_in(0);
        if !data.vn(vn).is_written() {
            return Ok(0);
        }
        let op2 = data.vn(vn).get_def().expect("written varnode without defining op");
        if data.op(op2).code() != OpCode::Subpiece {
            return Ok(0);
        }
        let in_vn = data.op(op2).get_in(0);
        if data.vn(in_vn).is_free() {
            return Ok(0);
        }
        let offset1 = data.vn(data.op(op).get_in(1)).get_offset() as i32;
        let offset2 = data.vn(data.op(op2).get_in(1)).get_offset() as i32;
        data.op_set_input(op, in_vn, 0)?;
        let newconst = data.new_constant(4, offset1.wrapping_add(offset2) as u64, glb);
        data.op_set_input(op, newconst, 1)?;
        Ok(1)
    }
}

pub struct RuleDoubleShift {
    pub base: RuleBase,
}

impl RuleDoubleShift {
    pub fn new(group: &str) -> RuleDoubleShift {
        RuleDoubleShift {
            base: RuleBase::new(group, 0, "doubleshift"),
        }
    }
}

impl Rule for RuleDoubleShift {
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
        Some(Box::new(RuleDoubleShift::new(self.get_group())))
    }

    fn get_op_list(&self, oplist: &mut Vec<OpCode>) {
        oplist.push(OpCode::IntLeft);
        oplist.push(OpCode::IntRight);
        oplist.push(OpCode::IntMult);
    }

    fn apply_op(&mut self, op: OpId, data: &mut Funcdata, glb: &mut Architecture) -> Result<i32> {
        if !data.vn(data.op(op).get_in(1)).is_constant() {
            return Ok(0);
        }
        let secvn = data.op(op).get_in(0);
        if !data.vn(secvn).is_written() {
            return Ok(0);
        }
        let secop = data.vn(secvn).get_def().expect("written varnode without defining op");
        let mut opc2 = data.op(secop).code();
        if opc2 != OpCode::IntLeft && opc2 != OpCode::IntRight && opc2 != OpCode::IntMult {
            return Ok(0);
        }
        if !data.vn(data.op(secop).get_in(1)).is_constant() {
            return Ok(0);
        }
        let mut opc1 = data.op(op).code();
        let size = data.vn(secvn).get_size();
        let secin = data.op(secop).get_in(0);
        if !data.vn(secin).is_heritage_known() {
            return Ok(0);
        }
        let sa1: i32;
        let sa2: i32;
        if opc1 == OpCode::IntMult {
            let val = data.vn(data.op(op).get_in(1)).get_offset();
            sa1 = leastsigbit_set(val);
            if val.wrapping_shr(sa1 as u32) != 1 {
                return Ok(0);
            }
            opc1 = OpCode::IntLeft;
        } else {
            sa1 = data.vn(data.op(op).get_in(1)).get_offset() as i32;
        }
        if opc2 == OpCode::IntMult {
            let val = data.vn(data.op(secop).get_in(1)).get_offset();
            sa2 = leastsigbit_set(val);
            if val.wrapping_shr(sa2 as u32) != 1 {
                return Ok(0);
            }
            opc2 = OpCode::IntLeft;
        } else {
            sa2 = data.vn(data.op(secop).get_in(1)).get_offset() as i32;
        }
        if opc1 == opc2 {
            if sa1.wrapping_add(sa2) < 8 * size {
                let newvn = data.new_constant(4, sa1.wrapping_add(sa2) as u64, glb);
                data.op_set_opcode(op, opc1, glb);
                data.op_set_input(op, secin, 0)?;
                data.op_set_input(op, newvn, 1)?;
            } else {
                let newvn = data.new_constant(size, 0, glb);
                data.op_set_opcode(op, OpCode::Copy, glb);
                data.op_set_input(op, newvn, 0)?;
                data.op_remove_input(op, 1);
            }
        } else {
            if size > 8 {
                return Ok(0);
            }
            let mut mask = calc_mask(size);
            let mut diffsa: i32;
            if opc1 == OpCode::IntLeft {
                if data.vn(secvn).lone_descend().is_none() {
                    return Ok(0);
                }
                mask = mask.wrapping_shl(sa2 as u32) & mask;
                diffsa = sa1.wrapping_sub(sa2);
                if diffsa != 0 {
                    return Ok(0);
                }
            } else {
                mask = mask.wrapping_shr(sa2 as u32) & mask;
                diffsa = sa2.wrapping_sub(sa1);
            }
            if diffsa == 0 {
                let newvn = data.new_constant(size, mask, glb);
                data.op_set_opcode(op, OpCode::IntAnd, glb);
                data.op_set_input(op, secin, 0)?;
                data.op_set_input(op, newvn, 1)?;
            } else {
                let addr = data.op(op).get_addr().clone();
                let new_and = data.new_op(2, &addr);
                data.op_set_opcode(new_and, OpCode::IntAnd, glb);
                data.op_set_input(new_and, secin, 0)?;
                let maskvn = data.new_constant(size, mask, glb);
                data.op_set_input(new_and, maskvn, 1)?;
                let new_out = data.new_unique_out(size, new_and, glb)?;
                data.op_insert_before(new_and, op);
                let mut finalopc = OpCode::IntLeft;
                if diffsa < 0 {
                    finalopc = OpCode::IntRight;
                    diffsa = diffsa.wrapping_neg();
                }
                data.op_set_opcode(op, finalopc, glb);
                data.op_set_input(op, new_out, 0)?;
                let amount = data.new_constant(4, diffsa as u64, glb);
                data.op_set_input(op, amount, 1)?;
            }
        }
        Ok(1)
    }
}

pub struct RuleDoubleArithShift {
    pub base: RuleBase,
}

impl RuleDoubleArithShift {
    pub fn new(group: &str) -> RuleDoubleArithShift {
        RuleDoubleArithShift {
            base: RuleBase::new(group, 0, "doublearithshift"),
        }
    }
}

impl Rule for RuleDoubleArithShift {
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
        Some(Box::new(RuleDoubleArithShift::new(self.get_group())))
    }

    fn get_op_list(&self, oplist: &mut Vec<OpCode>) {
        oplist.push(OpCode::IntSright);
    }

    fn apply_op(&mut self, op: OpId, data: &mut Funcdata, glb: &mut Architecture) -> Result<i32> {
        let const_d = data.op(op).get_in(1);
        if !data.vn(const_d).is_constant() {
            return Ok(0);
        }
        let shiftin = data.op(op).get_in(0);
        if !data.vn(shiftin).is_written() {
            return Ok(0);
        }
        let shift2op = data.vn(shiftin).get_def().expect("written varnode without defining op");
        if data.op(shift2op).code() != OpCode::IntSright {
            return Ok(0);
        }
        let const_c = data.op(shift2op).get_in(1);
        if !data.vn(const_c).is_constant() {
            return Ok(0);
        }
        let in_vn = data.op(shift2op).get_in(0);
        if data.vn(in_vn).is_free() {
            return Ok(0);
        }
        let max = data.vn(data.op(op).get_out().expect("op without output")).get_size() * 8 - 1;
        let mut shift_amount =
            (data.vn(const_c).get_offset() as i32).wrapping_add(data.vn(const_d).get_offset() as i32);
        if shift_amount <= 0 {
            return Ok(0);
        }
        if shift_amount > max {
            shift_amount = max;
        }
        data.op_set_input(op, in_vn, 0)?;
        let newconst = data.new_constant(4, shift_amount as u64, glb);
        data.op_set_input(op, newconst, 1)?;
        Ok(1)
    }
}

pub struct RuleConcatShift {
    pub base: RuleBase,
}

impl RuleConcatShift {
    pub fn new(group: &str) -> RuleConcatShift {
        RuleConcatShift {
            base: RuleBase::new(group, 0, "concatshift"),
        }
    }
}

impl Rule for RuleConcatShift {
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
        Some(Box::new(RuleConcatShift::new(self.get_group())))
    }

    fn get_op_list(&self, oplist: &mut Vec<OpCode>) {
        oplist.push(OpCode::IntRight);
        oplist.push(OpCode::IntSright);
    }

    fn apply_op(&mut self, op: OpId, data: &mut Funcdata, glb: &mut Architecture) -> Result<i32> {
        if !data.vn(data.op(op).get_in(1)).is_constant() {
            return Ok(0);
        }
        let shiftin = data.op(op).get_in(0);
        if !data.vn(shiftin).is_written() {
            return Ok(0);
        }
        let concat = data.vn(shiftin).get_def().expect("written varnode without defining op");
        if data.op(concat).code() != OpCode::Piece {
            return Ok(0);
        }
        let mut shift_amount = data.vn(data.op(op).get_in(1)).get_offset() as i32;
        let leastsize = data.vn(data.op(concat).get_in(1)).get_size() * 8;
        if shift_amount < leastsize {
            return Ok(0);
        }
        let mainin = data.op(concat).get_in(0);
        if data.vn(mainin).is_free() {
            return Ok(0);
        }
        shift_amount -= leastsize;
        let extcode = if data.op(op).code() == OpCode::IntRight {
            OpCode::IntZext
        } else {
            OpCode::IntSext
        };
        if shift_amount == 0 {
            data.op_remove_input(op, 1);
            data.op_set_opcode(op, extcode, glb);
            data.op_set_input(op, mainin, 0)?;
        } else {
            let addr = data.op(op).get_addr().clone();
            let extop = data.new_op(1, &addr);
            data.op_set_opcode(extop, extcode, glb);
            let shiftsize = data.vn(shiftin).get_size();
            let newvn = data.new_unique_out(shiftsize, extop, glb)?;
            data.op_set_input(extop, mainin, 0)?;
            data.op_set_input(op, newvn, 0)?;
            let constsize = data.vn(data.op(op).get_in(1)).get_size();
            let newconst = data.new_constant(constsize, shift_amount as u64, glb);
            data.op_set_input(op, newconst, 1)?;
            data.op_insert_before(extop, op);
        }
        Ok(1)
    }
}

pub struct RuleLeftRight {
    pub base: RuleBase,
}

impl RuleLeftRight {
    pub fn new(group: &str) -> RuleLeftRight {
        RuleLeftRight {
            base: RuleBase::new(group, 0, "leftright"),
        }
    }
}

impl Rule for RuleLeftRight {
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
        Some(Box::new(RuleLeftRight::new(self.get_group())))
    }

    fn get_op_list(&self, oplist: &mut Vec<OpCode>) {
        oplist.push(OpCode::IntRight);
        oplist.push(OpCode::IntSright);
    }

    fn apply_op(&mut self, op: OpId, data: &mut Funcdata, glb: &mut Architecture) -> Result<i32> {
        if !data.vn(data.op(op).get_in(1)).is_constant() {
            return Ok(0);
        }
        let shiftin = data.op(op).get_in(0);
        if !data.vn(shiftin).is_written() {
            return Ok(0);
        }
        let leftshift = data.vn(shiftin).get_def().expect("written varnode without defining op");
        if data.op(leftshift).code() != OpCode::IntLeft {
            return Ok(0);
        }
        if !data.vn(data.op(leftshift).get_in(1)).is_constant() {
            return Ok(0);
        }
        let shift_amount = data.vn(data.op(op).get_in(1)).get_offset();
        if data.vn(data.op(leftshift).get_in(1)).get_offset() != shift_amount {
            return Ok(0);
        }
        if (shift_amount & 7) != 0 {
            return Ok(0);
        }
        let isa = (shift_amount >> 3) as i32;
        let tsz = data.vn(shiftin).get_size().wrapping_sub(isa);
        if tsz != 1 && tsz != 2 && tsz != 4 && tsz != 8 {
            return Ok(0);
        }
        if data.vn(shiftin).lone_descend() != Some(op) {
            return Ok(0);
        }
        let mut addr = data.vn(shiftin).get_addr().clone();
        if addr.is_big_endian() {
            addr = addr.add(isa as i64);
        }
        data.op_unset_input(op, 0);
        data.op_unset_output(leftshift)?;
        addr.renormalize(tsz)?;
        let newvn = data.new_varnode_out(tsz, &addr, leftshift, glb)?;
        data.op_set_opcode(leftshift, OpCode::Subpiece, glb);
        let constsize = data.vn(data.op(leftshift).get_in(1)).get_size();
        let zero = data.new_constant(constsize, 0, glb);
        data.op_set_input(leftshift, zero, 1)?;
        data.op_set_input(op, newvn, 0)?;
        data.op_remove_input(op, 1);
        let extcode = if data.op(op).code() == OpCode::IntSright {
            OpCode::IntSext
        } else {
            OpCode::IntZext
        };
        data.op_set_opcode(op, extcode, glb);
        Ok(1)
    }
}

pub struct RuleShiftCompare {
    pub base: RuleBase,
}

impl RuleShiftCompare {
    pub fn new(group: &str) -> RuleShiftCompare {
        RuleShiftCompare {
            base: RuleBase::new(group, 0, "shiftcompare"),
        }
    }
}

impl Rule for RuleShiftCompare {
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
        Some(Box::new(RuleShiftCompare::new(self.get_group())))
    }

    fn get_op_list(&self, oplist: &mut Vec<OpCode>) {
        oplist.push(OpCode::IntEqual);
        oplist.push(OpCode::IntNotequal);
    }

    fn apply_op(&mut self, op: OpId, data: &mut Funcdata, glb: &mut Architecture) -> Result<i32> {
        let shiftvn = data.op(op).get_in(0);
        let constvn = data.op(op).get_in(1);
        if !data.vn(constvn).is_constant() {
            return Ok(0);
        }
        if !data.vn(shiftvn).is_written() {
            return Ok(0);
        }
        let shiftop = data.vn(shiftvn).get_def().expect("written varnode without defining op");
        let opc = data.op(shiftop).code();
        let isleft: bool;
        let mut shift_amount: i32;
        if opc == OpCode::IntLeft {
            isleft = true;
            let savn = data.op(shiftop).get_in(1);
            if !data.vn(savn).is_constant() {
                return Ok(0);
            }
            shift_amount = data.vn(savn).get_offset() as i32;
        } else if opc == OpCode::IntRight {
            isleft = false;
            let savn = data.op(shiftop).get_in(1);
            if !data.vn(savn).is_constant() {
                return Ok(0);
            }
            shift_amount = data.vn(savn).get_offset() as i32;
            if data.vn(shiftvn).lone_descend() != Some(op) {
                return Ok(0);
            }
        } else if opc == OpCode::IntMult {
            isleft = true;
            let savn = data.op(shiftop).get_in(1);
            if !data.vn(savn).is_constant() {
                return Ok(0);
            }
            let val = data.vn(savn).get_offset();
            shift_amount = leastsigbit_set(val);
            if val.wrapping_shr(shift_amount as u32) != 1 {
                return Ok(0);
            }
        } else if opc == OpCode::IntDiv {
            isleft = false;
            let savn = data.op(shiftop).get_in(1);
            if !data.vn(savn).is_constant() {
                return Ok(0);
            }
            let val = data.vn(savn).get_offset();
            shift_amount = leastsigbit_set(val);
            if val.wrapping_shr(shift_amount as u32) != 1 {
                return Ok(0);
            }
            if data.vn(shiftvn).lone_descend() != Some(op) {
                return Ok(0);
            }
        } else {
            return Ok(0);
        }
        if shift_amount == 0 {
            return Ok(0);
        }
        let mainvn = data.op(shiftop).get_in(0);
        if data.vn(mainvn).is_free() {
            return Ok(0);
        }
        if data.vn(mainvn).get_size() > 8 {
            return Ok(0);
        }
        let constval = data.vn(constvn).get_offset();
        let nzmask = data.vn(mainvn).get_nz_mask();
        let constsize = data.vn(constvn).get_size();
        let newconst: u64;
        if isleft {
            newconst = constval.wrapping_shr(shift_amount as u32);
            if newconst.wrapping_shl(shift_amount as u32) != constval {
                return Ok(0);
            }
            let mut tmp = nzmask.wrapping_shl(shift_amount as u32) & calc_mask(data.vn(shiftvn).get_size());
            if tmp.wrapping_shr(shift_amount as u32) != nzmask {
                if data.vn(shiftvn).lone_descend() != Some(op) {
                    return Ok(0);
                }
                shift_amount = (8 * data.vn(shiftvn).get_size()).wrapping_sub(shift_amount);
                tmp = 1u64.wrapping_shl(shift_amount as u32).wrapping_sub(1);
                let newmask = data.new_constant(constsize, tmp, glb);
                let addr = data.op(op).get_addr().clone();
                let newop = data.new_op(2, &addr);
                data.op_set_opcode(newop, OpCode::IntAnd, glb);
                let newtmpvn = data.new_unique_out(constsize, newop, glb)?;
                data.op_set_input(newop, mainvn, 0)?;
                data.op_set_input(newop, newmask, 1)?;
                data.op_insert_before(newop, shiftop);
                data.op_set_input(op, newtmpvn, 0)?;
                let replacement = data.new_constant(constsize, newconst, glb);
                data.op_set_input(op, replacement, 1)?;
                return Ok(1);
            }
        } else {
            if nzmask
                .wrapping_shr(shift_amount as u32)
                .wrapping_shl(shift_amount as u32)
                != nzmask
            {
                return Ok(0);
            }
            newconst = constval.wrapping_shl(shift_amount as u32) & calc_mask(data.vn(shiftvn).get_size());
            if newconst.wrapping_shr(shift_amount as u32) != constval {
                return Ok(0);
            }
        }
        let newconstvn = data.new_constant(constsize, newconst, glb);
        data.op_set_input(op, mainvn, 0)?;
        data.op_set_input(op, newconstvn, 1)?;
        Ok(1)
    }
}

pub struct RuleLessEqual {
    pub base: RuleBase,
}

impl RuleLessEqual {
    pub fn new(group: &str) -> RuleLessEqual {
        RuleLessEqual {
            base: RuleBase::new(group, 0, "lessequal"),
        }
    }
}

impl Rule for RuleLessEqual {
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
        Some(Box::new(RuleLessEqual::new(self.get_group())))
    }

    fn get_op_list(&self, oplist: &mut Vec<OpCode>) {
        oplist.push(OpCode::BoolOr);
    }

    fn apply_op(&mut self, op: OpId, data: &mut Funcdata, glb: &mut Architecture) -> Result<i32> {
        let vnout1 = data.op(op).get_in(0);
        if !data.vn(vnout1).is_written() {
            return Ok(0);
        }
        let vnout2 = data.op(op).get_in(1);
        if !data.vn(vnout2).is_written() {
            return Ok(0);
        }
        let mut op_less = data.vn(vnout1).get_def().expect("written varnode without defining op");
        let mut opc = data.op(op_less).code();
        let op_equal: OpId;
        if opc != OpCode::IntLess && opc != OpCode::IntSless {
            op_equal = op_less;
            op_less = data.vn(vnout2).get_def().expect("written varnode without defining op");
            opc = data.op(op_less).code();
            if opc != OpCode::IntLess && opc != OpCode::IntSless {
                return Ok(0);
            }
        } else {
            op_equal = data.vn(vnout2).get_def().expect("written varnode without defining op");
        }
        let equalopc = data.op(op_equal).code();
        if equalopc != OpCode::IntEqual && equalopc != OpCode::IntNotequal {
            return Ok(0);
        }
        let compvn1 = data.op(op_less).get_in(0);
        let compvn2 = data.op(op_less).get_in(1);
        if !data.vn(compvn1).is_heritage_known() {
            return Ok(0);
        }
        if !data.vn(compvn2).is_heritage_known() {
            return Ok(0);
        }
        let equal0 = data.op(op_equal).get_in(0);
        let equal1 = data.op(op_equal).get_in(1);
        if (data.vn_not_equal(compvn1, equal0) || data.vn_not_equal(compvn2, equal1))
            && (data.vn_not_equal(compvn1, equal1) || data.vn_not_equal(compvn2, equal0))
        {
            return Ok(0);
        }
        if equalopc == OpCode::IntNotequal {
            data.op_set_opcode(op, OpCode::Copy, glb);
            data.op_remove_input(op, 1);
            let equal_out = data.op(op_equal).get_out().expect("op without output");
            data.op_set_input(op, equal_out, 0)?;
        } else {
            data.op_set_input(op, compvn1, 0)?;
            data.op_set_input(op, compvn2, 1)?;
            let newopc = if opc == OpCode::IntSless {
                OpCode::IntSlessequal
            } else {
                OpCode::IntLessequal
            };
            data.op_set_opcode(op, newopc, glb);
        }
        Ok(1)
    }
}

pub struct RuleLessNotEqual {
    pub base: RuleBase,
}

impl RuleLessNotEqual {
    pub fn new(group: &str) -> RuleLessNotEqual {
        RuleLessNotEqual {
            base: RuleBase::new(group, 0, "lessnotequal"),
        }
    }
}

impl Rule for RuleLessNotEqual {
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
        Some(Box::new(RuleLessNotEqual::new(self.get_group())))
    }

    fn get_op_list(&self, oplist: &mut Vec<OpCode>) {
        oplist.push(OpCode::BoolAnd);
    }

    fn apply_op(&mut self, op: OpId, data: &mut Funcdata, glb: &mut Architecture) -> Result<i32> {
        let vnout1 = data.op(op).get_in(0);
        if !data.vn(vnout1).is_written() {
            return Ok(0);
        }
        let vnout2 = data.op(op).get_in(1);
        if !data.vn(vnout2).is_written() {
            return Ok(0);
        }
        let mut op_less = data.vn(vnout1).get_def().expect("written varnode without defining op");
        let mut opc = data.op(op_less).code();
        let op_equal: OpId;
        if opc != OpCode::IntLessequal && opc != OpCode::IntSlessequal {
            op_equal = op_less;
            op_less = data.vn(vnout2).get_def().expect("written varnode without defining op");
            opc = data.op(op_less).code();
            if opc != OpCode::IntLessequal && opc != OpCode::IntSlessequal {
                return Ok(0);
            }
        } else {
            op_equal = data.vn(vnout2).get_def().expect("written varnode without defining op");
        }
        if data.op(op_equal).code() != OpCode::IntNotequal {
            return Ok(0);
        }
        let compvn1 = data.op(op_less).get_in(0);
        let compvn2 = data.op(op_less).get_in(1);
        if !data.vn(compvn1).is_heritage_known() {
            return Ok(0);
        }
        if !data.vn(compvn2).is_heritage_known() {
            return Ok(0);
        }
        let equal0 = data.op(op_equal).get_in(0);
        let equal1 = data.op(op_equal).get_in(1);
        if (data.vn_not_equal(compvn1, equal0) || data.vn_not_equal(compvn2, equal1))
            && (data.vn_not_equal(compvn1, equal1) || data.vn_not_equal(compvn2, equal0))
        {
            return Ok(0);
        }
        data.op_set_input(op, compvn1, 0)?;
        data.op_set_input(op, compvn2, 1)?;
        let newopc = if opc == OpCode::IntSlessequal {
            OpCode::IntSless
        } else {
            OpCode::IntLess
        };
        data.op_set_opcode(op, newopc, glb);
        Ok(1)
    }
}

pub struct RuleTrivialArith {
    pub base: RuleBase,
}

impl RuleTrivialArith {
    pub fn new(group: &str) -> RuleTrivialArith {
        RuleTrivialArith {
            base: RuleBase::new(group, 0, "trivialarith"),
        }
    }
}

impl Rule for RuleTrivialArith {
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
        Some(Box::new(RuleTrivialArith::new(self.get_group())))
    }

    fn get_op_list(&self, oplist: &mut Vec<OpCode>) {
        oplist.extend_from_slice(&[
            OpCode::IntNotequal,
            OpCode::IntSless,
            OpCode::IntLess,
            OpCode::BoolXor,
            OpCode::BoolAnd,
            OpCode::BoolOr,
            OpCode::IntEqual,
            OpCode::IntSlessequal,
            OpCode::IntLessequal,
            OpCode::IntXor,
            OpCode::IntAnd,
            OpCode::IntOr,
            OpCode::FloatEqual,
            OpCode::FloatNotequal,
            OpCode::FloatLess,
            OpCode::FloatLessequal,
        ]);
    }

    fn apply_op(&mut self, op: OpId, data: &mut Funcdata, glb: &mut Architecture) -> Result<i32> {
        if data.op(op).num_input() != 2 {
            return Ok(0);
        }
        let in0 = data.op(op).get_in(0);
        let in1 = data.op(op).get_in(1);
        if in0 != in1 {
            if !data.vn(in0).is_written() {
                return Ok(0);
            }
            if !data.vn(in1).is_written() {
                return Ok(0);
            }
            let def0 = data.vn(in0).get_def().expect("written varnode without defining op");
            let def1 = data.vn(in1).get_def().expect("written varnode without defining op");
            if !data.op_is_cse_match(def0, def1) {
                return Ok(0);
            }
        }
        let vn = match data.op(op).code() {
            OpCode::IntNotequal
            | OpCode::IntSless
            | OpCode::IntLess
            | OpCode::BoolXor
            | OpCode::FloatNotequal
            | OpCode::FloatLess => Some(data.new_constant(1, 0, glb)),
            OpCode::IntEqual
            | OpCode::IntSlessequal
            | OpCode::IntLessequal
            | OpCode::FloatEqual
            | OpCode::FloatLessequal => Some(data.new_constant(1, 1, glb)),
            OpCode::IntXor => {
                let size = data.vn(data.op(op).get_out().expect("op without output")).get_size();
                Some(data.new_constant(size, 0, glb))
            }
            OpCode::BoolAnd | OpCode::BoolOr | OpCode::IntAnd | OpCode::IntOr => None,
            _ => return Ok(0),
        };
        data.op_remove_input(op, 1);
        data.op_set_opcode(op, OpCode::Copy, glb);
        if let Some(vn) = vn {
            data.op_set_input(op, vn, 0)?;
        }
        Ok(1)
    }
}

pub struct RuleTrivialBool {
    pub base: RuleBase,
}

impl RuleTrivialBool {
    pub fn new(group: &str) -> RuleTrivialBool {
        RuleTrivialBool {
            base: RuleBase::new(group, 0, "trivialbool"),
        }
    }
}

impl Rule for RuleTrivialBool {
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
        Some(Box::new(RuleTrivialBool::new(self.get_group())))
    }

    fn get_op_list(&self, oplist: &mut Vec<OpCode>) {
        oplist.extend_from_slice(&[OpCode::BoolAnd, OpCode::BoolOr, OpCode::BoolXor]);
    }

    fn apply_op(&mut self, op: OpId, data: &mut Funcdata, glb: &mut Architecture) -> Result<i32> {
        let vnconst = data.op(op).get_in(1);
        if !data.vn(vnconst).is_constant() {
            return Ok(0);
        }
        let val = data.vn(vnconst).get_offset();
        let (vn, opc) = match data.op(op).code() {
            OpCode::BoolXor => {
                let opc = if val == 1 { OpCode::BoolNegate } else { OpCode::Copy };
                (data.op(op).get_in(0), opc)
            }
            OpCode::BoolAnd => {
                if val == 1 {
                    (data.op(op).get_in(0), OpCode::Copy)
                } else {
                    (data.new_constant(1, 0, glb), OpCode::Copy)
                }
            }
            OpCode::BoolOr => {
                if val == 1 {
                    (data.new_constant(1, 1, glb), OpCode::Copy)
                } else {
                    (data.op(op).get_in(0), OpCode::Copy)
                }
            }
            _ => return Ok(0),
        };
        data.op_remove_input(op, 1);
        data.op_set_opcode(op, opc, glb);
        data.op_set_input(op, vn, 0)?;
        Ok(1)
    }
}

pub struct RuleZextEliminate {
    pub base: RuleBase,
}

impl RuleZextEliminate {
    pub fn new(group: &str) -> RuleZextEliminate {
        RuleZextEliminate {
            base: RuleBase::new(group, 0, "zexteliminate"),
        }
    }
}

impl Rule for RuleZextEliminate {
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
        Some(Box::new(RuleZextEliminate::new(self.get_group())))
    }

    fn get_op_list(&self, oplist: &mut Vec<OpCode>) {
        oplist.extend_from_slice(&[
            OpCode::IntEqual,
            OpCode::IntNotequal,
            OpCode::IntLess,
            OpCode::IntLessequal,
        ]);
    }

    fn apply_op(&mut self, op: OpId, data: &mut Funcdata, glb: &mut Architecture) -> Result<i32> {
        let mut vn1 = data.op(op).get_in(0);
        let mut vn2 = data.op(op).get_in(1);
        let mut zextslot = 0;
        let mut otherslot = 1;
        if data.vn(vn2).is_written()
            && data
                .op(data.vn(vn2).get_def().expect("written varnode without defining op"))
                .code()
                == OpCode::IntZext
        {
            vn1 = vn2;
            vn2 = data.op(op).get_in(0);
            zextslot = 1;
            otherslot = 0;
        } else if !data.vn(vn1).is_written()
            || data
                .op(data.vn(vn1).get_def().expect("written varnode without defining op"))
                .code()
                != OpCode::IntZext
        {
            return Ok(0);
        }
        if !data.vn(vn2).is_constant() {
            return Ok(0);
        }
        let zext = data.vn(vn1).get_def().expect("written varnode without defining op");
        let zextin = data.op(zext).get_in(0);
        if !data.vn(zextin).is_heritage_known() {
            return Ok(0);
        }
        if data.vn(vn1).lone_descend() != Some(op) {
            return Ok(0);
        }
        let smallsize = data.vn(zextin).get_size();
        let val = data.vn(vn2).get_offset();
        if val.wrapping_shr((8 * smallsize) as u32) == 0 {
            let newvn = data.new_constant(smallsize, val, glb);
            data.vn_copy_symbol_if_valid(newvn, vn2, glb)?;
            data.op_set_input(op, zextin, zextslot)?;
            data.op_set_input(op, newvn, otherslot)?;
            return Ok(1);
        }
        Ok(0)
    }
}

pub struct RuleSlessToLess {
    pub base: RuleBase,
}

impl RuleSlessToLess {
    pub fn new(group: &str) -> RuleSlessToLess {
        RuleSlessToLess {
            base: RuleBase::new(group, 0, "slesstoless"),
        }
    }
}

impl Rule for RuleSlessToLess {
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
        Some(Box::new(RuleSlessToLess::new(self.get_group())))
    }

    fn get_op_list(&self, oplist: &mut Vec<OpCode>) {
        oplist.push(OpCode::IntSless);
        oplist.push(OpCode::IntSlessequal);
    }

    fn apply_op(&mut self, op: OpId, data: &mut Funcdata, glb: &mut Architecture) -> Result<i32> {
        let vn = data.op(op).get_in(0);
        let size = data.vn(vn).get_size();
        if signbit_negative(data.vn(vn).get_nz_mask(), size) {
            return Ok(0);
        }
        if signbit_negative(data.vn(data.op(op).get_in(1)).get_nz_mask(), size) {
            return Ok(0);
        }
        if data.op(op).code() == OpCode::IntSless {
            data.op_set_opcode(op, OpCode::IntLess, glb);
        } else {
            data.op_set_opcode(op, OpCode::IntLessequal, glb);
        }
        Ok(1)
    }
}

pub struct RuleZextSless {
    pub base: RuleBase,
}

impl RuleZextSless {
    pub fn new(group: &str) -> RuleZextSless {
        RuleZextSless {
            base: RuleBase::new(group, 0, "zextsless"),
        }
    }
}

impl Rule for RuleZextSless {
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
        Some(Box::new(RuleZextSless::new(self.get_group())))
    }

    fn get_op_list(&self, oplist: &mut Vec<OpCode>) {
        oplist.push(OpCode::IntSless);
        oplist.push(OpCode::IntSlessequal);
    }

    fn apply_op(&mut self, op: OpId, data: &mut Funcdata, glb: &mut Architecture) -> Result<i32> {
        let mut vn1 = data.op(op).get_in(0);
        let mut vn2 = data.op(op).get_in(1);
        let mut zextslot = 0;
        let mut otherslot = 1;
        if data.vn(vn2).is_written()
            && data
                .op(data.vn(vn2).get_def().expect("written varnode without defining op"))
                .code()
                == OpCode::IntZext
        {
            vn1 = vn2;
            vn2 = data.op(op).get_in(0);
            zextslot = 1;
            otherslot = 0;
        } else if !data.vn(vn1).is_written()
            || data
                .op(data.vn(vn1).get_def().expect("written varnode without defining op"))
                .code()
                != OpCode::IntZext
        {
            return Ok(0);
        }
        if !data.vn(vn2).is_constant() {
            return Ok(0);
        }
        let zext = data.vn(vn1).get_def().expect("written varnode without defining op");
        let zextin = data.op(zext).get_in(0);
        if !data.vn(zextin).is_heritage_known() {
            return Ok(0);
        }
        let smallsize = data.vn(zextin).get_size();
        let val = data.vn(vn2).get_offset();
        if val.wrapping_shr((8 * smallsize - 1) as u32) != 0 {
            return Ok(0);
        }
        let newvn = data.new_constant(smallsize, val, glb);
        data.op_set_input(op, zextin, zextslot)?;
        data.op_set_input(op, newvn, otherslot)?;
        let newopc = if data.op(op).code() == OpCode::IntSless {
            OpCode::IntLess
        } else {
            OpCode::IntLessequal
        };
        data.op_set_opcode(op, newopc, glb);
        Ok(1)
    }
}

pub struct RuleBitUndistribute {
    pub base: RuleBase,
}

impl RuleBitUndistribute {
    pub fn new(group: &str) -> RuleBitUndistribute {
        RuleBitUndistribute {
            base: RuleBase::new(group, 0, "bitundistribute"),
        }
    }
}

impl Rule for RuleBitUndistribute {
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
        Some(Box::new(RuleBitUndistribute::new(self.get_group())))
    }

    fn get_op_list(&self, oplist: &mut Vec<OpCode>) {
        oplist.extend_from_slice(&[OpCode::IntAnd, OpCode::IntOr, OpCode::IntXor]);
    }

    fn apply_op(&mut self, op: OpId, data: &mut Funcdata, glb: &mut Architecture) -> Result<i32> {
        let vn1 = data.op(op).get_in(0);
        let vn2 = data.op(op).get_in(1);
        if !data.vn(vn1).is_written() {
            return Ok(0);
        }
        if !data.vn(vn2).is_written() {
            return Ok(0);
        }
        let def1 = data.vn(vn1).get_def().expect("written varnode without defining op");
        let def2 = data.vn(vn2).get_def().expect("written varnode without defining op");
        let opc = data.op(def1).code();
        if data.op(def2).code() != opc {
            return Ok(0);
        }
        let in1: VarnodeId;
        let in2: VarnodeId;
        match opc {
            OpCode::IntZext | OpCode::IntSext => {
                in1 = data.op(def1).get_in(0);
                if data.vn(in1).is_free() {
                    return Ok(0);
                }
                in2 = data.op(def2).get_in(0);
                if data.vn(in2).is_free() {
                    return Ok(0);
                }
                if data.vn(in1).get_size() != data.vn(in2).get_size() {
                    return Ok(0);
                }
                data.op_remove_input(op, 1);
            }
            OpCode::IntLeft | OpCode::IntRight | OpCode::IntSright => {
                let amount1 = data.op(def1).get_in(1);
                let amount2 = data.op(def2).get_in(1);
                let vnextra = if data.vn(amount1).is_constant() && data.vn(amount2).is_constant() {
                    if data.vn(amount1).get_offset() != data.vn(amount2).get_offset() {
                        return Ok(0);
                    }
                    let size = data.vn(amount1).get_size();
                    let offset = data.vn(amount1).get_offset();
                    data.new_constant(size, offset, glb)
                } else if amount1 != amount2 {
                    return Ok(0);
                } else {
                    if data.vn(amount1).is_free() {
                        return Ok(0);
                    }
                    amount1
                };
                in1 = data.op(def1).get_in(0);
                if data.vn(in1).is_free() {
                    return Ok(0);
                }
                in2 = data.op(def2).get_in(0);
                if data.vn(in2).is_free() {
                    return Ok(0);
                }
                data.op_set_input(op, vnextra, 1)?;
            }
            _ => return Ok(0),
        }
        let addr = data.op(op).get_addr().clone();
        let newext = data.new_op(2, &addr);
        let insize = data.vn(in1).get_size();
        let smalllogic = data.new_unique_out(insize, newext, glb)?;
        data.op_set_input(newext, in1, 0)?;
        data.op_set_input(newext, in2, 1)?;
        let logicopc = data.op(op).code();
        data.op_set_opcode(newext, logicopc, glb);
        data.op_set_opcode(op, opc, glb);
        data.op_set_input(op, smalllogic, 0)?;
        data.op_insert_before(newext, op);
        Ok(1)
    }
}

pub struct RuleBooleanUndistribute {
    pub base: RuleBase,
}

impl RuleBooleanUndistribute {
    pub fn new(group: &str) -> RuleBooleanUndistribute {
        RuleBooleanUndistribute {
            base: RuleBase::new(group, 0, "booleanundistribute"),
        }
    }

    pub fn is_match(left_vn: VarnodeId, right_vn: VarnodeId, right_flip: &mut bool, data: &Funcdata) -> bool {
        let val = BooleanMatch::evaluate(left_vn, right_vn, 1, data);
        if val == BooleanMatch::SAME {
            return true;
        }
        if val == BooleanMatch::COMPLEMENTARY {
            *right_flip = !*right_flip;
            return true;
        }
        false
    }
}

impl Rule for RuleBooleanUndistribute {
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
        Some(Box::new(RuleBooleanUndistribute::new(self.get_group())))
    }

    fn get_op_list(&self, oplist: &mut Vec<OpCode>) {
        oplist.push(OpCode::IntEqual);
        oplist.push(OpCode::IntNotequal);
    }

    fn apply_op(&mut self, op: OpId, data: &mut Funcdata, glb: &mut Architecture) -> Result<i32> {
        let vn0 = data.op(op).get_in(0);
        if !data.vn(vn0).is_written() {
            return Ok(0);
        }
        let vn1 = data.op(op).get_in(1);
        if !data.vn(vn1).is_written() {
            return Ok(0);
        }
        let op0 = data.vn(vn0).get_def().expect("written varnode without defining op");
        let opc0 = data.op(op0).code();
        if opc0 != OpCode::BoolAnd && opc0 != OpCode::BoolOr {
            return Ok(0);
        }
        let op1 = data.vn(vn1).get_def().expect("written varnode without defining op");
        let opc1 = data.op(op1).code();
        if opc1 != OpCode::BoolAnd && opc1 != OpCode::BoolOr {
            return Ok(0);
        }
        let ins: [VarnodeId; 4] = [
            data.op(op0).get_in(0),
            data.op(op0).get_in(1),
            data.op(op1).get_in(0),
            data.op(op1).get_in(1),
        ];
        if ins.iter().any(|&input| data.vn(input).is_free()) {
            return Ok(0);
        }
        let mut isflipped = [false; 4];
        let mut central_equal = data.op(op).code() == OpCode::IntEqual;
        if opc0 == OpCode::BoolOr {
            isflipped[0] = !isflipped[0];
            isflipped[1] = !isflipped[1];
            central_equal = !central_equal;
        }
        if opc1 == OpCode::BoolOr {
            isflipped[2] = !isflipped[2];
            isflipped[3] = !isflipped[3];
            central_equal = !central_equal;
        }
        let (left_slot, right_slot) = if RuleBooleanUndistribute::is_match(ins[0], ins[2], &mut isflipped[2], data) {
            (0usize, 2usize)
        } else if RuleBooleanUndistribute::is_match(ins[0], ins[3], &mut isflipped[3], data) {
            (0, 3)
        } else if RuleBooleanUndistribute::is_match(ins[1], ins[2], &mut isflipped[2], data) {
            (1, 2)
        } else if RuleBooleanUndistribute::is_match(ins[1], ins[3], &mut isflipped[3], data) {
            (1, 3)
        } else {
            return Ok(0);
        };
        if isflipped[left_slot] != isflipped[right_slot] {
            return Ok(0);
        }
        let combine_opc = if central_equal {
            isflipped[left_slot] = !isflipped[left_slot];
            OpCode::BoolOr
        } else {
            OpCode::BoolAnd
        };
        let mut final_a = ins[left_slot];
        if isflipped[left_slot] {
            final_a = data.op_bool_negate(final_a, op, false, glb)?;
        }
        if isflipped[1 - left_slot] {
            central_equal = !central_equal;
        }
        if isflipped[5 - right_slot] {
            central_equal = !central_equal;
        }
        let final_b = ins[1 - left_slot];
        let final_c = ins[5 - right_slot];
        let addr = data.op(op).get_addr().clone();
        let eq_op = data.new_op(2, &addr);
        data.op_set_opcode(
            eq_op,
            if central_equal {
                OpCode::IntEqual
            } else {
                OpCode::IntNotequal
            },
            glb,
        );
        let tmp1 = data.new_unique_out(1, eq_op, glb)?;
        data.op_set_input(eq_op, final_b, 0)?;
        data.op_set_input(eq_op, final_c, 1)?;
        data.op_insert_before(eq_op, op);
        data.op_set_opcode(op, combine_opc, glb);
        data.op_set_input(op, tmp1, 1)?;
        data.op_set_input(op, final_a, 0)?;
        Ok(1)
    }
}

pub struct RuleBooleanDedup {
    pub base: RuleBase,
}

impl RuleBooleanDedup {
    pub fn new(group: &str) -> RuleBooleanDedup {
        RuleBooleanDedup {
            base: RuleBase::new(group, 0, "booleandedup"),
        }
    }

    pub fn is_match(left_vn: VarnodeId, right_vn: VarnodeId, is_flip: &mut bool, data: &Funcdata) -> bool {
        let val = BooleanMatch::evaluate(left_vn, right_vn, 1, data);
        if val == BooleanMatch::SAME {
            *is_flip = false;
            return true;
        }
        if val == BooleanMatch::COMPLEMENTARY {
            *is_flip = true;
            return true;
        }
        false
    }
}

impl Rule for RuleBooleanDedup {
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
        Some(Box::new(RuleBooleanDedup::new(self.get_group())))
    }

    fn get_op_list(&self, oplist: &mut Vec<OpCode>) {
        oplist.push(OpCode::BoolAnd);
        oplist.push(OpCode::BoolOr);
    }

    fn apply_op(&mut self, op: OpId, data: &mut Funcdata, glb: &mut Architecture) -> Result<i32> {
        let vn0 = data.op(op).get_in(0);
        if !data.vn(vn0).is_written() {
            return Ok(0);
        }
        let vn1 = data.op(op).get_in(1);
        if !data.vn(vn1).is_written() {
            return Ok(0);
        }
        let op0 = data.vn(vn0).get_def().expect("written varnode without defining op");
        let opc0 = data.op(op0).code();
        if opc0 != OpCode::BoolAnd && opc0 != OpCode::BoolOr {
            return Ok(0);
        }
        let op1 = data.vn(vn1).get_def().expect("written varnode without defining op");
        let opc1 = data.op(op1).code();
        if opc1 != OpCode::BoolAnd && opc1 != OpCode::BoolOr {
            return Ok(0);
        }
        let ins: [VarnodeId; 4] = [
            data.op(op0).get_in(0),
            data.op(op0).get_in(1),
            data.op(op1).get_in(0),
            data.op(op1).get_in(1),
        ];
        if ins.iter().any(|&input| data.vn(input).is_free()) {
            return Ok(0);
        }
        let mut isflipped = false;
        let (left_a, right_a, left_o, right_o) = if RuleBooleanDedup::is_match(ins[0], ins[2], &mut isflipped, data) {
            (ins[0], ins[2], ins[1], ins[3])
        } else if RuleBooleanDedup::is_match(ins[0], ins[3], &mut isflipped, data) {
            (ins[0], ins[3], ins[1], ins[2])
        } else if RuleBooleanDedup::is_match(ins[1], ins[2], &mut isflipped, data) {
            (ins[1], ins[2], ins[0], ins[3])
        } else if RuleBooleanDedup::is_match(ins[1], ins[3], &mut isflipped, data) {
            (ins[1], ins[3], ins[0], ins[2])
        } else {
            return Ok(0);
        };
        let central_opc = data.op(op).code();
        let bc_opc: OpCode;
        let final_opc: OpCode;
        let final_a: VarnodeId;
        if isflipped {
            if central_opc == OpCode::BoolAnd && opc0 == OpCode::BoolAnd && opc1 == OpCode::BoolAnd {
                data.op_set_opcode(op, OpCode::Copy, glb);
                data.op_remove_input(op, 1);
                let falsevn = data.new_constant(1, 0, glb);
                data.op_set_input(op, falsevn, 0)?;
                return Ok(1);
            }
            if central_opc == OpCode::BoolOr && opc0 == OpCode::BoolOr && opc1 == OpCode::BoolOr {
                data.op_set_opcode(op, OpCode::Copy, glb);
                data.op_remove_input(op, 1);
                let truevn = data.new_constant(1, 1, glb);
                data.op_set_input(op, truevn, 0)?;
                return Ok(1);
            }
            if central_opc == OpCode::BoolOr && opc0 != opc1 {
                final_a = if opc0 == OpCode::BoolOr { left_a } else { right_a };
                final_opc = OpCode::BoolOr;
                bc_opc = OpCode::BoolOr;
            } else {
                return Ok(0);
            }
        } else if central_opc == opc0 && central_opc == opc1 {
            final_a = left_a;
            final_opc = central_opc;
            bc_opc = central_opc;
        } else if opc0 == opc1 && central_opc != opc0 {
            final_a = left_a;
            final_opc = opc0;
            bc_opc = central_opc;
        } else {
            return Ok(0);
        }
        let addr = data.op(op).get_addr().clone();
        let bc_op = data.new_op(2, &addr);
        let tmp = data.new_unique_out(1, bc_op, glb)?;
        data.op_set_opcode(bc_op, bc_opc, glb);
        data.op_set_input(bc_op, left_o, 0)?;
        data.op_set_input(bc_op, right_o, 1)?;
        data.op_insert_before(bc_op, op);
        data.op_set_opcode(op, final_opc, glb);
        data.op_set_input(op, final_a, 0)?;
        data.op_set_input(op, tmp, 1)?;
        Ok(1)
    }
}

pub struct RuleBooleanNegate {
    pub base: RuleBase,
}

impl RuleBooleanNegate {
    pub fn new(group: &str) -> RuleBooleanNegate {
        RuleBooleanNegate {
            base: RuleBase::new(group, 0, "booleannegate"),
        }
    }
}

impl Rule for RuleBooleanNegate {
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
        Some(Box::new(RuleBooleanNegate::new(self.get_group())))
    }

    fn get_op_list(&self, oplist: &mut Vec<OpCode>) {
        oplist.extend_from_slice(&[OpCode::IntNotequal, OpCode::IntEqual]);
    }

    fn apply_op(&mut self, op: OpId, data: &mut Funcdata, glb: &mut Architecture) -> Result<i32> {
        let opc = data.op(op).code();
        let constvn = data.op(op).get_in(1);
        let subbool = data.op(op).get_in(0);
        if !data.vn(constvn).is_constant() {
            return Ok(0);
        }
        let val = data.vn(constvn).get_offset();
        if val != 0 && val != 1 {
            return Ok(0);
        }
        let mut negate = opc == OpCode::IntNotequal;
        if val == 0 {
            negate = !negate;
        }
        if !data.vn_is_boolean_value(subbool, data.is_type_recovery_on(), glb) {
            return Ok(0);
        }
        data.op_remove_input(op, 1);
        data.op_set_input(op, subbool, 0)?;
        if negate {
            data.op_set_opcode(op, OpCode::BoolNegate, glb);
        } else {
            data.op_set_opcode(op, OpCode::Copy, glb);
        }
        Ok(1)
    }
}

pub struct RuleBoolZext {
    pub base: RuleBase,
}

impl RuleBoolZext {
    pub fn new(group: &str) -> RuleBoolZext {
        RuleBoolZext {
            base: RuleBase::new(group, 0, "boolzext"),
        }
    }
}

impl Rule for RuleBoolZext {
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
        Some(Box::new(RuleBoolZext::new(self.get_group())))
    }

    fn get_op_list(&self, oplist: &mut Vec<OpCode>) {
        oplist.push(OpCode::IntZext);
    }

    fn apply_op(&mut self, op: OpId, data: &mut Funcdata, glb: &mut Architecture) -> Result<i32> {
        let bool_vn1 = data.op(op).get_in(0);
        if !data.vn_is_boolean_value(bool_vn1, data.is_type_recovery_on(), glb) {
            return Ok(0);
        }
        let outvn = data.op(op).get_out().expect("op without output");
        let Some(multop1) = data.vn(outvn).lone_descend() else {
            return Ok(0);
        };
        if data.op(multop1).code() != OpCode::IntMult {
            return Ok(0);
        }
        let multconst = data.op(multop1).get_in(1);
        if !data.vn(multconst).is_constant() {
            return Ok(0);
        }
        let mut coeff = data.vn(multconst).get_offset();
        if coeff != calc_mask(data.vn(multconst).get_size()) {
            return Ok(0);
        }
        let multout = data.op(multop1).get_out().expect("op without output");
        let size = data.vn(multout).get_size();
        let Some(actionop) = data.vn(multout).lone_descend() else {
            return Ok(0);
        };
        let opc = match data.op(actionop).code() {
            OpCode::IntAdd => {
                let addconst = data.op(actionop).get_in(1);
                if !data.vn(addconst).is_constant() {
                    return Ok(0);
                }
                if data.vn(addconst).get_offset() == 1 {
                    let addr = data.op(op).get_addr().clone();
                    let newop = data.new_op(1, &addr);
                    data.op_set_opcode(newop, OpCode::BoolNegate, glb);
                    let vn = data.new_unique_out(1, newop, glb)?;
                    data.op_set_input(newop, bool_vn1, 0)?;
                    data.op_insert_before(newop, op);
                    data.op_set_input(op, vn, 0)?;
                    data.op_remove_input(actionop, 1);
                    data.op_set_opcode(actionop, OpCode::Copy, glb);
                    data.op_set_input(actionop, outvn, 0)?;
                    return Ok(1);
                }
                return Ok(0);
            }
            OpCode::IntEqual | OpCode::IntNotequal => {
                let cmpconst = data.op(actionop).get_in(1);
                let mut val = if data.vn(cmpconst).is_constant() {
                    data.vn(cmpconst).get_offset()
                } else {
                    return Ok(0);
                };
                if val == coeff {
                    val = 1;
                } else if val != 0 {
                    return Ok(0);
                }
                data.op_set_input(actionop, bool_vn1, 0)?;
                let newconst = data.new_constant(1, val, glb);
                data.op_set_input(actionop, newconst, 1)?;
                return Ok(1);
            }
            OpCode::IntAnd => OpCode::BoolAnd,
            OpCode::IntOr => OpCode::BoolOr,
            OpCode::IntXor => OpCode::BoolXor,
            _ => return Ok(0),
        };
        let action_def0 = data.vn(data.op(actionop).get_in(0)).get_def();
        let multop2 = if Some(multop1) == action_def0 {
            data.vn(data.op(actionop).get_in(1)).get_def()
        } else {
            action_def0
        };
        let Some(multop2) = multop2 else {
            return Ok(0);
        };
        if data.op(multop2).code() != OpCode::IntMult {
            return Ok(0);
        }
        let multconst2 = data.op(multop2).get_in(1);
        if !data.vn(multconst2).is_constant() {
            return Ok(0);
        }
        coeff = data.vn(multconst2).get_offset();
        if coeff != calc_mask(size) {
            return Ok(0);
        }
        let Some(zextop2) = data.vn(data.op(multop2).get_in(0)).get_def() else {
            return Ok(0);
        };
        if data.op(zextop2).code() != OpCode::IntZext {
            return Ok(0);
        }
        let bool_vn2 = data.op(zextop2).get_in(0);
        if !data.vn_is_boolean_value(bool_vn2, data.is_type_recovery_on(), glb) {
            return Ok(0);
        }
        let action_addr = data.op(actionop).get_addr().clone();
        let newop = data.new_op(2, &action_addr);
        let newres = data.new_unique_out(1, newop, glb)?;
        data.op_set_opcode(newop, opc, glb);
        data.op_set_input(newop, bool_vn1, 0)?;
        data.op_set_input(newop, bool_vn2, 1)?;
        data.op_insert_before(newop, actionop);
        let newzext = data.new_op(1, &action_addr);
        let newzout = data.new_unique_out(size, newzext, glb)?;
        data.op_set_opcode(newzext, OpCode::IntZext, glb);
        data.op_set_input(newzext, newres, 0)?;
        data.op_insert_before(newzext, actionop);
        data.op_set_opcode(actionop, OpCode::IntMult, glb);
        data.op_set_input(actionop, newzout, 0)?;
        let newconst = data.new_constant(size, coeff, glb);
        data.op_set_input(actionop, newconst, 1)?;
        Ok(1)
    }
}

pub struct RuleLogic2Bool {
    pub base: RuleBase,
}

impl RuleLogic2Bool {
    pub fn new(group: &str) -> RuleLogic2Bool {
        RuleLogic2Bool {
            base: RuleBase::new(group, 0, "logic2bool"),
        }
    }
}

impl Rule for RuleLogic2Bool {
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
        Some(Box::new(RuleLogic2Bool::new(self.get_group())))
    }

    fn get_op_list(&self, oplist: &mut Vec<OpCode>) {
        oplist.extend_from_slice(&[OpCode::IntAnd, OpCode::IntOr, OpCode::IntXor]);
    }

    fn apply_op(&mut self, op: OpId, data: &mut Funcdata, glb: &mut Architecture) -> Result<i32> {
        let bool_vn = data.op(op).get_in(0);
        if !data.vn_is_boolean_value(bool_vn, data.is_type_recovery_on(), glb) {
            return Ok(0);
        }
        let in1 = data.op(op).get_in(1);
        if data.vn(in1).is_constant() {
            if data.vn(in1).get_offset() > 1 {
                return Ok(0);
            }
        } else if !data.vn_is_boolean_value(in1, data.is_type_recovery_on(), glb) {
            return Ok(0);
        }
        match data.op(op).code() {
            OpCode::IntAnd => data.op_set_opcode(op, OpCode::BoolAnd, glb),
            OpCode::IntOr => data.op_set_opcode(op, OpCode::BoolOr, glb),
            OpCode::IntXor => data.op_set_opcode(op, OpCode::BoolXor, glb),
            _ => return Ok(0),
        }
        Ok(1)
    }
}

pub struct RuleAliasUpdate {
    pub base: RuleBase,
}

impl RuleAliasUpdate {
    pub fn new(group: &str) -> RuleAliasUpdate {
        RuleAliasUpdate {
            base: RuleBase::new(group, 0, "aliasupdate"),
        }
    }
}

impl Rule for RuleAliasUpdate {
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
        Some(Box::new(RuleAliasUpdate::new(self.get_group())))
    }

    fn get_op_list(&self, oplist: &mut Vec<OpCode>) {
        oplist.push(OpCode::Store);
        oplist.push(OpCode::Call);
        oplist.push(OpCode::Callind);
        oplist.push(OpCode::Callother);
    }

    fn apply_op(&mut self, op: OpId, data: &mut Funcdata, _glb: &mut Architecture) -> Result<i32> {
        if !data.op(op).has_alias_update() {
            return Ok(0);
        }
        data.op_collapse_indirects_for_alias(op)?;
        Ok(1)
    }
}

pub struct RuleMultiCollapse {
    pub base: RuleBase,
}

impl RuleMultiCollapse {
    pub fn new(group: &str) -> RuleMultiCollapse {
        RuleMultiCollapse {
            base: RuleBase::new(group, 0, "multicollapse"),
        }
    }
}

impl Rule for RuleMultiCollapse {
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
        Some(Box::new(RuleMultiCollapse::new(self.get_group())))
    }

    fn get_op_list(&self, oplist: &mut Vec<OpCode>) {
        oplist.push(OpCode::Multiequal);
    }

    fn apply_op(&mut self, op: OpId, data: &mut Funcdata, glb: &mut Architecture) -> Result<i32> {
        let num_input = data.op(op).num_input();
        for slot in 0..num_input {
            if !data.vn(data.op(op).get_in(slot)).is_heritage_known() {
                return Ok(0);
            }
        }
        let mut func_eq = false;
        let mut nofunc = false;
        let mut defcopyr: Option<VarnodeId> = None;
        let mut skiplist: Vec<VarnodeId> = Vec::new();
        let mut matchlist: Vec<VarnodeId> = Vec::new();
        for slot in 0..num_input {
            matchlist.push(data.op(op).get_in(slot));
        }
        for slot in 0..num_input as usize {
            let copyr = matchlist[slot];
            let is_multi = data.vn(copyr).is_written()
                && data
                    .op(data.vn(copyr).get_def().expect("written varnode without defining op"))
                    .code()
                    == OpCode::Multiequal;
            if !is_multi {
                defcopyr = Some(copyr);
                break;
            }
        }
        let mut success = true;
        let outvn = data.op(op).get_out().expect("op without output");
        data.vn_mut(outvn).set_mark();
        skiplist.push(outvn);
        let mut position = 0usize;
        while position < matchlist.len() {
            let copyr = matchlist[position];
            position += 1;
            if data.vn(copyr).is_mark() {
                continue;
            }
            match defcopyr {
                None => {
                    defcopyr = Some(copyr);
                    if data.vn(copyr).is_written() {
                        let def = data.vn(copyr).get_def().expect("written varnode without defining op");
                        if data.op(def).code() == OpCode::Multiequal {
                            nofunc = true;
                        }
                    } else {
                        nofunc = true;
                    }
                }
                Some(base) if base == copyr => continue,
                Some(base) => {
                    if !nofunc && functional_equality(base, copyr, data) {
                        func_eq = true;
                        continue;
                    } else if data.vn(copyr).is_written()
                        && data
                            .op(data.vn(copyr).get_def().expect("written varnode without defining op"))
                            .code()
                            == OpCode::Multiequal
                    {
                        let newop = data.vn(copyr).get_def().expect("written varnode without defining op");
                        skiplist.push(copyr);
                        data.vn_mut(copyr).set_mark();
                        for slot in 0..data.op(newop).num_input() {
                            matchlist.push(data.op(newop).get_in(slot));
                        }
                    } else {
                        success = false;
                        break;
                    }
                }
            }
        }
        if success {
            let defcopyr = defcopyr.expect("missing defining branch");
            for &copyr in skiplist.iter() {
                data.vn_mut(copyr).clear_mark();
                let curop = data.vn(copyr).get_def().expect("written varnode without defining op");
                if func_eq {
                    let parent = data.op(curop).get_parent().expect("op without parent block");
                    let curout = data.op(curop).get_out().expect("op without output");
                    let earliest = data.block_earliest_use(parent, curout);
                    let newop = data
                        .vn(defcopyr)
                        .get_def()
                        .expect("written varnode without defining op");
                    let mut substitute: Option<OpId> = None;
                    for slot in 0..data.op(newop).num_input() {
                        let invn = data.op(newop).get_in(slot);
                        if !data.vn(invn).is_constant() {
                            substitute = data.cse_find_in_block(newop, invn, parent, earliest);
                            break;
                        }
                    }
                    if let Some(substitute) = substitute {
                        let subout = data.op(substitute).get_out().expect("op without output");
                        data.total_replace(copyr, subout)?;
                        data.op_destroy(curop)?;
                    } else {
                        let needsreinsert = data.op(curop).code() == OpCode::Multiequal;
                        let parms: Vec<VarnodeId> = (0..data.op(newop).num_input())
                            .map(|slot| data.op(newop).get_in(slot))
                            .collect();
                        data.op_set_all_input(curop, &parms)?;
                        let newopc = data.op(newop).code();
                        data.op_set_opcode(curop, newopc, glb);
                        if needsreinsert {
                            let bl = data.op(curop).get_parent().expect("op without parent block");
                            data.op_uninsert(curop);
                            data.op_insert_begin(curop, bl);
                        }
                    }
                } else {
                    data.total_replace(copyr, defcopyr)?;
                    data.op_destroy(curop)?;
                }
            }
            return Ok(1);
        }
        for &copyr in skiplist.iter() {
            data.vn_mut(copyr).clear_mark();
        }
        Ok(0)
    }
}

pub struct RuleSborrow {
    pub base: RuleBase,
}

impl RuleSborrow {
    pub fn new(group: &str) -> RuleSborrow {
        RuleSborrow {
            base: RuleBase::new(group, 0, "sborrow"),
        }
    }
}

impl Rule for RuleSborrow {
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
        Some(Box::new(RuleSborrow::new(self.get_group())))
    }

    fn get_op_list(&self, oplist: &mut Vec<OpCode>) {
        oplist.push(OpCode::IntSborrow);
    }

    fn apply_op(&mut self, op: OpId, data: &mut Funcdata, glb: &mut Architecture) -> Result<i32> {
        let svn = data.op(op).get_out().expect("op without output");
        let avn = data.op(op).get_in(0);
        let bvn = data.op(op).get_in(1);
        if data.vn(bvn).is_constant() && data.vn(bvn).get_offset() == 0 {
            data.op_set_opcode(op, OpCode::Copy, glb);
            let falsevn = data.new_constant(1, 0, glb);
            data.op_set_input(op, falsevn, 0)?;
            data.op_remove_input(op, 1);
            return Ok(1);
        }
        let descendants: Vec<OpId> = data.vn(svn).descend().to_vec();
        for compop in descendants {
            let compopc = data.op(compop).code();
            if compopc != OpCode::IntEqual && compopc != OpCode::IntNotequal {
                continue;
            }
            let cvn = if data.op(compop).get_in(0) == svn {
                data.op(compop).get_in(1)
            } else {
                data.op(compop).get_in(0)
            };
            if !data.vn(cvn).is_written() {
                continue;
            }
            let signop = data.vn(cvn).get_def().expect("written varnode without defining op");
            if data.op(signop).code() != OpCode::IntSless {
                continue;
            }
            let zside: i32 = if !data.vn(data.op(signop).get_in(0)).constant_match(0) {
                if !data.vn(data.op(signop).get_in(1)).constant_match(0) {
                    continue;
                }
                1
            } else {
                0
            };
            let xvn = data.op(signop).get_in(1 - zside);
            if !data.vn(xvn).is_written() {
                continue;
            }
            let mut expr1 = AddExpression::new();
            expr1.gather_two_terms_subtract(avn, bvn, data);
            let mut expr2 = AddExpression::new();
            expr2.gather_two_terms_root(xvn, data);
            if !expr1.is_equivalent(&expr2, data) {
                continue;
            }
            if compopc == OpCode::IntNotequal {
                data.op_set_opcode(compop, OpCode::IntSless, glb);
                data.op_set_input(compop, avn, 1 - zside)?;
                data.op_set_input(compop, bvn, zside)?;
            } else {
                data.op_set_opcode(compop, OpCode::IntSlessequal, glb);
                data.op_set_input(compop, avn, zside)?;
                data.op_set_input(compop, bvn, 1 - zside)?;
            }
            return Ok(1);
        }
        Ok(0)
    }
}

pub struct RuleScarry {
    pub base: RuleBase,
}

impl RuleScarry {
    pub fn new(group: &str) -> RuleScarry {
        RuleScarry {
            base: RuleBase::new(group, 0, "scarry"),
        }
    }
}

impl Rule for RuleScarry {
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
        Some(Box::new(RuleScarry::new(self.get_group())))
    }

    fn get_op_list(&self, oplist: &mut Vec<OpCode>) {
        oplist.push(OpCode::IntScarry);
    }

    fn apply_op(&mut self, op: OpId, data: &mut Funcdata, glb: &mut Architecture) -> Result<i32> {
        let svn = data.op(op).get_out().expect("op without output");
        let mut avn = data.op(op).get_in(0);
        let mut bvn = data.op(op).get_in(1);
        if (data.vn(bvn).is_constant() && data.vn(bvn).get_offset() == 0)
            || (data.vn(avn).is_constant() && data.vn(avn).get_offset() == 0)
        {
            data.op_set_opcode(op, OpCode::Copy, glb);
            let falsevn = data.new_constant(1, 0, glb);
            data.op_set_input(op, falsevn, 0)?;
            data.op_remove_input(op, 1);
            return Ok(1);
        }
        if !data.vn(bvn).is_constant() {
            if !data.vn(avn).is_constant() {
                return Ok(0);
            }
            avn = bvn;
            bvn = data.op(op).get_in(0);
            let mut val = calc_mask(data.vn(bvn).get_size());
            val ^= val >> 1;
            if val == data.vn(bvn).get_offset() {
                return Ok(0);
            }
        }
        let descendants: Vec<OpId> = data.vn(svn).descend().to_vec();
        for compop in descendants {
            let compopc = data.op(compop).code();
            if compopc != OpCode::IntEqual && compopc != OpCode::IntNotequal {
                continue;
            }
            let cvn = if data.op(compop).get_in(0) == svn {
                data.op(compop).get_in(1)
            } else {
                data.op(compop).get_in(0)
            };
            if !data.vn(cvn).is_written() {
                continue;
            }
            let signop = data.vn(cvn).get_def().expect("written varnode without defining op");
            if data.op(signop).code() != OpCode::IntSless {
                continue;
            }
            let zside: i32 = if !data.vn(data.op(signop).get_in(0)).constant_match(0) {
                if !data.vn(data.op(signop).get_in(1)).constant_match(0) {
                    continue;
                }
                1
            } else {
                0
            };
            let xvn = data.op(signop).get_in(1 - zside);
            if !data.vn(xvn).is_written() {
                continue;
            }
            let mut expr1 = AddExpression::new();
            expr1.gather_two_terms_add(avn, bvn, data);
            let mut expr2 = AddExpression::new();
            expr2.gather_two_terms_root(xvn, data);
            if !expr1.is_equivalent(&expr2, data) {
                continue;
            }
            let bsize = data.vn(bvn).get_size();
            let newval = data.vn(bvn).get_offset().wrapping_neg() & calc_mask(bsize);
            let new_const = data.new_constant(bsize, newval, glb);
            if compopc == OpCode::IntNotequal {
                data.op_set_opcode(compop, OpCode::IntSless, glb);
                data.op_set_input(compop, avn, 1 - zside)?;
                data.op_set_input(compop, new_const, zside)?;
            } else {
                data.op_set_opcode(compop, OpCode::IntSlessequal, glb);
                data.op_set_input(compop, avn, zside)?;
                data.op_set_input(compop, new_const, 1 - zside)?;
            }
            return Ok(1);
        }
        Ok(0)
    }
}

pub struct RuleTrivialShift {
    pub base: RuleBase,
}

impl RuleTrivialShift {
    pub fn new(group: &str) -> RuleTrivialShift {
        RuleTrivialShift {
            base: RuleBase::new(group, 0, "trivialshift"),
        }
    }
}

impl Rule for RuleTrivialShift {
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
        Some(Box::new(RuleTrivialShift::new(self.get_group())))
    }

    fn get_op_list(&self, oplist: &mut Vec<OpCode>) {
        oplist.extend_from_slice(&[OpCode::IntLeft, OpCode::IntRight, OpCode::IntSright]);
    }

    fn apply_op(&mut self, op: OpId, data: &mut Funcdata, glb: &mut Architecture) -> Result<i32> {
        let constvn = data.op(op).get_in(1);
        if !data.vn(constvn).is_constant() {
            return Ok(0);
        }
        let val = data.vn(constvn).get_offset();
        if val != 0 {
            let insize = data.vn(data.op(op).get_in(0)).get_size();
            if val < (8 * insize) as u64 {
                return Ok(0);
            }
            if data.op(op).code() == OpCode::IntSright {
                return Ok(0);
            }
            let replace = data.new_constant(insize, 0, glb);
            data.op_set_input(op, replace, 0)?;
        }
        data.op_remove_input(op, 1);
        data.op_set_opcode(op, OpCode::Copy, glb);
        Ok(1)
    }
}

pub struct RuleSignShift {
    pub base: RuleBase,
}

impl RuleSignShift {
    pub fn new(group: &str) -> RuleSignShift {
        RuleSignShift {
            base: RuleBase::new(group, 0, "signshift"),
        }
    }
}

impl Rule for RuleSignShift {
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
        Some(Box::new(RuleSignShift::new(self.get_group())))
    }

    fn get_op_list(&self, oplist: &mut Vec<OpCode>) {
        oplist.push(OpCode::IntRight);
    }

    fn apply_op(&mut self, op: OpId, data: &mut Funcdata, glb: &mut Architecture) -> Result<i32> {
        let const_vn = data.op(op).get_in(1);
        if !data.vn(const_vn).is_constant() {
            return Ok(0);
        }
        let val = data.vn(const_vn).get_offset();
        let in_vn = data.op(op).get_in(0);
        let insize = data.vn(in_vn).get_size();
        if val != (8 * insize - 1) as u64 {
            return Ok(0);
        }
        if data.vn(in_vn).is_free() {
            return Ok(0);
        }
        let mut do_conversion = false;
        let out_vn = data.op(op).get_out().expect("op without output");
        for &arith_op in data.vn(out_vn).descend() {
            match data.op(arith_op).code() {
                OpCode::IntEqual | OpCode::IntNotequal if data.vn(data.op(arith_op).get_in(1)).is_constant() => {
                    do_conversion = true;
                }
                OpCode::IntAdd | OpCode::IntMult => {
                    do_conversion = true;
                }
                _ => {}
            }
            if do_conversion {
                break;
            }
        }
        if !do_conversion {
            return Ok(0);
        }
        let addr = data.op(op).get_addr().clone();
        let shift_op = data.new_op(2, &addr);
        data.op_set_opcode(shift_op, OpCode::IntSright, glb);
        let unique_vn = data.new_unique_out(insize, shift_op, glb)?;
        data.op_set_input(op, unique_vn, 0)?;
        let maskvn = data.new_constant(insize, calc_mask(insize), glb);
        data.op_set_input(op, maskvn, 1)?;
        data.op_set_opcode(op, OpCode::IntMult, glb);
        data.op_set_input(shift_op, in_vn, 0)?;
        data.op_set_input(shift_op, const_vn, 1)?;
        data.op_insert_before(shift_op, op);
        Ok(1)
    }
}

pub struct RuleTestSign {
    pub base: RuleBase,
}

impl RuleTestSign {
    pub fn new(group: &str) -> RuleTestSign {
        RuleTestSign {
            base: RuleBase::new(group, 0, "testsign"),
        }
    }

    pub fn find_comparisons(&self, vn: VarnodeId, res: &mut Vec<OpId>, data: &Funcdata) {
        for &op in data.vn(vn).descend() {
            let opc = data.op(op).code();
            if (opc == OpCode::IntEqual || opc == OpCode::IntNotequal) && data.vn(data.op(op).get_in(1)).is_constant() {
                res.push(op);
            }
        }
    }
}

impl Rule for RuleTestSign {
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
        Some(Box::new(RuleTestSign::new(self.get_group())))
    }

    fn get_op_list(&self, oplist: &mut Vec<OpCode>) {
        oplist.push(OpCode::IntSright);
    }

    fn apply_op(&mut self, op: OpId, data: &mut Funcdata, glb: &mut Architecture) -> Result<i32> {
        let const_vn = data.op(op).get_in(1);
        if !data.vn(const_vn).is_constant() {
            return Ok(0);
        }
        let val = data.vn(const_vn).get_offset();
        let in_vn = data.op(op).get_in(0);
        let insize = data.vn(in_vn).get_size();
        if val != (8 * insize - 1) as u64 {
            return Ok(0);
        }
        let out_vn = data.op(op).get_out().expect("op without output");
        if data.vn(in_vn).is_free() {
            return Ok(0);
        }
        let mut compare_ops: Vec<OpId> = Vec::new();
        self.find_comparisons(out_vn, &mut compare_ops, data);
        let mut result_code = 0;
        for compare_op in compare_ops {
            let comp_vn = data.op(compare_op).get_in(0);
            let comp_size = data.vn(comp_vn).get_size();
            let offset = data.vn(data.op(compare_op).get_in(1)).get_offset();
            let mut sgn: i32 = if offset == 0 {
                1
            } else if offset == calc_mask(comp_size) {
                -1
            } else {
                continue;
            };
            if data.op(compare_op).code() == OpCode::IntNotequal {
                sgn = -sgn;
            }
            let zero_vn = data.new_constant(insize, 0, glb);
            if sgn == 1 {
                data.op_set_input(compare_op, in_vn, 1)?;
                data.op_set_input(compare_op, zero_vn, 0)?;
                data.op_set_opcode(compare_op, OpCode::IntSlessequal, glb);
            } else {
                data.op_set_input(compare_op, in_vn, 0)?;
                data.op_set_input(compare_op, zero_vn, 1)?;
                data.op_set_opcode(compare_op, OpCode::IntSless, glb);
            }
            result_code = 1;
        }
        Ok(result_code)
    }
}
