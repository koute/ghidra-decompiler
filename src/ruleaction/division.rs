use super::written_def;
use crate::action::{ActionGroupList, Rule, RuleBase};
use crate::address::{calc_mask, count_leading_zeros, mostsigbit_set, popcount, signbit_negative};
use crate::architecture::Architecture;
use crate::error::Error;
use crate::error::Result;
use crate::funcdata::Funcdata;
use crate::multiprecision::{add128, leftshift128, set_u128, subtract128, udiv128, uless128, ulessequal128};
use crate::op::OpId;
use crate::opcodes::OpCode;
use crate::userop::UserPcodeOpKind;
use crate::varnode::VarnodeId;
use crate::varnode::{contiguous_test, find_contiguous_whole};

pub struct RuleSubNormal {
    pub base: RuleBase,
}

impl RuleSubNormal {
    pub fn new(group: &str) -> RuleSubNormal {
        RuleSubNormal {
            base: RuleBase::new(group, 0, "subnormal"),
        }
    }
}

impl Rule for RuleSubNormal {
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
        Some(Box::new(RuleSubNormal::new(self.get_group())))
    }

    fn get_op_list(&self, oplist: &mut Vec<OpCode>) {
        oplist.push(OpCode::Subpiece);
    }

    fn apply_op(&mut self, op: OpId, data: &mut Funcdata, glb: &mut Architecture) -> Result<i32> {
        let shiftout = data.op(op).get_in(0);
        let Some(shiftop) = written_def(data, shiftout) else {
            return Ok(0);
        };
        let mut opc = data.op(shiftop).code();
        if opc != OpCode::IntRight && opc != OpCode::IntSright {
            return Ok(0);
        }
        if !data.vn(data.op(shiftop).get_in(1)).is_constant() {
            return Ok(0);
        }
        let avn = data.op(shiftop).get_in(0);
        if data.vn(avn).is_free() {
            return Ok(0);
        }
        let outvn = data.op(op).get_out().expect("op without output");
        if data.vn(outvn).is_precis_hi() || data.vn(outvn).is_precis_lo() {
            return Ok(0);
        }
        let mut shift = data.vn(data.op(shiftop).get_in(1)).get_offset() as i32;
        let mut cut = data.vn(data.op(op).get_in(1)).get_offset() as i32;
        let mut kbytes = shift / 8;
        let insize = data.vn(avn).get_size();
        let outsize = data.vn(outvn).get_size();
        if shift + 8 * cut + 8 * outsize < 8 * insize && shift != kbytes * 8 {
            return Ok(0);
        }
        if kbytes + cut + outsize > insize {
            let trunc_size = insize - cut - kbytes;
            if shift == kbytes * 8 && trunc_size > 0 && popcount(trunc_size as u64) == 1 {
                cut += kbytes;
                let addr = data.op(op).get_addr().clone();
                let newop = data.new_op(2, &addr);
                opc = if opc == OpCode::IntSright {
                    OpCode::IntSext
                } else {
                    OpCode::IntZext
                };
                data.op_set_opcode(newop, OpCode::Subpiece, glb);
                let newout = data.new_unique_out(trunc_size, newop, glb)?;
                data.op_set_input(newop, avn, 0)?;
                let cutvn = data.new_constant(4, cut as i64 as u64, glb);
                data.op_set_input(newop, cutvn, 1)?;
                data.op_insert_before(newop, op);
                data.op_set_input(op, newout, 0)?;
                data.op_remove_input(op, 1);
                data.op_set_opcode(op, opc, glb);
                return Ok(1);
            } else {
                kbytes = insize - cut - outsize;
            }
        }
        cut += kbytes;
        shift -= kbytes * 8;
        if shift == 0 {
            data.op_set_input(op, avn, 0)?;
            let cutvn = data.new_constant(4, cut as i64 as u64, glb);
            data.op_set_input(op, cutvn, 1)?;
            return Ok(1);
        } else if shift >= outsize * 8 {
            shift = outsize * 8;
            if opc == OpCode::IntSright {
                shift -= 1;
            }
        }
        let addr = data.op(op).get_addr().clone();
        let newop = data.new_op(2, &addr);
        data.op_set_opcode(newop, OpCode::Subpiece, glb);
        let newout = data.new_unique_out(outsize, newop, glb)?;
        data.op_set_input(newop, avn, 0)?;
        let cutvn = data.new_constant(4, cut as i64 as u64, glb);
        data.op_set_input(newop, cutvn, 1)?;
        data.op_insert_before(newop, op);
        data.op_set_input(op, newout, 0)?;
        let shiftvn = data.new_constant(4, shift as i64 as u64, glb);
        data.op_set_input(op, shiftvn, 1)?;
        data.op_set_opcode(op, opc, glb);
        Ok(1)
    }
}

pub struct RulePositiveDiv {
    pub base: RuleBase,
}

impl RulePositiveDiv {
    pub fn new(group: &str) -> RulePositiveDiv {
        RulePositiveDiv {
            base: RuleBase::new(group, 0, "positivediv"),
        }
    }
}

impl Rule for RulePositiveDiv {
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
        Some(Box::new(RulePositiveDiv::new(self.get_group())))
    }

    fn get_op_list(&self, oplist: &mut Vec<OpCode>) {
        oplist.push(OpCode::IntSdiv);
        oplist.push(OpCode::IntSrem);
    }

    fn apply_op(&mut self, op: OpId, data: &mut Funcdata, glb: &mut Architecture) -> Result<i32> {
        let mut shift_amount = data.vn(data.op(op).get_out().expect("op without output")).get_size();
        if shift_amount > 8 {
            return Ok(0);
        }
        shift_amount = shift_amount * 8 - 1;
        if ((data.vn(data.op(op).get_in(0)).get_nz_mask() >> shift_amount) & 1) != 0 {
            return Ok(0);
        }
        if ((data.vn(data.op(op).get_in(1)).get_nz_mask() >> shift_amount) & 1) != 0 {
            return Ok(0);
        }
        let opc = if data.op(op).code() == OpCode::IntSdiv {
            OpCode::IntDiv
        } else {
            OpCode::IntRem
        };
        data.op_set_opcode(op, opc, glb);
        Ok(1)
    }
}

pub struct RuleDivTermAdd {
    pub base: RuleBase,
}

impl RuleDivTermAdd {
    pub fn new(group: &str) -> RuleDivTermAdd {
        RuleDivTermAdd {
            base: RuleBase::new(group, 0, "divtermadd"),
        }
    }

    pub fn find_subshift(op: OpId, n: &mut u32, shiftopc: &mut OpCode, data: &Funcdata) -> Option<OpId> {
        let subop;
        *shiftopc = data.op(op).code();
        if *shiftopc != OpCode::Subpiece {
            let vn = data.op(op).get_in(0);
            subop = written_def(data, vn)?;
            if data.op(subop).code() != OpCode::Subpiece {
                return None;
            }
            if !data.vn(data.op(op).get_in(1)).is_constant() {
                return None;
            }
            *n = data.vn(data.op(op).get_in(1)).get_offset() as u32;
        } else {
            *shiftopc = OpCode::Max;
            subop = op;
            *n = 0;
        }
        let cut = data.vn(data.op(subop).get_in(1)).get_offset() as u32;
        let outsize = data.vn(data.op(subop).get_out().expect("op without output")).get_size() as u32;
        if outsize.wrapping_add(cut) != data.vn(data.op(subop).get_in(0)).get_size() as u32 {
            return None;
        }
        *n = n.wrapping_add(cut.wrapping_mul(8));
        Some(subop)
    }
}

impl Rule for RuleDivTermAdd {
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
        Some(Box::new(RuleDivTermAdd::new(self.get_group())))
    }

    fn get_op_list(&self, oplist: &mut Vec<OpCode>) {
        oplist.push(OpCode::Subpiece);
        oplist.push(OpCode::IntRight);
        oplist.push(OpCode::IntSright);
    }

    fn apply_op(&mut self, op: OpId, data: &mut Funcdata, glb: &mut Architecture) -> Result<i32> {
        let mut shift: u32 = 0;
        let mut shiftopc = OpCode::Max;
        let Some(subop) = RuleDivTermAdd::find_subshift(op, &mut shift, &mut shiftopc, data) else {
            return Ok(0);
        };
        if shift > 127 {
            return Ok(0);
        }
        let multvn = data.op(subop).get_in(0);
        let Some(multop) = written_def(data, multvn) else {
            return Ok(0);
        };
        if data.op(multop).code() != OpCode::IntMult {
            return Ok(0);
        }
        let mut mult_const: [u64; 2] = [0; 2];
        if !data.vn_is_constant_extended(data.op(multop).get_in(1), &mut mult_const) {
            return Ok(0);
        }
        let extvn = data.op(multop).get_in(0);
        let Some(extop) = written_def(data, extvn) else {
            return Ok(0);
        };
        let opc = data.op(extop).code();
        if opc == OpCode::IntZext {
            if data.op(op).code() == OpCode::IntSright {
                return Ok(0);
            }
        } else if opc == OpCode::IntSext && data.op(op).code() == OpCode::IntRight {
            return Ok(0);
        }
        let mut power = set_u128(1);
        power = leftshift128(&power, shift as i32);
        mult_const = add128(&mult_const, &power);
        let xvn = data.op(extop).get_in(0);
        let outvn = data.op(op).get_out().expect("op without output");
        let descendants = data.vn(outvn).descend().to_vec();
        for addop in descendants {
            if data.op(addop).code() != OpCode::IntAdd {
                continue;
            }
            if data.op(addop).get_in(0) != xvn && data.op(addop).get_in(1) != xvn {
                continue;
            }
            let extsize = data.vn(extvn).get_size();
            let new_const_vn = data.new_extended_constant(extsize, &mult_const, op, glb)?;
            let addr = data.op(op).get_addr().clone();
            let newmultop = data.new_op(2, &addr);
            data.op_set_opcode(newmultop, OpCode::IntMult, glb);
            let newmultvn = data.new_unique_out(extsize, newmultop, glb)?;
            data.op_set_input(newmultop, extvn, 0)?;
            data.op_set_input(newmultop, new_const_vn, 1)?;
            data.op_insert_before(newmultop, op);
            let newshiftop = data.new_op(2, &addr);
            if shiftopc == OpCode::Max {
                shiftopc = OpCode::IntRight;
            }
            data.op_set_opcode(newshiftop, shiftopc, glb);
            let newshiftvn = data.new_unique_out(extsize, newshiftop, glb)?;
            data.op_set_input(newshiftop, newmultvn, 0)?;
            let shiftvn = data.new_constant(4, shift as u64, glb);
            data.op_set_input(newshiftop, shiftvn, 1)?;
            data.op_insert_before(newshiftop, op);
            data.op_set_opcode(addop, OpCode::Subpiece, glb);
            data.op_set_input(addop, newshiftvn, 0)?;
            let zerovn = data.new_constant(4, 0, glb);
            data.op_set_input(addop, zerovn, 1)?;
            return Ok(1);
        }
        Ok(0)
    }
}

pub struct RuleDivTermAdd2 {
    pub base: RuleBase,
}

impl RuleDivTermAdd2 {
    pub fn new(group: &str) -> RuleDivTermAdd2 {
        RuleDivTermAdd2 {
            base: RuleBase::new(group, 0, "divtermadd2"),
        }
    }
}

impl Rule for RuleDivTermAdd2 {
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
        Some(Box::new(RuleDivTermAdd2::new(self.get_group())))
    }

    fn get_op_list(&self, oplist: &mut Vec<OpCode>) {
        oplist.push(OpCode::IntRight);
    }

    fn apply_op(&mut self, op: OpId, data: &mut Funcdata, glb: &mut Architecture) -> Result<i32> {
        if !data.vn(data.op(op).get_in(1)).is_constant() {
            return Ok(0);
        }
        if data.vn(data.op(op).get_in(1)).get_offset() != 1 {
            return Ok(0);
        }
        let Some(subop) = written_def(data, data.op(op).get_in(0)) else {
            return Ok(0);
        };
        if data.op(subop).code() != OpCode::IntAdd {
            return Ok(0);
        }
        let mut xvn: Option<VarnodeId> = None;
        let mut found: Option<OpId> = None;
        for index in 0..2 {
            let compvn = data.op(subop).get_in(index);
            if let Some(compop) = written_def(data, compvn)
                && data.op(compop).code() == OpCode::IntMult
            {
                let invn = data.op(compop).get_in(1);
                if data.vn(invn).is_constant() && data.vn(invn).get_offset() == calc_mask(data.vn(invn).get_size()) {
                    xvn = Some(data.op(subop).get_in(1 - index));
                    found = Some(compop);
                    break;
                }
            }
        }
        let Some(compop) = found else { return Ok(0) };
        let zvn = data.op(compop).get_in(0);
        let Some(subpieceop) = written_def(data, zvn) else {
            return Ok(0);
        };
        if data.op(subpieceop).code() != OpCode::Subpiece {
            return Ok(0);
        }
        let shift = (data.vn(data.op(subpieceop).get_in(1)).get_offset() as u32).wrapping_mul(8);
        let truncation = 8 * (data.vn(data.op(subpieceop).get_in(0)).get_size() - data.vn(zvn).get_size());
        if shift > 127 || shift != truncation as u32 {
            return Ok(0);
        }
        let multvn = data.op(subpieceop).get_in(0);
        let Some(multop) = written_def(data, multvn) else {
            return Ok(0);
        };
        if data.op(multop).code() != OpCode::IntMult {
            return Ok(0);
        }
        let mut mult_const: [u64; 2] = [0; 2];
        if !data.vn_is_constant_extended(data.op(multop).get_in(1), &mut mult_const) {
            return Ok(0);
        }
        let zextvn = data.op(multop).get_in(0);
        let Some(zextop) = written_def(data, zextvn) else {
            return Ok(0);
        };
        if data.op(zextop).code() != OpCode::IntZext {
            return Ok(0);
        }
        if Some(data.op(zextop).get_in(0)) != xvn {
            return Ok(0);
        }
        let outvn = data.op(op).get_out().expect("op without output");
        let descendants = data.vn(outvn).descend().to_vec();
        for addop in descendants {
            if data.op(addop).code() != OpCode::IntAdd {
                continue;
            }
            if data.op(addop).get_in(0) != zvn && data.op(addop).get_in(1) != zvn {
                continue;
            }
            let mut pow = set_u128(1);
            pow = leftshift128(&pow, shift as i32);
            mult_const = add128(&mult_const, &pow);
            let addr = data.op(op).get_addr().clone();
            let zextsize = data.vn(zextvn).get_size();
            let newmultop = data.new_op(2, &addr);
            data.op_set_opcode(newmultop, OpCode::IntMult, glb);
            let newmultvn = data.new_unique_out(zextsize, newmultop, glb)?;
            data.op_set_input(newmultop, zextvn, 0)?;
            let new_const_vn = data.new_extended_constant(zextsize, &mult_const, op, glb)?;
            data.op_set_input(newmultop, new_const_vn, 1)?;
            data.op_insert_before(newmultop, op);
            let newshiftop = data.new_op(2, &addr);
            data.op_set_opcode(newshiftop, OpCode::IntRight, glb);
            let newshiftvn = data.new_unique_out(zextsize, newshiftop, glb)?;
            data.op_set_input(newshiftop, newmultvn, 0)?;
            let shiftvn = data.new_constant(4, (shift + 1) as u64, glb);
            data.op_set_input(newshiftop, shiftvn, 1)?;
            data.op_insert_before(newshiftop, op);
            data.op_set_opcode(addop, OpCode::Subpiece, glb);
            data.op_set_input(addop, newshiftvn, 0)?;
            let zerovn = data.new_constant(4, 0, glb);
            data.op_set_input(addop, zerovn, 1)?;
            return Ok(1);
        }
        Ok(0)
    }
}

pub struct RuleDivOpt {
    pub base: RuleBase,
}

impl RuleDivOpt {
    pub fn new(group: &str) -> RuleDivOpt {
        RuleDivOpt {
            base: RuleBase::new(group, 0, "divopt"),
        }
    }

    pub fn calc_divisor(shift_amount: u32, multiplier: &mut [u64; 2], xsize: u32) -> Result<u64> {
        if shift_amount > 127 || xsize > 64 {
            return Ok(0);
        }
        let mut power = set_u128(1);
        if ulessequal128(multiplier, &power) {
            return Ok(0);
        }
        *multiplier = subtract128(multiplier, &power);
        power = leftshift128(&power, shift_amount as i32);
        let (mut quotient, mut remainder) = udiv128(&power, multiplier)?;
        if quotient[1] != 0 {
            return Ok(0);
        }
        if uless128(multiplier, &quotient) {
            return Ok(0);
        }
        let mut diff: u64 = 0;
        if !uless128(&remainder, &quotient) {
            quotient[0] = quotient[0].wrapping_add(1);
            remainder = subtract128(&remainder, multiplier);
            remainder = add128(&remainder, &quotient);
            if !uless128(&remainder, &quotient) {
                return Ok(0);
            }
            diff = quotient[0];
        }
        let mut maxx: u64 = if xsize == 64 { 0 } else { 1u64 << xsize };
        maxx = maxx.wrapping_sub(1);
        diff = diff.wrapping_add(quotient[0].wrapping_sub(remainder[0]));
        let denom = set_u128(diff);
        let (tmp, _) = udiv128(&power, &denom)?;
        if tmp[1] != 0 {
            return Ok(quotient[0]);
        }
        if tmp[0] <= maxx {
            return Ok(0);
        }
        Ok(quotient[0])
    }

    pub fn move_sign_bit_extraction(first_vn: VarnodeId, replace_vn: VarnodeId, data: &mut Funcdata) -> Result<()> {
        let mut test_list: Vec<VarnodeId> = vec![first_vn];
        if let Some(op) = written_def(data, first_vn)
            && data.op(op).code() == OpCode::IntSright
        {
            test_list.push(data.op(op).get_in(0));
        }
        let mut index = 0;
        while index < test_list.len() {
            let vn = test_list[index];
            index += 1;
            let descendants = data.vn(vn).descend().to_vec();
            for op in descendants {
                let opc = data.op(op).code();
                if opc == OpCode::IntRight || opc == OpCode::IntSright {
                    let mut const_vn = data.op(op).get_in(1);
                    if let Some(const_op) = written_def(data, const_vn) {
                        if data.op(const_op).code() == OpCode::Copy {
                            const_vn = data.op(const_op).get_in(0);
                        } else if data.op(const_op).code() == OpCode::IntAnd {
                            const_vn = data.op(const_op).get_in(0);
                            let other_vn = data.op(const_op).get_in(1);
                            if !data.vn(other_vn).is_constant() {
                                continue;
                            }
                            let offset = data.vn(const_vn).get_offset();
                            if offset != (offset & data.vn(other_vn).get_offset()) {
                                continue;
                            }
                        }
                    }
                    if data.vn(const_vn).is_constant() {
                        let shift_amount = data.vn(first_vn).get_size() * 8 - 1;
                        if shift_amount == data.vn(const_vn).get_offset() as i32 {
                            data.op_set_input(op, replace_vn, 0)?;
                        }
                    }
                } else if opc == OpCode::Copy {
                    test_list.push(data.op(op).get_out().expect("op without output"));
                }
            }
        }
        Ok(())
    }

    pub fn check_form_overlap(op: OpId, data: &Funcdata) -> bool {
        if data.op(op).code() != OpCode::Subpiece {
            return false;
        }
        let vn = data.op(op).get_out().expect("op without output");
        for &super_op in data.vn(vn).descend() {
            let opc = data.op(super_op).code();
            if opc != OpCode::IntRight && opc != OpCode::IntSright {
                continue;
            }
            let cvn = data.op(super_op).get_in(1);
            if !data.vn(cvn).is_constant() {
                return true;
            }
            let mut shift: u32 = 0;
            let mut xsize: u32 = 0;
            let mut coeff: [u64; 2] = [0; 2];
            let mut extopc = OpCode::Max;
            if RuleDivOpt::find_form(super_op, &mut shift, &mut coeff, &mut xsize, &mut extopc, data).is_some() {
                return true;
            }
        }
        false
    }

    pub fn find_form(
        op: OpId,
        n: &mut u32,
        y: &mut [u64; 2],
        xsize: &mut u32,
        extopc: &mut OpCode,
        data: &Funcdata,
    ) -> Option<VarnodeId> {
        let mut cur_op = op;
        let mut shiftopc = data.op(cur_op).code();
        if shiftopc == OpCode::IntRight || shiftopc == OpCode::IntSright {
            let vn = data.op(cur_op).get_in(0);
            if !data.vn(vn).is_written() {
                return None;
            }
            let cvn = data.op(cur_op).get_in(1);
            if !data.vn(cvn).is_constant() {
                return None;
            }
            *n = data.vn(cvn).get_offset() as u32;
            cur_op = data.vn(vn).get_def().expect("written varnode without defining op");
        } else {
            *n = 0;
            if shiftopc != OpCode::Subpiece {
                return None;
            }
            shiftopc = OpCode::Max;
        }
        if data.op(cur_op).code() == OpCode::Subpiece {
            let cut = data.vn(data.op(cur_op).get_in(1)).get_offset() as i32;
            let in_vn = data.op(cur_op).get_in(0);
            if !data.vn(in_vn).is_written() {
                return None;
            }
            if data
                .vn(data.op(cur_op).get_out().expect("op without output"))
                .get_size()
                + cut
                != data.vn(in_vn).get_size()
            {
                return None;
            }
            *n = n.wrapping_add((8 * cut) as u32);
            cur_op = data.vn(in_vn).get_def().expect("written varnode without defining op");
        }
        if data.op(cur_op).code() != OpCode::IntMult {
            return None;
        }
        let mut in_vn = data.op(cur_op).get_in(0);
        if !data.vn(in_vn).is_written() {
            return None;
        }
        if data.vn_is_constant_extended(in_vn, y) {
            in_vn = data.op(cur_op).get_in(1);
            if !data.vn(in_vn).is_written() {
                return None;
            }
        } else if !data.vn_is_constant_extended(data.op(cur_op).get_in(1), y) {
            return None;
        }
        let ext_op = data.vn(in_vn).get_def().expect("written varnode without defining op");
        *extopc = data.op(ext_op).code();
        if *extopc != OpCode::IntSext {
            let nz_mask = if *extopc == OpCode::IntZext {
                data.vn(data.op(ext_op).get_in(0)).get_nz_mask()
            } else {
                data.vn(in_vn).get_nz_mask()
            };
            *xsize = (64 - count_leading_zeros(nz_mask)) as u32;
            if *xsize == 0 {
                return None;
            }
            if *xsize > (4 * data.vn(in_vn).get_size()) as u32 {
                return None;
            }
        } else {
            *xsize = (data.vn(data.op(ext_op).get_in(0)).get_size() * 8) as u32;
        }
        let res_vn;
        if *extopc == OpCode::IntZext || *extopc == OpCode::IntSext {
            let ext_vn = data.op(ext_op).get_in(0);
            if data.vn(ext_vn).is_free() {
                return None;
            }
            if data.vn(in_vn).get_size() == data.vn(data.op(op).get_out().expect("op without output")).get_size() {
                res_vn = in_vn;
            } else {
                res_vn = ext_vn;
            }
        } else {
            *extopc = OpCode::IntZext;
            res_vn = in_vn;
        }
        if (*extopc == OpCode::IntZext && shiftopc == OpCode::IntSright)
            || (*extopc == OpCode::IntSext && shiftopc == OpCode::IntRight)
        {
            let outbits = (8 * data.vn(data.op(op).get_out().expect("op without output")).get_size()) as u32;
            if outbits.wrapping_sub(*n) != *xsize {
                return None;
            }
        }
        Some(res_vn)
    }
}

impl Rule for RuleDivOpt {
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
        Some(Box::new(RuleDivOpt::new(self.get_group())))
    }

    fn get_op_list(&self, oplist: &mut Vec<OpCode>) {
        oplist.push(OpCode::Subpiece);
        oplist.push(OpCode::IntRight);
        oplist.push(OpCode::IntSright);
    }

    fn apply_op(&mut self, op: OpId, data: &mut Funcdata, glb: &mut Architecture) -> Result<i32> {
        let mut op = op;
        let mut shift: u32 = 0;
        let mut xsize: u32 = 0;
        let mut coeff: [u64; 2] = [0; 2];
        let mut ext_opc = OpCode::Max;
        let Some(mut in_vn) = RuleDivOpt::find_form(op, &mut shift, &mut coeff, &mut xsize, &mut ext_opc, data) else {
            return Ok(0);
        };
        if RuleDivOpt::check_form_overlap(op, data) {
            return Ok(0);
        }
        if ext_opc == OpCode::IntSext {
            xsize = xsize.wrapping_sub(1);
        }
        let divisor = RuleDivOpt::calc_divisor(shift, &mut coeff, xsize)?;
        if divisor == 0 {
            return Ok(0);
        }
        let mut out_size = data.vn(data.op(op).get_out().expect("op without output")).get_size();
        let addr = data.op(op).get_addr().clone();
        if data.vn(in_vn).get_size() < out_size {
            let in_ext = data.new_op(1, &addr);
            data.op_set_opcode(in_ext, ext_opc, glb);
            let ext_out = data.new_unique_out(out_size, in_ext, glb)?;
            data.op_set_input(in_ext, in_vn, 0)?;
            in_vn = ext_out;
            data.op_insert_before(in_ext, op);
        } else if data.vn(in_vn).get_size() > out_size {
            let newop = data.new_op(2, &addr);
            data.op_set_opcode(newop, OpCode::IntAdd, glb);
            let res_vn = data.new_unique_out(data.vn(in_vn).get_size(), newop, glb)?;
            data.op_insert_before(newop, op);
            data.op_set_opcode(op, OpCode::Subpiece, glb);
            data.op_set_input(op, res_vn, 0)?;
            let zerovn = data.new_constant(4, 0, glb);
            data.op_set_input(op, zerovn, 1)?;
            op = newop;
            out_size = data.vn(in_vn).get_size();
        }
        if ext_opc == OpCode::IntZext {
            data.op_set_input(op, in_vn, 0)?;
            let divvn = data.new_constant(out_size, divisor, glb);
            data.op_set_input(op, divvn, 1)?;
            data.op_set_opcode(op, OpCode::IntDiv, glb);
        } else {
            let outvn = data.op(op).get_out().expect("op without output");
            RuleDivOpt::move_sign_bit_extraction(outvn, in_vn, data)?;
            let divop = data.new_op(2, &addr);
            data.op_set_opcode(divop, OpCode::IntSdiv, glb);
            let newout = data.new_unique_out(out_size, divop, glb)?;
            data.op_set_input(divop, in_vn, 0)?;
            let divvn = data.new_constant(out_size, divisor, glb);
            data.op_set_input(divop, divvn, 1)?;
            data.op_insert_before(divop, op);
            let sgnop = data.new_op(2, &addr);
            data.op_set_opcode(sgnop, OpCode::IntSright, glb);
            let sgnvn = data.new_unique_out(out_size, sgnop, glb)?;
            data.op_set_input(sgnop, in_vn, 0)?;
            let shiftvn = data.new_constant(out_size, (out_size * 8 - 1) as i64 as u64, glb);
            data.op_set_input(sgnop, shiftvn, 1)?;
            data.op_insert_before(sgnop, op);
            data.op_set_input(op, newout, 0)?;
            data.op_set_input(op, sgnvn, 1)?;
            data.op_set_opcode(op, OpCode::IntAdd, glb);
        }
        Ok(1)
    }
}

pub struct RuleSignDiv2 {
    pub base: RuleBase,
}

impl RuleSignDiv2 {
    pub fn new(group: &str) -> RuleSignDiv2 {
        RuleSignDiv2 {
            base: RuleBase::new(group, 0, "signdiv2"),
        }
    }
}

impl Rule for RuleSignDiv2 {
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
        Some(Box::new(RuleSignDiv2::new(self.get_group())))
    }

    fn get_op_list(&self, oplist: &mut Vec<OpCode>) {
        oplist.push(OpCode::IntSright);
    }

    fn apply_op(&mut self, op: OpId, data: &mut Funcdata, glb: &mut Architecture) -> Result<i32> {
        if !data.vn(data.op(op).get_in(1)).is_constant() {
            return Ok(0);
        }
        if data.vn(data.op(op).get_in(1)).get_offset() != 1 {
            return Ok(0);
        }
        let addout = data.op(op).get_in(0);
        let Some(addop) = written_def(data, addout) else {
            return Ok(0);
        };
        if data.op(addop).code() != OpCode::IntAdd {
            return Ok(0);
        }
        let mut found: Option<VarnodeId> = None;
        for index in 0..2 {
            let multout = data.op(addop).get_in(index);
            let Some(multop) = written_def(data, multout) else {
                continue;
            };
            if data.op(multop).code() != OpCode::IntMult {
                continue;
            }
            let multconst = data.op(multop).get_in(1);
            if !data.vn(multconst).is_constant() {
                continue;
            }
            if data.vn(multconst).get_offset() != calc_mask(data.vn(multconst).get_size()) {
                continue;
            }
            let shiftout = data.op(multop).get_in(0);
            let Some(shiftop) = written_def(data, shiftout) else {
                continue;
            };
            if data.op(shiftop).code() != OpCode::IntSright {
                continue;
            }
            if !data.vn(data.op(shiftop).get_in(1)).is_constant() {
                continue;
            }
            let shift = data.vn(data.op(shiftop).get_in(1)).get_offset() as i32;
            let avn = data.op(shiftop).get_in(0);
            if avn != data.op(addop).get_in(1 - index) {
                continue;
            }
            if shift != 8 * data.vn(avn).get_size() - 1 {
                continue;
            }
            if data.vn(avn).is_free() {
                continue;
            }
            found = Some(avn);
            break;
        }
        let Some(avn) = found else { return Ok(0) };
        data.op_set_input(op, avn, 0)?;
        let twovn = data.new_constant(data.vn(avn).get_size(), 2, glb);
        data.op_set_input(op, twovn, 1)?;
        data.op_set_opcode(op, OpCode::IntSdiv, glb);
        Ok(1)
    }
}

pub struct RuleDivChain {
    pub base: RuleBase,
}

impl RuleDivChain {
    pub fn new(group: &str) -> RuleDivChain {
        RuleDivChain {
            base: RuleBase::new(group, 0, "divchain"),
        }
    }
}

impl Rule for RuleDivChain {
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
        Some(Box::new(RuleDivChain::new(self.get_group())))
    }

    fn get_op_list(&self, oplist: &mut Vec<OpCode>) {
        oplist.push(OpCode::IntDiv);
        oplist.push(OpCode::IntSdiv);
    }

    fn apply_op(&mut self, op: OpId, data: &mut Funcdata, glb: &mut Architecture) -> Result<i32> {
        let opc2 = data.op(op).code();
        let const_vn2 = data.op(op).get_in(1);
        if !data.vn(const_vn2).is_constant() {
            return Ok(0);
        }
        let vn = data.op(op).get_in(0);
        let Some(div_op) = written_def(data, vn) else {
            return Ok(0);
        };
        let opc1 = data.op(div_op).code();
        if opc1 != opc2 && (opc2 != OpCode::IntDiv || opc1 != OpCode::IntRight) {
            return Ok(0);
        }
        let const_vn1 = data.op(div_op).get_in(1);
        if !data.vn(const_vn1).is_constant() {
            return Ok(0);
        }
        if data.vn(vn).lone_descend().is_none() {
            return Ok(0);
        }
        let mut val1: u64;
        if opc1 == opc2 {
            val1 = data.vn(const_vn1).get_offset();
        } else {
            let shift_amount = data.vn(const_vn1).get_offset() as i32;
            val1 = 1u64.wrapping_shl(shift_amount as u32);
        }
        let base_vn = data.op(div_op).get_in(0);
        if data.vn(base_vn).is_free() {
            return Ok(0);
        }
        let sz = data.vn(vn).get_size();
        let mut val2 = data.vn(const_vn2).get_offset();
        let resval = val1.wrapping_mul(val2) & calc_mask(sz);
        if resval == 0 {
            return Ok(0);
        }
        if signbit_negative(val1, sz) {
            val1 = (!val1).wrapping_add(1) & calc_mask(sz);
        }
        if signbit_negative(val2, sz) {
            val2 = (!val2).wrapping_add(1) & calc_mask(sz);
        }
        let bitcount = mostsigbit_set(val1) + mostsigbit_set(val2) + 2;
        if opc2 == OpCode::IntDiv && bitcount > sz * 8 {
            return Ok(0);
        }
        if opc2 == OpCode::IntSdiv && bitcount > sz * 8 - 2 {
            return Ok(0);
        }
        data.op_set_input(op, base_vn, 0)?;
        let constvn = data.new_constant(sz, resval, glb);
        data.op_set_input(op, constvn, 1)?;
        Ok(1)
    }
}

pub struct RuleSignForm {
    pub base: RuleBase,
}

impl RuleSignForm {
    pub fn new(group: &str) -> RuleSignForm {
        RuleSignForm {
            base: RuleBase::new(group, 0, "signform"),
        }
    }
}

impl Rule for RuleSignForm {
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
        Some(Box::new(RuleSignForm::new(self.get_group())))
    }

    fn get_op_list(&self, oplist: &mut Vec<OpCode>) {
        oplist.push(OpCode::Subpiece);
    }

    fn apply_op(&mut self, op: OpId, data: &mut Funcdata, glb: &mut Architecture) -> Result<i32> {
        let sextout = data.op(op).get_in(0);
        let Some(sextop) = written_def(data, sextout) else {
            return Ok(0);
        };
        if data.op(sextop).code() != OpCode::IntSext {
            return Ok(0);
        }
        let avn = data.op(sextop).get_in(0);
        let cut = data.vn(data.op(op).get_in(1)).get_offset() as i32;
        if cut < data.vn(avn).get_size() {
            return Ok(0);
        }
        if data.vn(avn).is_free() {
            return Ok(0);
        }
        data.op_set_input(op, avn, 0)?;
        let shift = 8 * data.vn(avn).get_size() - 1;
        let shiftvn = data.new_constant(4, shift as i64 as u64, glb);
        data.op_set_input(op, shiftvn, 1)?;
        data.op_set_opcode(op, OpCode::IntSright, glb);
        Ok(1)
    }
}

pub struct RuleSignForm2 {
    pub base: RuleBase,
}

impl RuleSignForm2 {
    pub fn new(group: &str) -> RuleSignForm2 {
        RuleSignForm2 {
            base: RuleBase::new(group, 0, "signform2"),
        }
    }
}

impl Rule for RuleSignForm2 {
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
        Some(Box::new(RuleSignForm2::new(self.get_group())))
    }

    fn get_op_list(&self, oplist: &mut Vec<OpCode>) {
        oplist.push(OpCode::IntSright);
    }

    fn apply_op(&mut self, op: OpId, data: &mut Funcdata, _glb: &mut Architecture) -> Result<i32> {
        let const_vn = data.op(op).get_in(1);
        if !data.vn(const_vn).is_constant() {
            return Ok(0);
        }
        let in_vn = data.op(op).get_in(0);
        let sizeout = data.vn(in_vn).get_size();
        if data.vn(const_vn).get_offset() as i32 != sizeout * 8 - 1 {
            return Ok(0);
        }
        let Some(sub_op) = written_def(data, in_vn) else {
            return Ok(0);
        };
        if data.op(sub_op).code() != OpCode::Subpiece {
            return Ok(0);
        }
        let cut = data.vn(data.op(sub_op).get_in(1)).get_offset() as i32;
        let mult_out = data.op(sub_op).get_in(0);
        let mult_size = data.vn(mult_out).get_size();
        if cut + sizeout != mult_size {
            return Ok(0);
        }
        let Some(mult_op) = written_def(data, mult_out) else {
            return Ok(0);
        };
        if data.op(mult_op).code() != OpCode::IntMult {
            return Ok(0);
        }
        let mut found: Option<(i32, OpId)> = None;
        for slot in 0..2 {
            let vn = data.op(mult_op).get_in(slot);
            let Some(sext_op) = written_def(data, vn) else { continue };
            if data.op(sext_op).code() == OpCode::IntSext {
                found = Some((slot, sext_op));
                break;
            }
        }
        let Some((slot, sext_op)) = found else { return Ok(0) };
        let avn = data.op(sext_op).get_in(0);
        if data.vn(avn).is_free() || data.vn(avn).get_size() != sizeout {
            return Ok(0);
        }
        let other_vn = data.op(mult_op).get_in(1 - slot);
        if data.vn(other_vn).is_constant() {
            if data.vn(other_vn).get_offset() > calc_mask(sizeout) {
                return Ok(0);
            }
            if 2 * sizeout > mult_size {
                return Ok(0);
            }
        } else if let Some(zext_op) = written_def(data, other_vn) {
            if data.op(zext_op).code() != OpCode::IntZext {
                return Ok(0);
            }
            if data.vn(data.op(zext_op).get_in(0)).get_size() + sizeout > mult_size {
                return Ok(0);
            }
        } else {
            return Ok(0);
        }
        data.op_set_input(op, avn, 0)?;
        Ok(0)
    }
}

pub struct RuleSignNearMult {
    pub base: RuleBase,
}

impl RuleSignNearMult {
    pub fn new(group: &str) -> RuleSignNearMult {
        RuleSignNearMult {
            base: RuleBase::new(group, 0, "signnearmult"),
        }
    }
}

impl Rule for RuleSignNearMult {
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
        Some(Box::new(RuleSignNearMult::new(self.get_group())))
    }

    fn get_op_list(&self, oplist: &mut Vec<OpCode>) {
        oplist.push(OpCode::IntAnd);
    }

    fn apply_op(&mut self, op: OpId, data: &mut Funcdata, glb: &mut Architecture) -> Result<i32> {
        if !data.vn(data.op(op).get_in(1)).is_constant() {
            return Ok(0);
        }
        let Some(addop) = written_def(data, data.op(op).get_in(0)) else {
            return Ok(0);
        };
        if data.op(addop).code() != OpCode::IntAdd {
            return Ok(0);
        }
        let mut found: Option<(i32, VarnodeId, OpId)> = None;
        for index in 0..2 {
            let shiftvn = data.op(addop).get_in(index);
            let Some(unshiftop) = written_def(data, shiftvn) else {
                continue;
            };
            if data.op(unshiftop).code() == OpCode::IntRight {
                if !data.vn(data.op(unshiftop).get_in(1)).is_constant() {
                    continue;
                }
                found = Some((index, shiftvn, unshiftop));
                break;
            }
        }
        let Some((index, shiftvn, unshiftop)) = found else {
            return Ok(0);
        };
        let xvn = data.op(addop).get_in(1 - index);
        if data.vn(xvn).is_free() {
            return Ok(0);
        }
        let mut shift = data.vn(data.op(unshiftop).get_in(1)).get_offset() as i32;
        if shift <= 0 {
            return Ok(0);
        }
        shift = data.vn(shiftvn).get_size() * 8 - shift;
        if shift <= 0 {
            return Ok(0);
        }
        let mut mask = calc_mask(data.vn(shiftvn).get_size());
        mask = mask.wrapping_shl(shift as u32) & mask;
        if mask != data.vn(data.op(op).get_in(1)).get_offset() {
            return Ok(0);
        }
        let sgnvn = data.op(unshiftop).get_in(0);
        let Some(sshiftop) = written_def(data, sgnvn) else {
            return Ok(0);
        };
        if data.op(sshiftop).code() != OpCode::IntSright {
            return Ok(0);
        }
        if !data.vn(data.op(sshiftop).get_in(1)).is_constant() {
            return Ok(0);
        }
        if data.op(sshiftop).get_in(0) != xvn {
            return Ok(0);
        }
        let val = data.vn(data.op(sshiftop).get_in(1)).get_offset() as i32;
        if val != 8 * data.vn(xvn).get_size() - 1 {
            return Ok(0);
        }
        let pow = 1u64.wrapping_shl(shift as u32);
        let addr = data.op(op).get_addr().clone();
        let xsize = data.vn(xvn).get_size();
        let newdiv = data.new_op(2, &addr);
        data.op_set_opcode(newdiv, OpCode::IntSdiv, glb);
        let divvn = data.new_unique_out(xsize, newdiv, glb)?;
        data.op_set_input(newdiv, xvn, 0)?;
        let powvn = data.new_constant(xsize, pow, glb);
        data.op_set_input(newdiv, powvn, 1)?;
        data.op_insert_before(newdiv, op);
        data.op_set_opcode(op, OpCode::IntMult, glb);
        data.op_set_input(op, divvn, 0)?;
        let powvn = data.new_constant(xsize, pow, glb);
        data.op_set_input(op, powvn, 1)?;
        Ok(1)
    }
}

pub struct RuleModOpt {
    pub base: RuleBase,
}

impl RuleModOpt {
    pub fn new(group: &str) -> RuleModOpt {
        RuleModOpt {
            base: RuleBase::new(group, 0, "modopt"),
        }
    }
}

impl Rule for RuleModOpt {
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
        Some(Box::new(RuleModOpt::new(self.get_group())))
    }

    fn get_op_list(&self, oplist: &mut Vec<OpCode>) {
        oplist.push(OpCode::IntDiv);
        oplist.push(OpCode::IntSdiv);
    }

    fn apply_op(&mut self, op: OpId, data: &mut Funcdata, glb: &mut Architecture) -> Result<i32> {
        let xvn = data.op(op).get_in(0);
        let div = data.op(op).get_in(1);
        let outvn = data.op(op).get_out().expect("op without output");
        let mult_ops = data.vn(outvn).descend().to_vec();
        for multop in mult_ops {
            if data.op(multop).code() != OpCode::IntMult {
                continue;
            }
            let mut div2 = data.op(multop).get_in(1);
            if div2 == outvn {
                div2 = data.op(multop).get_in(0);
            }
            if data.vn(div2).is_constant() {
                if !data.vn(div).is_constant() {
                    continue;
                }
                let mask = calc_mask(data.vn(div2).get_size());
                if ((data.vn(div2).get_offset() ^ mask).wrapping_add(1) & mask) != data.vn(div).get_offset() {
                    continue;
                }
            } else {
                let Some(div2_def) = written_def(data, div2) else {
                    continue;
                };
                if data.op(div2_def).code() != OpCode::Int2comp {
                    continue;
                }
                if data.op(div2_def).get_in(0) != div {
                    continue;
                }
            }
            let outvn2 = data.op(multop).get_out().expect("op without output");
            let add_ops = data.vn(outvn2).descend().to_vec();
            for addop in add_ops {
                if data.op(addop).code() != OpCode::IntAdd {
                    continue;
                }
                let mut lvn = data.op(addop).get_in(0);
                if lvn == outvn2 {
                    lvn = data.op(addop).get_in(1);
                }
                if lvn != xvn {
                    continue;
                }
                data.op_set_input(addop, xvn, 0)?;
                if data.vn(div).is_constant() {
                    let constvn = data.new_constant(data.vn(div).get_size(), data.vn(div).get_offset(), glb);
                    data.op_set_input(addop, constvn, 1)?;
                } else {
                    data.op_set_input(addop, div, 1)?;
                }
                if data.op(op).code() == OpCode::IntDiv {
                    data.op_set_opcode(addop, OpCode::IntRem, glb);
                } else {
                    data.op_set_opcode(addop, OpCode::IntSrem, glb);
                }
                return Ok(1);
            }
        }
        Ok(0)
    }
}

pub struct RuleSignMod2nOpt {
    pub base: RuleBase,
}

impl RuleSignMod2nOpt {
    pub fn new(group: &str) -> RuleSignMod2nOpt {
        RuleSignMod2nOpt {
            base: RuleBase::new(group, 0, "signmod2nopt"),
        }
    }

    pub fn check_sign_extraction(out_vn: VarnodeId, data: &Funcdata) -> Option<VarnodeId> {
        let sign_op = written_def(data, out_vn)?;
        if data.op(sign_op).code() != OpCode::IntSright {
            return None;
        }
        let const_vn = data.op(sign_op).get_in(1);
        if !data.vn(const_vn).is_constant() {
            return None;
        }
        let val = data.vn(const_vn).get_offset() as i32;
        let res_vn = data.op(sign_op).get_in(0);
        let insize = data.vn(res_vn).get_size();
        if val != insize * 8 - 1 {
            return None;
        }
        Some(res_vn)
    }
}

impl Rule for RuleSignMod2nOpt {
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
        Some(Box::new(RuleSignMod2nOpt::new(self.get_group())))
    }

    fn get_op_list(&self, oplist: &mut Vec<OpCode>) {
        oplist.push(OpCode::IntRight);
    }

    fn apply_op(&mut self, op: OpId, data: &mut Funcdata, glb: &mut Architecture) -> Result<i32> {
        if !data.vn(data.op(op).get_in(1)).is_constant() {
            return Ok(0);
        }
        let shift_amt = data.vn(data.op(op).get_in(1)).get_offset() as i32;
        let avn = match RuleSignMod2nOpt::check_sign_extraction(data.op(op).get_in(0), data) {
            Some(avn) if !data.vn(avn).is_free() => avn,
            _ => return Ok(0),
        };
        let correct_vn = data.op(op).get_out().expect("op without output");
        let shift = data.vn(avn).get_size() * 8 - shift_amt;
        let mask = 1u64.wrapping_shl(shift as u32).wrapping_sub(1);
        let mult_ops = data.vn(correct_vn).descend().to_vec();
        for multop in mult_ops {
            if data.op(multop).code() != OpCode::IntMult {
                continue;
            }
            let negone = data.op(multop).get_in(1);
            if !data.vn(negone).is_constant() {
                continue;
            }
            if data.vn(negone).get_offset() != calc_mask(data.vn(correct_vn).get_size()) {
                continue;
            }
            let multout = data.op(multop).get_out().expect("op without output");
            let Some(base_op) = data.vn(multout).lone_descend() else {
                continue;
            };
            if data.op(base_op).code() != OpCode::IntAdd {
                continue;
            }
            let slot = 1 - data.op(base_op).get_slot(multout);
            let mut and_out = data.op(base_op).get_in(slot);
            let Some(mut and_op) = written_def(data, and_out) else {
                continue;
            };
            let mut trunc_size = -1;
            if data.op(and_op).code() == OpCode::IntZext {
                and_out = data.op(and_op).get_in(0);
                let Some(inner) = written_def(data, and_out) else {
                    continue;
                };
                and_op = inner;
                if data.op(and_op).code() != OpCode::IntAnd {
                    continue;
                }
                trunc_size = data.vn(and_out).get_size();
            } else if data.op(and_op).code() != OpCode::IntAnd {
                continue;
            }
            let const_vn = data.op(and_op).get_in(1);
            if !data.vn(const_vn).is_constant() {
                continue;
            }
            if data.vn(const_vn).get_offset() != mask {
                continue;
            }
            let add_out = data.op(and_op).get_in(0);
            let Some(add_op) = written_def(data, add_out) else {
                continue;
            };
            if data.op(add_op).code() != OpCode::IntAdd {
                continue;
            }
            let mut a_slot = 0;
            while a_slot < 2 {
                let mut vn = data.op(add_op).get_in(a_slot);
                if trunc_size >= 0 {
                    let Some(sub_op) = written_def(data, vn) else {
                        a_slot += 1;
                        continue;
                    };
                    if data.op(sub_op).code() != OpCode::Subpiece
                        || data.vn(data.op(sub_op).get_in(1)).get_offset() != 0
                    {
                        a_slot += 1;
                        continue;
                    }
                    vn = data.op(sub_op).get_in(0);
                }
                if avn == vn {
                    break;
                }
                a_slot += 1;
            }
            if a_slot > 1 {
                continue;
            }
            let ext_vn = data.op(add_op).get_in(1 - a_slot);
            let Some(shift_op) = written_def(data, ext_vn) else {
                continue;
            };
            if data.op(shift_op).code() != OpCode::IntRight {
                continue;
            }
            let const_vn = data.op(shift_op).get_in(1);
            if !data.vn(const_vn).is_constant() {
                continue;
            }
            let mut shiftval = data.vn(const_vn).get_offset() as i32;
            if trunc_size >= 0 {
                shiftval += (data.vn(avn).get_size() - trunc_size) * 8;
            }
            if shiftval != shift_amt {
                continue;
            }
            let Some(mut ext_vn) = RuleSignMod2nOpt::check_sign_extraction(data.op(shift_op).get_in(0), data) else {
                continue;
            };
            if trunc_size >= 0 {
                let Some(sub_op) = written_def(data, ext_vn) else {
                    continue;
                };
                if data.op(sub_op).code() != OpCode::Subpiece {
                    continue;
                }
                if data.vn(data.op(sub_op).get_in(1)).get_offset() as i32 != trunc_size {
                    continue;
                }
                ext_vn = data.op(sub_op).get_in(0);
            }
            if avn != ext_vn {
                continue;
            }
            data.op_set_opcode(base_op, OpCode::IntSrem, glb);
            data.op_set_input(base_op, avn, 0)?;
            let constvn = data.new_constant(data.vn(avn).get_size(), mask.wrapping_add(1), glb);
            data.op_set_input(base_op, constvn, 1)?;
            return Ok(1);
        }
        Ok(0)
    }
}

pub struct RuleSignMod2Opt {
    pub base: RuleBase,
}

impl RuleSignMod2Opt {
    pub fn new(group: &str) -> RuleSignMod2Opt {
        RuleSignMod2Opt {
            base: RuleBase::new(group, 0, "signmod2opt"),
        }
    }
}

impl Rule for RuleSignMod2Opt {
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
        Some(Box::new(RuleSignMod2Opt::new(self.get_group())))
    }

    fn get_op_list(&self, oplist: &mut Vec<OpCode>) {
        oplist.push(OpCode::IntAnd);
    }

    fn apply_op(&mut self, op: OpId, data: &mut Funcdata, glb: &mut Architecture) -> Result<i32> {
        let const_vn = data.op(op).get_in(1);
        if !data.vn(const_vn).is_constant() {
            return Ok(0);
        }
        if data.vn(const_vn).get_offset() != 1 {
            return Ok(0);
        }
        let add_out = data.op(op).get_in(0);
        let Some(add_op) = written_def(data, add_out) else {
            return Ok(0);
        };
        if data.op(add_op).code() != OpCode::IntAdd {
            return Ok(0);
        }
        let mut found: Option<(i32, OpId)> = None;
        let mut trunc = false;
        for mult_slot in 0..2 {
            let vn = data.op(add_op).get_in(mult_slot);
            let Some(mult_op) = written_def(data, vn) else { continue };
            if data.op(mult_op).code() != OpCode::IntMult {
                continue;
            }
            let const_vn = data.op(mult_op).get_in(1);
            if !data.vn(const_vn).is_constant() {
                continue;
            }
            if data.vn(const_vn).get_offset() == calc_mask(data.vn(const_vn).get_size()) {
                found = Some((mult_slot, mult_op));
                break;
            }
        }
        let Some((mult_slot, mult_op)) = found else {
            return Ok(0);
        };
        let Some(mut base) = RuleSignMod2nOpt::check_sign_extraction(data.op(mult_op).get_in(0), data) else {
            return Ok(0);
        };
        let mut other_base = data.op(add_op).get_in(1 - mult_slot);
        if base != other_base {
            if !data.vn(base).is_written() || !data.vn(other_base).is_written() {
                return Ok(0);
            }
            let mut sub_op = data.vn(base).get_def().expect("written varnode without defining op");
            if data.op(sub_op).code() != OpCode::Subpiece {
                return Ok(0);
            }
            let trunc_amt = data.vn(data.op(sub_op).get_in(1)).get_offset() as i32;
            if trunc_amt + data.vn(base).get_size() != data.vn(data.op(sub_op).get_in(0)).get_size() {
                return Ok(0);
            }
            base = data.op(sub_op).get_in(0);
            sub_op = data
                .vn(other_base)
                .get_def()
                .expect("written varnode without defining op");
            if data.op(sub_op).code() != OpCode::Subpiece {
                return Ok(0);
            }
            if data.vn(data.op(sub_op).get_in(1)).get_offset() != 0 {
                return Ok(0);
            }
            other_base = data.op(sub_op).get_in(0);
            if other_base != base {
                return Ok(0);
            }
            trunc = true;
        }
        if data.vn(base).is_free() {
            return Ok(0);
        }
        let mut and_out = data.op(op).get_out().expect("op without output");
        if trunc {
            match data.vn(and_out).lone_descend() {
                Some(ext_op) if data.op(ext_op).code() == OpCode::IntZext => {
                    and_out = data.op(ext_op).get_out().expect("op without output");
                }
                _ => return Ok(0),
            }
        }
        let root_ops = data.vn(and_out).descend().to_vec();
        for root_op in root_ops {
            if data.op(root_op).code() != OpCode::IntAdd {
                continue;
            }
            let slot = data.op(root_op).get_slot(and_out);
            let other = RuleSignMod2nOpt::check_sign_extraction(data.op(root_op).get_in(1 - slot), data);
            if other != Some(base) {
                continue;
            }
            data.op_set_opcode(root_op, OpCode::IntSrem, glb);
            data.op_set_input(root_op, base, 0)?;
            let twovn = data.new_constant(data.vn(base).get_size(), 2, glb);
            data.op_set_input(root_op, twovn, 1)?;
            return Ok(1);
        }
        Ok(0)
    }
}

pub struct RuleSignMod2nOpt2 {
    pub base: RuleBase,
}

impl RuleSignMod2nOpt2 {
    pub fn new(group: &str) -> RuleSignMod2nOpt2 {
        RuleSignMod2nOpt2 {
            base: RuleBase::new(group, 0, "signmod2nopt2"),
        }
    }

    pub fn check_multiequal_form(op: OpId, npow: u64, data: &Funcdata) -> Option<VarnodeId> {
        if data.op(op).num_input() != 2 {
            return None;
        }
        let npow = npow.wrapping_sub(1);
        let mut found: Option<(i32, VarnodeId)> = None;
        for slot in 0..data.op(op).num_input() {
            let add_out = data.op(op).get_in(slot);
            let Some(add_op) = written_def(data, add_out) else {
                continue;
            };
            if data.op(add_op).code() != OpCode::IntAdd {
                continue;
            }
            let const_vn = data.op(add_op).get_in(1);
            if !data.vn(const_vn).is_constant() {
                continue;
            }
            if data.vn(const_vn).get_offset() != npow {
                continue;
            }
            let base = data.op(add_op).get_in(0);
            let other_base = data.op(op).get_in(1 - slot);
            if other_base == base {
                found = Some((slot, base));
                break;
            }
        }
        let (slot, base) = found?;
        let bl = data.op(op).get_parent().expect("op without parent block");
        let mut inner_slot = 0;
        let mut inner = data.block(bl).get_in(inner_slot);
        if data.block(inner).size_out() != 1 || data.block(inner).size_in() != 1 {
            inner_slot = 1;
            inner = data.block(bl).get_in(inner_slot);
            if data.block(inner).size_out() != 1 || data.block(inner).size_in() != 1 {
                return None;
            }
        }
        let decision = data.block(inner).get_in(0);
        if data.block(bl).get_in(1 - inner_slot) != decision {
            return None;
        }
        let cbranch = data.block_last_op(decision)?;
        if data.op(cbranch).code() != OpCode::Cbranch {
            return None;
        }
        let bool_vn = data.op(cbranch).get_in(1);
        let less_op = written_def(data, bool_vn)?;
        if data.op(less_op).code() != OpCode::IntSless {
            return None;
        }
        if !data.vn(data.op(less_op).get_in(1)).is_constant() {
            return None;
        }
        if data.vn(data.op(less_op).get_in(1)).get_offset() != 0 {
            return None;
        }
        let neg_block = if data.op(cbranch).is_boolean_flip() {
            data.block(decision).get_false_out()
        } else {
            data.block(decision).get_true_out()
        };
        let neg_slot = if neg_block == inner { inner_slot } else { 1 - inner_slot };
        if neg_slot != slot {
            return None;
        }
        Some(base)
    }

    pub fn check_sign_ext_form(op: OpId, data: &Funcdata) -> Option<VarnodeId> {
        for slot in 0..2 {
            let minus_vn = data.op(op).get_in(slot);
            let Some(mult_op) = written_def(data, minus_vn) else {
                continue;
            };
            if data.op(mult_op).code() != OpCode::IntMult {
                continue;
            }
            let const_vn = data.op(mult_op).get_in(1);
            if !data.vn(const_vn).is_constant() {
                continue;
            }
            if data.vn(const_vn).get_offset() != calc_mask(data.vn(const_vn).get_size()) {
                continue;
            }
            let base = data.op(op).get_in(1 - slot);
            let sign_ext = data.op(mult_op).get_in(0);
            let Some(shift_op) = written_def(data, sign_ext) else {
                continue;
            };
            if data.op(shift_op).code() != OpCode::IntSright {
                continue;
            }
            if data.op(shift_op).get_in(0) != base {
                continue;
            }
            let const_vn = data.op(shift_op).get_in(1);
            if !data.vn(const_vn).is_constant() {
                continue;
            }
            if data.vn(const_vn).get_offset() as i32 != 8 * data.vn(base).get_size() - 1 {
                continue;
            }
            return Some(base);
        }
        None
    }
}

impl Rule for RuleSignMod2nOpt2 {
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
        Some(Box::new(RuleSignMod2nOpt2::new(self.get_group())))
    }

    fn get_op_list(&self, oplist: &mut Vec<OpCode>) {
        oplist.push(OpCode::IntMult);
    }

    fn apply_op(&mut self, op: OpId, data: &mut Funcdata, glb: &mut Architecture) -> Result<i32> {
        let const_vn = data.op(op).get_in(1);
        if !data.vn(const_vn).is_constant() {
            return Ok(0);
        }
        let mask = calc_mask(data.vn(const_vn).get_size());
        if data.vn(const_vn).get_offset() != mask {
            return Ok(0);
        }
        let and_out = data.op(op).get_in(0);
        let Some(and_op) = written_def(data, and_out) else {
            return Ok(0);
        };
        if data.op(and_op).code() != OpCode::IntAnd {
            return Ok(0);
        }
        let const_vn = data.op(and_op).get_in(1);
        if !data.vn(const_vn).is_constant() {
            return Ok(0);
        }
        let npow = (!data.vn(const_vn).get_offset()).wrapping_add(1) & mask;
        if popcount(npow) != 1 {
            return Ok(0);
        }
        if npow == 1 {
            return Ok(0);
        }
        let adj_vn = data.op(and_op).get_in(0);
        let Some(adj_op) = written_def(data, adj_vn) else {
            return Ok(0);
        };
        let base = if data.op(adj_op).code() == OpCode::IntAdd {
            if npow != 2 {
                return Ok(0);
            }
            RuleSignMod2nOpt2::check_sign_ext_form(adj_op, data)
        } else if data.op(adj_op).code() == OpCode::Multiequal {
            RuleSignMod2nOpt2::check_multiequal_form(adj_op, npow, data)
        } else {
            return Ok(0);
        };
        let Some(base) = base else { return Ok(0) };
        if data.vn(base).is_free() {
            return Ok(0);
        }
        let mult_out = data.op(op).get_out().expect("op without output");
        let root_ops = data.vn(mult_out).descend().to_vec();
        for root_op in root_ops {
            if data.op(root_op).code() != OpCode::IntAdd {
                continue;
            }
            let slot = data.op(root_op).get_slot(mult_out);
            if data.op(root_op).get_in(1 - slot) != base {
                continue;
            }
            if slot == 0 {
                data.op_set_input(root_op, base, 0)?;
            }
            let constvn = data.new_constant(data.vn(base).get_size(), npow, glb);
            data.op_set_input(root_op, constvn, 1)?;
            data.op_set_opcode(root_op, OpCode::IntSrem, glb);
            return Ok(1);
        }
        Ok(0)
    }
}

pub struct RuleSegment {
    pub base: RuleBase,
}

impl RuleSegment {
    pub fn new(group: &str) -> RuleSegment {
        RuleSegment {
            base: RuleBase::new(group, 0, "segment"),
        }
    }
}

impl Rule for RuleSegment {
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
        Some(Box::new(RuleSegment::new(self.get_group())))
    }

    fn get_op_list(&self, oplist: &mut Vec<OpCode>) {
        oplist.push(OpCode::Segmentop);
    }

    fn apply_op(&mut self, op: OpId, data: &mut Funcdata, glb: &mut Architecture) -> Result<i32> {
        let space_index = data
            .vn(data.op(op).get_in(0))
            .get_space_from_const(&glb.manager)
            .expect("segment operand without space")
            .get_index();
        let Some(segdef) = glb.userops.get_segment_op(space_index).cloned() else {
            return Err(Error::Lowlevel("Segment operand missing definition".to_string()));
        };
        let vn1 = data.op(op).get_in(1);
        let vn2 = data.op(op).get_in(2);
        if data.vn(vn1).is_constant() && data.vn(vn2).is_constant() {
            let bindlist = vec![data.vn(vn1).get_offset(), data.vn(vn2).get_offset()];
            let val = segdef.execute(&bindlist, glb)?;
            data.op_remove_input(op, 2);
            data.op_remove_input(op, 1);
            let outsize = data.vn(data.op(op).get_out().expect("op without output")).get_size();
            let constvn = data.new_constant(outsize, val, glb);
            data.op_set_input(op, constvn, 0)?;
            data.op_set_opcode(op, OpCode::Copy, glb);
            return Ok(1);
        }
        let far_pointer = match &segdef.kind {
            UserPcodeOpKind::Segment(segment) => segment.has_far_pointer_support(),
            _ => false,
        };
        if far_pointer {
            if !contiguous_test(data, vn1, vn2) {
                return Ok(0);
            }
            let Some(whole) = find_contiguous_whole(data, vn1, vn2) else {
                return Ok(0);
            };
            if data.vn(whole).is_free() {
                return Ok(0);
            }
            data.op_remove_input(op, 2);
            data.op_remove_input(op, 1);
            data.op_set_input(op, whole, 0)?;
            data.op_set_opcode(op, OpCode::Copy, glb);
            return Ok(1);
        }
        Ok(0)
    }
}

#[cfg(test)]
mod tests {
    use super::RuleDivOpt;

    fn divisor(shift: u32, coeff: u64, xsize: u32) -> u64 {
        let mut value = [coeff, 0];
        RuleDivOpt::calc_divisor(shift, &mut value, xsize).expect("division failed")
    }

    #[test]
    fn calc_divisor_recovers_unsigned_divisors() {
        assert_eq!(divisor(33, 0xaaaa_aaab, 32), 3);
        assert_eq!(divisor(34, 0xcccc_cccd, 32), 5);
    }

    #[test]
    fn calc_divisor_rejects_invalid_forms() {
        assert_eq!(divisor(33, 1, 32), 0);
        assert_eq!(divisor(128, 0xaaaa_aaab, 32), 0);
        assert_eq!(divisor(33, 0xaaaa_aaab, 65), 0);
        assert_eq!(divisor(33, 0xaaaa_aaab, 64), 0);
    }

    #[test]
    fn calc_divisor_decrements_coefficient_in_place() {
        let mut value = [0xaaaa_aaab, 0];
        RuleDivOpt::calc_divisor(33, &mut value, 32).expect("division failed");
        assert_eq!(value, [0xaaaa_aaaa, 0]);
    }
}
