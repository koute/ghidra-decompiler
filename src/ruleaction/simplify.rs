use crate::action::{ActionGroupList, Rule, RuleBase};
use crate::address::{Address, calc_mask, leastsigbit_set, pcode_left, pcode_right};
use crate::architecture::Architecture;
use crate::block::BlockId;
use crate::error::{Error, Result};
use crate::expression::{TermOrder, functional_equality, functional_equality_level};
use crate::funcdata::Funcdata;
use crate::op::{OpId, PcodeOp};
use crate::opcodes::OpCode;
use crate::rangeutil::CircleRange;
use crate::space::SpaceType;
use crate::varnode::VarnodeId;

pub struct RuleEarlyRemoval {
    pub base: RuleBase,
}

impl RuleEarlyRemoval {
    pub fn new(group: &str) -> RuleEarlyRemoval {
        RuleEarlyRemoval {
            base: RuleBase::new(group, 0, "earlyremoval"),
        }
    }
}

impl Rule for RuleEarlyRemoval {
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
        Some(Box::new(RuleEarlyRemoval::new(self.get_group())))
    }

    fn get_op_list(&self, oplist: &mut Vec<OpCode>) {
        oplist.extend_from_slice(&[
            OpCode::Copy,
            OpCode::Load,
            OpCode::Callother,
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
            OpCode::Multiequal,
            OpCode::Piece,
            OpCode::Subpiece,
            OpCode::Cast,
            OpCode::Ptradd,
            OpCode::Ptrsub,
            OpCode::Segmentop,
            OpCode::Cpoolref,
            OpCode::New,
            OpCode::Insert,
            OpCode::Zpull,
            OpCode::Popcount,
            OpCode::Lzcount,
            OpCode::Spull,
        ]);
    }

    fn apply_op(&mut self, op: OpId, data: &mut Funcdata, _glb: &mut Architecture) -> Result<i32> {
        if data.op(op).is_call() {
            return Ok(0);
        }
        if data.op(op).is_indirect_source() {
            return Ok(0);
        }
        let Some(vn) = data.op(op).get_out() else {
            return Ok(0);
        };
        if !data.vn(vn).has_no_descend() {
            return Ok(0);
        }
        if data.vn(vn).is_auto_live() {
            return Ok(0);
        }
        let spc = data.vn(vn).get_space().cloned().expect("varnode without address space");
        if spc.does_deadcode() && !data.dead_removal_allowed_seen(&spc) {
            return Ok(0);
        }
        data.op_destroy(op)?;
        Ok(1)
    }
}

pub struct RuleCollectTerms {
    pub base: RuleBase,
}

impl RuleCollectTerms {
    pub fn new(group: &str) -> RuleCollectTerms {
        RuleCollectTerms {
            base: RuleBase::new(group, 0, "collect_terms"),
        }
    }

    pub fn get_mult_coeff(vn: VarnodeId, coef: &mut u64, data: &Funcdata) -> VarnodeId {
        if !data.vn(vn).is_written() {
            *coef = 1;
            return vn;
        }
        let testop = data.vn(vn).get_def().expect("written varnode without defining op");
        if data.op(testop).code() != OpCode::IntMult || !data.vn(data.op(testop).get_in(1)).is_constant() {
            *coef = 1;
            return vn;
        }
        *coef = data.vn(data.op(testop).get_in(1)).get_offset();
        data.op(testop).get_in(0)
    }
}

impl Rule for RuleCollectTerms {
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
        Some(Box::new(RuleCollectTerms::new(self.get_group())))
    }

    fn get_op_list(&self, oplist: &mut Vec<OpCode>) {
        oplist.push(OpCode::IntAdd);
    }

    fn apply_op(&mut self, op: OpId, data: &mut Funcdata, glb: &mut Architecture) -> Result<i32> {
        let outvn = data.op(op).get_out().expect("op without output");
        if let Some(nextop) = data.vn(outvn).lone_descend()
            && data.op(nextop).code() == OpCode::IntAdd
        {
            return Ok(0);
        }
        let mut termorder = TermOrder::new(op);
        termorder.collect(data);
        termorder.sort_terms(data);
        let order: Vec<(VarnodeId, Option<OpId>, OpId, i32)> = termorder
            .get_sort()
            .iter()
            .map(|edge| {
                (
                    edge.get_varnode(),
                    edge.get_multiplier(),
                    edge.get_op(),
                    edge.get_slot(),
                )
            })
            .collect();
        let mut index = 0usize;
        let mut coef1: u64 = 0;
        let mut coef2: u64 = 0;
        if !data.vn(order[0].0).is_constant() {
            index = 1;
            while index < order.len() {
                let mut vn1 = order[index - 1].0;
                let mut vn2 = order[index].0;
                if data.vn(vn2).is_constant() {
                    break;
                }
                vn1 = RuleCollectTerms::get_mult_coeff(vn1, &mut coef1, data);
                vn2 = RuleCollectTerms::get_mult_coeff(vn2, &mut coef2, data);
                if vn1 == vn2 {
                    if let Some(multiplier) = order[index - 1].1 {
                        return Ok(if data.distribute_int_mult_add(multiplier, glb)? {
                            1
                        } else {
                            0
                        });
                    }
                    if let Some(multiplier) = order[index].1 {
                        return Ok(if data.distribute_int_mult_add(multiplier, glb)? {
                            1
                        } else {
                            0
                        });
                    }
                    let size = data.vn(vn1).get_size();
                    coef1 = coef1.wrapping_add(coef2) & calc_mask(size);
                    let newcoeff = data.new_constant(size, coef1, glb);
                    let zerocoeff = data.new_constant(size, 0, glb);
                    data.op_set_input(order[index - 1].2, zerocoeff, order[index - 1].3)?;
                    if coef1 == 0 {
                        data.op_set_input(order[index].2, newcoeff, order[index].3)?;
                    } else {
                        let addr = data.op(order[index].2).get_addr().clone();
                        let nextop = data.new_op(2, &addr);
                        let product = data.new_unique_out(size, nextop, glb)?;
                        data.op_set_opcode(nextop, OpCode::IntMult, glb);
                        data.op_set_input(nextop, vn1, 0)?;
                        data.op_set_input(nextop, newcoeff, 1)?;
                        data.op_insert_before(nextop, order[index].2);
                        data.op_set_input(order[index].2, product, order[index].3)?;
                    }
                    return Ok(1);
                }
                index += 1;
            }
        }
        coef1 = 0;
        let mut nonzerocount = 0;
        let mut lastconst = 0usize;
        let mut position = order.len();
        while position > index {
            position -= 1;
            if order[position].1.is_some() {
                continue;
            }
            let val = data.vn(order[position].0).get_offset();
            if val != 0 {
                nonzerocount += 1;
                coef1 = coef1.wrapping_add(val);
                lastconst = position;
            }
        }
        if nonzerocount <= 1 {
            return Ok(0);
        }
        let size = data.vn(order[lastconst].0).get_size();
        coef1 &= calc_mask(size);
        for position in lastconst + 1..order.len() {
            if order[position].1.is_none() {
                let zero = data.new_constant(size, 0, glb);
                data.op_set_input(order[position].2, zero, order[position].3)?;
            }
        }
        let sum = data.new_constant(size, coef1, glb);
        data.op_set_input(order[lastconst].2, sum, order[lastconst].3)?;
        Ok(1)
    }
}

pub struct RuleSelectCse {
    pub base: RuleBase,
}

impl RuleSelectCse {
    pub fn new(group: &str) -> RuleSelectCse {
        RuleSelectCse {
            base: RuleBase::new(group, 0, "selectcse"),
        }
    }
}

impl Rule for RuleSelectCse {
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
        Some(Box::new(RuleSelectCse::new(self.get_group())))
    }

    fn get_op_list(&self, oplist: &mut Vec<OpCode>) {
        oplist.push(OpCode::Subpiece);
        oplist.push(OpCode::IntSright);
    }

    fn apply_op(&mut self, op: OpId, data: &mut Funcdata, glb: &mut Architecture) -> Result<i32> {
        let vn = data.op(op).get_in(0);
        let opc = data.op(op).code();
        let mut list: Vec<(u32, OpId)> = Vec::new();
        let mut vlist: Vec<VarnodeId> = Vec::new();
        for &otherop in data.vn(vn).descend() {
            if data.op(otherop).code() != opc {
                continue;
            }
            let hash = data.op_get_cse_hash(otherop);
            if hash == 0 {
                continue;
            }
            list.push((hash, otherop));
        }
        if list.len() <= 1 {
            return Ok(0);
        }
        data.cse_eliminate_list(&mut list, &mut vlist, glb)?;
        if vlist.is_empty() {
            return Ok(0);
        }
        Ok(1)
    }
}

pub struct RulePiece2Zext {
    pub base: RuleBase,
}

impl RulePiece2Zext {
    pub fn new(group: &str) -> RulePiece2Zext {
        RulePiece2Zext {
            base: RuleBase::new(group, 0, "piece2zext"),
        }
    }
}

impl Rule for RulePiece2Zext {
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
        Some(Box::new(RulePiece2Zext::new(self.get_group())))
    }

    fn get_op_list(&self, oplist: &mut Vec<OpCode>) {
        oplist.push(OpCode::Piece);
    }

    fn apply_op(&mut self, op: OpId, data: &mut Funcdata, glb: &mut Architecture) -> Result<i32> {
        let constvn = data.op(op).get_in(0);
        if !data.vn(constvn).is_constant() {
            return Ok(0);
        }
        if data.vn(constvn).get_offset() != 0 {
            return Ok(0);
        }
        data.op_remove_input(op, 0);
        data.op_set_opcode(op, OpCode::IntZext, glb);
        Ok(1)
    }
}

pub struct RulePiece2Sext {
    pub base: RuleBase,
}

impl RulePiece2Sext {
    pub fn new(group: &str) -> RulePiece2Sext {
        RulePiece2Sext {
            base: RuleBase::new(group, 0, "piece2sext"),
        }
    }
}

impl Rule for RulePiece2Sext {
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
        Some(Box::new(RulePiece2Sext::new(self.get_group())))
    }

    fn get_op_list(&self, oplist: &mut Vec<OpCode>) {
        oplist.push(OpCode::Piece);
    }

    fn apply_op(&mut self, op: OpId, data: &mut Funcdata, glb: &mut Architecture) -> Result<i32> {
        let shiftout = data.op(op).get_in(0);
        if !data.vn(shiftout).is_written() {
            return Ok(0);
        }
        let shiftop = data
            .vn(shiftout)
            .get_def()
            .expect("written varnode without defining op");
        if data.op(shiftop).code() != OpCode::IntSright {
            return Ok(0);
        }
        if !data.vn(data.op(shiftop).get_in(1)).is_constant() {
            return Ok(0);
        }
        let amount = data.vn(data.op(shiftop).get_in(1)).get_offset() as i32;
        let base = data.op(shiftop).get_in(0);
        if base != data.op(op).get_in(1) {
            return Ok(0);
        }
        if amount != 8 * data.vn(base).get_size() - 1 {
            return Ok(0);
        }
        data.op_remove_input(op, 0);
        data.op_set_opcode(op, OpCode::IntSext, glb);
        Ok(1)
    }
}

pub struct RuleBxor2NotEqual {
    pub base: RuleBase,
}

impl RuleBxor2NotEqual {
    pub fn new(group: &str) -> RuleBxor2NotEqual {
        RuleBxor2NotEqual {
            base: RuleBase::new(group, 0, "bxor2notequal"),
        }
    }
}

impl Rule for RuleBxor2NotEqual {
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
        Some(Box::new(RuleBxor2NotEqual::new(self.get_group())))
    }

    fn get_op_list(&self, oplist: &mut Vec<OpCode>) {
        oplist.push(OpCode::BoolXor);
    }

    fn apply_op(&mut self, op: OpId, data: &mut Funcdata, glb: &mut Architecture) -> Result<i32> {
        data.op_set_opcode(op, OpCode::IntNotequal, glb);
        Ok(1)
    }
}

pub struct RuleOrMask {
    pub base: RuleBase,
}

impl RuleOrMask {
    pub fn new(group: &str) -> RuleOrMask {
        RuleOrMask {
            base: RuleBase::new(group, 0, "ormask"),
        }
    }
}

impl Rule for RuleOrMask {
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
        Some(Box::new(RuleOrMask::new(self.get_group())))
    }

    fn get_op_list(&self, oplist: &mut Vec<OpCode>) {
        oplist.push(OpCode::IntOr);
    }

    fn apply_op(&mut self, op: OpId, data: &mut Funcdata, glb: &mut Architecture) -> Result<i32> {
        let size = data.vn(data.op(op).get_out().expect("op without output")).get_size();
        if size > 8 {
            return Ok(0);
        }
        let constvn = data.op(op).get_in(1);
        if !data.vn(constvn).is_constant() {
            return Ok(0);
        }
        let val = data.vn(constvn).get_offset();
        let mask = calc_mask(size);
        if (val & mask) != mask {
            return Ok(0);
        }
        data.op_set_opcode(op, OpCode::Copy, glb);
        data.op_set_input(op, constvn, 0)?;
        data.op_remove_input(op, 1);
        Ok(1)
    }
}

pub struct RuleAndMask {
    pub base: RuleBase,
}

impl RuleAndMask {
    pub fn new(group: &str) -> RuleAndMask {
        RuleAndMask {
            base: RuleBase::new(group, 0, "andmask"),
        }
    }
}

impl Rule for RuleAndMask {
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
        Some(Box::new(RuleAndMask::new(self.get_group())))
    }

    fn get_op_list(&self, oplist: &mut Vec<OpCode>) {
        oplist.push(OpCode::IntAnd);
    }

    fn apply_op(&mut self, op: OpId, data: &mut Funcdata, glb: &mut Architecture) -> Result<i32> {
        let outvn = data.op(op).get_out().expect("op without output");
        let size = data.vn(outvn).get_size();
        if size > 8 {
            return Ok(0);
        }
        let mask1 = data.vn(data.op(op).get_in(0)).get_nz_mask();
        let andmask = if mask1 == 0 {
            0
        } else {
            mask1 & data.vn(data.op(op).get_in(1)).get_nz_mask()
        };
        let vn = if andmask == 0 || (andmask & data.vn(outvn).get_consume()) == 0 {
            data.new_constant(size, 0, glb)
        } else if andmask == mask1 {
            if !data.vn(data.op(op).get_in(1)).is_constant() {
                return Ok(0);
            }
            data.op(op).get_in(0)
        } else {
            return Ok(0);
        };
        if !data.vn(vn).is_heritage_known() {
            return Ok(0);
        }
        data.op_set_opcode(op, OpCode::Copy, glb);
        data.op_remove_input(op, 1);
        data.op_set_input(op, vn, 0)?;
        Ok(1)
    }
}

pub struct RuleOrConsume {
    pub base: RuleBase,
}

impl RuleOrConsume {
    pub fn new(group: &str) -> RuleOrConsume {
        RuleOrConsume {
            base: RuleBase::new(group, 0, "orconsume"),
        }
    }
}

impl Rule for RuleOrConsume {
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
        Some(Box::new(RuleOrConsume::new(self.get_group())))
    }

    fn get_op_list(&self, oplist: &mut Vec<OpCode>) {
        oplist.push(OpCode::IntOr);
        oplist.push(OpCode::IntXor);
    }

    fn apply_op(&mut self, op: OpId, data: &mut Funcdata, glb: &mut Architecture) -> Result<i32> {
        let outvn = data.op(op).get_out().expect("op without output");
        let size = data.vn(outvn).get_size();
        if size > 8 {
            return Ok(0);
        }
        let consume = data.vn(outvn).get_consume();
        if (consume & data.vn(data.op(op).get_in(0)).get_nz_mask()) == 0 {
            data.op_remove_input(op, 0);
            data.op_set_opcode(op, OpCode::Copy, glb);
            return Ok(1);
        } else if (consume & data.vn(data.op(op).get_in(1)).get_nz_mask()) == 0 {
            data.op_remove_input(op, 1);
            data.op_set_opcode(op, OpCode::Copy, glb);
            return Ok(1);
        }
        Ok(0)
    }
}

pub struct RuleOrCollapse {
    pub base: RuleBase,
}

impl RuleOrCollapse {
    pub fn new(group: &str) -> RuleOrCollapse {
        RuleOrCollapse {
            base: RuleBase::new(group, 0, "orcollapse"),
        }
    }
}

impl Rule for RuleOrCollapse {
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
        Some(Box::new(RuleOrCollapse::new(self.get_group())))
    }

    fn get_op_list(&self, oplist: &mut Vec<OpCode>) {
        oplist.push(OpCode::IntOr);
    }

    fn apply_op(&mut self, op: OpId, data: &mut Funcdata, glb: &mut Architecture) -> Result<i32> {
        let size = data.vn(data.op(op).get_out().expect("op without output")).get_size();
        let vn = data.op(op).get_in(1);
        if !data.vn(vn).is_constant() {
            return Ok(0);
        }
        if size > 8 {
            return Ok(0);
        }
        let mask = data.vn(data.op(op).get_in(0)).get_nz_mask();
        let val = data.vn(vn).get_offset();
        if (mask | val) != val {
            return Ok(0);
        }
        data.op_set_opcode(op, OpCode::Copy, glb);
        data.op_remove_input(op, 0);
        Ok(1)
    }
}

pub struct RuleAndOrLump {
    pub base: RuleBase,
}

impl RuleAndOrLump {
    pub fn new(group: &str) -> RuleAndOrLump {
        RuleAndOrLump {
            base: RuleBase::new(group, 0, "andorlump"),
        }
    }
}

impl Rule for RuleAndOrLump {
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
        Some(Box::new(RuleAndOrLump::new(self.get_group())))
    }

    fn get_op_list(&self, oplist: &mut Vec<OpCode>) {
        oplist.push(OpCode::IntAnd);
        oplist.push(OpCode::IntOr);
        oplist.push(OpCode::IntXor);
    }

    fn apply_op(&mut self, op: OpId, data: &mut Funcdata, glb: &mut Architecture) -> Result<i32> {
        let opc = data.op(op).code();
        if !data.vn(data.op(op).get_in(1)).is_constant() {
            return Ok(0);
        }
        let vn1 = data.op(op).get_in(0);
        if !data.vn(vn1).is_written() {
            return Ok(0);
        }
        let op2 = data.vn(vn1).get_def().expect("written varnode without defining op");
        if data.op(op2).code() != opc {
            return Ok(0);
        }
        if !data.vn(data.op(op2).get_in(1)).is_constant() {
            return Ok(0);
        }
        let basevn = data.op(op2).get_in(0);
        if data.vn(basevn).is_free() {
            return Ok(0);
        }
        let mut val = data.vn(data.op(op).get_in(1)).get_offset();
        let val2 = data.vn(data.op(op2).get_in(1)).get_offset();
        if opc == OpCode::IntAnd {
            val &= val2;
        } else if opc == OpCode::IntOr {
            val |= val2;
        } else if opc == OpCode::IntXor {
            val ^= val2;
        }
        data.op_set_input(op, basevn, 0)?;
        let size = data.vn(basevn).get_size();
        let newconst = data.new_constant(size, val, glb);
        data.op_set_input(op, newconst, 1)?;
        Ok(1)
    }
}

pub struct RuleNegateIdentity {
    pub base: RuleBase,
}

impl RuleNegateIdentity {
    pub fn new(group: &str) -> RuleNegateIdentity {
        RuleNegateIdentity {
            base: RuleBase::new(group, 0, "negateidentity"),
        }
    }
}

impl Rule for RuleNegateIdentity {
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
        Some(Box::new(RuleNegateIdentity::new(self.get_group())))
    }

    fn get_op_list(&self, oplist: &mut Vec<OpCode>) {
        oplist.push(OpCode::IntNegate);
    }

    fn apply_op(&mut self, op: OpId, data: &mut Funcdata, glb: &mut Architecture) -> Result<i32> {
        let vn = data.op(op).get_in(0);
        let out_vn = data.op(op).get_out().expect("op without output");
        let descendants: Vec<OpId> = data.vn(out_vn).descend().to_vec();
        for logic_op in descendants {
            let opc = data.op(logic_op).code();
            if opc != OpCode::IntAnd && opc != OpCode::IntOr && opc != OpCode::IntXor {
                continue;
            }
            let slot = data.op(logic_op).get_slot(out_vn);
            if data.op(logic_op).get_in(1 - slot) != vn {
                continue;
            }
            let mut value: u64 = 0;
            if opc != OpCode::IntAnd {
                value = calc_mask(data.vn(vn).get_size());
            }
            let size = data.vn(vn).get_size();
            let newconst = data.new_constant(size, value, glb);
            data.op_set_input(logic_op, newconst, 0)?;
            data.op_remove_input(logic_op, 1);
            data.op_set_opcode(logic_op, OpCode::Copy, glb);
            return Ok(1);
        }
        Ok(0)
    }
}

pub struct RuleShiftBitops {
    pub base: RuleBase,
}

impl RuleShiftBitops {
    pub fn new(group: &str) -> RuleShiftBitops {
        RuleShiftBitops {
            base: RuleBase::new(group, 0, "shiftbitops"),
        }
    }
}

impl Rule for RuleShiftBitops {
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
        Some(Box::new(RuleShiftBitops::new(self.get_group())))
    }

    fn get_op_list(&self, oplist: &mut Vec<OpCode>) {
        oplist.push(OpCode::IntLeft);
        oplist.push(OpCode::IntRight);
        oplist.push(OpCode::Subpiece);
        oplist.push(OpCode::IntMult);
    }

    fn apply_op(&mut self, op: OpId, data: &mut Funcdata, glb: &mut Architecture) -> Result<i32> {
        let constvn = data.op(op).get_in(1);
        if !data.vn(constvn).is_constant() {
            return Ok(0);
        }
        let mut vn = data.op(op).get_in(0);
        if !data.vn(vn).is_written() {
            return Ok(0);
        }
        if data.vn(vn).get_size() > 8 {
            return Ok(0);
        }
        let constval = data.vn(constvn).get_offset();
        let (shift_amount, leftshift) = match data.op(op).code() {
            OpCode::IntLeft => (constval as i32, true),
            OpCode::IntRight => (constval as i32, false),
            OpCode::Subpiece => ((constval as i32).wrapping_mul(8), false),
            OpCode::IntMult => {
                let amount = leastsigbit_set(constval);
                if amount == -1 {
                    return Ok(0);
                }
                (amount, true)
            }
            _ => return Ok(0),
        };
        let bitop = data.vn(vn).get_def().expect("written varnode without defining op");
        match data.op(bitop).code() {
            OpCode::IntAnd | OpCode::IntOr | OpCode::IntXor => {}
            OpCode::IntMult | OpCode::IntAdd => {
                if !leftshift {
                    return Ok(0);
                }
            }
            _ => return Ok(0),
        }
        let num_input = data.op(bitop).num_input();
        let mut slot = 0;
        while slot < num_input {
            let mut nzm = data.vn(data.op(bitop).get_in(slot)).get_nz_mask();
            let mask = calc_mask(data.vn(data.op(op).get_out().expect("op without output")).get_size());
            if leftshift {
                nzm = pcode_left(nzm, shift_amount);
            } else {
                nzm = pcode_right(nzm, shift_amount);
            }
            if (nzm & mask) == 0 {
                break;
            }
            slot += 1;
        }
        if slot == num_input {
            return Ok(0);
        }
        match data.op(bitop).code() {
            OpCode::IntMult | OpCode::IntAnd => {
                let size = data.vn(vn).get_size();
                vn = data.new_constant(size, 0, glb);
                data.op_set_input(op, vn, 0)?;
            }
            OpCode::IntAdd | OpCode::IntXor | OpCode::IntOr => {
                vn = data.op(bitop).get_in(1 - slot);
                if !data.vn(vn).is_heritage_known() {
                    return Ok(0);
                }
                data.op_set_input(op, vn, 0)?;
            }
            _ => {}
        }
        Ok(1)
    }
}

pub struct RuleRightShiftAnd {
    pub base: RuleBase,
}

impl RuleRightShiftAnd {
    pub fn new(group: &str) -> RuleRightShiftAnd {
        RuleRightShiftAnd {
            base: RuleBase::new(group, 0, "rightshiftand"),
        }
    }
}

impl Rule for RuleRightShiftAnd {
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
        Some(Box::new(RuleRightShiftAnd::new(self.get_group())))
    }

    fn get_op_list(&self, oplist: &mut Vec<OpCode>) {
        oplist.push(OpCode::IntRight);
        oplist.push(OpCode::IntSright);
    }

    fn apply_op(&mut self, op: OpId, data: &mut Funcdata, _glb: &mut Architecture) -> Result<i32> {
        let const_vn = data.op(op).get_in(1);
        if !data.vn(const_vn).is_constant() {
            return Ok(0);
        }
        let in_vn = data.op(op).get_in(0);
        if !data.vn(in_vn).is_written() {
            return Ok(0);
        }
        let and_op = data.vn(in_vn).get_def().expect("written varnode without defining op");
        if data.op(and_op).code() != OpCode::IntAnd {
            return Ok(0);
        }
        let mask_vn = data.op(and_op).get_in(1);
        if !data.vn(mask_vn).is_constant() {
            return Ok(0);
        }
        let shift_amount = data.vn(const_vn).get_offset() as i32;
        let mask = data.vn(mask_vn).get_offset().wrapping_shr(shift_amount as u32);
        let root_vn = data.op(and_op).get_in(0);
        let full = calc_mask(data.vn(root_vn).get_size()).wrapping_shr(shift_amount as u32);
        if full != mask {
            return Ok(0);
        }
        if data.vn(root_vn).is_free() {
            return Ok(0);
        }
        data.op_set_input(op, root_vn, 0)?;
        Ok(1)
    }
}

pub struct RuleIntLessEqual {
    pub base: RuleBase,
}

impl RuleIntLessEqual {
    pub fn new(group: &str) -> RuleIntLessEqual {
        RuleIntLessEqual {
            base: RuleBase::new(group, 0, "intlessequal"),
        }
    }
}

impl Rule for RuleIntLessEqual {
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
        Some(Box::new(RuleIntLessEqual::new(self.get_group())))
    }

    fn get_op_list(&self, oplist: &mut Vec<OpCode>) {
        oplist.push(OpCode::IntLessequal);
        oplist.push(OpCode::IntSlessequal);
    }

    fn apply_op(&mut self, op: OpId, data: &mut Funcdata, glb: &mut Architecture) -> Result<i32> {
        if data.replace_lessequal(op, glb)? {
            return Ok(1);
        }
        Ok(0)
    }
}

pub struct RuleEquality {
    pub base: RuleBase,
}

impl RuleEquality {
    pub fn new(group: &str) -> RuleEquality {
        RuleEquality {
            base: RuleBase::new(group, 0, "equality"),
        }
    }
}

impl Rule for RuleEquality {
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
        Some(Box::new(RuleEquality::new(self.get_group())))
    }

    fn get_op_list(&self, oplist: &mut Vec<OpCode>) {
        oplist.push(OpCode::IntEqual);
        oplist.push(OpCode::IntNotequal);
    }

    fn apply_op(&mut self, op: OpId, data: &mut Funcdata, glb: &mut Architecture) -> Result<i32> {
        if !functional_equality(data.op(op).get_in(0), data.op(op).get_in(1), data) {
            return Ok(0);
        }
        data.op_set_opcode(op, OpCode::Copy, glb);
        data.op_remove_input(op, 1);
        let value = if data.op(op).code() == OpCode::IntEqual { 1 } else { 0 };
        let vn = data.new_constant(1, value, glb);
        data.op_set_input(op, vn, 0)?;
        Ok(1)
    }
}

pub struct RuleTermOrder {
    pub base: RuleBase,
}

impl RuleTermOrder {
    pub fn new(group: &str) -> RuleTermOrder {
        RuleTermOrder {
            base: RuleBase::new(group, 0, "termorder"),
        }
    }
}

impl Rule for RuleTermOrder {
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
        Some(Box::new(RuleTermOrder::new(self.get_group())))
    }

    fn get_op_list(&self, oplist: &mut Vec<OpCode>) {
        oplist.extend_from_slice(&[
            OpCode::IntEqual,
            OpCode::IntNotequal,
            OpCode::IntAdd,
            OpCode::IntCarry,
            OpCode::IntScarry,
            OpCode::IntXor,
            OpCode::IntAnd,
            OpCode::IntOr,
            OpCode::IntMult,
            OpCode::BoolXor,
            OpCode::BoolAnd,
            OpCode::BoolOr,
            OpCode::FloatEqual,
            OpCode::FloatNotequal,
            OpCode::FloatAdd,
            OpCode::FloatMult,
        ]);
    }

    fn apply_op(&mut self, op: OpId, data: &mut Funcdata, _glb: &mut Architecture) -> Result<i32> {
        let vn1 = data.op(op).get_in(0);
        let vn2 = data.op(op).get_in(1);
        if data.vn(vn1).is_constant() && !data.vn(vn2).is_constant() {
            data.op_swap_input(op, 0, 1);
            return Ok(1);
        }
        Ok(0)
    }
}

pub struct RulePullsubMulti {
    pub base: RuleBase,
}

impl RulePullsubMulti {
    pub fn new(group: &str) -> RulePullsubMulti {
        RulePullsubMulti {
            base: RuleBase::new(group, 0, "pullsub_multi"),
        }
    }

    pub fn min_max_use(vn: VarnodeId, max_byte: &mut i32, min_byte: &mut i32, data: &Funcdata) {
        let in_size = data.vn(vn).get_size();
        *max_byte = -1;
        *min_byte = in_size;
        for &op in data.vn(vn).descend() {
            let opc = data.op(op).code();
            if opc == OpCode::Subpiece {
                let min = data.vn(data.op(op).get_in(1)).get_offset() as i32;
                let max = min + data.vn(data.op(op).get_out().expect("op without output")).get_size() - 1;
                if min < *min_byte {
                    *min_byte = min;
                }
                if max > *max_byte {
                    *max_byte = max;
                }
            } else {
                *max_byte = in_size - 1;
                *min_byte = 0;
                return;
            }
        }
    }

    pub fn replace_descendants(
        orig_vn: VarnodeId,
        new_vn: VarnodeId,
        _max_byte: i32,
        min_byte: i32,
        data: &mut Funcdata,
        glb: &mut Architecture,
    ) -> Result<()> {
        let descendants: Vec<OpId> = data.vn(orig_vn).descend().to_vec();
        for op in descendants {
            if data.op(op).code() == OpCode::Subpiece {
                let trunc_amount = data.vn(data.op(op).get_in(1)).get_offset() as i32;
                let out_size = data.vn(data.op(op).get_out().expect("op without output")).get_size();
                data.op_set_input(op, new_vn, 0)?;
                let new_size = data.vn(new_vn).get_size();
                if new_size == out_size {
                    if trunc_amount != min_byte {
                        return Err(Error::Lowlevel("Could not perform -replaceDescendants-".to_string()));
                    }
                    data.op_set_opcode(op, OpCode::Copy, glb);
                    data.op_remove_input(op, 1);
                } else if new_size > out_size {
                    let new_trunc = trunc_amount - min_byte;
                    if new_trunc < 0 {
                        return Err(Error::Lowlevel("Could not perform -replaceDescendants-".to_string()));
                    }
                    if new_trunc != trunc_amount {
                        let newconst = data.new_constant(4, new_trunc as u64, glb);
                        data.op_set_input(op, newconst, 1)?;
                    }
                } else {
                    return Err(Error::Lowlevel("Could not perform -replaceDescendants-".to_string()));
                }
            } else {
                return Err(Error::Lowlevel("Could not perform -replaceDescendants-".to_string()));
            }
        }
        Ok(())
    }

    pub fn acceptable_size(size: i32) -> bool {
        if size == 0 {
            return false;
        }
        if size >= 8 {
            return true;
        }
        size == 1 || size == 2 || size == 4 || size == 8
    }

    pub fn build_subpiece(
        basevn: VarnodeId,
        outsize: u32,
        shift: u32,
        data: &mut Funcdata,
        glb: &mut Architecture,
    ) -> Result<VarnodeId> {
        let newaddr = if data.vn(basevn).is_input() {
            let bb = data.block(data.get_basic_blocks()).get_block(0);
            data.block(bb).get_start()
        } else {
            if !data.vn(basevn).is_written() {
                return Err(Error::Lowlevel("Undefined pullsub".to_string()));
            }
            let def = data.vn(basevn).get_def().expect("written varnode without defining op");
            data.op(def).get_addr().clone()
        };
        let mut smalladdr1 = Address::invalid();
        let mut usetmp = false;
        let base_addr = data.vn(basevn).get_addr().clone();
        if base_addr.is_join() {
            usetmp = true;
            let joinrec = glb.manager.find_join(data.vn(basevn).get_offset())?;
            if joinrec.num_pieces() > 1 {
                let mut skipleft = shift;
                let mut index = joinrec.num_pieces() - 1;
                while index >= 0 {
                    let vdata = joinrec.get_piece(index);
                    if skipleft >= vdata.size {
                        skipleft -= vdata.size;
                    } else {
                        if skipleft.wrapping_add(outsize) > vdata.size {
                            break;
                        }
                        let piece_space = vdata.space.as_ref().expect("join piece without address space");
                        if piece_space.is_big_endian() {
                            smalladdr1 = vdata
                                .get_addr()
                                .add(vdata.size.wrapping_sub(outsize.wrapping_add(skipleft)) as i64);
                        } else {
                            smalladdr1 = vdata.get_addr().add(skipleft as i64);
                        }
                        usetmp = false;
                        break;
                    }
                    index -= 1;
                }
            }
        } else {
            let big_endian = data
                .vn(basevn)
                .get_space()
                .expect("varnode without address space")
                .is_big_endian();
            if !big_endian {
                smalladdr1 = base_addr.add(shift as i64);
            } else {
                let size = data.vn(basevn).get_size() as u32;
                smalladdr1 = base_addr.add(size.wrapping_sub(shift.wrapping_add(outsize)) as i64);
            }
        }
        let new_op = data.new_op(2, &newaddr);
        data.op_set_opcode(new_op, OpCode::Subpiece, glb);
        let outvn = if usetmp {
            data.new_unique_out(outsize as i32, new_op, glb)?
        } else {
            smalladdr1.renormalize(outsize as i32)?;
            data.new_varnode_out(outsize as i32, &smalladdr1, new_op, glb)?
        };
        data.op_set_input(new_op, basevn, 0)?;
        let shiftvn = data.new_constant(4, shift as u64, glb);
        data.op_set_input(new_op, shiftvn, 1)?;
        if data.vn(basevn).is_input() {
            let bb = data.block(data.get_basic_blocks()).get_block(0);
            data.op_insert_begin(new_op, bb);
        } else {
            let def = data.vn(basevn).get_def().expect("written varnode without defining op");
            data.op_insert_after(new_op, def);
        }
        Ok(outvn)
    }

    pub fn find_subpiece(basevn: VarnodeId, outsize: u32, shift: u32, data: &Funcdata) -> Option<VarnodeId> {
        for &prevop in data.vn(basevn).descend() {
            if data.op(prevop).code() != OpCode::Subpiece {
                continue;
            }
            let prev_parent = data.op(prevop).get_parent();
            if data.vn(basevn).is_input() {
                let parent = prev_parent.expect("op without parent block");
                if data.block(parent).get_index() != 0 {
                    continue;
                }
            }
            if !data.vn(basevn).is_written() {
                continue;
            }
            let def = data.vn(basevn).get_def().expect("written varnode without defining op");
            if data.op(def).get_parent() != prev_parent {
                continue;
            }
            let prev_out = data.op(prevop).get_out().expect("op without output");
            if data.op(prevop).get_in(0) == basevn
                && data.vn(prev_out).get_size() as u32 == outsize
                && data.vn(data.op(prevop).get_in(1)).get_offset() == shift as u64
            {
                return Some(prev_out);
            }
        }
        None
    }
}

impl Rule for RulePullsubMulti {
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
        Some(Box::new(RulePullsubMulti::new(self.get_group())))
    }

    fn get_op_list(&self, oplist: &mut Vec<OpCode>) {
        oplist.push(OpCode::Subpiece);
    }

    fn apply_op(&mut self, op: OpId, data: &mut Funcdata, glb: &mut Architecture) -> Result<i32> {
        let vn = data.op(op).get_in(0);
        if !data.vn(vn).is_written() {
            return Ok(0);
        }
        let mult = data.vn(vn).get_def().expect("written varnode without defining op");
        if data.op(mult).code() != OpCode::Multiequal {
            return Ok(0);
        }
        let mult_parent = data.op(mult).get_parent().expect("op without parent block");
        if data.block(mult_parent).has_loop_in() {
            return Ok(0);
        }
        let mut max_byte = 0;
        let mut min_byte = 0;
        RulePullsubMulti::min_max_use(vn, &mut max_byte, &mut min_byte, data);
        let new_size = max_byte - min_byte + 1;
        if max_byte < min_byte || new_size >= data.vn(vn).get_size() {
            return Ok(0);
        }
        if !RulePullsubMulti::acceptable_size(new_size) {
            return Ok(0);
        }
        let outvn = data.op(op).get_out().expect("op without output");
        if data.vn(outvn).is_precis_lo() || data.vn(outvn).is_precis_hi() {
            return Ok(0);
        }
        if min_byte > 8 {
            return Ok(0);
        }
        let mut consume: u64 = if min_byte < 8 {
            calc_mask(new_size).wrapping_shl((8 * min_byte) as u32)
        } else {
            0
        };
        consume = !consume;
        let branches = data.op(mult).num_input();
        for slot in 0..branches {
            let in_vn = data.op(mult).get_in(slot);
            if (consume & data.vn(in_vn).get_consume()) != 0 {
                if min_byte == 0 && data.vn(in_vn).is_written() {
                    let def_op = data.vn(in_vn).get_def().expect("written varnode without defining op");
                    let opc = data.op(def_op).code();
                    if (opc == OpCode::IntZext || opc == OpCode::IntSext)
                        && new_size == data.vn(data.op(def_op).get_in(0)).get_size()
                    {
                        continue;
                    }
                }
                return Ok(0);
            }
        }
        let vn_addr = data.vn(vn).get_addr().clone();
        let mut smalladdr2 = if !data
            .vn(vn)
            .get_space()
            .expect("varnode without address space")
            .is_big_endian()
        {
            vn_addr.add(min_byte as i64)
        } else {
            vn_addr.add((data.vn(vn).get_size() - max_byte - 1) as i64)
        };
        let mut params: Vec<VarnodeId> = Vec::new();
        for slot in 0..branches {
            let vn_piece = data.op(mult).get_in(slot);
            let vn_sub = match RulePullsubMulti::find_subpiece(vn_piece, new_size as u32, min_byte as u32, data) {
                Some(found) => found,
                None => RulePullsubMulti::build_subpiece(vn_piece, new_size as u32, min_byte as u32, data, glb)?,
            };
            params.push(vn_sub);
        }
        let mult_addr = data.op(mult).get_addr().clone();
        let new_multi = data.new_op(params.len() as i32, &mult_addr);
        smalladdr2.renormalize(new_size)?;
        let new_vn = data.new_varnode_out(new_size, &smalladdr2, new_multi, glb)?;
        data.op_set_opcode(new_multi, OpCode::Multiequal, glb);
        data.op_set_all_input(new_multi, &params)?;
        data.op_insert_begin(new_multi, mult_parent);
        RulePullsubMulti::replace_descendants(vn, new_vn, max_byte, min_byte, data, glb)?;
        Ok(1)
    }
}

pub struct RulePullsubIndirect {
    pub base: RuleBase,
}

impl RulePullsubIndirect {
    pub fn new(group: &str) -> RulePullsubIndirect {
        RulePullsubIndirect {
            base: RuleBase::new(group, 0, "pullsub_indirect"),
        }
    }
}

impl Rule for RulePullsubIndirect {
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
        Some(Box::new(RulePullsubIndirect::new(self.get_group())))
    }

    fn get_op_list(&self, oplist: &mut Vec<OpCode>) {
        oplist.push(OpCode::Subpiece);
    }

    fn apply_op(&mut self, op: OpId, data: &mut Funcdata, glb: &mut Architecture) -> Result<i32> {
        let vn = data.op(op).get_in(0);
        if !data.vn(vn).is_written() {
            return Ok(0);
        }
        if data.vn(vn).get_size() > 8 {
            return Ok(0);
        }
        let indir = data.vn(vn).get_def().expect("written varnode without defining op");
        if data.op(indir).code() != OpCode::Indirect {
            return Ok(0);
        }
        let iop_vn = data.op(indir).get_in(1);
        if data
            .vn(iop_vn)
            .get_space()
            .expect("varnode without address space")
            .get_type()
            != SpaceType::Iop
        {
            return Ok(0);
        }
        let targ_op = PcodeOp::get_op_from_const(data.vn(iop_vn).get_addr());
        if data.op(targ_op).is_dead() {
            return Ok(0);
        }
        if data.vn(vn).is_addr_force() {
            return Ok(0);
        }
        let mut max_byte = 0;
        let mut min_byte = 0;
        RulePullsubMulti::min_max_use(vn, &mut max_byte, &mut min_byte, data);
        let new_size = max_byte - min_byte + 1;
        if max_byte < min_byte || new_size >= data.vn(vn).get_size() {
            return Ok(0);
        }
        if !RulePullsubMulti::acceptable_size(new_size) {
            return Ok(0);
        }
        let outvn = data.op(op).get_out().expect("op without output");
        if data.vn(outvn).is_precis_lo() || data.vn(outvn).is_precis_hi() {
            return Ok(0);
        }
        let mut consume = calc_mask(new_size).wrapping_shl((8 * min_byte) as u32);
        consume = !consume;
        if (consume & data.vn(data.op(indir).get_in(0)).get_consume()) != 0 {
            return Ok(0);
        }
        let vn_addr = data.vn(vn).get_addr().clone();
        let smalladdr2 = if !data
            .vn(vn)
            .get_space()
            .expect("varnode without address space")
            .is_big_endian()
        {
            vn_addr.add(min_byte as i64)
        } else {
            vn_addr.add((data.vn(vn).get_size() - max_byte - 1) as i64)
        };
        let small2 = if data.op(indir).is_indirect_creation() {
            let possibleout = !data.vn(data.op(indir).get_in(0)).is_indirect_zero();
            let new_ind = data.new_indirect_creation(targ_op, &smalladdr2, new_size, possibleout, glb)?;
            data.op(new_ind).get_out().expect("op without output")
        } else {
            let basevn = data.op(indir).get_in(0);
            let shift = data.vn(data.op(op).get_in(1)).get_offset() as u32;
            let small1 = match RulePullsubMulti::find_subpiece(basevn, new_size as u32, shift, data) {
                Some(found) => found,
                None => RulePullsubMulti::build_subpiece(basevn, new_size as u32, shift, data, glb)?,
            };
            let new_ind = data.new_indirect(targ_op, glb)?;
            let small2 = data.new_varnode_out(new_size, &smalladdr2, new_ind, glb)?;
            data.op_set_input(new_ind, small1, 0)?;
            data.op_insert_before(new_ind, indir);
            small2
        };
        RulePullsubMulti::replace_descendants(vn, small2, max_byte, min_byte, data, glb)?;
        Ok(1)
    }
}

pub struct RulePushMulti {
    pub base: RuleBase,
}

impl RulePushMulti {
    pub fn new(group: &str) -> RulePushMulti {
        RulePushMulti {
            base: RuleBase::new(group, 0, "push_multi"),
        }
    }

    pub fn find_substitute(
        in1: VarnodeId,
        in2: VarnodeId,
        bb: BlockId,
        earliest: Option<OpId>,
        data: &Funcdata,
    ) -> Option<OpId> {
        for &op in data.vn(in1).descend() {
            if data.op(op).get_parent() != Some(bb) {
                continue;
            }
            if data.op(op).code() != OpCode::Multiequal {
                continue;
            }
            if data.op(op).get_in(0) != in1 {
                continue;
            }
            if data.op(op).get_in(1) != in2 {
                continue;
            }
            return Some(op);
        }
        if in1 == in2 {
            return None;
        }
        let mut buf1: [Option<VarnodeId>; 2] = [None, None];
        let mut buf2: [Option<VarnodeId>; 2] = [None, None];
        if 0 != functional_equality_level(in1, in2, &mut buf1, &mut buf2, data) {
            return None;
        }
        let op1 = data.vn(in1).get_def().expect("written varnode without defining op");
        let op2 = data.vn(in2).get_def().expect("written varnode without defining op");
        for slot in 0..data.op(op1).num_input() {
            let vn = data.op(op1).get_in(slot);
            if data.vn(vn).is_constant() {
                continue;
            }
            if vn == data.op(op2).get_in(slot) {
                return data.cse_find_in_block(op1, vn, bb, earliest);
            }
        }
        None
    }
}

impl Rule for RulePushMulti {
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
        Some(Box::new(RulePushMulti::new(self.get_group())))
    }

    fn get_op_list(&self, oplist: &mut Vec<OpCode>) {
        oplist.push(OpCode::Multiequal);
    }

    fn apply_op(&mut self, op: OpId, data: &mut Funcdata, glb: &mut Architecture) -> Result<i32> {
        if data.op(op).num_input() != 2 {
            return Ok(0);
        }
        let in1 = data.op(op).get_in(0);
        let in2 = data.op(op).get_in(1);
        if !data.vn(in1).is_written() {
            return Ok(0);
        }
        if !data.vn(in2).is_written() {
            return Ok(0);
        }
        if data.vn(in1).is_spacebase() {
            return Ok(0);
        }
        if data.vn(in2).is_spacebase() {
            return Ok(0);
        }
        let mut buf1: [Option<VarnodeId>; 2] = [None, None];
        let mut buf2: [Option<VarnodeId>; 2] = [None, None];
        let res = functional_equality_level(in1, in2, &mut buf1, &mut buf2, data);
        if res < 0 {
            return Ok(0);
        }
        if res > 1 {
            return Ok(0);
        }
        let op1 = data.vn(in1).get_def().expect("written varnode without defining op");
        if data.op(op1).code() == OpCode::Subpiece {
            return Ok(0);
        }
        let bl = data.op(op).get_parent().expect("op without parent block");
        let outvn = data.op(op).get_out().expect("op without output");
        let earliest = data.block_earliest_use(bl, outvn);
        if data.op(op1).code() == OpCode::Copy {
            if res == 0 {
                return Ok(0);
            }
            let first = buf1[0].expect("missing functional equality term");
            let second = buf2[0].expect("missing functional equality term");
            let Some(substitute) = RulePushMulti::find_substitute(first, second, bl, earliest, data) else {
                return Ok(0);
            };
            let subout = data.op(substitute).get_out().expect("op without output");
            data.total_replace(outvn, subout)?;
            data.op_destroy(op)?;
            return Ok(1);
        }
        let op2 = data.vn(in2).get_def().expect("written varnode without defining op");
        if data.vn(in1).lone_descend() != Some(op) {
            return Ok(0);
        }
        if data.vn(in2).lone_descend() != Some(op) {
            return Ok(0);
        }
        data.op_set_output(op1, outvn, glb)?;
        data.op_uninsert(op1);
        if res == 1 {
            let first = buf1[0].expect("missing functional equality term");
            let second = buf2[0].expect("missing functional equality term");
            let slot1 = data.op(op1).get_slot(first);
            let substitute = match RulePushMulti::find_substitute(first, second, bl, earliest, data) {
                Some(found) => found,
                None => {
                    let addr = data.op(op).get_addr().clone();
                    let substitute = data.new_op(2, &addr);
                    data.op_set_opcode(substitute, OpCode::Multiequal, glb);
                    let first_addr = data.vn(first).get_addr().clone();
                    let first_size = data.vn(first).get_size();
                    if first_addr == *data.vn(second).get_addr() && !data.vn(first).is_addr_tied() {
                        data.new_varnode_out(first_size, &first_addr, substitute, glb)?;
                    } else {
                        data.new_unique_out(first_size, substitute, glb)?;
                    }
                    data.op_set_input(substitute, first, 0)?;
                    data.op_set_input(substitute, second, 1)?;
                    data.op_insert_begin(substitute, bl);
                    substitute
                }
            };
            let subout = data.op(substitute).get_out().expect("op without output");
            data.op_set_input(op1, subout, slot1)?;
            data.op_insert_after(op1, substitute);
        } else {
            data.op_insert_begin(op1, bl);
        }
        data.op_destroy(op)?;
        data.op_destroy(op2)?;
        Ok(1)
    }
}

pub struct RuleNotDistribute {
    pub base: RuleBase,
}

impl RuleNotDistribute {
    pub fn new(group: &str) -> RuleNotDistribute {
        RuleNotDistribute {
            base: RuleBase::new(group, 0, "notdistribute"),
        }
    }
}

impl Rule for RuleNotDistribute {
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
        Some(Box::new(RuleNotDistribute::new(self.get_group())))
    }

    fn get_op_list(&self, oplist: &mut Vec<OpCode>) {
        oplist.push(OpCode::BoolNegate);
    }

    fn apply_op(&mut self, op: OpId, data: &mut Funcdata, glb: &mut Architecture) -> Result<i32> {
        let Some(compop) = data.vn(data.op(op).get_in(0)).get_def() else {
            return Ok(0);
        };
        let opc = match data.op(compop).code() {
            OpCode::BoolAnd => OpCode::BoolOr,
            OpCode::BoolOr => OpCode::BoolAnd,
            _ => return Ok(0),
        };
        let addr = data.op(op).get_addr().clone();
        let newneg1 = data.new_op(1, &addr);
        let newout1 = data.new_unique_out(1, newneg1, glb)?;
        data.op_set_opcode(newneg1, OpCode::BoolNegate, glb);
        let first = data.op(compop).get_in(0);
        data.op_set_input(newneg1, first, 0)?;
        data.op_insert_before(newneg1, op);
        let newneg2 = data.new_op(1, &addr);
        let newout2 = data.new_unique_out(1, newneg2, glb)?;
        data.op_set_opcode(newneg2, OpCode::BoolNegate, glb);
        let second = data.op(compop).get_in(1);
        data.op_set_input(newneg2, second, 0)?;
        data.op_insert_before(newneg2, op);
        data.op_set_opcode(op, opc, glb);
        data.op_set_input(op, newout1, 0)?;
        data.op_insert_input(op, newout2, 1)?;
        Ok(1)
    }
}

pub struct RuleHighOrderAnd {
    pub base: RuleBase,
}

impl RuleHighOrderAnd {
    pub fn new(group: &str) -> RuleHighOrderAnd {
        RuleHighOrderAnd {
            base: RuleBase::new(group, 0, "highorderand"),
        }
    }
}

impl Rule for RuleHighOrderAnd {
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
        Some(Box::new(RuleHighOrderAnd::new(self.get_group())))
    }

    fn get_op_list(&self, oplist: &mut Vec<OpCode>) {
        oplist.push(OpCode::IntAnd);
    }

    fn apply_op(&mut self, op: OpId, data: &mut Funcdata, glb: &mut Architecture) -> Result<i32> {
        let cvn1 = data.op(op).get_in(1);
        if !data.vn(cvn1).is_constant() {
            return Ok(0);
        }
        let invn = data.op(op).get_in(0);
        if !data.vn(invn).is_written() {
            return Ok(0);
        }
        let addop = data.vn(invn).get_def().expect("written varnode without defining op");
        if data.op(addop).code() != OpCode::IntAdd {
            return Ok(0);
        }
        let mut val = data.vn(cvn1).get_offset();
        let size = data.vn(cvn1).get_size();
        if (val.wrapping_sub(1) | val) != calc_mask(size) {
            return Ok(0);
        }
        let cvn2 = data.op(addop).get_in(1);
        if data.vn(cvn2).is_constant() {
            let xalign = data.op(addop).get_in(0);
            if data.vn(xalign).is_free() {
                return Ok(0);
            }
            let mask1 = data.vn(xalign).get_nz_mask();
            if (mask1 & val) != mask1 {
                return Ok(0);
            }
            data.op_set_opcode(op, OpCode::IntAdd, glb);
            data.op_set_input(op, xalign, 0)?;
            val &= data.vn(cvn2).get_offset();
            let newconst = data.new_constant(size, val, glb);
            data.op_set_input(op, newconst, 1)?;
            return Ok(1);
        } else {
            let addout = data.op(addop).get_out().expect("op without output");
            if data.vn(addout).lone_descend() != Some(op) {
                return Ok(0);
            }
            for slot in 0..2 {
                let zerovn = data.op(addop).get_in(slot);
                let mut mask2 = data.vn(zerovn).get_nz_mask();
                if (mask2 & val) != mask2 {
                    continue;
                }
                let nonzerovn = data.op(addop).get_in(1 - slot);
                if !data.vn(nonzerovn).is_written() {
                    continue;
                }
                let addop2 = data
                    .vn(nonzerovn)
                    .get_def()
                    .expect("written varnode without defining op");
                if data.op(addop2).code() != OpCode::IntAdd {
                    continue;
                }
                if data.vn(nonzerovn).lone_descend() != Some(addop) {
                    continue;
                }
                let cvn2 = data.op(addop2).get_in(1);
                if !data.vn(cvn2).is_constant() {
                    continue;
                }
                let xalign = data.op(addop2).get_in(0);
                mask2 = data.vn(xalign).get_nz_mask();
                if (mask2 & val) != mask2 {
                    continue;
                }
                val &= data.vn(cvn2).get_offset();
                let newconst = data.new_constant(size, val, glb);
                data.op_set_input(addop2, newconst, 1)?;
                data.op_remove_input(op, 1);
                data.op_set_opcode(op, OpCode::Copy, glb);
                return Ok(1);
            }
        }
        Ok(0)
    }
}

pub struct RuleAndDistribute {
    pub base: RuleBase,
}

impl RuleAndDistribute {
    pub fn new(group: &str) -> RuleAndDistribute {
        RuleAndDistribute {
            base: RuleBase::new(group, 0, "anddistribute"),
        }
    }
}

impl Rule for RuleAndDistribute {
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
        Some(Box::new(RuleAndDistribute::new(self.get_group())))
    }

    fn get_op_list(&self, oplist: &mut Vec<OpCode>) {
        oplist.push(OpCode::IntAnd);
    }

    fn apply_op(&mut self, op: OpId, data: &mut Funcdata, glb: &mut Architecture) -> Result<i32> {
        let size = data.vn(data.op(op).get_out().expect("op without output")).get_size();
        if size > 8 {
            return Ok(0);
        }
        let fullmask = calc_mask(size);
        let mut chosen: Option<(VarnodeId, OpId)> = None;
        for slot in 0..2 {
            let othervn = data.op(op).get_in(1 - slot);
            if !data.vn(othervn).is_heritage_known() {
                continue;
            }
            let orvn = data.op(op).get_in(slot);
            let Some(orop) = data.vn(orvn).get_def() else {
                continue;
            };
            if data.op(orop).code() != OpCode::IntOr {
                continue;
            }
            if !data.vn(data.op(orop).get_in(0)).is_heritage_known() {
                continue;
            }
            if !data.vn(data.op(orop).get_in(1)).is_heritage_known() {
                continue;
            }
            let othermask = data.vn(othervn).get_nz_mask();
            if othermask == 0 {
                continue;
            }
            if othermask == fullmask {
                continue;
            }
            let ormask1 = data.vn(data.op(orop).get_in(0)).get_nz_mask();
            if (ormask1 & othermask) == 0 {
                chosen = Some((othervn, orop));
                break;
            }
            let ormask2 = data.vn(data.op(orop).get_in(1)).get_nz_mask();
            if (ormask2 & othermask) == 0 {
                chosen = Some((othervn, orop));
                break;
            }
            if data.vn(othervn).is_constant() {
                if (ormask1 & othermask) == ormask1 {
                    chosen = Some((othervn, orop));
                    break;
                }
                if (ormask2 & othermask) == ormask2 {
                    chosen = Some((othervn, orop));
                    break;
                }
            }
        }
        let Some((othervn, orop)) = chosen else {
            return Ok(0);
        };
        let addr = data.op(op).get_addr().clone();
        let newop1 = data.new_op(2, &addr);
        let newvn1 = data.new_unique_out(size, newop1, glb)?;
        data.op_set_opcode(newop1, OpCode::IntAnd, glb);
        let orin0 = data.op(orop).get_in(0);
        data.op_set_input(newop1, orin0, 0)?;
        data.op_set_input(newop1, othervn, 1)?;
        data.op_insert_before(newop1, op);
        let newop2 = data.new_op(2, &addr);
        let newvn2 = data.new_unique_out(size, newop2, glb)?;
        data.op_set_opcode(newop2, OpCode::IntAnd, glb);
        let orin1 = data.op(orop).get_in(1);
        data.op_set_input(newop2, orin1, 0)?;
        data.op_set_input(newop2, othervn, 1)?;
        data.op_insert_before(newop2, op);
        data.op_set_input(op, newvn1, 0)?;
        data.op_set_input(op, newvn2, 1)?;
        data.op_set_opcode(op, OpCode::IntOr, glb);
        Ok(1)
    }
}

pub struct RuleLessOne {
    pub base: RuleBase,
}

impl RuleLessOne {
    pub fn new(group: &str) -> RuleLessOne {
        RuleLessOne {
            base: RuleBase::new(group, 0, "lessone"),
        }
    }
}

impl Rule for RuleLessOne {
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
        Some(Box::new(RuleLessOne::new(self.get_group())))
    }

    fn get_op_list(&self, oplist: &mut Vec<OpCode>) {
        oplist.push(OpCode::IntLess);
        oplist.push(OpCode::IntLessequal);
    }

    fn apply_op(&mut self, op: OpId, data: &mut Funcdata, glb: &mut Architecture) -> Result<i32> {
        let constvn = data.op(op).get_in(1);
        if !data.vn(constvn).is_constant() {
            return Ok(0);
        }
        let val = data.vn(constvn).get_offset();
        if data.op(op).code() == OpCode::IntLess && val != 1 {
            return Ok(0);
        }
        if data.op(op).code() == OpCode::IntLessequal && val != 0 {
            return Ok(0);
        }
        data.op_set_opcode(op, OpCode::IntEqual, glb);
        if val != 0 {
            let size = data.vn(constvn).get_size();
            let zero = data.new_constant(size, 0, glb);
            data.op_set_input(op, zero, 1)?;
        }
        Ok(1)
    }
}

pub struct RuleRangeMeld {
    pub base: RuleBase,
}

impl RuleRangeMeld {
    pub fn new(group: &str) -> RuleRangeMeld {
        RuleRangeMeld {
            base: RuleBase::new(group, 0, "rangemeld"),
        }
    }
}

impl Rule for RuleRangeMeld {
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
        Some(Box::new(RuleRangeMeld::new(self.get_group())))
    }

    fn get_op_list(&self, oplist: &mut Vec<OpCode>) {
        oplist.push(OpCode::BoolOr);
        oplist.push(OpCode::BoolAnd);
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
        let sub1 = data.vn(vn1).get_def().expect("written varnode without defining op");
        if !data.op(sub1).is_bool_output() {
            return Ok(0);
        }
        let sub2 = data.vn(vn2).get_def().expect("written varnode without defining op");
        if !data.op(sub2).is_bool_output() {
            return Ok(0);
        }
        let mut range1 = CircleRange::new_bool(true);
        let mut markup: Option<VarnodeId> = None;
        let Some(mut first) = range1.pull_back(sub1, Some(&mut markup), false, data) else {
            return Ok(0);
        };
        let mut range2 = CircleRange::new_bool(true);
        let Some(mut second) = range2.pull_back(sub2, Some(&mut markup), false, data) else {
            return Ok(0);
        };
        if data.op(sub1).code() == OpCode::BoolNegate {
            if !data.vn(first).is_written() {
                return Ok(0);
            }
            let def = data.vn(first).get_def().expect("written varnode without defining op");
            match range1.pull_back(def, Some(&mut markup), false, data) {
                Some(found) => first = found,
                None => return Ok(0),
            }
        }
        if data.op(sub2).code() == OpCode::BoolNegate {
            if !data.vn(second).is_written() {
                return Ok(0);
            }
            let def = data.vn(second).get_def().expect("written varnode without defining op");
            match range2.pull_back(def, Some(&mut markup), false, data) {
                Some(found) => second = found,
                None => return Ok(0),
            }
        }
        if !functional_equality(first, second, data) {
            if data.vn(second).get_size() == data.vn(first).get_size() {
                return Ok(0);
            }
            let mut first_opt = Some(first);
            let mut second_opt = Some(second);
            if data.vn(first).get_size() < data.vn(second).get_size() && data.vn(second).is_written() {
                let def = data.vn(second).get_def().expect("written varnode without defining op");
                second_opt = range2.pull_back(def, Some(&mut markup), false, data);
            } else if data.vn(first).is_written() {
                let def = data.vn(first).get_def().expect("written varnode without defining op");
                first_opt = range1.pull_back(def, Some(&mut markup), false, data);
            }
            if first_opt != second_opt {
                return Ok(0);
            }
            first = first_opt.expect("pulled back varnode missing");
        }
        if !data.vn(first).is_heritage_known() {
            return Ok(0);
        }
        let mut restype = if data.op(op).code() == OpCode::BoolAnd {
            range1.intersect(&range2)
        } else {
            range1.circle_union(&range2)
        };
        if restype == 0 {
            let mut opc = OpCode::Copy;
            let mut resc: u64 = 0;
            let mut resslot: i32 = 0;
            restype = range1.translate2_op(&mut opc, &mut resc, &mut resslot);
            if restype == 0 {
                let size = data.vn(first).get_size();
                let new_const = data.new_constant(size, resc, glb);
                if let Some(markup) = markup {
                    data.vn_copy_symbol_if_valid(new_const, markup, glb)?;
                }
                data.op_set_opcode(op, opc, glb);
                data.op_set_input(op, first, 1 - resslot)?;
                data.op_set_input(op, new_const, resslot)?;
                return Ok(1);
            }
        }
        if restype == 2 {
            return Ok(0);
        }
        if restype == 1 {
            data.op_set_opcode(op, OpCode::Copy, glb);
            data.op_remove_input(op, 1);
            let truevn = data.new_constant(1, 1, glb);
            data.op_set_input(op, truevn, 0)?;
        } else if restype == 3 {
            data.op_set_opcode(op, OpCode::Copy, glb);
            data.op_remove_input(op, 1);
            let falsevn = data.new_constant(1, 0, glb);
            data.op_set_input(op, falsevn, 0)?;
        }
        Ok(1)
    }
}

pub struct RuleFloatRange {
    pub base: RuleBase,
}

impl RuleFloatRange {
    pub fn new(group: &str) -> RuleFloatRange {
        RuleFloatRange {
            base: RuleBase::new(group, 0, "floatrange"),
        }
    }
}

impl Rule for RuleFloatRange {
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
        Some(Box::new(RuleFloatRange::new(self.get_group())))
    }

    fn get_op_list(&self, oplist: &mut Vec<OpCode>) {
        oplist.push(OpCode::BoolOr);
        oplist.push(OpCode::BoolAnd);
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
        let mut cmp1 = data.vn(vn1).get_def().expect("written varnode without defining op");
        let mut cmp2 = data.vn(vn2).get_def().expect("written varnode without defining op");
        let mut opccmp1 = data.op(cmp1).code();
        if opccmp1 != OpCode::FloatLess && opccmp1 != OpCode::FloatLessequal {
            cmp1 = cmp2;
            cmp2 = data.vn(vn1).get_def().expect("written varnode without defining op");
            opccmp1 = data.op(cmp1).code();
        }
        let mut resultopc = OpCode::Copy;
        if opccmp1 == OpCode::FloatLess {
            if data.op(cmp2).code() == OpCode::FloatEqual && data.op(op).code() == OpCode::BoolOr {
                resultopc = OpCode::FloatLessequal;
            }
        } else if opccmp1 == OpCode::FloatLessequal
            && data.op(cmp2).code() == OpCode::FloatNotequal
            && data.op(op).code() == OpCode::BoolAnd
        {
            resultopc = OpCode::FloatLess;
        }
        if resultopc == OpCode::Copy {
            return Ok(0);
        }
        let mut slot1 = 0;
        let mut nvn1 = data.op(cmp1).get_in(slot1);
        if data.vn(nvn1).is_constant() {
            slot1 = 1;
            nvn1 = data.op(cmp1).get_in(slot1);
            if data.vn(nvn1).is_constant() {
                return Ok(0);
            }
        }
        if data.vn(nvn1).is_free() {
            return Ok(0);
        }
        let cvn1 = data.op(cmp1).get_in(1 - slot1);
        let slot2 = if nvn1 != data.op(cmp2).get_in(0) {
            if nvn1 != data.op(cmp2).get_in(1) {
                return Ok(0);
            }
            1
        } else {
            0
        };
        let matchvn = data.op(cmp2).get_in(1 - slot2);
        if data.vn(cvn1).is_constant() {
            if !data.vn(matchvn).is_constant() {
                return Ok(0);
            }
            if data.vn(matchvn).get_offset() != data.vn(cvn1).get_offset() {
                return Ok(0);
            }
        } else if cvn1 != matchvn || data.vn(cvn1).is_free() {
            return Ok(0);
        }
        data.op_set_opcode(op, resultopc, glb);
        data.op_set_input(op, nvn1, slot1)?;
        if data.vn(cvn1).is_constant() {
            let size = data.vn(cvn1).get_size();
            let offset = data.vn(cvn1).get_offset();
            let newconst = data.new_constant(size, offset, glb);
            data.op_set_input(op, newconst, 1 - slot1)?;
        } else {
            data.op_set_input(op, cvn1, 1 - slot1)?;
        }
        Ok(1)
    }
}

pub struct RuleAndCommute {
    pub base: RuleBase,
}

impl RuleAndCommute {
    pub fn new(group: &str) -> RuleAndCommute {
        RuleAndCommute {
            base: RuleBase::new(group, 0, "andcommute"),
        }
    }
}

impl Rule for RuleAndCommute {
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
        Some(Box::new(RuleAndCommute::new(self.get_group())))
    }

    fn get_op_list(&self, oplist: &mut Vec<OpCode>) {
        oplist.push(OpCode::IntAnd);
    }

    fn apply_op(&mut self, op: OpId, data: &mut Funcdata, glb: &mut Architecture) -> Result<i32> {
        let size = data.vn(data.op(op).get_out().expect("op without output")).get_size();
        if size > 8 {
            return Ok(0);
        }
        let fullmask = calc_mask(size);
        let mut chosen: Option<(OpCode, VarnodeId, VarnodeId, VarnodeId)> = None;
        for slot in 0..2 {
            let shiftvn = data.op(op).get_in(slot);
            let Some(shiftop) = data.vn(shiftvn).get_def() else {
                continue;
            };
            let opc = data.op(shiftop).code();
            if opc != OpCode::IntLeft && opc != OpCode::IntRight {
                continue;
            }
            let savn = data.op(shiftop).get_in(1);
            if !data.vn(savn).is_constant() {
                continue;
            }
            let shift_amount = data.vn(savn).get_offset() as i32 as u32;
            let othervn = data.op(op).get_in(1 - slot);
            if !data.vn(othervn).is_heritage_known() {
                continue;
            }
            let mut othermask = data.vn(othervn).get_nz_mask();
            if opc == OpCode::IntRight {
                if fullmask.wrapping_shr(shift_amount) == othermask {
                    continue;
                }
                othermask = othermask.wrapping_shl(shift_amount);
            } else {
                let logical = (fullmask.wrapping_shl(shift_amount) != 0 && fullmask != 0) as u64;
                if logical == othermask {
                    continue;
                }
                othermask = othermask.wrapping_shr(shift_amount);
            }
            if othermask == 0 {
                continue;
            }
            if othermask == fullmask {
                continue;
            }
            let orvn = data.op(shiftop).get_in(0);
            if opc == OpCode::IntLeft && data.vn(othervn).is_constant() && data.vn(shiftvn).lone_descend() == Some(op) {
                chosen = Some((opc, orvn, othervn, savn));
                break;
            }
            if !data.vn(orvn).is_written() {
                continue;
            }
            let orop = data.vn(orvn).get_def().expect("written varnode without defining op");
            if data.op(orop).code() == OpCode::IntOr {
                let ormask1 = data.vn(data.op(orop).get_in(0)).get_nz_mask();
                if (ormask1 & othermask) == 0 {
                    chosen = Some((opc, orvn, othervn, savn));
                    break;
                }
                let ormask2 = data.vn(data.op(orop).get_in(1)).get_nz_mask();
                if (ormask2 & othermask) == 0 {
                    chosen = Some((opc, orvn, othervn, savn));
                    break;
                }
                if data.vn(othervn).is_constant() {
                    if (ormask1 & othermask) == ormask1 {
                        chosen = Some((opc, orvn, othervn, savn));
                        break;
                    }
                    if (ormask2 & othermask) == ormask2 {
                        chosen = Some((opc, orvn, othervn, savn));
                        break;
                    }
                }
            } else if data.op(orop).code() == OpCode::Piece {
                let ormask1 = data.vn(data.op(orop).get_in(1)).get_nz_mask();
                if (ormask1 & othermask) == 0 {
                    chosen = Some((opc, orvn, othervn, savn));
                    break;
                }
                let mut ormask2 = data.vn(data.op(orop).get_in(0)).get_nz_mask();
                ormask2 = ormask2.wrapping_shl((data.vn(data.op(orop).get_in(1)).get_size() * 8) as u32);
                if (ormask2 & othermask) == 0 {
                    chosen = Some((opc, orvn, othervn, savn));
                    break;
                }
            } else {
                continue;
            }
        }
        let Some((opc, orvn, othervn, savn)) = chosen else {
            return Ok(0);
        };
        let addr = data.op(op).get_addr().clone();
        let newop1 = data.new_op(2, &addr);
        let newvn1 = data.new_unique_out(size, newop1, glb)?;
        let reverse = if opc == OpCode::IntLeft {
            OpCode::IntRight
        } else {
            OpCode::IntLeft
        };
        data.op_set_opcode(newop1, reverse, glb);
        data.op_set_input(newop1, othervn, 0)?;
        data.op_set_input(newop1, savn, 1)?;
        data.op_insert_before(newop1, op);
        let newop2 = data.new_op(2, &addr);
        let newvn2 = data.new_unique_out(size, newop2, glb)?;
        data.op_set_opcode(newop2, OpCode::IntAnd, glb);
        data.op_set_input(newop2, orvn, 0)?;
        data.op_set_input(newop2, newvn1, 1)?;
        data.op_insert_before(newop2, op);
        data.op_set_input(op, newvn2, 0)?;
        data.op_set_input(op, savn, 1)?;
        data.op_set_opcode(op, opc, glb);
        Ok(1)
    }
}

pub struct RuleAndPiece {
    pub base: RuleBase,
}

impl RuleAndPiece {
    pub fn new(group: &str) -> RuleAndPiece {
        RuleAndPiece {
            base: RuleBase::new(group, 0, "andpiece"),
        }
    }
}

impl Rule for RuleAndPiece {
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
        Some(Box::new(RuleAndPiece::new(self.get_group())))
    }

    fn get_op_list(&self, oplist: &mut Vec<OpCode>) {
        oplist.push(OpCode::IntAnd);
    }

    fn apply_op(&mut self, op: OpId, data: &mut Funcdata, glb: &mut Architecture) -> Result<i32> {
        let size = data.vn(data.op(op).get_out().expect("op without output")).get_size();
        let mut chosen: Option<(i32, OpCode, VarnodeId, VarnodeId)> = None;
        for slot in 0..2 {
            let piecevn = data.op(op).get_in(slot);
            if !data.vn(piecevn).is_written() {
                continue;
            }
            let pieceop = data.vn(piecevn).get_def().expect("written varnode without defining op");
            if data.op(pieceop).code() != OpCode::Piece {
                continue;
            }
            let othervn = data.op(op).get_in(1 - slot);
            let othermask = data.vn(othervn).get_nz_mask();
            if othermask == calc_mask(size) {
                continue;
            }
            if othermask == 0 {
                continue;
            }
            let highvn = data.op(pieceop).get_in(0);
            if !data.vn(highvn).is_heritage_known() {
                continue;
            }
            let lowvn = data.op(pieceop).get_in(1);
            if !data.vn(lowvn).is_heritage_known() {
                continue;
            }
            let maskhigh = data.vn(highvn).get_nz_mask();
            let masklow = data.vn(lowvn).get_nz_mask();
            if (maskhigh & othermask.wrapping_shr((data.vn(lowvn).get_size() * 8) as u32)) == 0 {
                if maskhigh == 0 && data.vn(highvn).is_constant() {
                    continue;
                }
                chosen = Some((slot, OpCode::IntZext, highvn, lowvn));
                break;
            } else if (masklow & othermask) == 0 {
                if data.vn(lowvn).is_constant() {
                    continue;
                }
                chosen = Some((slot, OpCode::Piece, highvn, lowvn));
                break;
            }
        }
        let Some((slot, opc, highvn, lowvn)) = chosen else {
            return Ok(0);
        };
        let addr = data.op(op).get_addr().clone();
        let newop = if opc == OpCode::IntZext {
            let newop = data.new_op(1, &addr);
            data.op_set_opcode(newop, opc, glb);
            data.op_set_input(newop, lowvn, 0)?;
            newop
        } else {
            let lowsize = data.vn(lowvn).get_size();
            let newvn2 = data.new_constant(lowsize, 0, glb);
            let newop = data.new_op(2, &addr);
            data.op_set_opcode(newop, opc, glb);
            data.op_set_input(newop, highvn, 0)?;
            data.op_set_input(newop, newvn2, 1)?;
            newop
        };
        let newvn = data.new_unique_out(size, newop, glb)?;
        data.op_insert_before(newop, op);
        data.op_set_input(op, newvn, slot)?;
        Ok(1)
    }
}

pub struct RuleAndZext {
    pub base: RuleBase,
}

impl RuleAndZext {
    pub fn new(group: &str) -> RuleAndZext {
        RuleAndZext {
            base: RuleBase::new(group, 0, "andzext"),
        }
    }
}

impl Rule for RuleAndZext {
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
        Some(Box::new(RuleAndZext::new(self.get_group())))
    }

    fn get_op_list(&self, oplist: &mut Vec<OpCode>) {
        oplist.push(OpCode::IntAnd);
    }

    fn apply_op(&mut self, op: OpId, data: &mut Funcdata, glb: &mut Architecture) -> Result<i32> {
        let cvn1 = data.op(op).get_in(1);
        if !data.vn(cvn1).is_constant() {
            return Ok(0);
        }
        let invn = data.op(op).get_in(0);
        if !data.vn(invn).is_written() {
            return Ok(0);
        }
        let otherop = data.vn(invn).get_def().expect("written varnode without defining op");
        let opc = data.op(otherop).code();
        let rootvn = if opc == OpCode::IntSext {
            data.op(otherop).get_in(0)
        } else if opc == OpCode::Piece {
            data.op(otherop).get_in(1)
        } else {
            return Ok(0);
        };
        let mask = calc_mask(data.vn(rootvn).get_size());
        if mask != data.vn(cvn1).get_offset() {
            return Ok(0);
        }
        if data.vn(rootvn).is_free() {
            return Ok(0);
        }
        if data.vn(rootvn).get_size() > 8 {
            return Ok(0);
        }
        data.op_set_opcode(op, OpCode::IntZext, glb);
        data.op_remove_input(op, 1);
        data.op_set_input(op, rootvn, 0)?;
        Ok(1)
    }
}

pub struct RuleAndCompare {
    pub base: RuleBase,
}

impl RuleAndCompare {
    pub fn new(group: &str) -> RuleAndCompare {
        RuleAndCompare {
            base: RuleBase::new(group, 0, "andcompare"),
        }
    }
}

impl Rule for RuleAndCompare {
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
        Some(Box::new(RuleAndCompare::new(self.get_group())))
    }

    fn get_op_list(&self, oplist: &mut Vec<OpCode>) {
        oplist.push(OpCode::IntEqual);
        oplist.push(OpCode::IntNotequal);
    }

    fn apply_op(&mut self, op: OpId, data: &mut Funcdata, glb: &mut Architecture) -> Result<i32> {
        if !data.vn(data.op(op).get_in(1)).is_constant() {
            return Ok(0);
        }
        if data.vn(data.op(op).get_in(1)).get_offset() != 0 {
            return Ok(0);
        }
        let andvn = data.op(op).get_in(0);
        if !data.vn(andvn).is_written() {
            return Ok(0);
        }
        let andop = data.vn(andvn).get_def().expect("written varnode without defining op");
        if data.op(andop).code() != OpCode::IntAnd {
            return Ok(0);
        }
        let andconstvn = data.op(andop).get_in(1);
        if !data.vn(andconstvn).is_constant() {
            return Ok(0);
        }
        let subvn = data.op(andop).get_in(0);
        if !data.vn(subvn).is_written() {
            return Ok(0);
        }
        let subop = data.vn(subvn).get_def().expect("written varnode without defining op");
        let (basevn, baseconst, andconst) = match data.op(subop).code() {
            OpCode::Subpiece => {
                let basevn = data.op(subop).get_in(0);
                if data.vn(basevn).get_size() > 8 {
                    return Ok(0);
                }
                let baseconst = data.vn(andconstvn).get_offset();
                let amount = data.vn(data.op(subop).get_in(1)).get_offset().wrapping_mul(8);
                (basevn, baseconst, baseconst.wrapping_shl(amount as u32))
            }
            OpCode::IntZext => {
                let basevn = data.op(subop).get_in(0);
                let baseconst = data.vn(andconstvn).get_offset();
                (basevn, baseconst, baseconst & calc_mask(data.vn(basevn).get_size()))
            }
            _ => return Ok(0),
        };
        if baseconst == calc_mask(data.vn(andvn).get_size()) {
            return Ok(0);
        }
        if data.vn(basevn).is_free() {
            return Ok(0);
        }
        let basesize = data.vn(basevn).get_size();
        let constvn = data.new_constant(basesize, andconst, glb);
        if baseconst == andconst {
            data.vn_copy_symbol(constvn, andconstvn, glb)?;
        }
        let andaddr = data.op(andop).get_addr().clone();
        let newop = data.new_op(2, &andaddr);
        data.op_set_opcode(newop, OpCode::IntAnd, glb);
        let newout = data.new_unique_out(basesize, newop, glb)?;
        data.op_set_input(newop, basevn, 0)?;
        data.op_set_input(newop, constvn, 1)?;
        data.op_insert_before(newop, andop);
        data.op_set_input(op, newout, 0)?;
        let zero = data.new_constant(basesize, 0, glb);
        data.op_set_input(op, zero, 1)?;
        Ok(1)
    }
}
