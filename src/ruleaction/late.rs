use super::{types, types_mut, written_def};
use crate::action::{ActionGroupList, Rule, RuleBase};
use crate::address::{calc_mask, leastsigbit_set, mostsigbit_set, popcount};
use crate::architecture::Architecture;
use crate::block::BlockId;
use crate::error::Result;
use crate::expression::functional_equality;
use crate::funcdata::CloneBlockOps;
use crate::funcdata::Funcdata;
use crate::op::OpId;
use crate::op::PcodeOp;
use crate::opcodes::OpCode;
use crate::space::SpaceRef;
use crate::space::SpaceType;
use crate::stdsort::std_sort;
use crate::typeop::{TypeOpFloatInt2Float, float_sign_manipulation};
use crate::types::TypeId;
use crate::types::TypeMetatype;
use crate::varnode::VarnodeId;

pub struct RulePtrFlow {
    pub base: RuleBase,
    pub has_truncations: bool,
}

impl RulePtrFlow {
    pub fn new(group: &str, conf: &Architecture) -> RulePtrFlow {
        let has_truncations = conf
            .manager
            .get_default_data_space()
            .expect("default data space is not defined")
            .is_truncated();
        RulePtrFlow {
            base: RuleBase::new(group, 0, "ptrflow"),
            has_truncations,
        }
    }

    pub fn walk_indirects(&mut self, op: OpId, data: &mut Funcdata) -> bool {
        let mut cur = data.op_previous_op(op);
        let mut made_change = false;
        while let Some(indop) = cur {
            if data.op(indop).code() != OpCode::Indirect {
                break;
            }
            if !data.op(indop).is_ptr_flow() {
                cur = data.op_previous_op(indop);
                continue;
            }
            let outvn = data.op(indop).get_out().expect("op without output");
            if self.propagate_flow_to_reads(outvn, data) {
                made_change = true;
            }
            let invn = data.op(indop).get_in(0);
            if self.propagate_flow_to_def(invn, data) {
                made_change = true;
            }
            break;
        }
        made_change
    }

    pub fn trial_set_ptr_flow(&mut self, op: OpId, data: &mut Funcdata) -> bool {
        match data.op(op).code() {
            OpCode::Copy | OpCode::Multiequal | OpCode::IntAdd | OpCode::Indirect | OpCode::Ptrsub | OpCode::Ptradd
                if !data.op(op).is_ptr_flow() =>
            {
                data.op_mut(op).set_ptr_flow();
                return true;
            }
            _ => {}
        }
        false
    }

    pub fn propagate_flow_to_def(&mut self, vn: VarnodeId, data: &mut Funcdata) -> bool {
        let mut made_change = false;
        if !data.vn(vn).is_ptr_flow() {
            data.vn_mut(vn).set_ptr_flow();
            made_change = true;
        }
        let Some(op) = written_def(data, vn) else {
            return made_change;
        };
        if self.trial_set_ptr_flow(op, data) {
            made_change = true;
        }
        made_change
    }

    pub fn propagate_flow_to_reads(&mut self, vn: VarnodeId, data: &mut Funcdata) -> bool {
        let mut made_change = false;
        if !data.vn(vn).is_ptr_flow() {
            data.vn_mut(vn).set_ptr_flow();
            made_change = true;
        }
        let descendants = data.vn(vn).descend().to_vec();
        for op in descendants {
            if self.trial_set_ptr_flow(op, data) {
                made_change = true;
            }
        }
        made_change
    }

    pub fn truncate_pointer(
        &mut self,
        spc: SpaceRef,
        op: OpId,
        vn: VarnodeId,
        slot: i32,
        data: &mut Funcdata,
        glb: &mut Architecture,
    ) -> Result<VarnodeId> {
        let addr_size = spc.get_addr_size() as i32;
        let opaddr = data.op(op).get_addr().clone();
        let truncop = data.new_op(2, &opaddr);
        data.op_set_opcode(truncop, OpCode::Subpiece, glb);
        let zerovn = data.new_constant(data.vn(vn).get_size(), 0, glb);
        data.op_set_input(truncop, zerovn, 1)?;
        let newvn;
        if data.vn(vn).get_space().expect("varnode without space").get_type() == SpaceType::Internal {
            newvn = data.new_unique_out(addr_size, truncop, glb)?;
        } else {
            let mut addr = data.vn(vn).get_addr().clone();
            if addr.is_big_endian() {
                addr = addr.add((data.vn(vn).get_size() - addr_size) as i64);
            }
            addr.renormalize(addr_size)?;
            newvn = data.new_varnode_out(addr_size, &addr, truncop, glb)?;
        }
        data.op_set_input(op, newvn, slot)?;
        data.op_set_input(truncop, vn, 0)?;
        data.op_insert_before(truncop, op);
        Ok(newvn)
    }
}

impl Rule for RulePtrFlow {
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
        Some(Box::new(RulePtrFlow {
            base: RuleBase::new(self.get_group(), 0, "ptrflow"),
            has_truncations: self.has_truncations,
        }))
    }

    fn get_op_list(&self, oplist: &mut Vec<OpCode>) {
        if !self.has_truncations {
            return;
        }
        oplist.push(OpCode::Store);
        oplist.push(OpCode::Load);
        oplist.push(OpCode::Copy);
        oplist.push(OpCode::Multiequal);
        oplist.push(OpCode::IntAdd);
        oplist.push(OpCode::Call);
        oplist.push(OpCode::Callind);
        oplist.push(OpCode::Branchind);
        oplist.push(OpCode::Ptrsub);
        oplist.push(OpCode::Ptradd);
    }

    fn apply_op(&mut self, op: OpId, data: &mut Funcdata, glb: &mut Architecture) -> Result<i32> {
        let mut made_change = 0;
        match data.op(op).code() {
            OpCode::Load => {
                let mut vn = data.op(op).get_in(1);
                let spc = data
                    .vn(data.op(op).get_in(0))
                    .get_space_from_const(&glb.manager)
                    .expect("load operand without space");
                if data.vn(vn).get_size() > spc.get_addr_size() as i32 {
                    vn = self.truncate_pointer(spc, op, vn, 1, data, glb)?;
                    made_change = 1;
                }
                if self.propagate_flow_to_def(vn, data) {
                    made_change = 1;
                }
            }
            OpCode::Store => {
                let mut vn = data.op(op).get_in(1);
                let spc = data
                    .vn(data.op(op).get_in(0))
                    .get_space_from_const(&glb.manager)
                    .expect("store operand without space");
                if data.vn(vn).get_size() > spc.get_addr_size() as i32 {
                    vn = self.truncate_pointer(spc, op, vn, 1, data, glb)?;
                    made_change = 1;
                }
                if self.propagate_flow_to_def(vn, data) {
                    made_change = 1;
                }
                if self.walk_indirects(op, data) {
                    made_change = 1;
                }
            }
            OpCode::Call if self.walk_indirects(op, data) => {
                made_change = 1;
            }
            OpCode::Callind => {
                let mut vn = data.op(op).get_in(0);
                let spc = glb
                    .manager
                    .get_default_code_space()
                    .expect("default code space is not defined");
                if data.vn(vn).get_size() > spc.get_addr_size() as i32 {
                    vn = self.truncate_pointer(spc, op, vn, 0, data, glb)?;
                    made_change = 1;
                }
                if self.propagate_flow_to_def(vn, data) {
                    made_change = 1;
                }
                if self.walk_indirects(op, data) {
                    made_change = 1;
                }
            }
            OpCode::Branchind => {
                let mut vn = data.op(op).get_in(0);
                let spc = glb
                    .manager
                    .get_default_code_space()
                    .expect("default code space is not defined");
                if data.vn(vn).get_size() > spc.get_addr_size() as i32 {
                    vn = self.truncate_pointer(spc, op, vn, 0, data, glb)?;
                    made_change = 1;
                }
                if self.propagate_flow_to_def(vn, data) {
                    made_change = 1;
                }
            }
            OpCode::New => {
                let vn = data.op(op).get_out().expect("op without output");
                if self.propagate_flow_to_reads(vn, data) {
                    made_change = 1;
                }
            }
            OpCode::Copy | OpCode::Ptrsub | OpCode::Ptradd => {
                if !data.op(op).is_ptr_flow() {
                    return Ok(0);
                }
                let outvn = data.op(op).get_out().expect("op without output");
                if self.propagate_flow_to_reads(outvn, data) {
                    made_change = 1;
                }
                let invn = data.op(op).get_in(0);
                if self.propagate_flow_to_def(invn, data) {
                    made_change = 1;
                }
            }
            OpCode::Multiequal | OpCode::IntAdd => {
                if !data.op(op).is_ptr_flow() {
                    return Ok(0);
                }
                let outvn = data.op(op).get_out().expect("op without output");
                if self.propagate_flow_to_reads(outvn, data) {
                    made_change = 1;
                }
                for slot in 0..data.op(op).num_input() {
                    let invn = data.op(op).get_in(slot);
                    if self.propagate_flow_to_def(invn, data) {
                        made_change = 1;
                    }
                }
            }
            _ => {}
        }
        Ok(made_change)
    }
}

pub struct RuleNegateNegate {
    pub base: RuleBase,
}

impl RuleNegateNegate {
    pub fn new(group: &str) -> RuleNegateNegate {
        RuleNegateNegate {
            base: RuleBase::new(group, 0, "negatenegate"),
        }
    }
}

impl Rule for RuleNegateNegate {
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
        Some(Box::new(RuleNegateNegate::new(self.get_group())))
    }

    fn get_op_list(&self, oplist: &mut Vec<OpCode>) {
        oplist.push(OpCode::IntNegate);
    }

    fn apply_op(&mut self, op: OpId, data: &mut Funcdata, glb: &mut Architecture) -> Result<i32> {
        let vn1 = data.op(op).get_in(0);
        let Some(neg2) = written_def(data, vn1) else {
            return Ok(0);
        };
        if data.op(neg2).code() != OpCode::IntNegate {
            return Ok(0);
        }
        let vn2 = data.op(neg2).get_in(0);
        if data.vn(vn2).is_free() {
            return Ok(0);
        }
        data.op_set_input(op, vn2, 0)?;
        data.op_set_opcode(op, OpCode::Copy, glb);
        Ok(1)
    }
}

pub struct RuleConditionalMove {
    pub base: RuleBase,
}

impl RuleConditionalMove {
    pub fn new(group: &str) -> RuleConditionalMove {
        RuleConditionalMove {
            base: RuleBase::new(group, 0, "conditionalmove"),
        }
    }

    pub fn compare_op(op0: OpId, op1: OpId, data: &Funcdata) -> bool {
        data.op(op0).get_seq_num().get_order() < data.op(op1).get_seq_num().get_order()
    }

    pub fn check_boolean(vn: VarnodeId, data: &Funcdata) -> Option<VarnodeId> {
        let op = written_def(data, vn)?;
        if data.op(op).is_bool_output() {
            return Some(vn);
        }
        if data.op(op).code() == OpCode::Copy {
            let invn = data.op(op).get_in(0);
            if data.vn(invn).is_constant() {
                let val = data.vn(invn).get_offset();
                if (val & !1u64) == 0 {
                    return Some(invn);
                }
            }
        }
        None
    }

    pub fn gather_expression(
        vn: VarnodeId,
        ops: &mut Vec<OpId>,
        root: BlockId,
        branch: BlockId,
        data: &Funcdata,
    ) -> bool {
        if data.vn(vn).is_constant() {
            return true;
        }
        if data.vn(vn).is_free() {
            return false;
        }
        if data.vn(vn).is_addr_tied() {
            return false;
        }
        if root == branch {
            return true;
        }
        let Some(op) = written_def(data, vn) else { return true };
        if data.op(op).get_parent() != Some(branch) {
            return true;
        }
        ops.push(op);
        let mut pos = 0;
        while pos < ops.len() {
            let op = ops[pos];
            pos += 1;
            if data.op(op).get_eval_type() == PcodeOp::SPECIAL {
                return false;
            }
            for slot in 0..data.op(op).num_input() {
                let in0 = data.op(op).get_in(slot);
                if data.vn(in0).is_free() && !data.vn(in0).is_constant() {
                    return false;
                }
                if let Some(indef) = written_def(data, in0)
                    && data.op(indef).get_parent() == Some(branch)
                {
                    if data.vn(in0).is_addr_tied() {
                        return false;
                    }
                    if data.vn(in0).lone_descend() != Some(op) {
                        return false;
                    }
                    if ops.len() >= 4 {
                        return false;
                    }
                    ops.push(indef);
                }
            }
        }
        true
    }

    pub fn construct_bool(
        vn: VarnodeId,
        insertop: OpId,
        ops: &mut [OpId],
        data: &mut Funcdata,
        glb: &mut Architecture,
    ) -> Result<VarnodeId> {
        if ops.is_empty() {
            return Ok(vn);
        }
        std_sort(ops, |first, second| {
            data.op(*first).get_seq_num().get_order() < data.op(*second).get_seq_num().get_order()
        });
        let mut cloner = CloneBlockOps::new();
        cloner.clone_expression(data, ops, insertop, glb)
    }
}

impl Rule for RuleConditionalMove {
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
        Some(Box::new(RuleConditionalMove::new(self.get_group())))
    }

    fn get_op_list(&self, oplist: &mut Vec<OpCode>) {
        oplist.push(OpCode::Multiequal);
    }

    fn apply_op(&mut self, op: OpId, data: &mut Funcdata, glb: &mut Architecture) -> Result<i32> {
        if data.op(op).num_input() != 2 {
            return Ok(0);
        }
        let Some(bool0) = RuleConditionalMove::check_boolean(data.op(op).get_in(0), data) else {
            return Ok(0);
        };
        let Some(bool1) = RuleConditionalMove::check_boolean(data.op(op).get_in(1), data) else {
            return Ok(0);
        };
        let bb = data.op(op).get_parent().expect("op without parent block");
        let inblock0 = data.block(bb).get_in(0);
        let rootblock0 = if data.block(inblock0).size_out() == 1 {
            if data.block(inblock0).size_in() != 1 {
                return Ok(0);
            }
            data.block(inblock0).get_in(0)
        } else {
            inblock0
        };
        let inblock1 = data.block(bb).get_in(1);
        let rootblock1 = if data.block(inblock1).size_out() == 1 {
            if data.block(inblock1).size_in() != 1 {
                return Ok(0);
            }
            data.block(inblock1).get_in(0)
        } else {
            inblock1
        };
        if rootblock0 != rootblock1 {
            return Ok(0);
        }
        let Some(cbranch) = data.block_last_op(rootblock0) else {
            return Ok(0);
        };
        if data.op(cbranch).code() != OpCode::Cbranch {
            return Ok(0);
        }
        let mut op_list0: Vec<OpId> = Vec::new();
        if !RuleConditionalMove::gather_expression(bool0, &mut op_list0, rootblock0, inblock0, data) {
            return Ok(0);
        }
        let mut op_list1: Vec<OpId> = Vec::new();
        if !RuleConditionalMove::gather_expression(bool1, &mut op_list1, rootblock0, inblock1, data) {
            return Ok(0);
        }
        let mut path0istrue = if rootblock0 != inblock0 {
            data.block(rootblock0).get_true_out() == inblock0
        } else {
            data.block(rootblock0).get_true_out() != inblock1
        };
        if data.op(cbranch).is_boolean_flip() {
            path0istrue = !path0istrue;
        }
        if !data.vn(bool0).is_constant() && !data.vn(bool1).is_constant() {
            if inblock0 == rootblock0 {
                let boolvn = data.op(cbranch).get_in(1);
                let mut andorselect = path0istrue;
                if boolvn != data.op(op).get_in(0) {
                    let Some(negop) = written_def(data, boolvn) else {
                        return Ok(0);
                    };
                    if data.op(negop).code() != OpCode::BoolNegate {
                        return Ok(0);
                    }
                    if data.op(negop).get_in(0) != data.op(op).get_in(0) {
                        return Ok(0);
                    }
                    andorselect = !andorselect;
                }
                let opc = if andorselect { OpCode::BoolOr } else { OpCode::BoolAnd };
                data.op_uninsert(op);
                data.op_set_opcode(op, opc, glb);
                data.op_insert_begin(op, bb);
                let firstvn = RuleConditionalMove::construct_bool(bool0, op, &mut op_list0, data, glb)?;
                let secondvn = RuleConditionalMove::construct_bool(bool1, op, &mut op_list1, data, glb)?;
                data.op_set_input(op, firstvn, 0)?;
                data.op_set_input(op, secondvn, 1)?;
                return Ok(1);
            } else if inblock1 == rootblock0 {
                let boolvn = data.op(cbranch).get_in(1);
                let mut andorselect = !path0istrue;
                if boolvn != data.op(op).get_in(1) {
                    let Some(negop) = written_def(data, boolvn) else {
                        return Ok(0);
                    };
                    if data.op(negop).code() != OpCode::BoolNegate {
                        return Ok(0);
                    }
                    if data.op(negop).get_in(0) != data.op(op).get_in(1) {
                        return Ok(0);
                    }
                    andorselect = !andorselect;
                }
                data.op_uninsert(op);
                let opc = if andorselect { OpCode::BoolOr } else { OpCode::BoolAnd };
                data.op_set_opcode(op, opc, glb);
                data.op_insert_begin(op, bb);
                let firstvn = RuleConditionalMove::construct_bool(bool1, op, &mut op_list1, data, glb)?;
                let secondvn = RuleConditionalMove::construct_bool(bool0, op, &mut op_list0, data, glb)?;
                data.op_set_input(op, firstvn, 0)?;
                data.op_set_input(op, secondvn, 1)?;
                return Ok(1);
            }
            return Ok(0);
        }
        data.op_uninsert(op);
        let sz = data.vn(data.op(op).get_out().expect("op without output")).get_size();
        if data.vn(bool0).is_constant() && data.vn(bool1).is_constant() {
            if data.vn(bool0).get_offset() == data.vn(bool1).get_offset() {
                data.op_remove_input(op, 1);
                data.op_set_opcode(op, OpCode::Copy, glb);
                let constvn = data.new_constant(sz, data.vn(bool0).get_offset(), glb);
                data.op_set_input(op, constvn, 0)?;
                data.op_insert_begin(op, bb);
            } else {
                data.op_remove_input(op, 1);
                let mut boolvn = data.op(cbranch).get_in(1);
                let needcomplement = (data.vn(bool0).get_offset() == 0) == path0istrue;
                if sz == 1 {
                    if needcomplement {
                        data.op_set_opcode(op, OpCode::BoolNegate, glb);
                    } else {
                        data.op_set_opcode(op, OpCode::Copy, glb);
                    }
                    data.op_insert_begin(op, bb);
                    data.op_set_input(op, boolvn, 0)?;
                } else {
                    data.op_set_opcode(op, OpCode::IntZext, glb);
                    data.op_insert_begin(op, bb);
                    if needcomplement {
                        boolvn = data.op_bool_negate(boolvn, op, false, glb)?;
                    }
                    data.op_set_input(op, boolvn, 0)?;
                }
            }
        } else if data.vn(bool0).is_constant() {
            let needcomplement = path0istrue != (data.vn(bool0).get_offset() != 0);
            let opc = if data.vn(bool0).get_offset() != 0 {
                OpCode::BoolOr
            } else {
                OpCode::BoolAnd
            };
            data.op_set_opcode(op, opc, glb);
            data.op_insert_begin(op, bb);
            let mut boolvn = data.op(cbranch).get_in(1);
            if needcomplement {
                boolvn = data.op_bool_negate(boolvn, op, false, glb)?;
            }
            let body1 = RuleConditionalMove::construct_bool(bool1, op, &mut op_list1, data, glb)?;
            data.op_set_input(op, boolvn, 0)?;
            data.op_set_input(op, body1, 1)?;
        } else {
            let needcomplement = path0istrue == (data.vn(bool1).get_offset() != 0);
            let opc = if data.vn(bool1).get_offset() != 0 {
                OpCode::BoolOr
            } else {
                OpCode::BoolAnd
            };
            data.op_set_opcode(op, opc, glb);
            data.op_insert_begin(op, bb);
            let mut boolvn = data.op(cbranch).get_in(1);
            if needcomplement {
                boolvn = data.op_bool_negate(boolvn, op, false, glb)?;
            }
            let body0 = RuleConditionalMove::construct_bool(bool0, op, &mut op_list0, data, glb)?;
            data.op_set_input(op, boolvn, 0)?;
            data.op_set_input(op, body0, 1)?;
        }
        Ok(1)
    }
}

pub struct RuleFloatCast {
    pub base: RuleBase,
}

impl RuleFloatCast {
    pub fn new(group: &str) -> RuleFloatCast {
        RuleFloatCast {
            base: RuleBase::new(group, 0, "floatcast"),
        }
    }
}

impl Rule for RuleFloatCast {
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
        Some(Box::new(RuleFloatCast::new(self.get_group())))
    }

    fn get_op_list(&self, oplist: &mut Vec<OpCode>) {
        oplist.push(OpCode::FloatFloat2float);
        oplist.push(OpCode::FloatTrunc);
    }

    fn apply_op(&mut self, op: OpId, data: &mut Funcdata, glb: &mut Architecture) -> Result<i32> {
        let vn1 = data.op(op).get_in(0);
        let Some(castop) = written_def(data, vn1) else {
            return Ok(0);
        };
        let opc2 = data.op(castop).code();
        if opc2 != OpCode::FloatFloat2float && opc2 != OpCode::FloatInt2float {
            return Ok(0);
        }
        let opc1 = data.op(op).code();
        let vn2 = data.op(castop).get_in(0);
        let insize1 = data.vn(vn1).get_size();
        let insize2 = data.vn(vn2).get_size();
        let outsize = data.vn(data.op(op).get_out().expect("op without output")).get_size();
        if data.vn(vn2).is_free() {
            return Ok(0);
        }
        if opc2 == OpCode::FloatFloat2float && opc1 == OpCode::FloatFloat2float {
            if insize1 > outsize {
                data.op_set_input(op, vn2, 0)?;
                if outsize == insize2 {
                    data.op_set_opcode(op, OpCode::Copy, glb);
                }
                return Ok(1);
            } else if insize2 < insize1 {
                data.op_set_input(op, vn2, 0)?;
                return Ok(1);
            }
        } else if opc2 == OpCode::FloatInt2float && opc1 == OpCode::FloatFloat2float {
            data.op_set_input(op, vn2, 0)?;
            data.op_set_opcode(op, OpCode::FloatInt2float, glb);
            return Ok(1);
        } else if opc2 == OpCode::FloatFloat2float && opc1 == OpCode::FloatTrunc {
            data.op_set_input(op, vn2, 0)?;
            return Ok(1);
        }
        Ok(0)
    }
}

pub struct RuleIgnoreNan {
    pub base: RuleBase,
}

impl RuleIgnoreNan {
    pub fn new(group: &str) -> RuleIgnoreNan {
        RuleIgnoreNan {
            base: RuleBase::new(group, 0, "ignorenan"),
        }
    }

    pub fn check_back_for_compare(float_var: VarnodeId, root: VarnodeId, data: &Funcdata, glb: &Architecture) -> bool {
        let Some(mut def1) = written_def(data, root) else {
            return false;
        };
        if !data.op(def1).is_bool_output() {
            return false;
        }
        if data.op(def1).code() == OpCode::BoolNegate {
            let vn = data.op(def1).get_in(0);
            let Some(inner) = written_def(data, vn) else {
                return false;
            };
            def1 = inner;
        }
        if data.op(def1).get_opcode(glb).is_floating_point_op() {
            if data.op(def1).num_input() != 2 {
                return false;
            }
            if functional_equality(float_var, data.op(def1).get_in(0), data) {
                return true;
            }
            if functional_equality(float_var, data.op(def1).get_in(1), data) {
                return true;
            }
            return false;
        }
        let opc = data.op(def1).code();
        if opc != OpCode::BoolAnd && opc != OpCode::BoolOr {
            return false;
        }
        for slot in 0..2 {
            let vn = data.op(def1).get_in(slot);
            let Some(def2) = written_def(data, vn) else { continue };
            if !data.op(def2).is_bool_output() {
                continue;
            }
            if !data.op(def2).get_opcode(glb).is_floating_point_op() {
                continue;
            }
            if data.op(def2).num_input() != 2 {
                continue;
            }
            if functional_equality(float_var, data.op(def2).get_in(0), data) {
                return true;
            }
            if functional_equality(float_var, data.op(def2).get_in(1), data) {
                return true;
            }
        }
        false
    }

    pub fn is_another_nan(vn: VarnodeId, data: &Funcdata) -> bool {
        let Some(mut op) = written_def(data, vn) else {
            return false;
        };
        let mut opc = data.op(op).code();
        if opc == OpCode::BoolNegate {
            let invn = data.op(op).get_in(0);
            let Some(inner) = written_def(data, invn) else {
                return false;
            };
            op = inner;
            opc = data.op(op).code();
        }
        opc == OpCode::FloatNan
    }

    pub fn test_for_comparison(
        float_var: VarnodeId,
        op: OpId,
        slot: i32,
        match_code: OpCode,
        count: &mut i32,
        data: &mut Funcdata,
        glb: &mut Architecture,
    ) -> Result<Option<VarnodeId>> {
        let opc = data.op(op).code();
        if opc == match_code {
            let vn = data.op(op).get_in(1 - slot);
            if RuleIgnoreNan::check_back_for_compare(float_var, vn, data, glb) {
                data.op_set_opcode(op, OpCode::Copy, glb);
                data.op_remove_input(op, 1);
                data.op_set_input(op, vn, 0)?;
                *count += 1;
            } else if RuleIgnoreNan::is_another_nan(vn, data) {
                return Ok(data.op(op).get_out());
            }
        } else if opc == OpCode::IntEqual || opc == OpCode::IntNotequal {
            let vn = data.op(op).get_in(1 - slot);
            if RuleIgnoreNan::check_back_for_compare(float_var, vn, data, glb) {
                let constvn = data.new_constant(1, if match_code == OpCode::BoolOr { 0 } else { 1 }, glb);
                data.op_set_input(op, constvn, slot)?;
                *count += 1;
            }
        } else if opc == OpCode::Cbranch {
            let parent = data.op(op).get_parent().expect("op without parent block");
            let mut out_dir = if match_code == OpCode::BoolOr { 0 } else { 1 };
            if data.op(op).is_boolean_flip() {
                out_dir = 1 - out_dir;
            }
            let out_branch = data.block(parent).get_out(out_dir);
            if let Some(last_op) = data.block_last_op(out_branch)
                && data.op(last_op).code() == OpCode::Cbranch
            {
                let other_branch = data.block(parent).get_out(1 - out_dir);
                if (data.block(out_branch).get_out(0) == other_branch
                    || data.block(out_branch).get_out(1) == other_branch)
                    && RuleIgnoreNan::check_back_for_compare(float_var, data.op(last_op).get_in(1), data, glb)
                {
                    let constvn = data.new_constant(1, if match_code == OpCode::BoolOr { 0 } else { 1 }, glb);
                    data.op_set_input(op, constvn, 1)?;
                    *count += 1;
                }
            }
        }
        Ok(None)
    }
}

impl Rule for RuleIgnoreNan {
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
        Some(Box::new(RuleIgnoreNan::new(self.get_group())))
    }

    fn get_op_list(&self, oplist: &mut Vec<OpCode>) {
        oplist.push(OpCode::FloatNan);
    }

    fn apply_op(&mut self, op: OpId, data: &mut Funcdata, glb: &mut Architecture) -> Result<i32> {
        if glb.nan_ignore_all {
            data.op_set_opcode(op, OpCode::Copy, glb);
            let zerovn = data.new_constant(1, 0, glb);
            data.op_set_input(op, zerovn, 0)?;
            return Ok(1);
        }
        let float_var = data.op(op).get_in(0);
        if data.vn(float_var).is_free() {
            return Ok(0);
        }
        let out1 = data.op(op).get_out().expect("op without output");
        let mut count = 0;
        let reads1 = data.vn(out1).descend().to_vec();
        for bool_read1 in reads1 {
            let mut match_code = OpCode::BoolOr;
            let out2 = if data.op(bool_read1).code() == OpCode::BoolNegate {
                match_code = OpCode::BoolAnd;
                data.op(bool_read1).get_out()
            } else {
                let slot = data.op(bool_read1).get_slot(out1);
                RuleIgnoreNan::test_for_comparison(float_var, bool_read1, slot, match_code, &mut count, data, glb)?
            };
            let Some(out2) = out2 else { continue };
            let reads2 = data.vn(out2).descend().to_vec();
            for bool_read2 in reads2 {
                let slot = data.op(bool_read2).get_slot(out2);
                let out3 =
                    RuleIgnoreNan::test_for_comparison(float_var, bool_read2, slot, match_code, &mut count, data, glb)?;
                let Some(out3) = out3 else { continue };
                let reads3 = data.vn(out3).descend().to_vec();
                for bool_read3 in reads3 {
                    let slot = data.op(bool_read3).get_slot(out3);
                    RuleIgnoreNan::test_for_comparison(float_var, bool_read3, slot, match_code, &mut count, data, glb)?;
                }
            }
        }
        Ok(if count > 0 { 1 } else { 0 })
    }
}

pub struct RuleUnsigned2Float {
    pub base: RuleBase,
}

impl RuleUnsigned2Float {
    pub fn new(group: &str) -> RuleUnsigned2Float {
        RuleUnsigned2Float {
            base: RuleBase::new(group, 0, "unsigned2float"),
        }
    }
}

impl Rule for RuleUnsigned2Float {
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
        Some(Box::new(RuleUnsigned2Float::new(self.get_group())))
    }

    fn get_op_list(&self, oplist: &mut Vec<OpCode>) {
        oplist.push(OpCode::FloatInt2float);
    }

    fn apply_op(&mut self, op: OpId, data: &mut Funcdata, glb: &mut Architecture) -> Result<i32> {
        let invn = data.op(op).get_in(0);
        let Some(orop) = written_def(data, invn) else {
            return Ok(0);
        };
        if data.op(orop).code() != OpCode::IntOr {
            return Ok(0);
        }
        let first = data.op(orop).get_in(0);
        let second = data.op(orop).get_in(1);
        if !data.vn(first).is_written() || !data.vn(second).is_written() {
            return Ok(0);
        }
        let mut shiftop = data.vn(first).get_def().expect("written varnode without defining op");
        let mut andop;
        if data.op(shiftop).code() != OpCode::IntRight {
            andop = shiftop;
            shiftop = data.vn(second).get_def().expect("written varnode without defining op");
        } else {
            andop = data.vn(second).get_def().expect("written varnode without defining op");
        }
        if data.op(shiftop).code() != OpCode::IntRight {
            return Ok(0);
        }
        if !data.vn(data.op(shiftop).get_in(1)).constant_match(1) {
            return Ok(0);
        }
        let basevn = data.op(shiftop).get_in(0);
        if data.vn(basevn).is_free() {
            return Ok(0);
        }
        if data.op(andop).code() == OpCode::IntZext {
            let Some(inner) = written_def(data, data.op(andop).get_in(0)) else {
                return Ok(0);
            };
            andop = inner;
        }
        if data.op(andop).code() != OpCode::IntAnd {
            return Ok(0);
        }
        if !data.vn(data.op(andop).get_in(1)).constant_match(1) {
            return Ok(0);
        }
        let mut vn = data.op(andop).get_in(0);
        if basevn != vn {
            let Some(subop) = written_def(data, vn) else {
                return Ok(0);
            };
            if data.op(subop).code() != OpCode::Subpiece {
                return Ok(0);
            }
            if data.vn(data.op(subop).get_in(1)).get_offset() != 0 {
                return Ok(0);
            }
            vn = data.op(subop).get_in(0);
            if basevn != vn {
                return Ok(0);
            }
        }
        let outvn = data.op(op).get_out().expect("op without output");
        let descendants = data.vn(outvn).descend().to_vec();
        for addop in descendants {
            if data.op(addop).code() != OpCode::FloatAdd {
                continue;
            }
            if data.op(addop).get_in(0) != outvn {
                continue;
            }
            if data.op(addop).get_in(1) != outvn {
                continue;
            }
            let addr = data.op(addop).get_addr().clone();
            let zextop = data.new_op(1, &addr);
            data.op_set_opcode(zextop, OpCode::IntZext, glb);
            let zextsize = TypeOpFloatInt2Float::preferred_zext_size(data.vn(basevn).get_size());
            let zextout = data.new_unique_out(zextsize, zextop, glb)?;
            data.op_set_opcode(addop, OpCode::FloatInt2float, glb);
            data.op_remove_input(addop, 1);
            data.op_set_input(zextop, basevn, 0)?;
            data.op_set_input(addop, zextout, 0)?;
            data.op_insert_before(zextop, addop);
            return Ok(1);
        }
        Ok(0)
    }
}

pub struct RuleInt2FloatCollapse {
    pub base: RuleBase,
}

impl RuleInt2FloatCollapse {
    pub fn new(group: &str) -> RuleInt2FloatCollapse {
        RuleInt2FloatCollapse {
            base: RuleBase::new(group, 0, "int2floatcollapse"),
        }
    }
}

impl Rule for RuleInt2FloatCollapse {
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
        Some(Box::new(RuleInt2FloatCollapse::new(self.get_group())))
    }

    fn get_op_list(&self, oplist: &mut Vec<OpCode>) {
        oplist.push(OpCode::FloatInt2float);
    }

    fn apply_op(&mut self, op: OpId, data: &mut Funcdata, glb: &mut Architecture) -> Result<i32> {
        let Some(zextop) = written_def(data, data.op(op).get_in(0)) else {
            return Ok(0);
        };
        if data.op(zextop).code() != OpCode::IntZext {
            return Ok(0);
        }
        let basevn = data.op(zextop).get_in(0);
        if data.vn(basevn).is_free() {
            return Ok(0);
        }
        let outvn = data.op(op).get_out().expect("op without output");
        let Some(multiop) = data.vn(outvn).lone_descend() else {
            return Ok(0);
        };
        if data.op(multiop).code() != OpCode::Multiequal {
            return Ok(0);
        }
        if data.op(multiop).num_input() != 2 {
            return Ok(0);
        }
        let slot = data.op(multiop).get_slot(outvn);
        let otherout = data.op(multiop).get_in(1 - slot);
        let Some(op2) = written_def(data, otherout) else {
            return Ok(0);
        };
        if data.op(op2).code() != OpCode::FloatInt2float {
            return Ok(0);
        }
        if basevn != data.op(op2).get_in(0) {
            return Ok(0);
        }
        let mut dir2unsigned: i32 = 0;
        let multi_parent = data.op(multiop).get_parent().expect("op without parent block");
        let Some(cond) = data.block_find_condition(multi_parent, slot, multi_parent, 1 - slot, &mut dir2unsigned)
        else {
            return Ok(0);
        };
        let Some(cbranch) = data.block_last_op(cond) else {
            return Ok(0);
        };
        if data.op(cbranch).code() != OpCode::Cbranch {
            return Ok(0);
        }
        let Some(compare) = written_def(data, data.op(cbranch).get_in(1)) else {
            return Ok(0);
        };
        if data.op(cbranch).is_boolean_flip() {
            return Ok(0);
        }
        if data.op(compare).code() != OpCode::IntSless {
            return Ok(0);
        }
        if data.vn(data.op(compare).get_in(1)).constant_match(0) {
            if data.op(compare).get_in(0) != basevn {
                return Ok(0);
            }
            if dir2unsigned != 1 {
                return Ok(0);
            }
        } else if data
            .vn(data.op(compare).get_in(0))
            .constant_match(calc_mask(data.vn(basevn).get_size()))
        {
            if data.op(compare).get_in(1) != basevn {
                return Ok(0);
            }
            if dir2unsigned == 1 {
                return Ok(0);
            }
        } else {
            return Ok(0);
        }
        let outbl = multi_parent;
        data.op_uninsert(multiop);
        data.op_set_opcode(multiop, OpCode::FloatInt2float, glb);
        data.op_remove_input(multiop, 0);
        let addr = data.op(multiop).get_addr().clone();
        let newzext = data.new_op(1, &addr);
        data.op_set_opcode(newzext, OpCode::IntZext, glb);
        let zextsize = TypeOpFloatInt2Float::preferred_zext_size(data.vn(basevn).get_size());
        let newout = data.new_unique_out(zextsize, newzext, glb)?;
        data.op_set_input(newzext, basevn, 0)?;
        data.op_set_input(multiop, newout, 0)?;
        data.op_insert_begin(multiop, outbl);
        data.op_insert_before(newzext, multiop);
        Ok(1)
    }
}

pub struct RuleFuncPtrEncoding {
    pub base: RuleBase,
}

impl RuleFuncPtrEncoding {
    pub fn new(group: &str) -> RuleFuncPtrEncoding {
        RuleFuncPtrEncoding {
            base: RuleBase::new(group, 0, "funcptrencoding"),
        }
    }
}

impl Rule for RuleFuncPtrEncoding {
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
        Some(Box::new(RuleFuncPtrEncoding::new(self.get_group())))
    }

    fn get_op_list(&self, oplist: &mut Vec<OpCode>) {
        oplist.push(OpCode::Callind);
    }

    fn apply_op(&mut self, op: OpId, data: &mut Funcdata, glb: &mut Architecture) -> Result<i32> {
        let align = glb.funcptr_align;
        if align == 0 {
            return Ok(0);
        }
        let vn = data.op(op).get_in(0);
        let Some(andop) = written_def(data, vn) else {
            return Ok(0);
        };
        if data.op(andop).code() != OpCode::IntAnd {
            return Ok(0);
        }
        let maskvn = data.op(andop).get_in(1);
        if !data.vn(maskvn).is_constant() {
            return Ok(0);
        }
        let val = data.vn(maskvn).get_offset();
        let testmask = calc_mask(data.vn(maskvn).get_size());
        let slide = (!0u64).wrapping_shl(align as u32);
        if (testmask & slide) == val {
            data.op_remove_input(andop, 1);
            data.op_set_opcode(andop, OpCode::Copy, glb);
            return Ok(1);
        }
        Ok(0)
    }
}

pub struct RuleThreeWayCompare {
    pub base: RuleBase,
}

impl RuleThreeWayCompare {
    pub fn new(group: &str) -> RuleThreeWayCompare {
        RuleThreeWayCompare {
            base: RuleBase::new(group, 0, "threewaycomp"),
        }
    }

    pub fn detect_three_way(op: OpId, is_partial: &mut bool, data: &Funcdata) -> Option<OpId> {
        let zext1;
        let zext2;
        let vn2 = data.op(op).get_in(1);
        if data.vn(vn2).is_constant() {
            let mask = calc_mask(data.vn(vn2).get_size());
            if mask != data.vn(vn2).get_offset() {
                return None;
            }
            let vn1 = data.op(op).get_in(0);
            let addop = written_def(data, vn1)?;
            if data.op(addop).code() != OpCode::IntAdd {
                return None;
            }
            zext1 = written_def(data, data.op(addop).get_in(0))?;
            if data.op(zext1).code() != OpCode::IntZext {
                return None;
            }
            zext2 = written_def(data, data.op(addop).get_in(1))?;
            if data.op(zext2).code() != OpCode::IntZext {
                return None;
            }
        } else {
            let tmpop = written_def(data, vn2)?;
            if data.op(tmpop).code() == OpCode::IntZext {
                zext2 = tmpop;
                let vn1 = data.op(op).get_in(0);
                let addop = written_def(data, vn1)?;
                if data.op(addop).code() != OpCode::IntAdd {
                    zext1 = addop;
                    if data.op(zext1).code() != OpCode::IntZext {
                        return None;
                    }
                    *is_partial = true;
                } else {
                    let tmpvn = data.op(addop).get_in(1);
                    if !data.vn(tmpvn).is_constant() {
                        return None;
                    }
                    let mask = calc_mask(data.vn(tmpvn).get_size());
                    if mask != data.vn(tmpvn).get_offset() {
                        return None;
                    }
                    zext1 = written_def(data, data.op(addop).get_in(0))?;
                    if data.op(zext1).code() != OpCode::IntZext {
                        return None;
                    }
                }
            } else if data.op(tmpop).code() == OpCode::IntAdd {
                let addop = tmpop;
                let vn1 = data.op(op).get_in(0);
                zext1 = written_def(data, vn1)?;
                if data.op(zext1).code() != OpCode::IntZext {
                    return None;
                }
                let tmpvn = data.op(addop).get_in(1);
                if !data.vn(tmpvn).is_constant() {
                    return None;
                }
                let mask = calc_mask(data.vn(tmpvn).get_size());
                if mask != data.vn(tmpvn).get_offset() {
                    return None;
                }
                zext2 = written_def(data, data.op(addop).get_in(0))?;
                if data.op(zext2).code() != OpCode::IntZext {
                    return None;
                }
            } else {
                return None;
            }
        }
        let mut lessop = written_def(data, data.op(zext1).get_in(0))?;
        let mut lessequalop = written_def(data, data.op(zext2).get_in(0))?;
        let opc = data.op(lessop).code();
        if opc != OpCode::IntLess && opc != OpCode::IntSless && opc != OpCode::FloatLess {
            std::mem::swap(&mut lessop, &mut lessequalop);
        }
        let form = RuleThreeWayCompare::test_compare_equivalence(lessop, lessequalop, data);
        if form < 0 {
            return None;
        }
        if form == 1 {
            std::mem::swap(&mut lessop, &mut lessequalop);
        }
        Some(lessop)
    }

    pub fn test_compare_equivalence(lessop: OpId, lessequalop: OpId, data: &Funcdata) -> i32 {
        let mut two_less_than;
        let less_code = data.op(lessop).code();
        let lessequal_code = data.op(lessequalop).code();
        if less_code == OpCode::IntLess {
            if lessequal_code == OpCode::IntLessequal {
                two_less_than = false;
            } else if lessequal_code == OpCode::IntLess {
                two_less_than = true;
            } else {
                return -1;
            }
        } else if less_code == OpCode::IntSless {
            if lessequal_code == OpCode::IntSlessequal {
                two_less_than = false;
            } else if lessequal_code == OpCode::IntSless {
                two_less_than = true;
            } else {
                return -1;
            }
        } else if less_code == OpCode::FloatLess {
            if lessequal_code == OpCode::FloatLessequal {
                two_less_than = false;
            } else {
                return -1;
            }
        } else {
            return -1;
        }
        let a1 = data.op(lessop).get_in(0);
        let a2 = data.op(lessequalop).get_in(0);
        let b1 = data.op(lessop).get_in(1);
        let b2 = data.op(lessequalop).get_in(1);
        let mut res = 0;
        if a1 != a2 {
            if !data.vn(a1).is_constant() || !data.vn(a2).is_constant() {
                return -1;
            }
            let a1_off = data.vn(a1).get_offset();
            let a2_off = data.vn(a2).get_offset();
            if a1_off != a2_off && two_less_than {
                if a2_off.wrapping_add(1) == a1_off {
                    two_less_than = false;
                } else if a1_off.wrapping_add(1) == a2_off {
                    two_less_than = false;
                    res = 1;
                } else {
                    return -1;
                }
            }
        }
        if b1 != b2 {
            if !data.vn(b1).is_constant() || !data.vn(b2).is_constant() {
                return -1;
            }
            let b1_off = data.vn(b1).get_offset();
            let b2_off = data.vn(b2).get_offset();
            if b1_off != b2_off && two_less_than {
                if b1_off.wrapping_add(1) == b2_off {
                    two_less_than = false;
                } else if b2_off.wrapping_add(1) == b1_off {
                    two_less_than = false;
                    res = 1;
                }
            } else {
                return -1;
            }
        }
        if two_less_than {
            return -1;
        }
        res
    }
}

impl Rule for RuleThreeWayCompare {
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
        Some(Box::new(RuleThreeWayCompare::new(self.get_group())))
    }

    fn get_op_list(&self, oplist: &mut Vec<OpCode>) {
        oplist.push(OpCode::IntSless);
        oplist.push(OpCode::IntSlessequal);
        oplist.push(OpCode::IntEqual);
        oplist.push(OpCode::IntNotequal);
    }

    fn apply_op(&mut self, op: OpId, data: &mut Funcdata, glb: &mut Architecture) -> Result<i32> {
        let mut const_slot = 0;
        let mut tmpvn = data.op(op).get_in(const_slot);
        if !data.vn(tmpvn).is_constant() {
            const_slot = 1;
            tmpvn = data.op(op).get_in(const_slot);
            if !data.vn(tmpvn).is_constant() {
                return Ok(0);
            }
        }
        let val = data.vn(tmpvn).get_offset();
        let mut form: i32 = if val <= 2 {
            val as i32 + 1
        } else if val == calc_mask(data.vn(tmpvn).get_size()) {
            0
        } else {
            return Ok(0);
        };
        tmpvn = data.op(op).get_in(1 - const_slot);
        let Some(tmpdef) = written_def(data, tmpvn) else {
            return Ok(0);
        };
        if data.op(tmpdef).code() != OpCode::IntAdd {
            return Ok(0);
        }
        let mut is_partial = false;
        let Some(lessop) = RuleThreeWayCompare::detect_three_way(tmpdef, &mut is_partial, data) else {
            return Ok(0);
        };
        if is_partial {
            if form == 0 {
                return Ok(0);
            }
            form -= 1;
        }
        form <<= 1;
        if const_slot == 1 {
            form += 1;
        }
        let mut lessform = data.op(lessop).code();
        form <<= 2;
        match data.op(op).code() {
            OpCode::IntSlessequal => form += 1,
            OpCode::IntEqual => form += 2,
            OpCode::IntNotequal => form += 3,
            _ => {}
        }
        let bvn = data.op(lessop).get_in(0);
        let avn = data.op(lessop).get_in(1);
        if !data.vn(avn).is_constant() && data.vn(avn).is_free() {
            return Ok(0);
        }
        if !data.vn(bvn).is_constant() && data.vn(bvn).is_free() {
            return Ok(0);
        }
        let lessequalform = OpCode::from_index(lessform.index() as i64 + 1).expect("invalid comparison opcode");
        match form {
            1 | 21 => {
                data.op_set_opcode(op, OpCode::IntEqual, glb);
                let zerovn = data.new_constant(1, 0, glb);
                data.op_set_input(op, zerovn, 0)?;
                let zerovn = data.new_constant(1, 0, glb);
                data.op_set_input(op, zerovn, 1)?;
            }
            4 | 16 => {
                data.op_set_opcode(op, OpCode::IntNotequal, glb);
                let zerovn = data.new_constant(1, 0, glb);
                data.op_set_input(op, zerovn, 0)?;
                let zerovn = data.new_constant(1, 0, glb);
                data.op_set_input(op, zerovn, 1)?;
            }
            2 | 5 | 6 | 12 => {
                data.op_set_opcode(op, lessform, glb);
                data.op_set_input(op, avn, 0)?;
                data.op_set_input(op, bvn, 1)?;
            }
            13 | 19 | 20 | 23 => {
                data.op_set_opcode(op, lessequalform, glb);
                data.op_set_input(op, avn, 0)?;
                data.op_set_input(op, bvn, 1)?;
            }
            8 | 17 | 18 | 22 => {
                data.op_set_opcode(op, lessform, glb);
                data.op_set_input(op, bvn, 0)?;
                data.op_set_input(op, avn, 1)?;
            }
            0 | 3 | 7 | 9 => {
                data.op_set_opcode(op, lessequalform, glb);
                data.op_set_input(op, bvn, 0)?;
                data.op_set_input(op, avn, 1)?;
            }
            10 | 14 => {
                lessform = if lessform == OpCode::FloatLess {
                    OpCode::FloatEqual
                } else {
                    OpCode::IntEqual
                };
                data.op_set_opcode(op, lessform, glb);
                data.op_set_input(op, avn, 0)?;
                data.op_set_input(op, bvn, 1)?;
            }
            11 | 15 => {
                lessform = if lessform == OpCode::FloatLess {
                    OpCode::FloatNotequal
                } else {
                    OpCode::IntNotequal
                };
                data.op_set_opcode(op, lessform, glb);
                data.op_set_input(op, avn, 0)?;
                data.op_set_input(op, bvn, 1)?;
            }
            _ => return Ok(0),
        }
        Ok(1)
    }
}

pub struct RulePopcountBoolXor {
    pub base: RuleBase,
}

impl RulePopcountBoolXor {
    pub fn new(group: &str) -> RulePopcountBoolXor {
        RulePopcountBoolXor {
            base: RuleBase::new(group, 0, "popcountboolxor"),
        }
    }

    pub fn get_boolean_result(vn: VarnodeId, bit_pos: i32, const_res: &mut i32, data: &Funcdata) -> Option<VarnodeId> {
        *const_res = -1;
        let mut vn = vn;
        let mut bit_pos = bit_pos;
        let mut mask: u64 = 1u64.wrapping_shl(bit_pos as u32);
        loop {
            if data.vn(vn).is_constant() {
                *const_res = (data.vn(vn).get_offset().wrapping_shr(bit_pos as u32) & 1) as i32;
                return None;
            }
            if !data.vn(vn).is_written() {
                return None;
            }
            if bit_pos == 0 && data.vn(vn).get_size() == 1 && data.vn(vn).get_nz_mask() == mask {
                return Some(vn);
            }
            let op = data.vn(vn).get_def().expect("written varnode without defining op");
            match data.op(op).code() {
                OpCode::IntAnd => {
                    if !data.vn(data.op(op).get_in(1)).is_constant() {
                        return None;
                    }
                    vn = data.op(op).get_in(0);
                }
                OpCode::IntXor | OpCode::IntOr => {
                    let vn0 = data.op(op).get_in(0);
                    let vn1 = data.op(op).get_in(1);
                    if (data.vn(vn0).get_nz_mask() & mask) != 0 {
                        if (data.vn(vn1).get_nz_mask() & mask) != 0 {
                            return None;
                        }
                        vn = vn0;
                    } else if (data.vn(vn1).get_nz_mask() & mask) != 0 {
                        vn = vn1;
                    } else {
                        return None;
                    }
                }
                OpCode::IntZext | OpCode::IntSext => {
                    vn = data.op(op).get_in(0);
                    if bit_pos >= data.vn(vn).get_size() * 8 {
                        return None;
                    }
                }
                OpCode::Subpiece => {
                    let shift_amount = (data.vn(data.op(op).get_in(1)).get_offset() as i32).wrapping_mul(8);
                    bit_pos += shift_amount;
                    mask = mask.wrapping_shl(shift_amount as u32);
                    vn = data.op(op).get_in(0);
                }
                OpCode::Piece => {
                    let vn0 = data.op(op).get_in(0);
                    let vn1 = data.op(op).get_in(1);
                    let shift_amount = data.vn(vn1).get_size() * 8;
                    if bit_pos >= shift_amount {
                        vn = vn0;
                        bit_pos -= shift_amount;
                        mask = mask.wrapping_shr(shift_amount as u32);
                    } else {
                        vn = vn1;
                    }
                }
                OpCode::IntLeft => {
                    let vn1 = data.op(op).get_in(1);
                    if !data.vn(vn1).is_constant() {
                        return None;
                    }
                    let shift_amount = data.vn(vn1).get_offset() as i32;
                    if shift_amount > bit_pos {
                        return None;
                    }
                    bit_pos -= shift_amount;
                    mask = mask.wrapping_shr(shift_amount as u32);
                    vn = data.op(op).get_in(0);
                }
                OpCode::IntRight | OpCode::IntSright => {
                    let vn1 = data.op(op).get_in(1);
                    if !data.vn(vn1).is_constant() {
                        return None;
                    }
                    let shift_amount = data.vn(vn1).get_offset() as i32;
                    vn = data.op(op).get_in(0);
                    bit_pos = bit_pos.wrapping_add(shift_amount);
                    if bit_pos >= data.vn(vn).get_size() * 8 {
                        return None;
                    }
                    mask = mask.wrapping_shl(shift_amount as u32);
                }
                _ => return None,
            }
        }
    }
}

impl Rule for RulePopcountBoolXor {
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
        Some(Box::new(RulePopcountBoolXor::new(self.get_group())))
    }

    fn get_op_list(&self, oplist: &mut Vec<OpCode>) {
        oplist.push(OpCode::Popcount);
    }

    fn apply_op(&mut self, op: OpId, data: &mut Funcdata, glb: &mut Architecture) -> Result<i32> {
        let out_vn = data.op(op).get_out().expect("op without output");
        let descendants = data.vn(out_vn).descend().to_vec();
        for base_op in descendants {
            if data.op(base_op).code() != OpCode::IntAnd {
                continue;
            }
            let tmp_vn = data.op(base_op).get_in(1);
            if !data.vn(tmp_vn).is_constant() {
                continue;
            }
            if data.vn(tmp_vn).get_offset() != 1 {
                continue;
            }
            if data.vn(tmp_vn).get_size() != 1 {
                continue;
            }
            let in_vn = data.op(op).get_in(0);
            if !data.vn(in_vn).is_written() {
                return Ok(0);
            }
            let nz_mask = data.vn(in_vn).get_nz_mask();
            let count = popcount(nz_mask);
            if count == 1 {
                let least_pos = leastsigbit_set(nz_mask);
                let mut const_res = 0;
                let Some(b1) = RulePopcountBoolXor::get_boolean_result(in_vn, least_pos, &mut const_res, data) else {
                    continue;
                };
                data.op_set_opcode(base_op, OpCode::Copy, glb);
                data.op_remove_input(base_op, 1);
                data.op_set_input(base_op, b1, 0)?;
                return Ok(1);
            }
            if count == 2 {
                let pos0 = leastsigbit_set(nz_mask);
                let pos1 = mostsigbit_set(nz_mask);
                let mut const_res0 = 0;
                let mut const_res1 = 0;
                let b1 = RulePopcountBoolXor::get_boolean_result(in_vn, pos0, &mut const_res0, data);
                if b1.is_none() && const_res0 != 1 {
                    continue;
                }
                let b2 = RulePopcountBoolXor::get_boolean_result(in_vn, pos1, &mut const_res1, data);
                if b2.is_none() && const_res1 != 1 {
                    continue;
                }
                if b1.is_none() && b2.is_none() {
                    continue;
                }
                let b1 = match b1 {
                    Some(b1) => b1,
                    None => data.new_constant(1, 1, glb),
                };
                let b2 = match b2 {
                    Some(b2) => b2,
                    None => data.new_constant(1, 1, glb),
                };
                data.op_set_opcode(base_op, OpCode::IntXor, glb);
                data.op_set_input(base_op, b1, 0)?;
                data.op_set_input(base_op, b2, 1)?;
                return Ok(1);
            }
        }
        Ok(0)
    }
}

pub struct RulePiecePathology {
    pub base: RuleBase,
}

impl RulePiecePathology {
    pub fn new(group: &str) -> RulePiecePathology {
        RulePiecePathology {
            base: RuleBase::new(group, 0, "piecepathology"),
        }
    }

    pub fn is_pathology(vn: VarnodeId, data: &mut Funcdata) -> bool {
        let mut worklist: Vec<OpId> = Vec::new();
        let mut pos = 0;
        let mut slot = 0;
        let mut res = false;
        let mut vn = vn;
        loop {
            if data.vn(vn).is_input() && !data.vn(vn).is_persist() {
                res = true;
                break;
            }
            let mut cur = data.vn(vn).get_def();
            while !res {
                let Some(op) = cur else { break };
                match data.op(op).code() {
                    OpCode::Copy => {
                        vn = data.op(op).get_in(0);
                        cur = data.vn(vn).get_def();
                    }
                    OpCode::Multiequal => {
                        if !data.op(op).is_mark() {
                            data.op_mut(op).set_mark();
                            worklist.push(op);
                        }
                        cur = None;
                    }
                    OpCode::Indirect => {
                        let iopvn = data.op(op).get_in(1);
                        if data.vn(iopvn).get_space().expect("varnode without space").get_type() == SpaceType::Iop {
                            let call_op = PcodeOp::get_op_from_const(data.vn(iopvn).get_addr());
                            if data.op(call_op).is_call()
                                && let Some(fspec) = data.get_call_specs_op(call_op)
                                && !data.call_spec(fspec).is_output_active()
                            {
                                res = true;
                            }
                        }
                        cur = None;
                    }
                    OpCode::Call | OpCode::Callind => {
                        if let Some(fspec) = data.get_call_specs_op(op)
                            && !data.call_spec(fspec).is_output_active()
                        {
                            res = true;
                        }
                    }
                    _ => {
                        cur = None;
                    }
                }
            }
            if res {
                break;
            }
            if pos >= worklist.len() {
                break;
            }
            let op = worklist[pos];
            if slot < data.op(op).num_input() {
                vn = data.op(op).get_in(slot);
                slot += 1;
            } else {
                pos += 1;
                if pos >= worklist.len() {
                    break;
                }
                vn = data.op(worklist[pos]).get_in(0);
                slot = 1;
            }
        }
        for &op in worklist.iter() {
            data.op_mut(op).clear_mark();
        }
        res
    }

    pub fn trace_pathology_forward(op: OpId, data: &mut Funcdata, glb: &mut Architecture) -> i32 {
        let mut count = 0;
        let mut worklist: Vec<OpId> = Vec::new();
        let mut pos = 0;
        data.op_mut(op).set_mark();
        worklist.push(op);
        while pos < worklist.len() {
            let cur_op = worklist[pos];
            pos += 1;
            let out_vn = data.op(cur_op).get_out().expect("op without output");
            let descendants = data.vn(out_vn).descend().to_vec();
            for read_op in descendants {
                match data.op(read_op).code() {
                    OpCode::Copy | OpCode::Indirect | OpCode::Multiequal if !data.op(read_op).is_mark() => {
                        data.op_mut(read_op).set_mark();
                        worklist.push(read_op);
                    }
                    OpCode::Call | OpCode::Callind => {
                        if let Some(fc) = data.get_call_specs_op(read_op)
                            && !data.call_spec(fc).is_input_active()
                            && !data.call_spec_mut(fc).is_input_locked(glb)
                        {
                            let bytes_consumed = data.vn(data.op(op).get_in(1)).get_size();
                            for slot in 1..data.op(read_op).num_input() {
                                if data.op(read_op).get_in(slot) == out_vn
                                    && data.call_spec_mut(fc).set_input_bytes_consumed(slot, bytes_consumed)
                                {
                                    count += 1;
                                }
                            }
                        }
                    }
                    OpCode::Return if !data.get_func_proto().is_output_locked(glb) => {
                        let consumed = data.vn(data.op(op).get_in(1)).get_size();
                        if data.get_func_proto_mut().set_return_bytes_consumed(consumed) {
                            count += 1;
                        }
                    }
                    _ => {}
                }
            }
        }
        for &marked in worklist.iter() {
            data.op_mut(marked).clear_mark();
        }
        count
    }
}

impl Rule for RulePiecePathology {
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
        Some(Box::new(RulePiecePathology::new(self.get_group())))
    }

    fn get_op_list(&self, oplist: &mut Vec<OpCode>) {
        oplist.push(OpCode::Piece);
    }

    fn apply_op(&mut self, op: OpId, data: &mut Funcdata, glb: &mut Architecture) -> Result<i32> {
        let vn = data.op(op).get_in(0);
        let Some(sub_op) = written_def(data, vn) else {
            return Ok(0);
        };
        let opc = data.op(sub_op).code();
        if opc == OpCode::Subpiece {
            if data.vn(data.op(sub_op).get_in(1)).get_offset() == 0 {
                return Ok(0);
            }
            if !RulePiecePathology::is_pathology(data.op(sub_op).get_in(0), data) {
                return Ok(0);
            }
        } else if opc == OpCode::Indirect {
            if !data.op(sub_op).is_indirect_creation() {
                return Ok(0);
            }
            let lsb_vn = data.op(op).get_in(1);
            let Some(lsb_op) = written_def(data, lsb_vn) else {
                return Ok(0);
            };
            if (data.op(lsb_op).get_eval_type() & (PcodeOp::BINARY | PcodeOp::UNARY)) == 0 {
                if !data.op(lsb_op).is_call() {
                    return Ok(0);
                }
                let Some(fc) = data.get_call_specs_op(lsb_op) else {
                    return Ok(0);
                };
                if !data.call_spec(fc).is_output_locked(glb) {
                    return Ok(0);
                }
            }
            let mut addr = data.vn(lsb_vn).get_addr().clone();
            if addr.get_space().expect("address without space").is_big_endian() {
                addr = addr.sub(data.vn(vn).get_size() as i64);
            } else {
                addr = addr.add(data.vn(lsb_vn).get_size() as i64);
            }
            if addr != *data.vn(vn).get_addr() {
                return Ok(0);
            }
        } else {
            return Ok(0);
        }
        Ok(RulePiecePathology::trace_pathology_forward(op, data, glb))
    }
}

pub struct RuleXorSwap {
    pub base: RuleBase,
}

impl RuleXorSwap {
    pub fn new(group: &str) -> RuleXorSwap {
        RuleXorSwap {
            base: RuleBase::new(group, 0, "xorswap"),
        }
    }
}

impl Rule for RuleXorSwap {
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
        Some(Box::new(RuleXorSwap::new(self.get_group())))
    }

    fn get_op_list(&self, oplist: &mut Vec<OpCode>) {
        oplist.push(OpCode::IntXor);
    }

    fn apply_op(&mut self, op: OpId, data: &mut Funcdata, glb: &mut Architecture) -> Result<i32> {
        for index in 0..2 {
            let vn = data.op(op).get_in(index);
            let Some(op2) = written_def(data, vn) else { continue };
            if data.op(op2).code() != OpCode::IntXor {
                continue;
            }
            let othervn = data.op(op).get_in(1 - index);
            let vn0 = data.op(op2).get_in(0);
            let vn1 = data.op(op2).get_in(1);
            if othervn == vn0 && !data.vn(vn1).is_free() {
                data.op_remove_input(op, 1);
                data.op_set_opcode(op, OpCode::Copy, glb);
                data.op_set_input(op, vn1, 0)?;
                return Ok(1);
            } else if othervn == vn1 && !data.vn(vn0).is_free() {
                data.op_remove_input(op, 1);
                data.op_set_opcode(op, OpCode::Copy, glb);
                data.op_set_input(op, vn0, 0)?;
                return Ok(1);
            }
        }
        Ok(0)
    }
}

pub struct RuleLzcountShiftBool {
    pub base: RuleBase,
}

impl RuleLzcountShiftBool {
    pub fn new(group: &str) -> RuleLzcountShiftBool {
        RuleLzcountShiftBool {
            base: RuleBase::new(group, 0, "lzcountshiftbool"),
        }
    }
}

impl Rule for RuleLzcountShiftBool {
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
        Some(Box::new(RuleLzcountShiftBool::new(self.get_group())))
    }

    fn get_op_list(&self, oplist: &mut Vec<OpCode>) {
        oplist.push(OpCode::Lzcount);
    }

    fn apply_op(&mut self, op: OpId, data: &mut Funcdata, glb: &mut Architecture) -> Result<i32> {
        let out_vn = data.op(op).get_out().expect("op without output");
        let invn = data.op(op).get_in(0);
        let max_return = (8 * data.vn(invn).get_size()) as i64 as u64;
        if popcount(max_return) != 1 {
            return Ok(0);
        }
        let descendants = data.vn(out_vn).descend().to_vec();
        for base_op in descendants {
            let code = data.op(base_op).code();
            if code != OpCode::IntRight && code != OpCode::IntSright {
                continue;
            }
            let vn1 = data.op(base_op).get_in(1);
            if !data.vn(vn1).is_constant() {
                continue;
            }
            let shift = data.vn(vn1).get_offset();
            if max_return.wrapping_shr(shift as u32) == 1 {
                let addr = data.op(base_op).get_addr().clone();
                let new_op = data.new_op(2, &addr);
                data.op_set_opcode(new_op, OpCode::IntEqual, glb);
                let zerovn = data.new_constant(data.vn(invn).get_size(), 0, glb);
                data.op_set_input(new_op, invn, 0)?;
                data.op_set_input(new_op, zerovn, 1)?;
                let eq_res_vn = data.new_unique_out(1, new_op, glb)?;
                data.op_insert_before(new_op, base_op);
                data.op_remove_input(base_op, 1);
                if data
                    .vn(data.op(base_op).get_out().expect("op without output"))
                    .get_size()
                    == 1
                {
                    data.op_set_opcode(base_op, OpCode::Copy, glb);
                } else {
                    data.op_set_opcode(base_op, OpCode::IntZext, glb);
                }
                data.op_set_input(base_op, eq_res_vn, 0)?;
                return Ok(1);
            }
        }
        Ok(0)
    }
}

pub struct RuleFloatSign {
    pub base: RuleBase,
}

impl RuleFloatSign {
    pub fn new(group: &str) -> RuleFloatSign {
        RuleFloatSign {
            base: RuleBase::new(group, 0, "floatsign"),
        }
    }
}

impl Rule for RuleFloatSign {
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
        Some(Box::new(RuleFloatSign::new(self.get_group())))
    }

    fn get_op_list(&self, oplist: &mut Vec<OpCode>) {
        oplist.extend_from_slice(&[
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
            OpCode::FloatFloat2float,
            OpCode::FloatCeil,
            OpCode::FloatFloor,
            OpCode::FloatRound,
            OpCode::FloatInt2float,
            OpCode::FloatTrunc,
        ]);
    }

    fn apply_op(&mut self, op: OpId, data: &mut Funcdata, glb: &mut Architecture) -> Result<i32> {
        let mut res = 0;
        let opc = data.op(op).code();
        if opc != OpCode::FloatInt2float {
            let vn = data.op(op).get_in(0);
            if let Some(sign_op) = written_def(data, vn) {
                let res_code = float_sign_manipulation(sign_op, data);
                if res_code != OpCode::Max {
                    data.op_remove_input(sign_op, 1);
                    data.op_set_opcode(sign_op, res_code, glb);
                    res = 1;
                }
            }
            if data.op(op).num_input() == 2 {
                let vn = data.op(op).get_in(1);
                if let Some(sign_op) = written_def(data, vn) {
                    let res_code = float_sign_manipulation(sign_op, data);
                    if res_code != OpCode::Max {
                        data.op_remove_input(sign_op, 1);
                        data.op_set_opcode(sign_op, res_code, glb);
                        res = 1;
                    }
                }
            }
        }
        if data.op(op).is_bool_output() || opc == OpCode::FloatTrunc {
            return Ok(res);
        }
        let outvn = data.op(op).get_out().expect("op without output");
        let descendants = data.vn(outvn).descend().to_vec();
        for read_op in descendants {
            let res_code = float_sign_manipulation(read_op, data);
            if res_code != OpCode::Max {
                data.op_remove_input(read_op, 1);
                data.op_set_opcode(read_op, res_code, glb);
                res = 1;
            }
        }
        Ok(res)
    }
}

pub struct RuleFloatSignCleanup {
    pub base: RuleBase,
}

impl RuleFloatSignCleanup {
    pub fn new(group: &str) -> RuleFloatSignCleanup {
        RuleFloatSignCleanup {
            base: RuleBase::new(group, 0, "floatsigncleanup"),
        }
    }
}

impl Rule for RuleFloatSignCleanup {
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
        Some(Box::new(RuleFloatSignCleanup::new(self.get_group())))
    }

    fn get_op_list(&self, oplist: &mut Vec<OpCode>) {
        oplist.push(OpCode::IntAnd);
        oplist.push(OpCode::IntXor);
    }

    fn apply_op(&mut self, op: OpId, data: &mut Funcdata, glb: &mut Architecture) -> Result<i32> {
        let outvn = data.op(op).get_out().expect("op without output");
        if types(glb).get(data.vn(outvn).get_type()).get_metatype() != TypeMetatype::Float {
            return Ok(0);
        }
        let opc = float_sign_manipulation(op, data);
        if opc == OpCode::Max {
            return Ok(0);
        }
        data.op_remove_input(op, 1);
        data.op_set_opcode(op, opc, glb);
        Ok(1)
    }
}

pub struct RuleOrCompare {
    pub base: RuleBase,
}

impl RuleOrCompare {
    pub fn new(group: &str) -> RuleOrCompare {
        RuleOrCompare {
            base: RuleBase::new(group, 0, "orcompare"),
        }
    }
}

impl Rule for RuleOrCompare {
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
        Some(Box::new(RuleOrCompare::new(self.get_group())))
    }

    fn get_op_list(&self, oplist: &mut Vec<OpCode>) {
        oplist.push(OpCode::IntOr);
    }

    fn apply_op(&mut self, op: OpId, data: &mut Funcdata, glb: &mut Architecture) -> Result<i32> {
        let outvn = data.op(op).get_out().expect("op without output");
        let mut has_compares = false;
        for &comp_op in data.vn(outvn).descend() {
            let opc = data.op(comp_op).code();
            if opc != OpCode::IntEqual && opc != OpCode::IntNotequal {
                return Ok(0);
            }
            if !data.vn(data.op(comp_op).get_in(1)).constant_match(0) {
                return Ok(0);
            }
            has_compares = true;
        }
        if !has_compares {
            return Ok(0);
        }
        let vvn = data.op(op).get_in(0);
        let wvn = data.op(op).get_in(1);
        if data.vn(vvn).is_free() {
            return Ok(0);
        }
        if data.vn(wvn).is_free() {
            return Ok(0);
        }
        let descendants = data.vn(outvn).descend().to_vec();
        for equal_op in descendants {
            let opc = data.op(equal_op).code();
            let zero_v = data.new_constant(data.vn(vvn).get_size(), 0, glb);
            let zero_w = data.new_constant(data.vn(wvn).get_size(), 0, glb);
            let addr = data.op(equal_op).get_addr().clone();
            let eq_v = data.new_op(2, &addr);
            data.op_set_opcode(eq_v, opc, glb);
            data.op_set_input(eq_v, vvn, 0)?;
            data.op_set_input(eq_v, zero_v, 1)?;
            let eq_w = data.new_op(2, &addr);
            data.op_set_opcode(eq_w, opc, glb);
            data.op_set_input(eq_w, wvn, 0)?;
            data.op_set_input(eq_w, zero_w, 1)?;
            let eq_v_out = data.new_unique_out(1, eq_v, glb)?;
            let eq_w_out = data.new_unique_out(1, eq_w, glb)?;
            data.op_insert_before(eq_v, equal_op);
            data.op_insert_before(eq_w, equal_op);
            let combined = if opc == OpCode::IntEqual {
                OpCode::BoolAnd
            } else {
                OpCode::BoolOr
            };
            data.op_set_opcode(equal_op, combined, glb);
            data.op_set_input(equal_op, eq_v_out, 0)?;
            data.op_set_input(equal_op, eq_w_out, 1)?;
        }
        Ok(1)
    }
}

pub struct RuleExpandLoad {
    pub base: RuleBase,
}

impl RuleExpandLoad {
    pub fn new(group: &str) -> RuleExpandLoad {
        RuleExpandLoad {
            base: RuleBase::new(group, 0, "expandload"),
        }
    }

    pub fn check_and_comparison(vn: VarnodeId, data: &Funcdata) -> bool {
        for &op in data.vn(vn).descend() {
            if data.op(op).code() != OpCode::IntAnd {
                return false;
            }
            if !data.vn(data.op(op).get_in(1)).is_constant() {
                return false;
            }
            let outvn = data.op(op).get_out().expect("op without output");
            let Some(comp_op) = data.vn(outvn).lone_descend() else {
                return false;
            };
            let opc = data.op(comp_op).code();
            if opc != OpCode::IntEqual && opc != OpCode::IntNotequal {
                return false;
            }
            if !data.vn(data.op(comp_op).get_in(1)).is_constant() {
                return false;
            }
        }
        true
    }

    pub fn modify_and_comparison(
        data: &mut Funcdata,
        old_vn: VarnodeId,
        new_vn: VarnodeId,
        dt: TypeId,
        offset: i32,
        glb: &mut Architecture,
    ) -> Result<()> {
        let shift = (8 * offset) as u32;
        let dt_size = types(glb).get(dt).get_size();
        let and_ops = data.vn(old_vn).descend().to_vec();
        for and_op in and_ops {
            let and_out = data.op(and_op).get_out().expect("op without output");
            let comp_op = data
                .vn(and_out)
                .lone_descend()
                .expect("comparison without lone descendant");
            let mut new_off = data.vn(data.op(and_op).get_in(1)).get_offset();
            new_off = new_off.wrapping_shl(shift);
            let mut vn = data.new_constant(dt_size, new_off, glb);
            data.vn_update_type(vn, dt);
            data.op_set_input(and_op, new_vn, 0)?;
            data.op_set_input(and_op, vn, 1)?;
            new_off = data.vn(data.op(comp_op).get_in(1)).get_offset();
            new_off = new_off.wrapping_shl(shift);
            vn = data.new_constant(dt_size, new_off, glb);
            data.vn_update_type(vn, dt);
            data.op_set_input(comp_op, vn, 1)?;
        }
        Ok(())
    }
}

impl Rule for RuleExpandLoad {
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
        Some(Box::new(RuleExpandLoad::new(self.get_group())))
    }

    fn get_op_list(&self, oplist: &mut Vec<OpCode>) {
        oplist.push(OpCode::Load);
    }

    fn apply_op(&mut self, op: OpId, data: &mut Funcdata, glb: &mut Architecture) -> Result<i32> {
        let out_vn = data.op(op).get_out().expect("op without output");
        let out_size = data.vn(out_vn).get_size();
        let mut root_ptr = data.op(op).get_in(1);
        let mut add_op: Option<OpId> = None;
        let mut offset: i32 = 0;
        let pointer_type;
        match written_def(data, root_ptr) {
            Some(def_op)
                if data.op(def_op).code() == OpCode::IntAdd && data.vn(data.op(def_op).get_in(1)).is_constant() =>
            {
                add_op = Some(def_op);
                root_ptr = data.op(def_op).get_in(0);
                let off = data.vn(data.op(def_op).get_in(1)).get_offset();
                if off > 16 {
                    return Ok(0);
                }
                offset = off as i32;
                let def_out = data.op(def_op).get_out().expect("op without output");
                if data.vn(def_out).lone_descend().is_none() {
                    return Ok(0);
                }
                pointer_type = data.vn_get_type_read_facing(root_ptr, def_op, glb);
            }
            _ => {
                pointer_type = data.vn_get_type_read_facing(root_ptr, op, glb);
            }
        }
        let factory = types(glb);
        if factory.get(pointer_type).get_metatype() != TypeMetatype::Ptr {
            return Ok(0);
        }
        let mut el_type = factory.get(pointer_type).get_ptr_to();
        let el_size = factory.get(el_type).get_size();
        if el_size <= out_size {
            return Ok(0);
        }
        if el_size < out_size + offset {
            return Ok(0);
        }
        let meta = factory.get(el_type).get_metatype();
        if meta == TypeMetatype::Unknown
            || meta == TypeMetatype::Struct
            || meta == TypeMetatype::Array
            || meta == TypeMetatype::Union
            || meta == TypeMetatype::PartialStruct
            || meta == TypeMetatype::PartialUnion
        {
            return Ok(0);
        }
        let add_form = RuleExpandLoad::check_and_comparison(out_vn, data);
        let spc = data
            .vn(data.op(op).get_in(0))
            .get_space_from_const(&glb.manager)
            .expect("load operand without space");
        let mut lsb_cut = 0;
        if add_form {
            if spc.is_big_endian() {
                lsb_cut = el_size - out_size - offset;
            } else {
                lsb_cut = offset;
            }
        } else {
            if meta != TypeMetatype::Int && meta != TypeMetatype::Uint {
                return Ok(0);
            }
            let out_type = data.vn_get_type_def_facing(out_vn, glb);
            let out_meta = types(glb).get(out_type).get_metatype();
            if out_meta != TypeMetatype::Int
                && out_meta != TypeMetatype::Uint
                && out_meta != TypeMetatype::Unknown
                && out_meta != TypeMetatype::Bool
            {
                return Ok(0);
            }
            if spc.is_big_endian() {
                if out_size + offset != el_size {
                    return Ok(0);
                }
            } else if offset != 0 {
                return Ok(0);
            }
        }
        let new_out = data.new_unique(el_size, Some(el_type), glb);
        data.op_set_output(op, new_out, glb)?;
        if let Some(add_op) = add_op {
            data.op_set_input(op, root_ptr, 1)?;
            data.op_destroy(add_op)?;
        }
        if add_form {
            if meta != TypeMetatype::Int && meta != TypeMetatype::Uint {
                el_type = types_mut(glb).get_base(el_size, TypeMetatype::Uint)?;
            }
            RuleExpandLoad::modify_and_comparison(data, out_vn, new_out, el_type, lsb_cut, glb)?;
        } else {
            let addr = data.op(op).get_addr().clone();
            let sub_op = data.new_op(2, &addr);
            data.op_set_opcode(sub_op, OpCode::Subpiece, glb);
            data.op_set_input(sub_op, new_out, 0)?;
            let zerovn = data.new_constant(4, 0, glb);
            data.op_set_input(sub_op, zerovn, 1)?;
            data.op_set_output(sub_op, out_vn, glb)?;
            data.op_insert_after(sub_op, op);
        }
        Ok(1)
    }
}
