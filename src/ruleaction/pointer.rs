use super::{AddTreeState, types, types_mut, written_def};
use crate::action::{ActionGroupList, Rule, RuleBase};
use crate::address::*;
use crate::architecture::Architecture;
use crate::database::SymbolKind;
use crate::error::Result;
use crate::funcdata::Funcdata;
use crate::merge::Merge;
use crate::op::{OpId, PieceNode};
use crate::opcodes::OpCode;
use crate::opcodes::get_booleanflip;
use crate::space::{AddrSpace, SpaceType};
use crate::types::TypeId;
use crate::types::{Datatype, TypeMetatype};
use crate::varnode::VarnodeId;

pub struct RuleHumptyDumpty {
    pub base: RuleBase,
}

impl RuleHumptyDumpty {
    pub fn new(group: &str) -> RuleHumptyDumpty {
        RuleHumptyDumpty {
            base: RuleBase::new(group, 0, "humptydumpty"),
        }
    }
}

impl Rule for RuleHumptyDumpty {
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
        Some(Box::new(RuleHumptyDumpty::new(self.get_group())))
    }

    fn get_op_list(&self, oplist: &mut Vec<OpCode>) {
        oplist.push(OpCode::Piece);
    }

    fn apply_op(&mut self, op: OpId, data: &mut Funcdata, glb: &mut Architecture) -> Result<i32> {
        let vn1 = data.op(op).get_in(0);
        let Some(sub1) = written_def(data, vn1) else {
            return Ok(0);
        };
        if data.op(sub1).code() != OpCode::Subpiece {
            return Ok(0);
        }
        let vn2 = data.op(op).get_in(1);
        let Some(sub2) = written_def(data, vn2) else {
            return Ok(0);
        };
        if data.op(sub2).code() != OpCode::Subpiece {
            return Ok(0);
        }
        let root = data.op(sub1).get_in(0);
        if root != data.op(sub2).get_in(0) {
            return Ok(0);
        }
        let pos1 = data.vn(data.op(sub1).get_in(1)).get_offset();
        let pos2 = data.vn(data.op(sub2).get_in(1)).get_offset();
        let size1 = data.vn(vn1).get_size();
        let size2 = data.vn(vn2).get_size();
        if pos1 != pos2.wrapping_add(size2 as i64 as u64) {
            return Ok(0);
        }
        if pos2 == 0 && size1 + size2 == data.vn(root).get_size() {
            data.op_remove_input(op, 1);
            data.op_set_input(op, root, 0)?;
            data.op_set_opcode(op, OpCode::Copy, glb);
        } else {
            data.op_set_input(op, root, 0)?;
            let constsize = data.vn(data.op(sub2).get_in(1)).get_size();
            let constvn = data.new_constant(constsize, pos2, glb);
            data.op_set_input(op, constvn, 1)?;
            data.op_set_opcode(op, OpCode::Subpiece, glb);
        }
        Ok(1)
    }
}

pub struct RuleDumptyHump {
    pub base: RuleBase,
}

impl RuleDumptyHump {
    pub fn new(group: &str) -> RuleDumptyHump {
        RuleDumptyHump {
            base: RuleBase::new(group, 0, "dumptyhump"),
        }
    }
}

impl Rule for RuleDumptyHump {
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
        Some(Box::new(RuleDumptyHump::new(self.get_group())))
    }

    fn get_op_list(&self, oplist: &mut Vec<OpCode>) {
        oplist.push(OpCode::Subpiece);
    }

    fn apply_op(&mut self, op: OpId, data: &mut Funcdata, glb: &mut Architecture) -> Result<i32> {
        let base = data.op(op).get_in(0);
        let Some(pieceop) = written_def(data, base) else {
            return Ok(0);
        };
        if data.op(pieceop).code() != OpCode::Piece {
            return Ok(0);
        }
        let mut offset = data.vn(data.op(op).get_in(1)).get_offset() as i32;
        let outsize = data.vn(data.op(op).get_out().expect("op without output")).get_size();
        let vn1 = data.op(pieceop).get_in(0);
        let vn2 = data.op(pieceop).get_in(1);
        let vn2size = data.vn(vn2).get_size();
        let vn = if offset < vn2size {
            if offset + outsize > vn2size {
                return Ok(0);
            }
            vn2
        } else {
            offset -= vn2size;
            vn1
        };
        if data.vn(vn).is_free() && !data.vn(vn).is_constant() {
            return Ok(0);
        }
        if offset == 0 && outsize == data.vn(vn).get_size() {
            data.op_set_opcode(op, OpCode::Copy, glb);
            data.op_remove_input(op, 1);
            data.op_set_input(op, vn, 0)?;
        } else {
            data.op_set_input(op, vn, 0)?;
            let constvn = data.new_constant(4, offset as i64 as u64, glb);
            data.op_set_input(op, constvn, 1)?;
        }
        Ok(1)
    }
}

pub struct RuleHumptyOr {
    pub base: RuleBase,
}

impl RuleHumptyOr {
    pub fn new(group: &str) -> RuleHumptyOr {
        RuleHumptyOr {
            base: RuleBase::new(group, 0, "humptyor"),
        }
    }
}

impl Rule for RuleHumptyOr {
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
        Some(Box::new(RuleHumptyOr::new(self.get_group())))
    }

    fn get_op_list(&self, oplist: &mut Vec<OpCode>) {
        oplist.push(OpCode::IntOr);
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
        let and1 = data.vn(vn1).get_def().expect("written varnode without defining op");
        if data.op(and1).code() != OpCode::IntAnd {
            return Ok(0);
        }
        let and2 = data.vn(vn2).get_def().expect("written varnode without defining op");
        if data.op(and2).code() != OpCode::IntAnd {
            return Ok(0);
        }
        let mut avn = data.op(and1).get_in(0);
        let mut bvn = data.op(and1).get_in(1);
        let mut cvn = data.op(and2).get_in(0);
        let dvn = data.op(and2).get_in(1);
        if avn == cvn {
            cvn = dvn;
        } else if avn == dvn {
        } else if bvn == cvn {
            bvn = avn;
            avn = cvn;
            cvn = dvn;
        } else if bvn == dvn {
            bvn = avn;
            avn = dvn;
        } else {
            return Ok(0);
        }
        if data.vn(bvn).is_constant() && data.vn(cvn).is_constant() {
            let totalbits = data.vn(bvn).get_offset() | data.vn(cvn).get_offset();
            if totalbits == calc_mask(data.vn(avn).get_size()) {
                data.op_set_opcode(op, OpCode::Copy, glb);
                data.op_remove_input(op, 1);
                data.op_set_input(op, avn, 0)?;
            } else {
                data.op_set_opcode(op, OpCode::IntAnd, glb);
                data.op_set_input(op, avn, 0)?;
                let newconst = data.new_constant(data.vn(avn).get_size(), totalbits, glb);
                data.op_set_input(op, newconst, 1)?;
            }
        } else {
            if !data.vn(bvn).is_heritage_known() {
                return Ok(0);
            }
            if !data.vn(cvn).is_heritage_known() {
                return Ok(0);
            }
            let a_mask = data.vn(avn).get_nz_mask();
            if (data.vn(bvn).get_nz_mask() & a_mask) == 0 {
                return Ok(0);
            }
            if (data.vn(cvn).get_nz_mask() & a_mask) == 0 {
                return Ok(0);
            }
            let addr = data.op(op).get_addr().clone();
            let new_or_op = data.new_op(2, &addr);
            data.op_set_opcode(new_or_op, OpCode::IntOr, glb);
            let or_vn = data.new_unique_out(data.vn(avn).get_size(), new_or_op, glb)?;
            data.op_set_input(new_or_op, bvn, 0)?;
            data.op_set_input(new_or_op, cvn, 1)?;
            data.op_insert_before(new_or_op, op);
            data.op_set_input(op, avn, 0)?;
            data.op_set_input(op, or_vn, 1)?;
            data.op_set_opcode(op, OpCode::IntAnd, glb);
        }
        Ok(1)
    }
}

pub struct RuleSwitchSingle {
    pub base: RuleBase,
}

impl RuleSwitchSingle {
    pub fn new(group: &str) -> RuleSwitchSingle {
        RuleSwitchSingle {
            base: RuleBase::new(group, 0, "switchsingle"),
        }
    }
}

impl Rule for RuleSwitchSingle {
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
        Some(Box::new(RuleSwitchSingle::new(self.get_group())))
    }

    fn get_op_list(&self, oplist: &mut Vec<OpCode>) {
        oplist.push(OpCode::Branchind);
    }

    fn apply_op(&mut self, op: OpId, data: &mut Funcdata, glb: &mut Architecture) -> Result<i32> {
        let bb = data.op(op).get_parent().expect("op without parent block");
        if data.block(bb).size_out() != 1 {
            return Ok(0);
        }
        let Some(jt) = data.find_jump_table(op) else {
            return Ok(0);
        };
        let table = data.jump_table(jt);
        if table.num_entries() == 0 {
            return Ok(0);
        }
        if !table.is_labelled() {
            return Ok(0);
        }
        let addr = table.get_address_by_index(0);
        let mut needwarning = false;
        let mut allcasesmatch = false;
        let num_entries = table.num_entries();
        if num_entries != 1 {
            needwarning = true;
            allcasesmatch = true;
            for index in 1..num_entries {
                if table.get_address_by_index(index) != addr {
                    allcasesmatch = false;
                    break;
                }
            }
        }
        if !data.vn(data.op(op).get_in(0)).is_constant() {
            needwarning = true;
        }
        if needwarning {
            let mut message = String::from("Switch with 1 destination removed at ");
            data.op(op).get_addr().print_raw(&mut message);
            if allcasesmatch {
                message.push_str(&format!(" : {} cases all go to same destination", num_entries));
            }
            data.warning_header(&message, glb);
        }
        data.op_set_opcode(op, OpCode::Branch, glb);
        let coderef = data.new_code_ref(&addr, glb);
        data.op_set_input(op, coderef, 0)?;
        data.remove_jump_table(jt);
        let structure = data.get_structure();
        data.block_clear(structure);
        Ok(1)
    }
}

pub struct RuleCondNegate {
    pub base: RuleBase,
}

impl RuleCondNegate {
    pub fn new(group: &str) -> RuleCondNegate {
        RuleCondNegate {
            base: RuleBase::new(group, 0, "condnegate"),
        }
    }
}

impl Rule for RuleCondNegate {
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
        Some(Box::new(RuleCondNegate::new(self.get_group())))
    }

    fn get_op_list(&self, oplist: &mut Vec<OpCode>) {
        oplist.push(OpCode::Cbranch);
    }

    fn apply_op(&mut self, op: OpId, data: &mut Funcdata, glb: &mut Architecture) -> Result<i32> {
        if !data.op(op).is_boolean_flip() {
            return Ok(0);
        }
        if data.op_normalize_flip(op, glb)? {
            return Ok(1);
        }
        let vn = data.op(op).get_in(1);
        let addr = data.op(op).get_addr().clone();
        let newop = data.new_op(1, &addr);
        data.op_set_opcode(newop, OpCode::BoolNegate, glb);
        let outvn = data.new_unique_out(1, newop, glb)?;
        data.op_set_input(newop, vn, 0)?;
        data.op_set_input(op, outvn, 1)?;
        data.op_insert_before(newop, op);
        data.op_flip_condition(op);
        Ok(1)
    }
}

pub struct RuleBoolNegate {
    pub base: RuleBase,
}

impl RuleBoolNegate {
    pub fn new(group: &str) -> RuleBoolNegate {
        RuleBoolNegate {
            base: RuleBase::new(group, 0, "boolnegate"),
        }
    }
}

impl Rule for RuleBoolNegate {
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
        Some(Box::new(RuleBoolNegate::new(self.get_group())))
    }

    fn get_op_list(&self, oplist: &mut Vec<OpCode>) {
        oplist.push(OpCode::BoolNegate);
    }

    fn apply_op(&mut self, op: OpId, data: &mut Funcdata, glb: &mut Architecture) -> Result<i32> {
        let vn = data.op(op).get_in(0);
        let Some(flip_op) = written_def(data, vn) else {
            return Ok(0);
        };
        let descendants = data.vn(vn).descend().to_vec();
        for &descendant in descendants.iter() {
            if data.op(descendant).code() != OpCode::BoolNegate {
                return Ok(0);
            }
        }
        let Some((opc, flipyes)) = get_booleanflip(data.op(flip_op).code()) else {
            return Ok(0);
        };
        data.op_set_opcode(flip_op, opc, glb);
        if flipyes {
            data.op_swap_input(flip_op, 0, 1);
        }
        for &descendant in descendants.iter() {
            data.op_set_opcode(descendant, OpCode::Copy, glb);
        }
        Ok(1)
    }
}

pub struct RuleLess2Zero {
    pub base: RuleBase,
}

impl RuleLess2Zero {
    pub fn new(group: &str) -> RuleLess2Zero {
        RuleLess2Zero {
            base: RuleBase::new(group, 0, "less2zero"),
        }
    }
}

impl Rule for RuleLess2Zero {
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
        Some(Box::new(RuleLess2Zero::new(self.get_group())))
    }

    fn get_op_list(&self, oplist: &mut Vec<OpCode>) {
        oplist.push(OpCode::IntLess);
    }

    fn apply_op(&mut self, op: OpId, data: &mut Funcdata, glb: &mut Architecture) -> Result<i32> {
        let lvn = data.op(op).get_in(0);
        let rvn = data.op(op).get_in(1);
        if data.vn(lvn).is_constant() {
            if data.vn(lvn).get_offset() == 0 {
                data.op_set_opcode(op, OpCode::IntNotequal, glb);
                return Ok(1);
            } else if data.vn(lvn).get_offset() == calc_mask(data.vn(lvn).get_size()) {
                data.op_set_opcode(op, OpCode::Copy, glb);
                data.op_remove_input(op, 1);
                let constvn = data.new_constant(1, 0, glb);
                data.op_set_input(op, constvn, 0)?;
                return Ok(1);
            }
        } else if data.vn(rvn).is_constant() {
            if data.vn(rvn).get_offset() == 0 {
                data.op_set_opcode(op, OpCode::Copy, glb);
                data.op_remove_input(op, 1);
                let constvn = data.new_constant(1, 0, glb);
                data.op_set_input(op, constvn, 0)?;
                return Ok(1);
            } else if data.vn(rvn).get_offset() == calc_mask(data.vn(rvn).get_size()) {
                data.op_set_opcode(op, OpCode::IntNotequal, glb);
                return Ok(1);
            }
        }
        Ok(0)
    }
}

pub struct RuleLessEqual2Zero {
    pub base: RuleBase,
}

impl RuleLessEqual2Zero {
    pub fn new(group: &str) -> RuleLessEqual2Zero {
        RuleLessEqual2Zero {
            base: RuleBase::new(group, 0, "lessequal2zero"),
        }
    }
}

impl Rule for RuleLessEqual2Zero {
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
        Some(Box::new(RuleLessEqual2Zero::new(self.get_group())))
    }

    fn get_op_list(&self, oplist: &mut Vec<OpCode>) {
        oplist.push(OpCode::IntLessequal);
    }

    fn apply_op(&mut self, op: OpId, data: &mut Funcdata, glb: &mut Architecture) -> Result<i32> {
        let lvn = data.op(op).get_in(0);
        let rvn = data.op(op).get_in(1);
        if data.vn(lvn).is_constant() {
            if data.vn(lvn).get_offset() == 0 {
                data.op_set_opcode(op, OpCode::Copy, glb);
                data.op_remove_input(op, 1);
                let constvn = data.new_constant(1, 1, glb);
                data.op_set_input(op, constvn, 0)?;
                return Ok(1);
            } else if data.vn(lvn).get_offset() == calc_mask(data.vn(lvn).get_size()) {
                data.op_set_opcode(op, OpCode::IntEqual, glb);
                return Ok(1);
            }
        } else if data.vn(rvn).is_constant() {
            if data.vn(rvn).get_offset() == 0 {
                data.op_set_opcode(op, OpCode::IntEqual, glb);
                return Ok(1);
            } else if data.vn(rvn).get_offset() == calc_mask(data.vn(rvn).get_size()) {
                data.op_set_opcode(op, OpCode::Copy, glb);
                data.op_remove_input(op, 1);
                let constvn = data.new_constant(1, 1, glb);
                data.op_set_input(op, constvn, 0)?;
                return Ok(1);
            }
        }
        Ok(0)
    }
}

pub struct RuleSLess2Zero {
    pub base: RuleBase,
}

impl RuleSLess2Zero {
    pub fn new(group: &str) -> RuleSLess2Zero {
        RuleSLess2Zero {
            base: RuleBase::new(group, 0, "sless2zero"),
        }
    }

    pub fn get_hi_bit(op: OpId, data: &Funcdata) -> Option<VarnodeId> {
        let opc = data.op(op).code();
        if opc != OpCode::IntAdd && opc != OpCode::IntOr && opc != OpCode::IntXor {
            return None;
        }
        let vn1 = data.op(op).get_in(0);
        let vn2 = data.op(op).get_in(1);
        let mut mask = calc_mask(data.vn(vn1).get_size());
        mask ^= mask >> 1;
        let nzmask1 = data.vn(vn1).get_nz_mask();
        if nzmask1 != mask && (nzmask1 & mask) != 0 {
            return None;
        }
        let nzmask2 = data.vn(vn2).get_nz_mask();
        if nzmask2 != mask && (nzmask2 & mask) != 0 {
            return None;
        }
        if nzmask1 == mask {
            return Some(vn1);
        }
        if nzmask2 == mask {
            return Some(vn2);
        }
        None
    }
}

impl Rule for RuleSLess2Zero {
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
        Some(Box::new(RuleSLess2Zero::new(self.get_group())))
    }

    fn get_op_list(&self, oplist: &mut Vec<OpCode>) {
        oplist.push(OpCode::IntSless);
    }

    fn apply_op(&mut self, op: OpId, data: &mut Funcdata, glb: &mut Architecture) -> Result<i32> {
        let lvn = data.op(op).get_in(0);
        let rvn = data.op(op).get_in(1);
        if data.vn(lvn).is_constant() {
            if !data.vn(rvn).is_written() {
                return Ok(0);
            }
            if data.vn(lvn).get_offset() == calc_mask(data.vn(lvn).get_size()) {
                let feed_op = data.vn(rvn).get_def().expect("written varnode without defining op");
                let feed_op_code = data.op(feed_op).code();
                if let Some(hibit) = RuleSLess2Zero::get_hi_bit(feed_op, data) {
                    if data.vn(hibit).is_constant() {
                        let constvn = data.new_constant(data.vn(hibit).get_size(), data.vn(hibit).get_offset(), glb);
                        data.op_set_input(op, constvn, 1)?;
                    } else {
                        data.op_set_input(op, hibit, 1)?;
                    }
                    data.op_set_opcode(op, OpCode::IntEqual, glb);
                    let zerovn = data.new_constant(data.vn(hibit).get_size(), 0, glb);
                    data.op_set_input(op, zerovn, 0)?;
                    return Ok(1);
                } else if feed_op_code == OpCode::Subpiece {
                    let avn = data.op(feed_op).get_in(0);
                    if data.vn(avn).is_free() || data.vn(avn).get_size() > 8 {
                        return Ok(0);
                    }
                    let cut = data.vn(data.op(feed_op).get_in(1)).get_offset() as i32;
                    if data.vn(rvn).get_size() + cut == data.vn(avn).get_size() {
                        data.op_set_input(op, avn, 1)?;
                        let asize = data.vn(avn).get_size();
                        let constvn = data.new_constant(asize, calc_mask(asize), glb);
                        data.op_set_input(op, constvn, 0)?;
                        return Ok(1);
                    }
                } else if feed_op_code == OpCode::IntNegate {
                    let avn = data.op(feed_op).get_in(0);
                    if data.vn(avn).is_free() {
                        return Ok(0);
                    }
                    data.op_set_input(op, avn, 0)?;
                    let constvn = data.new_constant(data.vn(avn).get_size(), 0, glb);
                    data.op_set_input(op, constvn, 1)?;
                    return Ok(1);
                } else if feed_op_code == OpCode::IntAnd {
                    let avn = data.op(feed_op).get_in(0);
                    if data.vn(avn).is_free() || data.vn(rvn).lone_descend().is_none() {
                        return Ok(0);
                    }
                    let mask_vn = data.op(feed_op).get_in(1);
                    if data.vn(mask_vn).is_constant() {
                        let mut mask = data.vn(mask_vn).get_offset();
                        mask = mask.wrapping_shr((8 * data.vn(avn).get_size() - 1) as u32);
                        if (mask & 1) != 0 {
                            data.op_set_input(op, avn, 1)?;
                            return Ok(1);
                        }
                    }
                } else if feed_op_code == OpCode::Piece {
                    let avn = data.op(feed_op).get_in(0);
                    if data.vn(avn).is_free() {
                        return Ok(0);
                    }
                    data.op_set_input(op, avn, 1)?;
                    let asize = data.vn(avn).get_size();
                    let constvn = data.new_constant(asize, calc_mask(asize), glb);
                    data.op_set_input(op, constvn, 0)?;
                    return Ok(1);
                } else if feed_op_code == OpCode::IntLeft {
                    let coeff = data.op(feed_op).get_in(1);
                    if !data.vn(coeff).is_constant()
                        || data.vn(coeff).get_offset() != (data.vn(lvn).get_size() * 8 - 1) as i64 as u64
                    {
                        return Ok(0);
                    }
                    let avn = data.op(feed_op).get_in(0);
                    match written_def(data, avn) {
                        Some(def) if data.op(def).is_bool_output() => {}
                        _ => return Ok(0),
                    }
                    data.op_set_opcode(op, OpCode::BoolNegate, glb);
                    data.op_remove_input(op, 1);
                    data.op_set_input(op, avn, 0)?;
                    return Ok(1);
                }
            }
        } else if data.vn(rvn).is_constant() {
            if !data.vn(lvn).is_written() {
                return Ok(0);
            }
            if data.vn(rvn).get_offset() == 0 {
                let feed_op = data.vn(lvn).get_def().expect("written varnode without defining op");
                let feed_op_code = data.op(feed_op).code();
                if let Some(hibit) = RuleSLess2Zero::get_hi_bit(feed_op, data) {
                    if data.vn(hibit).is_constant() {
                        let constvn = data.new_constant(data.vn(hibit).get_size(), data.vn(hibit).get_offset(), glb);
                        data.op_set_input(op, constvn, 0)?;
                    } else {
                        data.op_set_input(op, hibit, 0)?;
                    }
                    data.op_set_opcode(op, OpCode::IntNotequal, glb);
                    return Ok(1);
                } else if feed_op_code == OpCode::Subpiece {
                    let avn = data.op(feed_op).get_in(0);
                    if data.vn(avn).is_free() || data.vn(avn).get_size() > 8 {
                        return Ok(0);
                    }
                    let cut = data.vn(data.op(feed_op).get_in(1)).get_offset() as i32;
                    if data.vn(lvn).get_size() + cut == data.vn(avn).get_size() {
                        data.op_set_input(op, avn, 0)?;
                        let constvn = data.new_constant(data.vn(avn).get_size(), 0, glb);
                        data.op_set_input(op, constvn, 1)?;
                        return Ok(1);
                    }
                } else if feed_op_code == OpCode::IntNegate {
                    let avn = data.op(feed_op).get_in(0);
                    if data.vn(avn).is_free() {
                        return Ok(0);
                    }
                    data.op_set_input(op, avn, 1)?;
                    let asize = data.vn(avn).get_size();
                    let constvn = data.new_constant(asize, calc_mask(asize), glb);
                    data.op_set_input(op, constvn, 0)?;
                    return Ok(1);
                } else if feed_op_code == OpCode::IntAnd {
                    let avn = data.op(feed_op).get_in(0);
                    if data.vn(avn).is_free() || data.vn(lvn).lone_descend().is_none() {
                        return Ok(0);
                    }
                    let mask_vn = data.op(feed_op).get_in(1);
                    if data.vn(mask_vn).is_constant() {
                        let mut mask = data.vn(mask_vn).get_offset();
                        mask = mask.wrapping_shr((8 * data.vn(avn).get_size() - 1) as u32);
                        if (mask & 1) != 0 {
                            data.op_set_input(op, avn, 0)?;
                            return Ok(1);
                        }
                    }
                } else if feed_op_code == OpCode::Piece {
                    let avn = data.op(feed_op).get_in(0);
                    if data.vn(avn).is_free() {
                        return Ok(0);
                    }
                    data.op_set_input(op, avn, 0)?;
                    let constvn = data.new_constant(data.vn(avn).get_size(), 0, glb);
                    data.op_set_input(op, constvn, 1)?;
                    return Ok(1);
                }
            }
        }
        Ok(0)
    }
}

pub struct RuleEqual2Zero {
    pub base: RuleBase,
}

impl RuleEqual2Zero {
    pub fn new(group: &str) -> RuleEqual2Zero {
        RuleEqual2Zero {
            base: RuleBase::new(group, 0, "equal2zero"),
        }
    }
}

impl Rule for RuleEqual2Zero {
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
        Some(Box::new(RuleEqual2Zero::new(self.get_group())))
    }

    fn get_op_list(&self, oplist: &mut Vec<OpCode>) {
        oplist.extend_from_slice(&[OpCode::IntEqual, OpCode::IntNotequal]);
    }

    fn apply_op(&mut self, op: OpId, data: &mut Funcdata, glb: &mut Architecture) -> Result<i32> {
        let mut vn = data.op(op).get_in(0);
        let addvn;
        if data.vn(vn).is_constant() && data.vn(vn).get_offset() == 0 {
            addvn = data.op(op).get_in(1);
        } else {
            addvn = vn;
            vn = data.op(op).get_in(1);
            if !data.vn(vn).is_constant() || data.vn(vn).get_offset() != 0 {
                return Ok(0);
            }
        }
        for &boolop in data.vn(addvn).descend() {
            if !data.op(boolop).is_bool_output() {
                return Ok(0);
            }
        }
        let Some(addop) = data.vn(addvn).get_def() else {
            return Ok(0);
        };
        if data.op(addop).code() != OpCode::IntAdd {
            return Ok(0);
        }
        vn = data.op(addop).get_in(0);
        let vn2 = data.op(addop).get_in(1);
        let posvn;
        let unnegvn;
        if data.vn(vn2).is_constant() {
            let val = Address::from_parts(
                data.vn(vn2).get_space().cloned(),
                uintb_negate(data.vn(vn2).get_offset().wrapping_sub(1), data.vn(vn2).get_size()),
            );
            unnegvn = data.new_varnode(data.vn(vn2).get_size(), &val, None, glb)?;
            data.vn_copy_symbol_if_valid(unnegvn, vn2, glb)?;
            posvn = vn;
        } else if written_def(data, vn).is_some_and(|def| data.op_verify_mult_neg_one(def)) {
            posvn = vn2;
            unnegvn = data
                .op(data.vn(vn).get_def().expect("written varnode without defining op"))
                .get_in(0);
        } else if written_def(data, vn2).is_some_and(|def| data.op_verify_mult_neg_one(def)) {
            posvn = vn;
            unnegvn = data
                .op(data.vn(vn2).get_def().expect("written varnode without defining op"))
                .get_in(0);
        } else {
            return Ok(0);
        }
        if !data.vn(posvn).is_heritage_known() {
            return Ok(0);
        }
        if !data.vn(unnegvn).is_heritage_known() {
            return Ok(0);
        }
        data.op_set_input(op, posvn, 0)?;
        data.op_set_input(op, unnegvn, 1)?;
        Ok(1)
    }
}

pub struct RuleEqual2Constant {
    pub base: RuleBase,
}

impl RuleEqual2Constant {
    pub fn new(group: &str) -> RuleEqual2Constant {
        RuleEqual2Constant {
            base: RuleBase::new(group, 0, "equal2constant"),
        }
    }
}

impl Rule for RuleEqual2Constant {
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
        Some(Box::new(RuleEqual2Constant::new(self.get_group())))
    }

    fn get_op_list(&self, oplist: &mut Vec<OpCode>) {
        oplist.extend_from_slice(&[OpCode::IntEqual, OpCode::IntNotequal]);
    }

    fn apply_op(&mut self, op: OpId, data: &mut Funcdata, glb: &mut Architecture) -> Result<i32> {
        let cvn = data.op(op).get_in(1);
        if !data.vn(cvn).is_constant() {
            return Ok(0);
        }
        let lhs = data.op(op).get_in(0);
        let Some(leftop) = written_def(data, lhs) else {
            return Ok(0);
        };
        let newconst: u64;
        let opc = data.op(leftop).code();
        if opc == OpCode::IntAdd {
            let otherconst = data.op(leftop).get_in(1);
            if !data.vn(otherconst).is_constant() {
                return Ok(0);
            }
            newconst = data.vn(cvn).get_offset().wrapping_sub(data.vn(otherconst).get_offset())
                & calc_mask(data.vn(cvn).get_size());
        } else if opc == OpCode::IntMult {
            let otherconst = data.op(leftop).get_in(1);
            if !data.vn(otherconst).is_constant() {
                return Ok(0);
            }
            if data.vn(otherconst).get_offset() != calc_mask(data.vn(otherconst).get_size()) {
                return Ok(0);
            }
            newconst = data.vn(cvn).get_offset().wrapping_neg() & calc_mask(data.vn(otherconst).get_size());
        } else if opc == OpCode::IntNegate {
            newconst = !data.vn(cvn).get_offset() & calc_mask(data.vn(lhs).get_size());
        } else {
            return Ok(0);
        }
        let avn = data.op(leftop).get_in(0);
        if data.vn(avn).is_free() {
            return Ok(0);
        }
        for &dop in data.vn(lhs).descend() {
            if dop == op {
                continue;
            }
            let dopc = data.op(dop).code();
            if dopc != OpCode::IntEqual && dopc != OpCode::IntNotequal {
                return Ok(0);
            }
            if !data.vn(data.op(dop).get_in(1)).is_constant() {
                return Ok(0);
            }
        }
        data.op_set_input(op, avn, 0)?;
        let constvn = data.new_constant(data.vn(avn).get_size(), newconst, glb);
        data.op_set_input(op, constvn, 1)?;
        Ok(1)
    }
}

pub struct RulePtrArith {
    pub base: RuleBase,
}

impl RulePtrArith {
    pub fn new(group: &str) -> RulePtrArith {
        RulePtrArith {
            base: RuleBase::new(group, 0, "ptrarith"),
        }
    }

    pub fn verify_preferred_pointer(op: OpId, slot: i32, data: &Funcdata, glb: &Architecture) -> bool {
        let vn = data.op(op).get_in(slot);
        let Some(pre_op) = written_def(data, vn) else {
            return true;
        };
        if data.op(pre_op).code() != OpCode::IntAdd {
            return true;
        }
        let mut preslot = 0;
        let first_type = data.vn_get_type_read_facing(data.op(pre_op).get_in(preslot), pre_op, glb);
        if types(glb).get(first_type).get_metatype() != TypeMetatype::Ptr {
            preslot = 1;
            let second_type = data.vn_get_type_read_facing(data.op(pre_op).get_in(preslot), pre_op, glb);
            if types(glb).get(second_type).get_metatype() != TypeMetatype::Ptr {
                return true;
            }
        }
        1 != RulePtrArith::evaluate_pointer_expression(pre_op, preslot, data, glb)
    }

    pub fn evaluate_pointer_expression(op: OpId, slot: i32, data: &Funcdata, glb: &Architecture) -> i32 {
        let mut res = 1;
        let mut count = 0;
        let ptr_base = data.op(op).get_in(slot);
        if data.vn(ptr_base).is_free() && !data.vn(ptr_base).is_constant() {
            return 0;
        }
        let other_type = data.vn_get_type_read_facing(data.op(op).get_in(1 - slot), op, glb);
        if types(glb).get(other_type).get_metatype() == TypeMetatype::Ptr {
            res = 2;
        }
        let out_vn = data.op(op).get_out().expect("op without output");
        for &dec_op in data.vn(out_vn).descend() {
            count += 1;
            let opc = data.op(dec_op).code();
            if opc == OpCode::IntAdd {
                let other_vn = data.op(dec_op).get_in(1 - data.op(dec_op).get_slot(out_vn));
                if data.vn(other_vn).is_free() && !data.vn(other_vn).is_constant() {
                    return 0;
                }
                let other_vn_type = data.vn_get_type_read_facing(other_vn, dec_op, glb);
                if types(glb).get(other_vn_type).get_metatype() == TypeMetatype::Ptr {
                    res = 2;
                }
            } else if (opc == OpCode::Load || opc == OpCode::Store) && data.op(dec_op).get_in(1) == out_vn {
                let base = data.vn(ptr_base);
                if base.is_spacebase()
                    && (base.is_input() || base.is_constant())
                    && data.vn(data.op(op).get_in(1 - slot)).is_constant()
                {
                    return 0;
                }
                res = 2;
            } else {
                res = 2;
            }
        }
        if count == 0 {
            return 0;
        }
        if count > 1 && data.vn(out_vn).is_spacebase() {
            return 0;
        }
        res
    }
}

impl Rule for RulePtrArith {
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
        Some(Box::new(RulePtrArith::new(self.get_group())))
    }

    fn get_op_list(&self, oplist: &mut Vec<OpCode>) {
        oplist.push(OpCode::IntAdd);
    }

    fn apply_op(&mut self, op: OpId, data: &mut Funcdata, glb: &mut Architecture) -> Result<i32> {
        if !data.has_type_recovery_started() {
            return Ok(0);
        }
        let num_input = data.op(op).num_input();
        let mut slot = 0;
        while slot < num_input {
            let ct = data.vn_get_type_read_facing(data.op(op).get_in(slot), op, glb);
            if types(glb).get(ct).get_metatype() == TypeMetatype::Ptr {
                break;
            }
            slot += 1;
        }
        if slot == num_input {
            return Ok(0);
        }
        if RulePtrArith::evaluate_pointer_expression(op, slot, data, glb) != 2 {
            return Ok(0);
        }
        if !RulePtrArith::verify_preferred_pointer(op, slot, data, glb) {
            return Ok(0);
        }
        let mut state = AddTreeState::new(data, op, slot, glb);
        if state.apply(data, glb)? {
            return Ok(1);
        }
        if state.init_alternate_form(glb) && state.apply(data, glb)? {
            return Ok(1);
        }
        Ok(0)
    }
}

pub struct RuleStructOffset0 {
    pub base: RuleBase,
}

impl RuleStructOffset0 {
    pub fn new(group: &str) -> RuleStructOffset0 {
        RuleStructOffset0 {
            base: RuleBase::new(group, 0, "structoffset0"),
        }
    }
}

impl Rule for RuleStructOffset0 {
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
        Some(Box::new(RuleStructOffset0::new(self.get_group())))
    }

    fn get_op_list(&self, oplist: &mut Vec<OpCode>) {
        oplist.extend_from_slice(&[OpCode::Load, OpCode::Store]);
    }

    fn apply_op(&mut self, op: OpId, data: &mut Funcdata, glb: &mut Architecture) -> Result<i32> {
        if !data.has_type_recovery_started() {
            return Ok(0);
        }
        let movesize = match data.op(op).code() {
            OpCode::Load => data.vn(data.op(op).get_out().expect("op without output")).get_size(),
            OpCode::Store => data.vn(data.op(op).get_in(2)).get_size(),
            _ => return Ok(0),
        };
        let ptr_vn = data.op(op).get_in(1);
        let ptr_size = data.vn(ptr_vn).get_size();
        let ct = data.vn_get_type_read_facing(ptr_vn, op, glb);
        let factory = types(glb);
        let ct_type = factory.get(ct);
        if ct_type.get_metatype() != TypeMetatype::Ptr {
            return Ok(0);
        }
        let mut base_type = ct_type.get_ptr_to();
        if ct_type.is_formal_pointer_rel() && ct_type.evaluate_thru_parent(0, factory) {
            base_type = ct_type.get_parent();
            let base = factory.get(base_type);
            if base.get_metatype() != TypeMetatype::Struct {
                return Ok(0);
            }
            let offset = ct_type.get_byte_offset() as i64;
            if offset >= base.get_size() as i64 {
                return Ok(0);
            }
            if base.get_size() < movesize {
                return Ok(0);
            }
            let mut newoff: i64 = 0;
            let Some(sub_type) = base.get_sub_type(offset, &mut newoff, glb) else {
                return Ok(0);
            };
            if factory.get(sub_type).get_size() < movesize {
                return Ok(0);
            }
            newoff = AddrSpace::byte_to_address(newoff as u64, ct_type.get_word_size()) as i64;
            let offset = (newoff.wrapping_neg() as u64) & calc_mask(ptr_size);
            let constvn = data.new_constant(ptr_size, offset, glb);
            let newop = data.new_op_before(op, OpCode::Ptrsub, ptr_vn, constvn, None, glb)?;
            let ptr_type = data.vn(ptr_vn).get_type();
            if types(glb).get(ptr_type).needs_resolution() {
                data.inherit_union_field(ptr_type, newop, 0, op, 1, glb);
            }
            data.op_mut(newop).set_stop_type_propagation();
            let newout = data.op(newop).get_out().expect("op without output");
            if newoff != 0 {
                let addconst = data.new_constant(ptr_size, newoff as u64, glb);
                let addop = data.new_op_before(op, OpCode::IntAdd, newout, addconst, None, glb)?;
                let addout = data.op(addop).get_out().expect("op without output");
                data.op_set_input(op, addout, 1)?;
            } else {
                data.op_set_input(op, newout, 1)?;
            }
            return Ok(1);
        }
        let base = factory.get(base_type);
        if base.get_metatype() == TypeMetatype::Struct {
            if base.get_size() < movesize {
                return Ok(0);
            }
            let mut offset: i64 = 0;
            let Some(sub_type) = base.get_sub_type(0, &mut offset, glb) else {
                return Ok(0);
            };
            if factory.get(sub_type).get_size() < movesize {
                return Ok(0);
            }
        } else if base.get_metatype() == TypeMetatype::Array {
            if base.get_size() < movesize {
                return Ok(0);
            }
            if base.get_size() == movesize && base.num_elements() != 1 {
                return Ok(0);
            }
        } else {
            return Ok(0);
        }
        let constvn = data.new_constant(ptr_size, 0, glb);
        let newop = data.new_op_before(op, OpCode::Ptrsub, ptr_vn, constvn, None, glb)?;
        let ptr_type = data.vn(ptr_vn).get_type();
        if types(glb).get(ptr_type).needs_resolution() {
            data.inherit_union_field(ptr_type, newop, 0, op, 1, glb);
        }
        data.op_mut(newop).set_stop_type_propagation();
        let newout = data.op(newop).get_out().expect("op without output");
        data.op_set_input(op, newout, 1)?;
        Ok(1)
    }
}

pub struct RulePushPtr {
    pub base: RuleBase,
}

impl RulePushPtr {
    pub fn new(group: &str) -> RulePushPtr {
        RulePushPtr {
            base: RuleBase::new(group, 0, "pushptr"),
        }
    }

    pub fn build_varnode_out(
        vn: VarnodeId,
        op: OpId,
        data: &mut Funcdata,
        glb: &mut Architecture,
    ) -> Result<VarnodeId> {
        let size = data.vn(vn).get_size();
        let is_internal = data.vn(vn).get_space().expect("varnode without space").get_type() == SpaceType::Internal;
        if data.vn(vn).is_addr_tied() || is_internal {
            return data.new_unique_out(size, op, glb);
        }
        let addr = data.vn(vn).get_addr().clone();
        data.new_varnode_out(size, &addr, op, glb)
    }

    pub fn collect_duplicate_needs(reslist: &mut Vec<OpId>, vn: VarnodeId, data: &Funcdata) {
        let mut vn = vn;
        loop {
            if !data.vn(vn).is_written() {
                return;
            }
            if data.vn(vn).is_auto_live() {
                return;
            }
            if data.vn(vn).lone_descend().is_none() {
                return;
            }
            let op = data.vn(vn).get_def().expect("written varnode without defining op");
            let opc = data.op(op).code();
            if opc == OpCode::IntZext || opc == OpCode::IntSext || opc == OpCode::Int2comp {
                reslist.push(op);
            } else if opc == OpCode::IntMult {
                if data.vn(data.op(op).get_in(1)).is_constant() {
                    reslist.push(op);
                }
            } else {
                return;
            }
            vn = data.op(op).get_in(0);
        }
    }

    pub fn duplicate_need(op: OpId, data: &mut Funcdata, glb: &mut Architecture) -> Result<()> {
        let out_vn = data.op(op).get_out().expect("op without output");
        let in_vn = data.op(op).get_in(0);
        let num = data.op(op).num_input();
        let opc = data.op(op).code();
        let addr = data.op(op).get_addr().clone();
        loop {
            let dec_op = data.vn(out_vn).descend()[0];
            let slot = data.op(dec_op).get_slot(out_vn);
            let new_op = data.new_op(num, &addr);
            let new_out = RulePushPtr::build_varnode_out(out_vn, new_op, data, glb)?;
            let out_type = data.vn(out_vn).get_type();
            data.vn_update_type(new_out, out_type);
            data.op_set_opcode(new_op, opc, glb);
            data.op_set_input(new_op, in_vn, 0)?;
            if num > 1 {
                let second = data.op(op).get_in(1);
                data.op_set_input(new_op, second, 1)?;
            }
            data.op_set_input(dec_op, new_out, slot)?;
            data.op_insert_before(new_op, dec_op);
            if data.vn(out_vn).descend().is_empty() {
                break;
            }
        }
        data.op_destroy(op)
    }
}

impl Rule for RulePushPtr {
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
        Some(Box::new(RulePushPtr::new(self.get_group())))
    }

    fn get_op_list(&self, oplist: &mut Vec<OpCode>) {
        oplist.push(OpCode::IntAdd);
    }

    fn apply_op(&mut self, op: OpId, data: &mut Funcdata, glb: &mut Architecture) -> Result<i32> {
        if !data.has_type_recovery_started() {
            return Ok(0);
        }
        let num_input = data.op(op).num_input();
        let mut slot = 0;
        let mut vni = None;
        while slot < num_input {
            let candidate = data.op(op).get_in(slot);
            vni = Some(candidate);
            let ct = data.vn_get_type_read_facing(candidate, op, glb);
            if types(glb).get(ct).get_metatype() == TypeMetatype::Ptr {
                break;
            }
            slot += 1;
        }
        if slot == num_input {
            return Ok(0);
        }
        let vni = vni.expect("op without inputs");
        if RulePtrArith::evaluate_pointer_expression(op, slot, data, glb) != 1 {
            return Ok(0);
        }
        let vn = data.op(op).get_out().expect("op without output");
        let vnadd2 = data.op(op).get_in(1 - slot);
        let mut duplicate_list: Vec<OpId> = Vec::new();
        if data.vn(vn).lone_descend().is_none() {
            RulePushPtr::collect_duplicate_needs(&mut duplicate_list, vnadd2, data);
        }
        loop {
            let Some(&decop) = data.vn(vn).descend().first() else {
                break;
            };
            let decslot = data.op(decop).get_slot(vn);
            let vnadd1 = data.op(decop).get_in(1 - decslot);
            let addr = data.op(decop).get_addr().clone();
            let newop = data.new_op(2, &addr);
            data.op_set_opcode(newop, OpCode::IntAdd, glb);
            let newout = data.new_unique_out(data.vn(vnadd1).get_size(), newop, glb)?;
            data.op_set_input(decop, vni, 0)?;
            data.op_set_input(decop, newout, 1)?;
            data.op_set_input(newop, vnadd1, 0)?;
            data.op_set_input(newop, vnadd2, 1)?;
            data.op_insert_before(newop, decop);
        }
        if !data.vn(vn).is_auto_live() {
            data.op_destroy(op)?;
        }
        for &duplicate in duplicate_list.iter() {
            RulePushPtr::duplicate_need(duplicate, data, glb)?;
        }
        Ok(1)
    }
}

pub struct RulePtraddUndo {
    pub base: RuleBase,
}

impl RulePtraddUndo {
    pub fn new(group: &str) -> RulePtraddUndo {
        RulePtraddUndo {
            base: RuleBase::new(group, 0, "ptraddundo"),
        }
    }
}

impl Rule for RulePtraddUndo {
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
        Some(Box::new(RulePtraddUndo::new(self.get_group())))
    }

    fn get_op_list(&self, oplist: &mut Vec<OpCode>) {
        oplist.push(OpCode::Ptradd);
    }

    fn apply_op(&mut self, op: OpId, data: &mut Funcdata, glb: &mut Architecture) -> Result<i32> {
        if !data.has_type_recovery_started() {
            return Ok(0);
        }
        let size = data.vn(data.op(op).get_in(2)).get_offset() as i32;
        let basevn = data.op(op).get_in(0);
        let dt = data.vn_get_type_read_facing(basevn, op, glb);
        let factory = types(glb);
        let dt_type = factory.get(dt);
        if dt_type.get_metatype() == TypeMetatype::Ptr
            && factory.get(dt_type.get_ptr_to()).get_align_size() as i64
                == AddrSpace::address_to_byte_int(size as i64, dt_type.get_word_size())
        {
            let ind_vn = data.op(op).get_in(1);
            if !data.vn(ind_vn).is_constant() || data.vn(ind_vn).get_offset() != 0 {
                return Ok(0);
            }
        }
        data.op_undo_ptradd(op, false, glb)?;
        Ok(1)
    }
}

pub struct RulePtrsubUndo {
    pub base: RuleBase,
}

impl RulePtrsubUndo {
    pub fn new(group: &str) -> RulePtrsubUndo {
        RulePtrsubUndo {
            base: RuleBase::new(group, 0, "ptrsubundo"),
        }
    }

    pub const DEPTH_LIMIT: i32 = 8;

    pub fn get_const_offset_back(vn: VarnodeId, multiplier: &mut i64, max_level: i32, data: &Funcdata) -> i64 {
        *multiplier = 0;
        let mut submultiplier: i64 = 0;
        if data.vn(vn).is_constant() {
            return data.vn(vn).get_offset() as i64;
        }
        if !data.vn(vn).is_written() {
            return 0;
        }
        let max_level = max_level - 1;
        if max_level < 0 {
            return 0;
        }
        let op = data.vn(vn).get_def().expect("written varnode without defining op");
        let opc = data.op(op).code();
        let mut retval: i64 = 0;
        if opc == OpCode::IntAdd {
            retval = retval.wrapping_add(RulePtrsubUndo::get_const_offset_back(
                data.op(op).get_in(0),
                &mut submultiplier,
                max_level,
                data,
            ));
            if submultiplier > *multiplier {
                *multiplier = submultiplier;
            }
            retval = retval.wrapping_add(RulePtrsubUndo::get_const_offset_back(
                data.op(op).get_in(1),
                &mut submultiplier,
                max_level,
                data,
            ));
            if submultiplier > *multiplier {
                *multiplier = submultiplier;
            }
        } else if opc == OpCode::IntMult {
            let cvn = data.op(op).get_in(1);
            if !data.vn(cvn).is_constant() {
                return 0;
            }
            *multiplier = data.vn(cvn).get_offset() as i64;
            RulePtrsubUndo::get_const_offset_back(data.op(op).get_in(0), &mut submultiplier, max_level, data);
            if submultiplier > 0 {
                *multiplier = multiplier.wrapping_mul(submultiplier);
            }
        }
        retval
    }

    pub fn get_extra_offset(op: OpId, multiplier: &mut i64, data: &Funcdata) -> i64 {
        let mut extra: i64 = 0;
        *multiplier = 0;
        let mut submultiplier: i64 = 0;
        let mut outvn = data.op(op).get_out().expect("op without output");
        let mut cur = data.vn(outvn).lone_descend();
        while let Some(curop) = cur {
            let opc = data.op(curop).code();
            if opc == OpCode::IntAdd {
                let slot = data.op(curop).get_slot(outvn);
                extra = extra.wrapping_add(RulePtrsubUndo::get_const_offset_back(
                    data.op(curop).get_in(1 - slot),
                    &mut submultiplier,
                    RulePtrsubUndo::DEPTH_LIMIT,
                    data,
                ));
                if submultiplier > *multiplier {
                    *multiplier = submultiplier;
                }
            } else if opc == OpCode::Ptrsub {
                extra = extra.wrapping_add(data.vn(data.op(curop).get_in(1)).get_offset() as i64);
            } else if opc == OpCode::Ptradd {
                if data.op(curop).get_in(0) != outvn {
                    break;
                }
                let mut ptraddmult = data.vn(data.op(curop).get_in(2)).get_offset() as i64;
                let invn = data.op(curop).get_in(1);
                if data.vn(invn).is_constant() {
                    extra = extra.wrapping_add(ptraddmult.wrapping_mul(data.vn(invn).get_offset() as i64));
                }
                RulePtrsubUndo::get_const_offset_back(invn, &mut submultiplier, RulePtrsubUndo::DEPTH_LIMIT, data);
                if submultiplier != 0 {
                    ptraddmult = ptraddmult.wrapping_mul(submultiplier);
                }
                if ptraddmult > *multiplier {
                    *multiplier = ptraddmult;
                }
            } else {
                break;
            }
            outvn = data.op(curop).get_out().expect("op without output");
            cur = data.vn(outvn).lone_descend();
        }
        sign_extend(extra, 8 * data.vn(outvn).get_size() - 1)
    }

    pub fn remove_local_adds(vn: VarnodeId, data: &mut Funcdata, glb: &mut Architecture) -> Result<i64> {
        let mut extra: i64 = 0;
        let mut cur = data.vn(vn).lone_descend();
        let mut next_vn = vn;
        while let Some(op) = cur {
            let opc = data.op(op).code();
            if opc == OpCode::IntAdd {
                let slot = data.op(op).get_slot(next_vn);
                if slot == 0 && data.vn(data.op(op).get_in(1)).is_constant() {
                    extra = extra.wrapping_add(data.vn(data.op(op).get_in(1)).get_offset() as i64);
                    data.op_remove_input(op, 1);
                    data.op_set_opcode(op, OpCode::Copy, glb);
                } else {
                    extra = extra.wrapping_add(RulePtrsubUndo::remove_local_add_recurse(
                        op,
                        1 - slot,
                        RulePtrsubUndo::DEPTH_LIMIT,
                        data,
                        glb,
                    ));
                }
            } else if opc == OpCode::Ptrsub {
                extra = extra.wrapping_add(data.vn(data.op(op).get_in(1)).get_offset() as i64);
                data.op_mut(op).clear_stop_type_propagation();
                data.op_remove_input(op, 1);
                data.op_set_opcode(op, OpCode::Copy, glb);
            } else if opc == OpCode::Ptradd {
                if data.op(op).get_in(0) != next_vn {
                    break;
                }
                let ptraddmult = data.vn(data.op(op).get_in(2)).get_offset() as i64;
                let invn = data.op(op).get_in(1);
                if data.vn(invn).is_constant() {
                    extra = extra.wrapping_add(ptraddmult.wrapping_mul(data.vn(invn).get_offset() as i64));
                    data.op_remove_input(op, 2);
                    data.op_remove_input(op, 1);
                    data.op_set_opcode(op, OpCode::Copy, glb);
                } else {
                    data.op_undo_ptradd(op, false, glb)?;
                    extra = extra.wrapping_add(RulePtrsubUndo::remove_local_add_recurse(
                        op,
                        1,
                        RulePtrsubUndo::DEPTH_LIMIT,
                        data,
                        glb,
                    ));
                }
            } else {
                break;
            }
            next_vn = data.op(op).get_out().expect("op without output");
            cur = data.vn(next_vn).lone_descend();
        }
        if next_vn != vn {
            let next_type = data.vn(next_vn).get_type();
            data.vn_update_type(vn, next_type);
        }
        Ok(extra)
    }

    pub fn remove_local_add_recurse(
        op: OpId,
        slot: i32,
        max_level: i32,
        data: &mut Funcdata,
        glb: &mut Architecture,
    ) -> i64 {
        let vn = data.op(op).get_in(slot);
        if !data.vn(vn).is_written() {
            return 0;
        }
        if data.vn(vn).lone_descend() != Some(op) {
            return 0;
        }
        let max_level = max_level - 1;
        if max_level < 0 {
            return 0;
        }
        let op = data.vn(vn).get_def().expect("written varnode without defining op");
        let mut retval: i64 = 0;
        if data.op(op).code() == OpCode::IntAdd {
            if data.vn(data.op(op).get_in(1)).is_constant() {
                retval = retval.wrapping_add(data.vn(data.op(op).get_in(1)).get_offset() as i64);
                data.op_remove_input(op, 1);
                data.op_set_opcode(op, OpCode::Copy, glb);
            } else {
                retval = retval.wrapping_add(RulePtrsubUndo::remove_local_add_recurse(op, 0, max_level, data, glb));
                retval = retval.wrapping_add(RulePtrsubUndo::remove_local_add_recurse(op, 1, max_level, data, glb));
            }
        }
        retval
    }
}

impl Rule for RulePtrsubUndo {
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
        Some(Box::new(RulePtrsubUndo::new(self.get_group())))
    }

    fn get_op_list(&self, oplist: &mut Vec<OpCode>) {
        oplist.push(OpCode::Ptrsub);
    }

    fn apply_op(&mut self, op: OpId, data: &mut Funcdata, glb: &mut Architecture) -> Result<i32> {
        if !data.has_type_recovery_started() {
            return Ok(0);
        }
        let basevn = data.op(op).get_in(0);
        let cvn = data.op(op).get_in(1);
        let mut val = data.vn(cvn).get_offset() as i64;
        let mut multiplier: i64 = 0;
        let mut extra = RulePtrsubUndo::get_extra_offset(op, &mut multiplier, data);
        let base_type = data.vn_get_type_read_facing(basevn, op, glb);
        let factory = types(glb);
        if factory.get(base_type).is_ptrsub_matching(val, extra, multiplier, glb) {
            return Ok(0);
        }
        data.op_set_opcode(op, OpCode::IntAdd, glb);
        data.op_mut(op).clear_stop_type_propagation();
        let outvn = data.op(op).get_out().expect("op without output");
        extra = RulePtrsubUndo::remove_local_adds(outvn, data, glb)?;
        if extra != 0 {
            val = val.wrapping_add(extra);
            let csize = data.vn(cvn).get_size();
            let constvn = data.new_constant(csize, (val as u64) & calc_mask(csize), glb);
            data.op_set_input(op, constvn, 1)?;
        }
        Ok(1)
    }
}

pub struct RuleMultNegOne {
    pub base: RuleBase,
}

impl RuleMultNegOne {
    pub fn new(group: &str) -> RuleMultNegOne {
        RuleMultNegOne {
            base: RuleBase::new(group, 0, "multnegone"),
        }
    }
}

impl Rule for RuleMultNegOne {
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
        Some(Box::new(RuleMultNegOne::new(self.get_group())))
    }

    fn get_op_list(&self, oplist: &mut Vec<OpCode>) {
        oplist.push(OpCode::IntMult);
    }

    fn apply_op(&mut self, op: OpId, data: &mut Funcdata, glb: &mut Architecture) -> Result<i32> {
        let constvn = data.op(op).get_in(1);
        if !data.vn(constvn).is_constant() {
            return Ok(0);
        }
        if data.vn(constvn).get_offset() != calc_mask(data.vn(constvn).get_size()) {
            return Ok(0);
        }
        data.op_set_opcode(op, OpCode::Int2comp, glb);
        data.op_remove_input(op, 1);
        Ok(1)
    }
}

pub struct RuleAddUnsigned {
    pub base: RuleBase,
}

impl RuleAddUnsigned {
    pub fn new(group: &str) -> RuleAddUnsigned {
        RuleAddUnsigned {
            base: RuleBase::new(group, 0, "addunsigned"),
        }
    }
}

impl Rule for RuleAddUnsigned {
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
        Some(Box::new(RuleAddUnsigned::new(self.get_group())))
    }

    fn get_op_list(&self, oplist: &mut Vec<OpCode>) {
        oplist.push(OpCode::IntAdd);
    }

    fn apply_op(&mut self, op: OpId, data: &mut Funcdata, glb: &mut Architecture) -> Result<i32> {
        let constvn = data.op(op).get_in(1);
        if !data.vn(constvn).is_constant() {
            return Ok(0);
        }
        let dt = data.vn_get_type_read_facing(constvn, op, glb);
        let factory = types(glb);
        let dt_type = factory.get(dt);
        if dt_type.get_metatype() != TypeMetatype::Uint {
            return Ok(0);
        }
        if dt_type.is_char_print() {
            return Ok(0);
        }
        let val = data.vn(constvn).get_offset();
        let csize = data.vn(constvn).get_size();
        let mask = calc_mask(csize);
        let shift_amount = (csize * 6) as u32;
        let quarter = (mask.wrapping_shr(shift_amount)).wrapping_shl(shift_amount);
        if (val & quarter) != quarter {
            return Ok(0);
        }
        if let Some(entry) = data.vn(constvn).get_symbol_entry() {
            let database = glb.symboltab.as_deref().expect("symbol table is not initialized");
            let symbol = database.symbols.get(database.entries.get(entry).get_symbol());
            if matches!(symbol.kind, SymbolKind::Equate { .. }) && symbol.is_name_locked() {
                return Ok(0);
            }
        }
        let negated_val = val.wrapping_neg() & mask;
        if dt_type.is_enum_type()
            && !dt_type.has_named_value(negated_val, factory)
            && dt_type.has_named_value(!val & mask, factory)
        {
            return Ok(0);
        }
        data.op_set_opcode(op, OpCode::IntSub, glb);
        let cvn = data.new_constant(csize, negated_val, glb);
        data.vn_copy_symbol(cvn, constvn, glb)?;
        data.op_set_input(op, cvn, 1)?;
        Ok(1)
    }
}

pub struct Rule2Comp2Sub {
    pub base: RuleBase,
}

impl Rule2Comp2Sub {
    pub fn new(group: &str) -> Rule2Comp2Sub {
        Rule2Comp2Sub {
            base: RuleBase::new(group, 0, "2comp2sub"),
        }
    }
}

impl Rule for Rule2Comp2Sub {
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
        Some(Box::new(Rule2Comp2Sub::new(self.get_group())))
    }

    fn get_op_list(&self, oplist: &mut Vec<OpCode>) {
        oplist.push(OpCode::Int2comp);
    }

    fn apply_op(&mut self, op: OpId, data: &mut Funcdata, glb: &mut Architecture) -> Result<i32> {
        let outvn = data.op(op).get_out().expect("op without output");
        let Some(addop) = data.vn(outvn).lone_descend() else {
            return Ok(0);
        };
        if data.op(addop).code() != OpCode::IntAdd {
            return Ok(0);
        }
        if data.op(addop).get_in(0) == outvn {
            let other = data.op(addop).get_in(1);
            data.op_set_input(addop, other, 0)?;
        }
        let input = data.op(op).get_in(0);
        data.op_set_input(addop, input, 1)?;
        data.op_set_opcode(addop, OpCode::IntSub, glb);
        data.op_destroy(op)?;
        Ok(1)
    }
}

pub struct RuleSubRight {
    pub base: RuleBase,
}

impl RuleSubRight {
    pub fn new(group: &str) -> RuleSubRight {
        RuleSubRight {
            base: RuleBase::new(group, 0, "subright"),
        }
    }
}

impl Rule for RuleSubRight {
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
        Some(Box::new(RuleSubRight::new(self.get_group())))
    }

    fn get_op_list(&self, oplist: &mut Vec<OpCode>) {
        oplist.push(OpCode::Subpiece);
    }

    fn apply_op(&mut self, op: OpId, data: &mut Funcdata, glb: &mut Architecture) -> Result<i32> {
        let mut op = op;
        if data.op(op).does_special_printing() {
            return Ok(0);
        }
        let in_type = data.vn_get_type_read_facing(data.op(op).get_in(0), op, glb);
        if types(glb).get(in_type).is_piece_structured() {
            data.op_mark_special_print(op);
            return Ok(0);
        }
        let cut = data.vn(data.op(op).get_in(1)).get_offset() as i32;
        if cut == 0 {
            return Ok(0);
        }
        let avn = data.op(op).get_in(0);
        let outvn = data.op(op).get_out().expect("op without output");
        if data.vn(outvn).is_addr_tied() && data.vn(avn).is_addr_tied() && data.vn(outvn).overlap(data.vn(avn)) == cut {
            return Ok(0);
        }
        let mut opc = OpCode::IntRight;
        let mut shift_bits = cut * 8;
        if let Some(lone) = data.vn(outvn).lone_descend() {
            let opc2 = data.op(lone).code();
            if (opc2 == OpCode::IntRight || opc2 == OpCode::IntSright)
                && data.vn(data.op(lone).get_in(1)).is_constant()
                && data.vn(outvn).get_size() + cut == data.vn(avn).get_size()
            {
                shift_bits = shift_bits.wrapping_add(data.vn(data.op(lone).get_in(1)).get_offset() as i32);
                if shift_bits >= data.vn(avn).get_size() * 8 {
                    if opc2 == OpCode::IntRight {
                        return Ok(0);
                    }
                    shift_bits = data.vn(avn).get_size() * 8 - 1;
                }
                data.op_unlink(op)?;
                op = lone;
                data.op_set_opcode(op, OpCode::Subpiece, glb);
                opc = opc2;
            }
        }
        let asize = data.vn(avn).get_size();
        let ct = if opc == OpCode::IntRight {
            types_mut(glb).get_base(asize, TypeMetatype::Uint)?
        } else {
            types_mut(glb).get_base(asize, TypeMetatype::Int)?
        };
        let addr = data.op(op).get_addr().clone();
        let shiftop = data.new_op(2, &addr);
        data.op_set_opcode(shiftop, opc, glb);
        let newout = data.new_unique(asize, Some(ct), glb);
        data.op_set_output(shiftop, newout, glb)?;
        data.op_set_input(shiftop, avn, 0)?;
        let shiftvn = data.new_constant(4, shift_bits as i64 as u64, glb);
        data.op_set_input(shiftop, shiftvn, 1)?;
        data.op_insert_before(shiftop, op);
        data.op_set_input(op, newout, 0)?;
        let zerovn = data.new_constant(4, 0, glb);
        data.op_set_input(op, zerovn, 1)?;
        Ok(1)
    }
}

pub struct RulePtrsubCharConstant {
    pub base: RuleBase,
}

impl RulePtrsubCharConstant {
    pub fn new(group: &str) -> RulePtrsubCharConstant {
        RulePtrsubCharConstant {
            base: RuleBase::new(group, 0, "ptrsubcharconstant"),
        }
    }

    pub fn push_const_further(
        &mut self,
        data: &mut Funcdata,
        outtype: TypeId,
        op: OpId,
        slot: i32,
        val: u64,
        glb: &mut Architecture,
    ) -> Result<bool> {
        if data.op(op).code() != OpCode::Ptradd {
            return Ok(false);
        }
        if slot != 0 {
            return Ok(false);
        }
        let vn = data.op(op).get_in(1);
        if !data.vn(vn).is_constant() {
            return Ok(false);
        }
        let mut addval = data.vn(vn).get_offset();
        addval = addval.wrapping_mul(data.vn(data.op(op).get_in(2)).get_offset());
        let val = val.wrapping_add(addval);
        let newconst = data.new_constant(data.vn(vn).get_size(), val, glb);
        data.vn_update_type(newconst, outtype);
        data.op_remove_input(op, 2);
        data.op_remove_input(op, 1);
        data.op_set_opcode(op, OpCode::Copy, glb);
        data.op_set_input(op, newconst, 0)?;
        Ok(true)
    }
}

impl Rule for RulePtrsubCharConstant {
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
        Some(Box::new(RulePtrsubCharConstant::new(self.get_group())))
    }

    fn get_op_list(&self, oplist: &mut Vec<OpCode>) {
        oplist.push(OpCode::Ptrsub);
    }

    fn apply_op(&mut self, op: OpId, data: &mut Funcdata, glb: &mut Architecture) -> Result<i32> {
        let sb = data.op(op).get_in(0);
        let sb_type = data.vn_get_type_read_facing(sb, op, glb);
        let factory = types(glb);
        if factory.get(sb_type).get_metatype() != TypeMetatype::Ptr {
            return Ok(0);
        }
        let dt = factory.get(sb_type).get_ptr_to();
        if factory.get(dt).get_metatype() != TypeMetatype::Spacebase {
            return Ok(0);
        }
        let vn1 = data.op(op).get_in(1);
        if !data.vn(vn1).is_constant() {
            return Ok(0);
        }
        let outvn = data.op(op).get_out().expect("op without output");
        let outtype = data.vn_get_type_def_facing(outvn, glb);
        let factory = types(glb);
        if factory.get(outtype).get_metatype() != TypeMetatype::Ptr {
            return Ok(0);
        }
        let basetype = factory.get(outtype).get_ptr_to();
        if !factory.get(basetype).is_char_print() {
            return Ok(0);
        }
        let opaddr = data.op(op).get_addr().clone();
        let symaddr = factory
            .get(dt)
            .get_address(data.vn(vn1).get_offset(), data.vn(vn1).get_size(), &opaddr, glb);
        let scope = factory.get(dt).get_map(glb)?;
        let database = glb.symboltab.as_deref().expect("symbol table is not initialized");
        if !database.scope_is_read_only(scope, &symaddr, 1, &opaddr) {
            return Ok(0);
        }
        let loader = glb.loader.clone().expect("load image is not initialized");
        let factory = glb.types.as_deref().expect("type factory is not initialized");
        let string_manager = glb
            .string_manager
            .as_deref_mut()
            .expect("string manager is not initialized");
        if !string_manager.is_string(&symaddr, basetype, factory, loader.as_ref())? {
            return Ok(0);
        }
        let mut remove_copy = false;
        if !data.vn(outvn).is_addr_force() {
            remove_copy = true;
            let descendants = data.vn(outvn).descend().to_vec();
            for subop in descendants {
                let subslot = data.op(subop).get_slot(outvn);
                let offset = data.vn(vn1).get_offset();
                if !self.push_const_further(data, outtype, subop, subslot, offset, glb)? {
                    remove_copy = false;
                }
            }
        }
        if remove_copy {
            data.op_destroy(op)?;
        } else {
            let newvn = data.new_constant(data.vn(outvn).get_size(), data.vn(vn1).get_offset(), glb);
            data.vn_update_type(newvn, outtype);
            data.op_remove_input(op, 1);
            data.op_set_input(op, newvn, 0)?;
            data.op_set_opcode(op, OpCode::Copy, glb);
        }
        Ok(1)
    }
}

pub struct RuleExtensionPush {
    pub base: RuleBase,
}

impl RuleExtensionPush {
    pub fn new(group: &str) -> RuleExtensionPush {
        RuleExtensionPush {
            base: RuleBase::new(group, 0, "extensionpush"),
        }
    }
}

impl Rule for RuleExtensionPush {
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
        Some(Box::new(RuleExtensionPush::new(self.get_group())))
    }

    fn get_op_list(&self, oplist: &mut Vec<OpCode>) {
        oplist.push(OpCode::IntZext);
        oplist.push(OpCode::IntSext);
    }

    fn apply_op(&mut self, op: OpId, data: &mut Funcdata, glb: &mut Architecture) -> Result<i32> {
        let in_vn = data.op(op).get_in(0);
        if data.vn(in_vn).is_constant() {
            return Ok(0);
        }
        if data.vn(in_vn).is_addr_force() {
            return Ok(0);
        }
        if data.vn(in_vn).is_addr_tied() {
            return Ok(0);
        }
        let out_vn = data.op(op).get_out().expect("op without output");
        if data.vn(out_vn).is_type_lock() || data.vn(out_vn).is_name_lock() {
            return Ok(0);
        }
        if data.vn(out_vn).is_addr_force() || data.vn(out_vn).is_addr_tied() {
            return Ok(0);
        }
        let mut addcount = 0;
        let mut ptrcount = 0;
        for &dec_op in data.vn(out_vn).descend() {
            let opc = data.op(dec_op).code();
            if opc == OpCode::Ptradd {
                ptrcount += 1;
            } else if opc == OpCode::IntAdd {
                let dec_out = data.op(dec_op).get_out().expect("op without output");
                match data.vn(dec_out).lone_descend() {
                    Some(sub_op) if data.op(sub_op).code() == OpCode::Ptradd => {}
                    _ => return Ok(0),
                }
                addcount += 1;
            } else {
                return Ok(0);
            }
        }
        if addcount + ptrcount <= 1 {
            return Ok(0);
        }
        if addcount > 0 && data.vn(data.op(op).get_in(0)).lone_descend().is_some() {
            return Ok(0);
        }
        RulePushPtr::duplicate_need(op, data, glb)?;
        Ok(1)
    }
}

pub struct RulePieceStructure {
    pub base: RuleBase,
}

impl RulePieceStructure {
    pub fn new(group: &str) -> RulePieceStructure {
        RulePieceStructure {
            base: RuleBase::new(group, 0, "piecestructure"),
        }
    }

    pub fn determine_datatype(
        vn: VarnodeId,
        base_offset: &mut i32,
        data: &Funcdata,
        glb: &Architecture,
    ) -> Option<TypeId> {
        let ct = data.vn_get_structured_type(vn, glb)?;
        let factory = types(glb);
        let vnsize = data.vn(vn).get_size();
        if factory.get(ct).get_size() != vnsize {
            let entry_id = data
                .vn(vn)
                .get_symbol_entry()
                .expect("partial varnode without symbol entry");
            let database = glb.symboltab.as_deref().expect("symbol table is not initialized");
            let entry = database.entries.get(entry_id);
            if entry.is_dynamic() {
                return None;
            }
            *base_offset = data
                .vn(vn)
                .get_addr()
                .overlap(0, entry.get_addr(), factory.get(ct).get_size());
            if *base_offset < 0 {
                return None;
            }
            *base_offset += entry.get_offset();
            let mut sub_type = Some(ct);
            let mut sub_offset = *base_offset as i64;
            while let Some(current) = sub_type {
                if factory.get(current).get_size() <= vnsize {
                    break;
                }
                let mut next_offset = 0;
                sub_type = factory.get(current).get_sub_type(sub_offset, &mut next_offset, glb);
                sub_offset = next_offset;
            }
            if let Some(current) = sub_type
                && factory.get(current).get_size() == vnsize
                && sub_offset == 0
                && !factory.get(current).is_piece_structured()
            {
                return None;
            }
        } else {
            *base_offset = 0;
        }
        Some(ct)
    }

    pub fn spanning_range(ct: TypeId, off: i32, size: i32, glb: &Architecture) -> bool {
        let factory = types(glb);
        if off + size > factory.get(ct).get_size() {
            return false;
        }
        let mut new_off = off as i64;
        let mut current = ct;
        loop {
            let mut next_off = 0;
            match factory.get(current).get_sub_type(new_off, &mut next_off, glb) {
                None => return true,
                Some(sub) => current = sub,
            }
            new_off = next_off;
            if new_off + size as i64 > factory.get(current).get_size() as i64 {
                return true;
            }
            if !factory.get(current).is_piece_structured() {
                break;
            }
        }
        false
    }

    pub fn convert_zext_to_piece(
        zext: OpId,
        structured_type: TypeId,
        offset: i32,
        data: &mut Funcdata,
        glb: &mut Architecture,
    ) -> Result<bool> {
        let outvn = data.op(zext).get_out().expect("op without output");
        let invn = data.op(zext).get_in(0);
        if data.vn(invn).is_constant() {
            return Ok(false);
        }
        let insize = data.vn(invn).get_size();
        let sz = data.vn(outvn).get_size() - insize;
        if sz > 8 {
            return Ok(false);
        }
        let big_endian = data
            .vn(outvn)
            .get_space()
            .expect("varnode without space")
            .is_big_endian();
        let offset = offset + if big_endian { 0 } else { insize };
        let mut new_off = offset as i64;
        let mut ct = Some(structured_type);
        let factory = types(glb);
        while let Some(current) = ct {
            if factory.get(current).get_size() <= sz {
                break;
            }
            let mut next_off = 0;
            ct = factory.get(current).get_sub_type(new_off, &mut next_off, glb);
            new_off = next_off;
        }
        let zerovn = data.new_constant(sz, 0, glb);
        if let Some(current) = ct
            && types(glb).get(current).get_size() == sz
        {
            data.vn_update_type(zerovn, current);
        }
        data.op_set_opcode(zext, OpCode::Piece, glb);
        data.op_insert_input(zext, zerovn, 0)?;
        let in_type = data.vn(invn).get_type();
        if types(glb).get(in_type).needs_resolution() {
            data.inherit_union_field(in_type, zext, 1, zext, 0, glb);
        }
        Ok(true)
    }

    pub fn find_replace_zext(
        stack: &mut [PieceNode],
        structured_type: TypeId,
        data: &mut Funcdata,
        glb: &mut Architecture,
    ) -> Result<bool> {
        let mut change = false;
        for index in 0..stack.len() {
            let node = &stack[index];
            if !node.is_leaf() {
                continue;
            }
            let vn = node.get_varnode(data);
            let type_offset = node.get_type_offset();
            let Some(op) = written_def(data, vn) else { continue };
            if data.op(op).code() != OpCode::IntZext {
                continue;
            }
            if !RulePieceStructure::spanning_range(structured_type, type_offset, data.vn(vn).get_size(), glb) {
                continue;
            }
            if RulePieceStructure::convert_zext_to_piece(op, structured_type, type_offset, data, glb)? {
                change = true;
            }
        }
        Ok(change)
    }

    pub fn separate_symbol(root: VarnodeId, leaf: VarnodeId, data: &Funcdata, glb: &Architecture) -> bool {
        let root_vn = data.vn(root);
        let leaf_vn = data.vn(leaf);
        if root_vn.get_symbol_entry() != leaf_vn.get_symbol_entry() {
            return true;
        }
        if root_vn.is_addr_tied() {
            return false;
        }
        if !leaf_vn.is_written() {
            return true;
        }
        if leaf_vn.is_proto_partial() {
            return true;
        }
        let op = leaf_vn.get_def().expect("written varnode without defining op");
        if data.op(op).is_marker() {
            return true;
        }
        if data.op(op).code() != OpCode::Piece {
            return false;
        }
        if types(glb).get(leaf_vn.get_type()).is_piece_structured() {
            return true;
        }
        false
    }
}

impl Rule for RulePieceStructure {
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
        Some(Box::new(RulePieceStructure::new(self.get_group())))
    }

    fn get_op_list(&self, oplist: &mut Vec<OpCode>) {
        oplist.push(OpCode::Piece);
        oplist.push(OpCode::IntZext);
    }

    fn apply_op(&mut self, op: OpId, data: &mut Funcdata, glb: &mut Architecture) -> Result<i32> {
        if data.op(op).is_partial_root() {
            return Ok(0);
        }
        let outvn = data.op(op).get_out().expect("op without output");
        let mut base_offset: i32 = 0;
        let Some(ct) = RulePieceStructure::determine_datatype(outvn, &mut base_offset, data, glb) else {
            return Ok(0);
        };
        if data.op(op).code() == OpCode::IntZext {
            let out_type = data.vn(outvn).get_type();
            if RulePieceStructure::convert_zext_to_piece(op, out_type, 0, data, glb)? {
                return Ok(1);
            }
            return Ok(0);
        }
        if let Some(zext) = data.vn(outvn).lone_descend() {
            if data.op(zext).code() == OpCode::Piece {
                return Ok(0);
            }
            if data.op(zext).code() == OpCode::IntZext {
                let zext_out = data.op(zext).get_out().expect("op without output");
                let zext_type = data.vn(zext_out).get_type();
                if RulePieceStructure::convert_zext_to_piece(zext, zext_type, 0, data, glb)? {
                    return Ok(1);
                }
                return Ok(0);
            }
        }
        let mut stack: Vec<PieceNode> = Vec::new();
        loop {
            PieceNode::gather_pieces(data, &mut stack, outvn, op, base_offset, base_offset);
            if !RulePieceStructure::find_replace_zext(&mut stack, ct, data, glb)? {
                break;
            }
            stack.clear();
        }
        data.op_mut(op).set_partial_root();
        let mut any_addr_tied = data.vn(outvn).is_addr_tied();
        let base_addr = data.vn(outvn).get_addr().sub(base_offset as i64);
        for node in stack.iter() {
            let vn = node.get_varnode(data);
            let vnsize = data.vn(vn).get_size();
            let mut addr = base_addr.add(node.get_type_offset() as i64);
            addr.renormalize(vnsize)?;
            if *data.vn(vn).get_addr() == addr
                && (!node.is_leaf() || !RulePieceStructure::separate_symbol(outvn, vn, data, glb))
            {
                if !data.vn(vn).is_addr_tied() && !data.vn(vn).is_proto_partial() {
                    data.vn_mut(vn).set_proto_partial();
                }
                any_addr_tied = any_addr_tied || data.vn(vn).is_addr_tied();
                continue;
            }
            if node.is_leaf() {
                let node_addr = data.op(node.get_op()).get_addr().clone();
                let copy_op = data.new_op(1, &node_addr);
                let new_vn = data.new_varnode_out(vnsize, &addr, copy_op, glb)?;
                any_addr_tied = any_addr_tied || data.vn(new_vn).is_addr_tied();
                let new_type = match types_mut(glb).get_exact_piece(ct, node.get_type_offset(), vnsize)? {
                    Some(new_type) => new_type,
                    None => data.vn(vn).get_type(),
                };
                data.vn_update_type(new_vn, new_type);
                data.op_set_opcode(copy_op, OpCode::Copy, glb);
                data.op_set_input(copy_op, vn, 0)?;
                data.op_set_input(node.get_op(), new_vn, node.get_slot())?;
                data.op_insert_before(copy_op, node.get_op());
                let vn_type = data.vn(vn).get_type();
                if types(glb).get(vn_type).needs_resolution() {
                    data.inherit_union_field(vn_type, copy_op, 0, node.get_op(), node.get_slot(), glb);
                }
                if types(glb).get(new_type).needs_resolution() {
                    Datatype::resolve_in_flow(new_type, copy_op, -1, data, glb)?;
                }
                if !data.vn(new_vn).is_addr_tied() {
                    data.vn_mut(new_vn).set_proto_partial();
                }
            } else {
                let def_op = data.vn(vn).get_def().expect("written varnode without defining op");
                let lone_op = data.vn(vn).lone_descend().expect("varnode without lone descendant");
                let slot = data.op(lone_op).get_slot(vn);
                let vn_type = data.vn(vn).get_type();
                let new_vn = data.new_varnode(vnsize, &addr, Some(vn_type), glb)?;
                data.op_set_output(def_op, new_vn, glb)?;
                data.op_set_input(lone_op, new_vn, slot)?;
                data.delete_varnode(vn)?;
                if !data.vn(new_vn).is_addr_tied() {
                    data.vn_mut(new_vn).set_proto_partial();
                }
            }
        }
        if !any_addr_tied {
            Merge::register_proto_partial_root(data, outvn);
        }
        Ok(1)
    }
}

pub struct RuleAndStructure {
    pub base: RuleBase,
}

impl RuleAndStructure {
    pub fn new(group: &str) -> RuleAndStructure {
        RuleAndStructure {
            base: RuleBase::new(group, 0, "andstructure"),
        }
    }
}

impl Rule for RuleAndStructure {
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
        Some(Box::new(RuleAndStructure::new(self.get_group())))
    }

    fn get_op_list(&self, oplist: &mut Vec<OpCode>) {
        oplist.push(OpCode::IntAnd);
    }

    fn apply_op(&mut self, op: OpId, data: &mut Funcdata, glb: &mut Architecture) -> Result<i32> {
        let cvn = data.op(op).get_in(1);
        if !data.vn(cvn).is_constant() {
            return Ok(0);
        }
        let vn = data.op(op).get_in(0);
        let base_type = data.vn_get_type_read_facing(vn, op, glb);
        let meta = types(glb).get(base_type).get_metatype();
        if meta != TypeMetatype::Struct && meta != TypeMetatype::PartialStruct && meta != TypeMetatype::Array {
            return Ok(0);
        }
        let off = data.vn(cvn).get_offset();
        let count = 64 - count_leading_zeros(off);
        let mut size = count / 8;
        if count % 8 != 0 {
            size += 1;
        }
        let vnsize = data.vn(vn).get_size();
        let big_endian = data.vn(vn).get_space().expect("varnode without space").is_big_endian();
        let mut struct_off: i64 = if big_endian { (vnsize - size) as i64 } else { 0 };
        let mut new_struct_off: i64 = 0;
        let ct = Datatype::find_smallest_container(base_type, struct_off, size as i64, &mut new_struct_off, glb);
        struct_off = new_struct_off;
        let ct_size = types(glb).get(ct).get_size();
        if ct_size >= vnsize || struct_off != 0 {
            return Ok(0);
        }
        let opaddr = data.op(op).get_addr().clone();
        let sub_op = data.new_op(2, &opaddr);
        data.op_set_opcode(sub_op, OpCode::Subpiece, glb);
        let zerovn = data.new_constant(4, 0, glb);
        data.op_set_input(sub_op, zerovn, 1)?;
        data.op_mark_special_print(sub_op);
        let mut addr = data
            .vn(data.op(op).get_out().expect("op without output"))
            .get_addr()
            .clone();
        if addr.is_big_endian() {
            addr = addr.add((vnsize - ct_size) as i64);
        }
        addr.renormalize(vnsize)?;
        let outvn = data.new_varnode_out(ct_size, &addr, sub_op, glb)?;
        data.vn_update_type(outvn, ct);
        if calc_mask(size) == off {
            data.op_remove_input(op, 1);
            data.op_set_input(op, outvn, 0)?;
            data.op_set_opcode(op, OpCode::IntZext, glb);
            data.op_set_input(sub_op, vn, 0)?;
            data.op_insert_before(sub_op, op);
        } else {
            let new_zext = data.new_op(1, &opaddr);
            data.op_set_opcode(new_zext, OpCode::IntZext, glb);
            let outzext = data.new_unique_out(vnsize, new_zext, glb)?;
            data.op_set_input(op, outzext, 0)?;
            data.op_set_input(sub_op, vn, 0)?;
            data.op_set_input(new_zext, outvn, 0)?;
            data.op_insert_before(new_zext, op);
            data.op_insert_before(sub_op, new_zext);
        }
        Ok(1)
    }
}
