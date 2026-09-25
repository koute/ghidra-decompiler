use std::collections::BTreeMap;

use crate::action::{Action, ActionBase, ActionGroupList, Rule, RuleBase};
use crate::architecture::Architecture;
use crate::block::BlockId;
use crate::error::{Error, Result};
use crate::expression::BooleanExpressionMatch;
use crate::funcdata::Funcdata;
use crate::op::OpId;
use crate::opcodes::OpCode;
use crate::varnode::VarnodeId;

#[derive(Clone, Debug, Default)]
pub struct ConditionalExecution {
    pub cbranch: Option<OpId>,
    pub initblock: Option<BlockId>,
    pub iblock: Option<BlockId>,
    pub prea_inslot: i32,
    pub init2a_true: bool,
    pub iblock2posta_true: bool,
    pub camethruposta_slot: i32,
    pub posta_outslot: i32,
    pub posta_block: Option<BlockId>,
    pub postb_block: Option<BlockId>,
    pub replacement: BTreeMap<i32, VarnodeId>,
    pub pullback: Vec<Option<VarnodeId>>,
    pub heritageyes: Vec<bool>,
}

impl ConditionalExecution {
    pub fn new(data: &mut Funcdata, glb: &mut Architecture) -> Result<ConditionalExecution> {
        let mut condexe = ConditionalExecution::default();
        condexe.build_heritage_array(data, glb)?;
        Ok(condexe)
    }

    fn iblock(&self) -> BlockId {
        self.iblock.expect("conditional execution without iblock")
    }

    pub fn build_heritage_array(&mut self, data: &mut Funcdata, glb: &Architecture) -> Result<()> {
        self.heritageyes.clear();
        let numspaces = glb.manager.num_spaces();
        self.heritageyes.resize(numspaces as usize, false);
        for index in 0..numspaces {
            let spc = match glb.manager.get_space(index) {
                None => continue,
                Some(spc) => spc,
            };
            let spaceindex = spc.get_index();
            if !spc.is_heritaged() {
                continue;
            }
            if data.num_heritage_passes(&spc)? > 0 {
                self.heritageyes[spaceindex as usize] = true;
            }
        }
        Ok(())
    }

    pub fn test_i_block(&mut self, data: &Funcdata) -> bool {
        let iblock = self.iblock();
        if data.block(iblock).size_in() != 2 {
            return false;
        }
        if data.block(iblock).size_out() != 2 {
            return false;
        }
        self.cbranch = data.block_last_op(iblock);
        match self.cbranch {
            None => false,
            Some(cbranch) => data.op(cbranch).code() == OpCode::Cbranch,
        }
    }

    pub fn find_init_pre(&mut self, data: &Funcdata) -> bool {
        let iblock = self.iblock();
        let mut tmp = data.block(iblock).get_in(self.prea_inslot);
        let mut last = iblock;
        while data.block(tmp).size_out() == 1 && data.block(tmp).size_in() == 1 {
            last = tmp;
            tmp = data.block(tmp).get_in(0);
        }
        if data.block(tmp).size_out() != 2 {
            return false;
        }
        let initblock = tmp;
        self.initblock = Some(initblock);
        tmp = data.block(iblock).get_in(1 - self.prea_inslot);
        while data.block(tmp).size_out() == 1 && data.block(tmp).size_in() == 1 {
            tmp = data.block(tmp).get_in(0);
        }
        if tmp != initblock {
            return false;
        }
        if initblock == iblock {
            return false;
        }
        self.init2a_true = data.block(initblock).get_true_out() == last;
        true
    }

    pub fn verify_same_condition(&mut self, data: &Funcdata) -> bool {
        let initblock = self.initblock.expect("conditional execution without initblock");
        let init_cbranch = match data.block_last_op(initblock) {
            None => return false,
            Some(op) => op,
        };
        if data.op(init_cbranch).code() != OpCode::Cbranch {
            return false;
        }
        let mut tester = BooleanExpressionMatch::new();
        let cbranch = self.cbranch.expect("conditional execution without cbranch");
        if !tester.verify_condition(cbranch, init_cbranch, data) {
            return false;
        }
        if tester.get_flip() {
            self.init2a_true = !self.init2a_true;
        }
        true
    }

    pub fn test_op_read(&mut self, vn: VarnodeId, op: OpId, data: &Funcdata) -> bool {
        let iblock = self.iblock();
        if data.op(op).get_parent() == Some(iblock) {
            return true;
        }
        let write_op = data.vn(vn).get_def().expect("tested varnode is not written");
        let opc = data.op(write_op).code();
        if opc == OpCode::Copy || opc == OpCode::Subpiece || opc == OpCode::IntAdd || opc == OpCode::Ptrsub {
            if (opc == OpCode::IntAdd || opc == OpCode::Ptrsub) && !data.vn(data.op(write_op).get_in(1)).is_constant() {
                return false;
            }
            let invn = data.op(write_op).get_in(0);
            match data.vn(invn).get_def() {
                Some(upop) => {
                    if data.op(upop).get_parent() == Some(iblock) && data.op(upop).code() != OpCode::Multiequal {
                        return false;
                    }
                }
                None => {
                    if data.vn(invn).is_free() {
                        return false;
                    }
                }
            }
            return true;
        }
        false
    }

    pub fn test_multi_read(&mut self, vn: VarnodeId, op: OpId, data: &Funcdata) -> bool {
        let readop = data.op(op);
        if readop.get_parent() == Some(self.iblock()) {
            return readop.code() == OpCode::Copy || readop.code() == OpCode::Subpiece;
        }
        if readop.code() == OpCode::Return && (readop.num_input() < 2 || readop.get_in(1) != vn) {
            return false;
        }
        true
    }

    pub fn test_removability(&mut self, op: OpId, data: &Funcdata) -> bool {
        if data.op(op).code() == OpCode::Multiequal {
            let vn = data.op(op).get_out().expect("MULTIEQUAL without output");
            for readop in data.vn(vn).descend().to_vec() {
                if !self.test_multi_read(vn, readop, data) {
                    return false;
                }
            }
        } else {
            let pcode = data.op(op);
            if pcode.is_flow_break() || pcode.is_call() {
                return false;
            }
            if pcode.code() == OpCode::Load || pcode.code() == OpCode::Store {
                return false;
            }
            if pcode.code() == OpCode::Indirect {
                return false;
            }
            if let Some(vn) = pcode.get_out() {
                if data.vn(vn).is_addr_tied() {
                    return false;
                }
                let mut hasnodescend = true;
                for readop in data.vn(vn).descend().to_vec() {
                    if !self.test_op_read(vn, readop, data) {
                        return false;
                    }
                    hasnodescend = false;
                }
                let spaceindex = data.vn(vn).get_space().expect("varnode without space").get_index();
                if hasnodescend && !self.heritageyes[spaceindex as usize] {
                    return false;
                }
            }
        }
        true
    }

    pub fn find_pullback(&mut self, inbranch: i32) -> Option<VarnodeId> {
        while self.pullback.len() <= inbranch as usize {
            self.pullback.push(None);
        }
        self.pullback[inbranch as usize]
    }

    pub fn pullback_op(
        &mut self,
        op: OpId,
        inbranch: i32,
        data: &mut Funcdata,
        glb: &mut Architecture,
    ) -> Result<VarnodeId> {
        if let Some(invn) = self.find_pullback(inbranch) {
            return Ok(invn);
        }
        let iblock = self.iblock();
        let mut invn = data.op(op).get_in(0);
        let bl = match data.vn(invn).get_def() {
            Some(def_op) if data.op(def_op).get_parent() == Some(iblock) => {
                invn = data.op(def_op).get_in(inbranch);
                data.block(iblock).get_in(inbranch)
            }
            _ => data
                .block(iblock)
                .get_immed_dom()
                .expect("iblock without immediate dominator"),
        };
        let numinput = data.op(op).num_input();
        let addr = data.op(op).get_addr().clone();
        let new_op = data.new_op(numinput, &addr);
        let orig_out_vn = data.op(op).get_out().expect("pulled back op without output");
        let outsize = data.vn(orig_out_vn).get_size();
        let outaddr = data.vn(orig_out_vn).get_addr().clone();
        let out_vn = data.new_varnode_out(outsize, &outaddr, new_op, glb)?;
        let opc = data.op(op).code();
        data.op_set_opcode(new_op, opc, glb);
        data.op_set_input(new_op, invn, 0)?;
        for slot in 1..numinput {
            let input = data.op(op).get_in(slot);
            data.op_set_input(new_op, input, slot)?;
        }
        data.op_insert_end(new_op, bl);
        self.pullback[inbranch as usize] = Some(out_vn);
        Ok(out_vn)
    }

    pub fn get_new_multi(
        &mut self,
        op: OpId,
        bl: BlockId,
        data: &mut Funcdata,
        glb: &mut Architecture,
    ) -> Result<VarnodeId> {
        let sizein = data.block(bl).size_in();
        let start = data.block(bl).get_start();
        let newop = data.new_op(sizein, &start);
        let outvn = data.op(op).get_out().expect("iblock op without output");
        let outsize = data.vn(outvn).get_size();
        let newoutvn = data.new_unique_out(outsize, newop, glb)?;
        data.op_set_opcode(newop, OpCode::Multiequal, glb);
        for slot in 0..sizein {
            data.op_set_input(newop, outvn, slot)?;
        }
        data.op_insert_begin(newop, bl);
        Ok(newoutvn)
    }

    pub fn resolve_read(
        &mut self,
        op: OpId,
        bl: BlockId,
        data: &mut Funcdata,
        glb: &mut Architecture,
    ) -> Result<VarnodeId> {
        if data.block(bl).size_in() == 1 {
            let slot = if data.block(bl).get_in_rev_index(0) == self.posta_outslot {
                self.camethruposta_slot
            } else {
                1 - self.camethruposta_slot
            };
            self.resolve_iblock_read(op, slot, data, glb)
        } else {
            self.get_new_multi(op, bl, data, glb)
        }
    }

    pub fn resolve_iblock_read(
        &mut self,
        op: OpId,
        inbranch: i32,
        data: &mut Funcdata,
        glb: &mut Architecture,
    ) -> Result<VarnodeId> {
        let mut op = op;
        if data.op(op).code() == OpCode::Copy {
            let vn = data.op(op).get_in(0);
            let def_op = match data.vn(vn).get_def() {
                None => return Ok(vn),
                Some(def_op) => def_op,
            };
            if data.op(def_op).code() == OpCode::Multiequal && data.op(def_op).get_parent() == Some(self.iblock()) {
                op = def_op;
            } else {
                return Ok(vn);
            }
        }
        let opc = data.op(op).code();
        if opc == OpCode::Multiequal {
            return Ok(data.op(op).get_in(inbranch));
        } else if opc == OpCode::Subpiece || opc == OpCode::IntAdd || opc == OpCode::Ptrsub {
            return self.pullback_op(op, inbranch, data, glb);
        }
        Err(Error::Lowlevel(
            "Conditional execution: Illegal op in iblock".to_string(),
        ))
    }

    pub fn get_multiequal_read(
        &mut self,
        op: OpId,
        readop: OpId,
        slot: i32,
        data: &mut Funcdata,
        glb: &mut Architecture,
    ) -> Result<VarnodeId> {
        let bl = data.op(readop).get_parent().expect("read op without block");
        let inbl = data.block(bl).get_in(slot);
        if inbl != self.iblock() {
            return self.get_replacement_read(op, inbl, data, glb);
        }
        let inslot = if data.block(bl).get_in_rev_index(slot) == self.posta_outslot {
            self.camethruposta_slot
        } else {
            1 - self.camethruposta_slot
        };
        self.resolve_iblock_read(op, inslot, data, glb)
    }

    pub fn get_replacement_read(
        &mut self,
        op: OpId,
        bl: BlockId,
        data: &mut Funcdata,
        glb: &mut Architecture,
    ) -> Result<VarnodeId> {
        let blindex = data.block(bl).get_index();
        if let Some(vn) = self.replacement.get(&blindex) {
            return Ok(*vn);
        }
        let iblock = self.iblock();
        let mut curbl = bl;
        while data.block(curbl).get_immed_dom() != Some(iblock) {
            curbl = match data.block(curbl).get_immed_dom() {
                None => {
                    return Err(Error::Lowlevel(
                        "Conditional execution: Could not find dominator".to_string(),
                    ));
                }
                Some(dom) => dom,
            };
        }
        let curindex = data.block(curbl).get_index();
        if let Some(vn) = self.replacement.get(&curindex).copied() {
            self.replacement.insert(blindex, vn);
            return Ok(vn);
        }
        let res = self.resolve_read(op, curbl, data, glb)?;
        self.replacement.insert(curindex, res);
        if curbl != bl {
            self.replacement.insert(blindex, res);
        }
        Ok(res)
    }

    pub fn do_replacement(&mut self, op: OpId, data: &mut Funcdata, glb: &mut Architecture) -> Result<()> {
        self.replacement.clear();
        self.pullback.clear();
        let vn = data.op(op).get_out().expect("replaced op without output");
        while let Some(first) = data.vn(vn).descend().first().copied() {
            let mut readop = first;
            let mut slot = data.op(readop).get_slot(vn);
            let bl = data.op(readop).get_parent().expect("read op without block");
            if bl == self.iblock() {
                data.op_unset_input(readop, slot);
            } else {
                let rvn = if data.op(readop).code() == OpCode::Multiequal {
                    self.get_multiequal_read(op, readop, slot, data, glb)?
                } else if data.op(readop).code() == OpCode::Return && slot > 0 {
                    let addr = data.op(readop).get_addr().clone();
                    let newcopyop = data.new_op(1, &addr);
                    data.op_set_opcode(newcopyop, OpCode::Copy, glb);
                    let size = data.vn(vn).get_size();
                    let vnaddr = data.vn(vn).get_addr().clone();
                    let outvn = data.new_varnode_out(size, &vnaddr, newcopyop, glb)?;
                    data.op_set_input(readop, outvn, slot)?;
                    data.op_insert_before(newcopyop, readop);
                    readop = newcopyop;
                    slot = 0;
                    self.get_replacement_read(op, bl, data, glb)?
                } else {
                    self.get_replacement_read(op, bl, data, glb)?
                };
                data.op_set_input(readop, rvn, slot)?;
            }
        }
        Ok(())
    }

    pub fn verify(&mut self, data: &Funcdata) -> bool {
        self.prea_inslot = 0;
        self.posta_outslot = 0;

        if !self.test_i_block(data) {
            return false;
        }
        if !self.find_init_pre(data) {
            return false;
        }
        if !self.verify_same_condition(data) {
            return false;
        }

        self.iblock2posta_true = self.posta_outslot == 1;
        self.camethruposta_slot = if self.init2a_true == self.iblock2posta_true {
            self.prea_inslot
        } else {
            1 - self.prea_inslot
        };
        let iblock = self.iblock();
        self.posta_block = Some(data.block(iblock).get_out(self.posta_outslot));
        self.postb_block = Some(data.block(iblock).get_out(1 - self.posta_outslot));

        let ops = data.block(iblock).get_op_list().to_vec(&data.obank.ops);
        if ops.is_empty() {
            return true;
        }
        for op in ops[..ops.len() - 1].iter().rev() {
            if !self.test_removability(*op, data) {
                return false;
            }
        }
        true
    }

    pub fn trial(&mut self, ib: BlockId, data: &mut Funcdata) -> bool {
        self.iblock = Some(ib);
        self.verify(data)
    }

    pub fn execute(&mut self, data: &mut Funcdata, glb: &mut Architecture) -> Result<()> {
        let iblock = self.iblock();
        let ops = data.block(iblock).get_op_list().to_vec(&data.obank.ops);
        for op in ops.into_iter().rev() {
            if !data.op(op).is_branch() {
                self.do_replacement(op, data, glb)?;
            }
            data.op_destroy(op)?;
        }
        data.remove_from_flow_split(iblock, self.posta_outslot != self.camethruposta_slot, glb)
    }
}

pub struct ActionConditionalExe {
    pub base: ActionBase,
}

impl ActionConditionalExe {
    pub fn new(group: &str) -> ActionConditionalExe {
        ActionConditionalExe {
            base: ActionBase::new(0, "conditionalexe", group),
        }
    }
}

impl Action for ActionConditionalExe {
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
        Some(Box::new(ActionConditionalExe::new(self.get_group())))
    }

    fn apply(&mut self, data: &mut Funcdata, glb: &mut Architecture) -> Result<i32> {
        if data.has_unreachable_blocks() {
            return Ok(0);
        }
        let mut condexe = ConditionalExecution::new(data, glb)?;
        let bblocks = data.bblocks;
        let mut numhits = 0;
        loop {
            let mut changethisround = false;
            let mut index = 0;
            while index < data.block(bblocks).get_size() {
                let bb = data.block(bblocks).get_block(index);
                if condexe.trial(bb, data) {
                    condexe.execute(data, glb)?;
                    numhits += 1;
                    changethisround = true;
                }
                index += 1;
            }
            if !changethisround {
                break;
            }
        }
        self.base.count += numhits;
        Ok(0)
    }
}

#[derive(Clone, Debug, Default)]
pub struct MultiPredicate {
    pub op: Option<OpId>,
    pub zero_slot: i32,
    pub zero_block: Option<BlockId>,
    pub cond_block: Option<BlockId>,
    pub cbranch: Option<OpId>,
    pub other_vn: Option<VarnodeId>,
    pub zero_path_is_true: bool,
}

impl MultiPredicate {
    fn op(&self) -> OpId {
        self.op.expect("predicate without MULTIEQUAL")
    }

    pub fn discover_zero_slot(&mut self, vn: VarnodeId, data: &Funcdata) -> bool {
        let op = match data.vn(vn).get_def() {
            None => return false,
            Some(op) => op,
        };
        self.op = Some(op);
        if data.op(op).code() != OpCode::Multiequal {
            return false;
        }
        if data.op(op).num_input() != 2 {
            return false;
        }
        self.zero_slot = 0;
        while self.zero_slot < 2 {
            let tmpvn = data.op(op).get_in(self.zero_slot);
            let copyop = data.vn(tmpvn).get_def();
            if let Some(copyop) = copyop
                && data.op(copyop).code() == OpCode::Copy
            {
                let zerovn = data.op(copyop).get_in(0);
                if data.vn(zerovn).is_constant() && data.vn(zerovn).get_offset() == 0 {
                    let other_vn = data.op(op).get_in(1 - self.zero_slot);
                    self.other_vn = Some(other_vn);
                    return !data.vn(other_vn).is_free();
                }
            }
            self.zero_slot += 1;
        }
        false
    }

    pub fn discover_cbranch(&mut self, data: &Funcdata) -> bool {
        let base_block = data.op(self.op()).get_parent().expect("MULTIEQUAL without block");
        let zero_block = data.block(base_block).get_in(self.zero_slot);
        self.zero_block = Some(zero_block);
        let other_block = data.block(base_block).get_in(1 - self.zero_slot);
        let cond_block = if data.block(zero_block).size_out() == 1 {
            if data.block(zero_block).size_in() != 1 {
                return false;
            }
            data.block(zero_block).get_in(0)
        } else if data.block(zero_block).size_out() == 2 {
            zero_block
        } else {
            return false;
        };
        self.cond_block = Some(cond_block);
        if data.block(cond_block).size_out() != 2 {
            return false;
        }
        if data.block(other_block).size_out() == 1 {
            if data.block(other_block).size_in() != 1 {
                return false;
            }
            if cond_block != data.block(other_block).get_in(0) {
                return false;
            }
        } else if data.block(other_block).size_out() == 2 {
            if cond_block != other_block {
                return false;
            }
        } else {
            return false;
        }
        self.cbranch = data.block_last_op(cond_block);
        match self.cbranch {
            None => false,
            Some(cbranch) => data.op(cbranch).code() == OpCode::Cbranch,
        }
    }

    pub fn discover_path_is_true(&mut self, data: &Funcdata) {
        let cond_block = data.block(self.cond_block.expect("predicate without condition block"));
        let zero_block = self.zero_block.expect("predicate without zero block");
        if cond_block.get_true_out() == zero_block {
            self.zero_path_is_true = true;
        } else if cond_block.get_false_out() == zero_block {
            self.zero_path_is_true = false;
        } else {
            self.zero_path_is_true = Some(cond_block.get_true_out()) == data.op(self.op()).get_parent();
        }
    }

    pub fn discover_conditional_zero(&mut self, vn: VarnodeId, data: &Funcdata) -> bool {
        let cbranch = self.cbranch.expect("predicate without CBRANCH");
        let boolvn = data.op(cbranch).get_in(1);
        let compareop = match data.vn(boolvn).get_def() {
            None => return false,
            Some(compareop) => compareop,
        };
        let opc = data.op(compareop).code();
        if opc == OpCode::IntNotequal {
            self.zero_path_is_true = !self.zero_path_is_true;
        } else if opc != OpCode::IntEqual {
            return false;
        }
        let a1 = data.op(compareop).get_in(0);
        let a2 = data.op(compareop).get_in(1);
        let zerovn = if a1 == vn {
            a2
        } else if a2 == vn {
            a1
        } else {
            return false;
        };
        if !data.vn(zerovn).is_constant() {
            return false;
        }
        if data.vn(zerovn).get_offset() != 0 {
            return false;
        }
        if data.op(cbranch).is_boolean_flip() {
            self.zero_path_is_true = !self.zero_path_is_true;
        }
        true
    }
}

pub struct RuleOrPredicate {
    pub base: RuleBase,
}

impl RuleOrPredicate {
    pub fn new(group: &str) -> RuleOrPredicate {
        RuleOrPredicate {
            base: RuleBase::new(group, 0, "orpredicate"),
        }
    }

    pub fn check_single(
        &mut self,
        vn: VarnodeId,
        branch: &mut MultiPredicate,
        op: OpId,
        data: &mut Funcdata,
        glb: &mut Architecture,
    ) -> Result<i32> {
        if data.vn(vn).is_free() {
            return Ok(0);
        }
        if !branch.discover_cbranch(data) {
            return Ok(0);
        }
        let branchop = branch.op();
        let branchout = data.op(branchop).get_out().expect("MULTIEQUAL without output");
        if data.vn(branchout).lone_descend() != Some(op) {
            return Ok(0);
        }
        branch.discover_path_is_true(data);
        if !branch.discover_conditional_zero(vn, data) {
            return Ok(0);
        }
        if branch.zero_path_is_true {
            return Ok(0);
        }
        data.op_set_input(branchop, vn, branch.zero_slot)?;
        data.op_remove_input(op, 1);
        data.op_set_opcode(op, OpCode::Copy, glb);
        data.op_set_input(op, branchout, 0)?;
        Ok(1)
    }
}

impl Rule for RuleOrPredicate {
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
        Some(Box::new(RuleOrPredicate::new(self.get_group())))
    }

    fn get_op_list(&self, oplist: &mut Vec<OpCode>) {
        oplist.push(OpCode::IntOr);
        oplist.push(OpCode::IntXor);
    }

    fn apply_op(&mut self, op: OpId, data: &mut Funcdata, glb: &mut Architecture) -> Result<i32> {
        let mut branch0 = MultiPredicate::default();
        let mut branch1 = MultiPredicate::default();
        let in0 = data.op(op).get_in(0);
        let in1 = data.op(op).get_in(1);
        let test0 = branch0.discover_zero_slot(in0, data);
        let test1 = branch1.discover_zero_slot(in1, data);
        if !test0 && !test1 {
            return Ok(0);
        }
        if !test0 {
            return self.check_single(in0, &mut branch1, op, data, glb);
        } else if !test1 {
            return self.check_single(in1, &mut branch0, op, data, glb);
        }
        if !branch0.discover_cbranch(data) {
            return Ok(0);
        }
        if !branch1.discover_cbranch(data) {
            return Ok(0);
        }
        if branch0.cond_block == branch1.cond_block {
            if branch0.zero_block == branch1.zero_block {
                return Ok(0);
            }
        } else {
            let mut condmarker = BooleanExpressionMatch::new();
            let cbranch0 = branch0.cbranch.expect("predicate without CBRANCH");
            let cbranch1 = branch1.cbranch.expect("predicate without CBRANCH");
            if !condmarker.verify_condition(cbranch0, cbranch1, data) {
                return Ok(0);
            }
            if condmarker.get_multi_slot() != -1 {
                return Ok(0);
            }
            branch0.discover_path_is_true(data);
            branch1.discover_path_is_true(data);
            let mut final_bool = branch0.zero_path_is_true == branch1.zero_path_is_true;
            if condmarker.get_flip() {
                final_bool = !final_bool;
            }
            if final_bool {
                return Ok(0);
            }
        }
        let order = data.op_compare_order(branch0.op(), branch1.op());
        if order == 0 {
            return Ok(0);
        }
        let (final_block, slot0_sets_branch0) = if order < 0 {
            (
                data.op(branch1.op()).get_parent().expect("MULTIEQUAL without block"),
                branch1.zero_slot == 0,
            )
        } else {
            (
                data.op(branch0.op()).get_parent().expect("MULTIEQUAL without block"),
                branch0.zero_slot == 1,
            )
        };
        let start = data.block(final_block).get_start();
        let new_multi = data.new_op(2, &start);
        data.op_set_opcode(new_multi, OpCode::Multiequal, glb);
        let other0 = branch0.other_vn.expect("predicate without other varnode");
        let other1 = branch1.other_vn.expect("predicate without other varnode");
        if slot0_sets_branch0 {
            data.op_set_input(new_multi, other0, 0)?;
            data.op_set_input(new_multi, other1, 1)?;
        } else {
            data.op_set_input(new_multi, other1, 0)?;
            data.op_set_input(new_multi, other0, 1)?;
        }
        let othersize = data.vn(other0).get_size();
        let newvn = data.new_unique_out(othersize, new_multi, glb)?;
        data.op_insert_begin(new_multi, final_block);
        data.op_remove_input(op, 1);
        data.op_set_input(op, newvn, 0)?;
        data.op_set_opcode(op, OpCode::Copy, glb);
        Ok(1)
    }
}
