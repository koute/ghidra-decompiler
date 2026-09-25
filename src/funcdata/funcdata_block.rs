use std::collections::BTreeMap;

use crate::action::ActionDatabase;
use crate::address::Address;
use crate::architecture::Architecture;
use crate::block::{BlockId, FlowBlock};
use crate::error::{Error, Result};
use crate::flow::FlowInfo;
use crate::funcdata::Funcdata;
use crate::jumptable::{JumpTable, JumpTableId, RecoveryMode};
use crate::op::{OpId, PcodeOp};
use crate::opcodes::OpCode;
use crate::oplist::{LinkedNode, OpList};
use crate::userop::UserOpType;
use crate::varnode::{Varnode, VarnodeId};

impl Funcdata {
    fn block_ops(&self, bl: BlockId) -> Vec<OpId> {
        self.block(bl).basic().op.to_vec(&self.obank.ops)
    }

    pub fn with_jump_table<R>(&mut self, jt: JumpTableId, run: impl FnOnce(&mut JumpTable, &mut Funcdata) -> R) -> R {
        let placeholder = self.jumptables.get(jt).identity_placeholder();
        let mut table = std::mem::replace(self.jumptables.get_mut(jt), placeholder);
        let res = run(&mut table, self);
        if let Some(slot) = self.jumptables.try_get_mut(jt) {
            *slot = table;
        }
        res
    }

    pub fn print_block_tree(&self, out: &mut String, _glb: &Architecture) {
        if self.block(self.sblocks).get_size() != 0 {
            self.block_print_tree(self.sblocks, out, 0);
        }
    }

    pub fn clear_blocks(&mut self) {
        self.block_clear(self.bblocks);
        self.block_clear(self.sblocks);
    }

    pub fn clear_jump_tables(&mut self) {
        let mut remain = Vec::new();
        for jt in std::mem::take(&mut self.jumpvec) {
            if self.jump_table(jt).is_override() {
                self.jump_table_mut(jt).clear();
                remain.push(jt);
            } else {
                self.jumptables.remove(jt);
            }
        }
        self.jumpvec = remain;
    }

    pub fn remove_jump_table(&mut self, jt: JumpTableId) {
        let remain: Vec<JumpTableId> = self.jumpvec.iter().copied().filter(|other| *other != jt).collect();
        let op = self.jump_table(jt).get_indirect_op();
        self.jumptables.remove(jt);
        if let Some(op) = op {
            let parent = self.op(op).get_parent().expect("jump table op has no parent block");
            self.block_mut(parent).clear_flag(FlowBlock::F_SWITCH_OUT);
        }
        self.jumpvec = remain;
    }

    pub fn create_replace_varnode(
        &mut self,
        origvn: VarnodeId,
        make_unique: bool,
        glb: &mut Architecture,
    ) -> Result<VarnodeId> {
        let (size, addr, tp) = {
            let varnode = self.vn(origvn);
            (varnode.get_size(), varnode.get_addr().clone(), varnode.get_type())
        };
        let replacevn = if make_unique {
            self.new_unique(size, Some(tp), glb)
        } else {
            self.new_varnode(size, &addr, Some(tp), glb)?
        };
        if self.is_high_on() {
            self.vn_replace_in_high(origvn, replacevn)?;
            self.vn_set_flags(replacevn, Varnode::EXPLICT);
        }
        Ok(replacevn)
    }

    pub fn push_multiequals(&mut self, bb: BlockId, glb: &mut Architecture) -> Result<()> {
        if self.block(bb).size_out() == 0 {
            return Ok(());
        }
        if self.block(bb).size_out() > 1 {
            self.warning_header("push_multiequal on block with multiple outputs", glb);
        }
        let outblock = self.block(bb).get_out(0);
        let outblock_ind = self.block(bb).get_out_rev_index(0);
        for origop in self.block_ops(bb) {
            if self.op(origop).code() != OpCode::Multiequal {
                continue;
            }
            let origvn = self.op(origop).get_out().expect("MULTIEQUAL has no output");
            if self.vn(origvn).has_no_descend() {
                continue;
            }
            let mut needreplace = false;
            let mut neednewunique = false;
            for op in self.vn(origvn).descend().iter().copied() {
                let pcode_op = self.op(op);
                if pcode_op.code() == OpCode::Multiequal && pcode_op.get_parent() == Some(outblock) {
                    let mut dead_edge = true;
                    for slot in 0..pcode_op.num_input() {
                        if slot == outblock_ind {
                            continue;
                        }
                        if pcode_op.get_in(slot) == origvn {
                            dead_edge = false;
                            break;
                        }
                    }
                    if dead_edge {
                        let out = pcode_op.get_out().expect("MULTIEQUAL has no output");
                        if self.vn(origvn).get_addr() == self.vn(out).get_addr() && self.vn(origvn).is_addr_tied() {
                            neednewunique = true;
                        }
                        continue;
                    }
                }
                needreplace = true;
                break;
            }
            if !needreplace {
                continue;
            }
            let replacevn = self.create_replace_varnode(origvn, neednewunique, glb)?;
            let mut branches = Vec::new();
            for slot in 0..self.block(outblock).size_in() {
                if self.block(outblock).get_in(slot) == bb {
                    branches.push(origvn);
                } else {
                    branches.push(replacevn);
                }
            }
            let start = self.block(outblock).get_start();
            let replaceop = self.new_op(branches.len() as i32, &start);
            self.op_set_opcode(replaceop, OpCode::Multiequal, glb);
            self.op_set_output(replaceop, replacevn, glb)?;
            self.op_set_all_input(replaceop, &branches)?;
            self.op_insert_begin(replaceop, outblock);
            for op in self.vn(origvn).descend().to_vec() {
                for slot in 0..self.op(op).num_input() {
                    if self.op(op).get_in(slot) != origvn {
                        continue;
                    }
                    if slot == outblock_ind
                        && self.op(op).get_parent() == Some(outblock)
                        && self.op(op).code() == OpCode::Multiequal
                    {
                        continue;
                    }
                    self.op_set_input(op, replacevn, slot)?;
                    break;
                }
            }
        }
        Ok(())
    }

    pub fn op_zero_multi(&mut self, op: OpId, glb: &mut Architecture) -> Result<()> {
        if self.op(op).num_input() == 0 {
            let out = self.op(op).get_out().expect("MULTIEQUAL has no output");
            let (size, addr) = (self.vn(out).get_size(), self.vn(out).get_addr().clone());
            let newvn = self.new_varnode(size, &addr, None, glb)?;
            self.op_insert_input(op, newvn, 0)?;
            let input = self.op(op).get_in(0);
            self.set_input_varnode(input, glb)?;
            self.op_set_opcode(op, OpCode::Copy, glb);
        } else if self.op(op).num_input() == 1 {
            self.op_set_opcode(op, OpCode::Copy, glb);
        }
        Ok(())
    }

    pub fn branch_remove_internal(&mut self, bb: BlockId, num: i32, glb: &mut Architecture) -> Result<()> {
        if self.block(bb).size_out() == 2 {
            let last = self.block_last_op(bb).expect("conditional block has no branch op");
            self.op_destroy(last)?;
        }
        let bbout = self.block(bb).get_out(num);
        let blocknum = self.block(bbout).get_in_index(bb);
        self.block_remove_edge(self.bblocks, bb, bbout)?;
        let mut iter = self.block(bbout).basic().op.front();
        while let Some(op) = iter {
            if self.op(op).code() != OpCode::Multiequal {
                break;
            }
            self.op_remove_input(op, blocknum);
            self.op_zero_multi(op, glb)?;
            iter = self.op(op).links(PcodeOp::BASIC_LIST).next;
        }
        Ok(())
    }

    pub fn remove_branch(&mut self, bb: BlockId, num: i32, glb: &mut Architecture) -> Result<()> {
        self.branch_remove_internal(bb, num, glb)?;
        self.structure_reset(glb)
    }

    pub fn descendants_outside(&self, vn: VarnodeId) -> bool {
        for op in self.vn(vn).descend().iter() {
            let parent = self.op(*op).get_parent().expect("p-code op has no parent block");
            if !self.block(parent).is_dead() {
                return true;
            }
        }
        false
    }

    pub fn block_remove_internal(&mut self, bb: BlockId, unreachable: bool, glb: &mut Architecture) -> Result<()> {
        if let Some(op) = self.block_last_op(bb)
            && self.op(op).code() == OpCode::Branchind
            && let Some(jt) = self.find_jump_table(op)
        {
            self.remove_jump_table(jt);
        }
        if !unreachable {
            self.push_multiequals(bb, glb)?;
            for index in 0..self.block(bb).size_out() {
                let bbout = self.block(bb).get_out(index);
                if self.block(bbout).is_dead() {
                    continue;
                }
                let blocknum = self.block(bbout).get_in_index(bb);
                let mut iter = self.block(bbout).basic().op.front();
                while let Some(op) = iter {
                    iter = self.op(op).links(PcodeOp::BASIC_LIST).next;
                    if self.op(op).code() != OpCode::Multiequal {
                        continue;
                    }
                    let deadvn = self.op(op).get_in(blocknum);
                    self.op_remove_input(op, blocknum);
                    let deadop = self.vn(deadvn).get_def();
                    let append_def = match deadop {
                        Some(def) => {
                            self.vn(deadvn).is_written()
                                && self.op(def).code() == OpCode::Multiequal
                                && self.op(def).get_parent() == Some(bb)
                        }
                        None => false,
                    };
                    if append_def {
                        let def = deadop.expect("dead varnode has no def");
                        for slot in 0..self.block(bb).size_in() {
                            let input = self.op(def).get_in(slot);
                            let position = self.op(op).num_input();
                            self.op_insert_input(op, input, position)?;
                        }
                    } else {
                        for _ in 0..self.block(bb).size_in() {
                            let position = self.op(op).num_input();
                            self.op_insert_input(op, deadvn, position)?;
                        }
                    }
                    self.op_zero_multi(op, glb)?;
                }
            }
        }
        self.block_remove_from_flow(self.bblocks, bb)?;
        let mut desc_warning = false;
        let mut iter = self.block(bb).basic().op.front();
        while let Some(op) = iter {
            if self.op(op).is_assignment() {
                let deadvn = self.op(op).get_out().expect("assignment has no output");
                if unreachable {
                    let undef = self.descend2_undef(deadvn, glb)?;
                    if undef && !desc_warning {
                        self.warning_header("Creating undefined varnodes in (possibly) reachable block", glb);
                        desc_warning = true;
                    }
                }
                if self.descendants_outside(deadvn) {
                    return Err(Error::Lowlevel("Deleting op with descendants\n".to_string()));
                }
            }
            if self.op(op).is_call() {
                self.delete_call_specs(op);
            }
            iter = self.op(op).links(PcodeOp::BASIC_LIST).next;
            self.op_destroy(op)?;
        }
        self.block_remove_block(self.bblocks, bb)
    }

    pub fn remove_do_nothing_block(&mut self, bb: BlockId, glb: &mut Architecture) -> Result<()> {
        if self.block(bb).size_out() > 1 {
            return Err(Error::Lowlevel(
                "Cannot delete a reachable block unless it has 1 out or less".to_string(),
            ));
        }
        self.block_mut(bb).set_dead();
        self.block_remove_internal(bb, false, glb)?;
        self.structure_reset(glb)
    }

    pub fn remove_unreachable_blocks(
        &mut self,
        issuewarning: bool,
        checkexistence: bool,
        glb: &mut Architecture,
    ) -> Result<bool> {
        let size = self.block(self.bblocks).get_size();
        if checkexistence {
            let mut index = 0;
            while index < size {
                let blk = self.block(self.block(self.bblocks).get_block(index));
                if !blk.is_entry_point() && blk.get_immed_dom().is_none() {
                    break;
                }
                index += 1;
            }
            if index == size {
                return Ok(false);
            }
        } else if !self.has_unreachable_blocks() {
            return Ok(false);
        }
        let mut index = 0;
        while index < size {
            if self.block(self.block(self.bblocks).get_block(index)).is_entry_point() {
                break;
            }
            index += 1;
        }
        let entry = self.block(self.bblocks).get_block(index);
        let mut list = Vec::new();
        self.block_collect_reachable(self.bblocks, &mut list, entry, true);
        for bl in list.iter().copied() {
            self.block_mut(bl).set_dead();
            if issuewarning {
                let start = self.block(bl).get_start();
                let mut msg = String::from("Removing unreachable block (");
                msg.push_str(start.get_space().expect("block start has no space").get_name());
                msg.push(',');
                start.print_raw(&mut msg);
                msg.push(')');
                self.warning_header(&msg, glb);
            }
        }
        for bl in list.iter().copied() {
            while self.block(bl).size_out() > 0 {
                self.branch_remove_internal(bl, 0, glb)?;
            }
        }
        for bl in list.iter().copied() {
            self.block_remove_internal(bl, true, glb)?;
        }
        self.structure_reset(glb)?;
        Ok(true)
    }

    pub fn push_branch(&mut self, bb: BlockId, slot: i32, bbnew: BlockId, glb: &mut Architecture) -> Result<()> {
        let cbranch = self.block_last_op(bb);
        let Some(cbranch) =
            cbranch.filter(|op| self.op(*op).code() == OpCode::Cbranch && self.block(bb).size_out() == 2)
        else {
            return Err(Error::Lowlevel("Cannot push non-conditional edge".to_string()));
        };
        let indop = self.block_last_op(bbnew);
        if indop.map(|op| self.op(op).code()) != Some(OpCode::Branchind) {
            return Err(Error::Lowlevel("Can only push branch into indirect jump".to_string()));
        }
        self.op_remove_input(cbranch, 1);
        self.op_set_opcode(cbranch, OpCode::Branch, glb);
        self.block_move_out_edge(self.bblocks, bb, slot, bbnew)?;
        self.structure_reset(glb)
    }

    pub fn link_jump_table(&mut self, op: OpId) -> Option<JumpTableId> {
        let addr = self.op(op).get_addr().clone();
        for jt in self.jumpvec.clone() {
            if *self.jump_table(jt).get_op_address() == addr {
                self.with_jump_table(jt, |table, data| table.set_indirect_op(data, op));
                return Some(jt);
            }
        }
        None
    }

    pub fn find_jump_table(&self, op: OpId) -> Option<JumpTableId> {
        let addr = self.op(op).get_addr();
        self.jumpvec
            .iter()
            .copied()
            .find(|jt| self.jump_table(*jt).get_op_address() == addr)
    }

    pub fn install_jump_table(&mut self, addr: &Address) -> Result<JumpTableId> {
        if self.is_proc_started() {
            return Err(Error::Lowlevel(
                "Cannot install jumptable if flow is already traced".to_string(),
            ));
        }
        for jt in self.jumpvec.iter() {
            if self.jump_table(*jt).get_op_address() == addr {
                return Err(Error::Lowlevel("Trying to install over existing jumptable".to_string()));
            }
        }
        let newjt = self.jumptables.alloc(JumpTable::new(addr.clone()));
        self.jumpvec.push(newjt);
        Ok(newjt)
    }

    pub fn switch_over_jump_tables(&mut self, flow: &FlowInfo, _glb: &mut Architecture) -> Result<()> {
        for jt in self.jumpvec.clone() {
            self.with_jump_table(jt, |table, data| table.switch_over(data, flow))?;
        }
        Ok(())
    }

    fn run_jumptable_action(&mut self, partial: &mut Funcdata, glb: &mut Architecture) -> Result<()> {
        glb.allacts.set_current("jumptable")?;
        if let Some(callback) = self.jtcallback {
            callback(self, partial);
            return Ok(());
        }
        let mut allacts = std::mem::replace(&mut glb.allacts, ActionDatabase::new());
        let res = match allacts.get_current() {
            Some(action) => {
                action.reset(partial, glb);
                action.perform(partial, glb).map(|_| ())
            }
            None => Ok(()),
        };
        glb.allacts = allacts;
        res
    }

    pub fn stage_jump_table(
        &mut self,
        partial: &mut Funcdata,
        jt: JumpTableId,
        op: OpId,
        flow: &mut FlowInfo,
        glb: &mut Architecture,
    ) -> Result<RecoveryMode> {
        self.jump_table_mut(jt).increment_recovery_count();
        let op_addr = self.op(op).get_addr().clone();
        if !partial.is_jumptable_recovery_on() {
            partial.flags |= Funcdata::JUMPTABLERECOVERY_ON;
            partial.truncated_flow(self, flow, glb)?;
            let oldactname = glb.allacts.get_current_name().to_string();
            let res = self.run_jumptable_action(partial, glb);
            let restore = glb.allacts.set_current(&oldactname).map(|_| ());
            match res {
                Ok(()) => restore?,
                Err(err) if err.is_lowlevel() => {
                    self.warning(err.explain(), &op_addr, glb);
                    return Ok(RecoveryMode::FailNormal);
                }
                Err(err) => return Err(err),
            }
        }
        let seq = self.op(op).get_seq_num().clone();
        let partop = partial.find_op(&seq);
        let Some(partop) = partop.filter(|partop| {
            partial.op(*partop).code() == OpCode::Branchind && *partial.op(*partop).get_addr() == op_addr
        }) else {
            return Err(Error::Lowlevel(
                "Error recovering jumptable: Bad partial clone".to_string(),
            ));
        };
        if partial.op(partop).is_dead() {
            return Ok(RecoveryMode::Success);
        }
        let target = partial.op(partop).get_in(0);
        if partial.test_for_return_address(target, glb) {
            return Ok(RecoveryMode::FailReturn);
        }
        let table = self.jump_table_mut(jt);
        table.set_load_collect(flow.does_jump_record());
        table.set_indirect_op(partial, partop);
        let res = if table.is_partial() {
            table.recover_multistage(partial, glb)
        } else {
            table.recover_addresses(partial, glb)
        };
        match res {
            Ok(()) => Ok(RecoveryMode::Success),
            Err(Error::JumptableThunk(_)) => Ok(RecoveryMode::FailThunk),
            Err(err) if err.is_lowlevel() => {
                self.warning(err.explain(), &op_addr, glb);
                Ok(RecoveryMode::FailNormal)
            }
            Err(err) => Err(err),
        }
    }

    pub fn early_jump_table_fail(&mut self, op: OpId, glb: &mut Architecture) -> RecoveryMode {
        let mut vn = self.op(op).get_in(0);
        let mut iter = op;
        let mut count_max = 8;
        while let Some(previous) = self.op(iter).links(PcodeOp::INSERT_LIST).prev {
            if self.vn(vn).get_size() == 1 {
                return RecoveryMode::Success;
            }
            count_max -= 1;
            if count_max < 0 {
                return RecoveryMode::Success;
            }
            iter = previous;
            let cur = self.op(iter);
            let outhit = match cur.get_out() {
                Some(outvn) => self.vn(vn).intersects(self.vn(outvn)),
                None => false,
            };
            let eval_type = cur.get_eval_type();
            if eval_type == PcodeOp::SPECIAL {
                if cur.is_call() {
                    let opc = cur.code();
                    if opc == OpCode::Callother {
                        let id = self.vn(cur.get_in(0)).get_offset() as i32;
                        let user_op_type = glb.userops.get_op(id as u32).map(|userop| userop.get_type());
                        if user_op_type == Some(UserOpType::Injected) {
                            return RecoveryMode::Success;
                        }
                        if user_op_type == Some(UserOpType::Jumpassist) {
                            return RecoveryMode::Success;
                        }
                        if user_op_type == Some(UserOpType::Segment) {
                            return RecoveryMode::Success;
                        }
                        if outhit {
                            return RecoveryMode::FailCallother;
                        }
                    } else {
                        return RecoveryMode::Success;
                    }
                } else if cur.is_branch() {
                    return RecoveryMode::Success;
                } else {
                    if cur.code() == OpCode::Store {
                        return RecoveryMode::Success;
                    }
                    if outhit {
                        return RecoveryMode::Success;
                    }
                }
            } else if eval_type == PcodeOp::UNARY {
                if outhit {
                    let invn = cur.get_in(0);
                    if self.vn(invn).get_size() != self.vn(vn).get_size() {
                        return RecoveryMode::Success;
                    }
                    vn = invn;
                }
            } else if eval_type == PcodeOp::BINARY {
                if outhit {
                    let opc = cur.code();
                    if opc != OpCode::IntAdd && opc != OpCode::IntSub && opc != OpCode::IntXor {
                        return RecoveryMode::Success;
                    }
                    if !self.vn(cur.get_in(1)).is_constant() {
                        return RecoveryMode::Success;
                    }
                    let invn = cur.get_in(0);
                    if self.vn(invn).get_size() != self.vn(vn).get_size() {
                        return RecoveryMode::Success;
                    }
                    vn = invn;
                }
            } else if outhit {
                return RecoveryMode::Success;
            }
        }
        RecoveryMode::Success
    }

    pub fn recover_jump_table(
        &mut self,
        partial: &mut Funcdata,
        op: OpId,
        flow: &mut FlowInfo,
        mode: &mut RecoveryMode,
        glb: &mut Architecture,
    ) -> Result<Option<JumpTableId>> {
        *mode = RecoveryMode::Success;
        if let Some(jt) = self.link_jump_table(op) {
            if !self.jump_table(jt).is_override()
                && !self.jump_table(jt).is_partial()
                && self.jump_table(jt).num_entries() != 0
            {
                return Ok(Some(jt));
            }
            *mode = self.stage_jump_table(partial, jt, op, flow, glb)?;
            if *mode != RecoveryMode::Success {
                return Ok(None);
            }
            self.with_jump_table(jt, |table, data| table.set_indirect_op(data, op));
            return Ok(Some(jt));
        }
        if (self.flags & Funcdata::JUMPTABLERECOVERY_DONT) != 0 {
            return Ok(None);
        }
        *mode = self.early_jump_table_fail(op, glb);
        if *mode != RecoveryMode::Success {
            return Ok(None);
        }
        let trialjt = self.jumptables.alloc(JumpTable::default());
        let staged = self.stage_jump_table(partial, trialjt, op, flow, glb);
        let trial = self.jumptables.remove(trialjt);
        *mode = staged?;
        if *mode != RecoveryMode::Success {
            return Ok(None);
        }
        let jt = self.jumptables.alloc(JumpTable::from_table(&trial));
        self.jumpvec.push(jt);
        self.with_jump_table(jt, |table, data| table.set_indirect_op(data, op));
        Ok(Some(jt))
    }

    pub fn install_switch_defaults(&mut self) {
        for jt in self.jumpvec.clone() {
            let table = self.jump_table(jt);
            let indop = table.get_indirect_op().expect("jump table has no indirect op");
            let ind = self.op(indop).get_parent().expect("jump table op has no parent block");
            let default_block = table.get_default_block();
            if default_block != -1 {
                self.block_set_default_switch(ind, default_block);
            }
        }
    }

    pub fn structure_reset(&mut self, glb: &mut Architecture) -> Result<()> {
        let mut rootlist = Vec::new();
        self.flags &= !Funcdata::BLOCKS_UNREACHABLE;
        self.block_structure_loops(self.bblocks, &mut rootlist)?;
        self.block_calc_forward_dominator(self.bblocks, &rootlist)?;
        if rootlist.len() > 1 {
            self.flags |= Funcdata::BLOCKS_UNREACHABLE;
        }
        let mut alivejumps = Vec::new();
        for jt in std::mem::take(&mut self.jumpvec) {
            let indop = self
                .jump_table(jt)
                .get_indirect_op()
                .expect("jump table has no indirect op");
            if self.op(indop).is_dead() {
                self.warning_header("Recovered jumptable eliminated as dead code", glb);
                self.jumptables.remove(jt);
                continue;
            }
            alivejumps.push(jt);
        }
        self.jumpvec = alivejumps;
        self.block_clear(self.sblocks);
        self.heritage.force_restructure();
        Ok(())
    }

    pub fn force_goto(&mut self, pcop: &Address, pcdest: &Address) -> bool {
        for index in 0..self.block(self.bblocks).get_size() {
            let bl = self.block(self.bblocks).get_block(index);
            let Some(op) = self.block_last_op(bl) else {
                continue;
            };
            if self.op(op).get_addr() != pcop {
                continue;
            }
            for slot in 0..self.block(bl).size_out() {
                let bl2 = self.block(bl).get_out(slot);
                let Some(op2) = self.block_last_op(bl2) else {
                    continue;
                };
                if self.op(op2).get_addr() != pcdest {
                    continue;
                }
                self.block_set_goto_branch(bl, slot)
                    .expect("goto branch index is within the out edges");
                return true;
            }
        }
        false
    }

    pub fn node_join_create_block(
        &mut self,
        block1: BlockId,
        block2: BlockId,
        exita: BlockId,
        exitb: BlockId,
        fora_block1ishigh: bool,
        forb_block1ishigh: bool,
        addr: &Address,
        glb: &mut Architecture,
    ) -> Result<BlockId> {
        let newblock = self.block_new_block_basic(self.bblocks);
        self.block_mut(newblock).set_flag(FlowBlock::F_JOINED_BLOCK);
        self.block_mut(newblock).set_initial_range(addr, addr);
        let swapa = if fora_block1ishigh {
            self.block_remove_edge(self.bblocks, block1, exita)?;
            block2
        } else {
            self.block_remove_edge(self.bblocks, block2, exita)?;
            block1
        };
        let swapb = if forb_block1ishigh {
            self.block_remove_edge(self.bblocks, block1, exitb)?;
            block2
        } else {
            self.block_remove_edge(self.bblocks, block2, exitb)?;
            block1
        };
        let slota = self.block(swapa).get_out_index(exita);
        self.block_move_out_edge(self.bblocks, swapa, slota, newblock)?;
        let slotb = self.block(swapb).get_out_index(exitb);
        self.block_move_out_edge(self.bblocks, swapb, slotb, newblock)?;
        self.block_add_edge(self.bblocks, block1, newblock)?;
        self.block_add_edge(self.bblocks, block2, newblock)?;
        self.structure_reset(glb)?;
        Ok(newblock)
    }

    pub fn node_split_block_edge(&mut self, block: BlockId, inedge: i32, _glb: &mut Architecture) -> Result<BlockId> {
        let from = self.block(block).get_in(inedge);
        let bprime = self.block_new_block_basic(self.bblocks);
        self.block_mut(bprime).set_flag(FlowBlock::F_DUPLICATE_BLOCK);
        self.block_copy_range(bprime, block);
        self.block_switch_edge(self.bblocks, from, block, bprime);
        for index in 0..self.block(block).size_out() {
            let out = self.block(block).get_out(index);
            self.block_add_edge(self.bblocks, bprime, out)?;
        }
        Ok(bprime)
    }

    pub fn node_split(&mut self, block: BlockId, inedge: i32, glb: &mut Architecture) -> Result<()> {
        if self.block(block).size_out() != 0 {
            return Err(Error::Lowlevel(
                "Cannot (currently) nodesplit block with out flow".to_string(),
            ));
        }
        if self.block(block).size_in() <= 1 {
            return Err(Error::Lowlevel(
                "Cannot nodesplit block with only 1 in edge".to_string(),
            ));
        }
        for index in 0..self.block(block).size_in() {
            let input = self.block(block).get_in(index);
            if self.block(input).is_mark() {
                return Err(Error::Lowlevel(
                    "Cannot nodesplit block with redundant in edges".to_string(),
                ));
            }
            self.block_mut(block).set_mark();
        }
        for _ in 0..self.block(block).size_in() {
            self.block_mut(block).clear_mark();
        }
        let bprime = self.node_split_block_edge(block, inedge, glb)?;
        let mut cloner = CloneBlockOps::new();
        cloner.clone_block(self, block, bprime, inedge, glb)?;
        self.structure_reset(glb)
    }

    pub fn remove_from_flow_split(&mut self, bl: BlockId, swap: bool, glb: &mut Architecture) -> Result<()> {
        if !self.block(bl).empty_op() {
            return Err(Error::Lowlevel(
                "Can only split the flow for an empty block".to_string(),
            ));
        }
        self.block_remove_from_flow_split(self.bblocks, bl, swap)?;
        self.block_remove_block(self.bblocks, bl)?;
        self.structure_reset(glb)
    }

    pub fn switch_edge(
        &mut self,
        inblock: BlockId,
        outbefore: BlockId,
        outafter: BlockId,
        glb: &mut Architecture,
    ) -> Result<()> {
        self.block_switch_edge(self.bblocks, inblock, outbefore, outafter);
        self.structure_reset(glb)
    }

    pub fn splice_block_basic(&mut self, bl: BlockId, glb: &mut Architecture) -> Result<()> {
        let mut outbl = None;
        if self.block(bl).size_out() == 1 {
            let candidate = self.block(bl).get_out(0);
            if self.block(candidate).size_in() == 1 {
                outbl = Some(candidate);
            }
        }
        let Some(outbl) = outbl else {
            return Err(Error::Lowlevel("Cannot splice basic blocks".to_string()));
        };
        if let Some(jumpop) = self.block(bl).basic().op.back()
            && self.op(jumpop).is_branch()
        {
            self.op_destroy(jumpop)?;
        }
        if let Some(firstop) = self.block(outbl).basic().op.front() {
            if self.op(firstop).code() == OpCode::Multiequal {
                return Err(Error::Lowlevel("Splicing block with MULTIEQUAL".to_string()));
            }
            self.op_mut(firstop).clear_flag(PcodeOp::STARTBASIC);
            for op in self.block_ops(outbl) {
                self.op_mut(op).set_parent(Some(bl));
            }
            let mut outlist = std::mem::replace(
                &mut self.block_mut(outbl).basic_mut().op,
                OpList::new(PcodeOp::BASIC_LIST),
            );
            let mut bllist =
                std::mem::replace(&mut self.block_mut(bl).basic_mut().op, OpList::new(PcodeOp::BASIC_LIST));
            bllist.append_all(&mut self.obank.ops, &mut outlist);
            self.block_mut(bl).basic_mut().op = bllist;
            self.block_mut(outbl).basic_mut().op = outlist;
            self.block_set_order(bl);
        }
        self.block_merge_range(bl, outbl);
        self.block_splice_block(self.bblocks, bl)?;
        self.structure_reset(glb)
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ClonePair {
    pub clone_op: OpId,
    pub orig_op: OpId,
}

impl ClonePair {
    pub fn new(clone_op: OpId, orig_op: OpId) -> ClonePair {
        ClonePair { clone_op, orig_op }
    }
}

#[derive(Clone, Debug, Default)]
pub struct CloneBlockOps {
    pub(crate) clone_list: Vec<ClonePair>,
    pub(crate) orig_to_clone: BTreeMap<OpId, OpId>,
}

impl CloneBlockOps {
    pub fn new() -> CloneBlockOps {
        CloneBlockOps {
            clone_list: Vec::new(),
            orig_to_clone: BTreeMap::new(),
        }
    }

    pub fn build_op_clone(&mut self, data: &mut Funcdata, op: OpId, glb: &mut Architecture) -> Result<Option<OpId>> {
        if data.op(op).is_branch() {
            if data.op(op).code() != OpCode::Branch {
                return Err(Error::Lowlevel(
                    "Cannot duplicate 2-way or n-way branch in nodeplit".to_string(),
                ));
            }
            return Ok(None);
        }
        let op_addr = data.op(op).get_addr().clone();
        let dup = data.new_op(data.op(op).num_input(), &op_addr);
        data.op_set_opcode(dup, data.op(op).code(), glb);
        let fl = data.op(op).flags
            & (PcodeOp::STARTBASIC
                | PcodeOp::NOCOLLAPSE
                | PcodeOp::STARTMARK
                | PcodeOp::NONPRINTING
                | PcodeOp::HALT
                | PcodeOp::BADINSTRUCTION
                | PcodeOp::UNIMPLEMENTED
                | PcodeOp::NORETURN
                | PcodeOp::MISSING
                | PcodeOp::INDIRECT_CREATION
                | PcodeOp::INDIRECT_STORE
                | PcodeOp::NO_INDIRECT_COLLAPSE
                | PcodeOp::CALCULATED_BOOL
                | PcodeOp::PTRFLOW);
        data.op_mut(dup).set_flag(fl);
        let addl = data.op(op).addlflags
            & (PcodeOp::SPECIAL_PROP
                | PcodeOp::SPECIAL_PRINT
                | PcodeOp::INCIDENTAL_COPY
                | PcodeOp::IS_CPOOL_TRANSFORMED
                | PcodeOp::STOP_TYPE_PROPAGATION
                | PcodeOp::STORE_UNMAPPED);
        data.op_mut(dup).set_additional_flag(addl);
        self.clone_list.push(ClonePair::new(dup, op));
        self.orig_to_clone.insert(op, dup);
        Ok(Some(dup))
    }

    pub fn build_varnode_output(
        &mut self,
        data: &mut Funcdata,
        orig_op: OpId,
        clone_op: OpId,
        glb: &mut Architecture,
    ) -> Result<()> {
        let Some(opvn) = data.op(orig_op).get_out() else {
            return Ok(());
        };
        let (size, addr) = (data.vn(opvn).get_size(), data.vn(opvn).get_addr().clone());
        let newvn = data.new_varnode_out(size, &addr, clone_op, glb)?;
        let vflags = data.vn(opvn).get_flags()
            & (Varnode::EXTERNREF
                | Varnode::VOLATIL
                | Varnode::INCIDENTAL_COPY
                | Varnode::READONLY
                | Varnode::PERSIST
                | Varnode::ADDRTIED
                | Varnode::ADDRFORCE
                | Varnode::NOLOCALALIAS
                | Varnode::SPACEBASE
                | Varnode::INDIRECT_CREATION
                | Varnode::RETURN_ADDRESS
                | Varnode::PRECISLO
                | Varnode::PRECISHI
                | Varnode::INCIDENTAL_COPY);
        data.vn_set_flags(newvn, vflags);
        let aflags = data.vn(opvn).addlflags & (Varnode::WRITEMASK | Varnode::PTRFLOW | Varnode::STACK_STORE);
        data.vn_mut(newvn).addlflags |= aflags;
        Ok(())
    }

    pub fn patch_inputs(&mut self, data: &mut Funcdata, inedge: i32, glb: &mut Architecture) -> Result<()> {
        for pos in 0..self.clone_list.len() {
            let orig_op = self.clone_list[pos].orig_op;
            let clone_op = self.clone_list[pos].clone_op;
            if data.op(orig_op).code() == OpCode::Multiequal {
                data.op_mut(clone_op).set_num_inputs(1);
                data.op_set_opcode(clone_op, OpCode::Copy, glb);
                let input = data.op(orig_op).get_in(inedge);
                data.op_set_input(clone_op, input, 0)?;
                data.op_remove_input(orig_op, inedge);
                if data.op(orig_op).num_input() == 1 {
                    data.op_set_opcode(orig_op, OpCode::Copy, glb);
                }
            } else if data.op(orig_op).code() == OpCode::Indirect {
                return Err(Error::Lowlevel("Can't clone INDIRECTs".to_string()));
            } else if data.op(orig_op).is_call() {
                return Err(Error::Lowlevel("Can't clone CALLs".to_string()));
            } else {
                for slot in 0..data.op(clone_op).num_input() {
                    let orig_vn = data.op(orig_op).get_in(slot);
                    let clone_vn = if data.vn(orig_vn).is_constant() {
                        orig_vn
                    } else if data.vn(orig_vn).is_annotation() {
                        let addr = data.vn(orig_vn).get_addr().clone();
                        data.new_code_ref(&addr, glb)
                    } else if data.vn(orig_vn).is_free() {
                        return Err(Error::Lowlevel("Can't clone free varnode".to_string()));
                    } else if data.vn(orig_vn).is_written() {
                        let def = data.vn(orig_vn).get_def().expect("written varnode has no def");
                        match self.orig_to_clone.get(&def) {
                            Some(clone_def) => data.op(*clone_def).get_out().expect("cloned op has no output"),
                            None => orig_vn,
                        }
                    } else {
                        orig_vn
                    };
                    data.op_set_input(clone_op, clone_vn, slot)?;
                }
            }
        }
        Ok(())
    }

    pub fn clone_block(
        &mut self,
        data: &mut Funcdata,
        block: BlockId,
        bprime: BlockId,
        inedge: i32,
        glb: &mut Architecture,
    ) -> Result<()> {
        for orig_op in data.block_ops(block) {
            let Some(clone_op) = self.build_op_clone(data, orig_op, glb)? else {
                continue;
            };
            self.build_varnode_output(data, orig_op, clone_op, glb)?;
            data.op_insert_end(clone_op, bprime);
        }
        self.patch_inputs(data, inedge, glb)
    }

    pub fn clone_expression(
        &mut self,
        data: &mut Funcdata,
        ops: &[OpId],
        follow_op: OpId,
        glb: &mut Architecture,
    ) -> Result<VarnodeId> {
        for orig_op in ops.iter().copied() {
            let Some(clone_op) = self.build_op_clone(data, orig_op, glb)? else {
                continue;
            };
            self.build_varnode_output(data, orig_op, clone_op, glb)?;
            data.op_insert_before(clone_op, follow_op);
        }
        let Some(last) = self.clone_list.last().copied() else {
            return Err(Error::Lowlevel("No expression to clone".to_string()));
        };
        self.patch_inputs(data, 0, glb)?;
        Ok(data
            .op(last.clone_op)
            .get_out()
            .expect("cloned expression has no output"))
    }
}
