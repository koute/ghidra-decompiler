use crate::space::SpaceType;
use std::cell::RefCell;
use std::collections::{BTreeMap, BTreeSet};
use std::ops::Bound;
use std::rc::Rc;

use crate::address::{Address, SeqNum};
use crate::architecture::Architecture;
use crate::comment::Comment;
use crate::database::Database;
use crate::error::{Error, Result};
use crate::fspec::{CallSpecId, FuncCallSpecs};
use crate::funcdata::{Funcdata, PcodeEmitFd};
use crate::jumptable::{JumpTableId, RecoveryMode};
use crate::op::{OpId, PcodeOp};
use crate::opcodes::OpCode;
use crate::overrides::Override;
use crate::pcoderaw::VarnodeData;
use crate::userop::UserOpType;
use crate::varnode::{Varnode, VarnodeId};

pub const IGNORE_OUTOFBOUNDS: u32 = 1;
pub const IGNORE_UNIMPLEMENTED: u32 = 2;
pub const ERROR_OUTOFBOUNDS: u32 = 4;
pub const ERROR_UNIMPLEMENTED: u32 = 8;
pub const ERROR_REINTERPRETED: u32 = 0x10;
pub const ERROR_TOOMANYINSTRUCTIONS: u32 = 0x20;
pub const ERROR_BADDATA: u32 = 0x40;
pub const UNIMPLEMENTED_PRESENT: u32 = 0x80;
pub const BADDATA_PRESENT: u32 = 0x100;
pub const OUTOFBOUNDS_PRESENT: u32 = 0x200;
pub const REINTERPRETED_PRESENT: u32 = 0x400;
pub const TOOMANYINSTRUCTIONS_PRESENT: u32 = 0x800;
pub const POSSIBLE_UNREACHABLE: u32 = 0x1000;
pub const FLOW_FORINLINE: u32 = 0x2000;
pub const RECORD_JUMPLOADS: u32 = 0x4000;

#[derive(Clone, Debug, Default)]
pub struct VisitStat {
    pub seqnum: SeqNum,
    pub size: i32,
}

#[derive(Clone, Debug)]
pub struct InlineHead {
    pub baseaddr: Address,
    pub jumptable_recovery: bool,
    pub pending: RefCell<Vec<(String, Address)>>,
}

impl InlineHead {
    pub fn new(data: &Funcdata) -> InlineHead {
        InlineHead {
            baseaddr: data.get_address().clone(),
            jumptable_recovery: data.is_jumptable_recovery_on(),
            pending: RefCell::new(Vec::new()),
        }
    }

    pub fn defer_warning(&self, txt: &str, ad: &Address) {
        self.pending.borrow_mut().push((txt.to_string(), ad.clone()));
    }

    pub fn flush_warnings(&self, glb: &mut Architecture) {
        let pending = std::mem::take(&mut *self.pending.borrow_mut());
        for (txt, ad) in pending {
            self.warning(&txt, &ad, glb);
        }
    }

    pub fn warning(&self, txt: &str, ad: &Address, glb: &mut Architecture) {
        let mut msg = if self.jumptable_recovery {
            String::from("WARNING (jumptable): ")
        } else {
            String::from("WARNING: ")
        };
        msg.push_str(txt);
        glb.commentdb
            .as_mut()
            .expect("comment database is missing")
            .add_comment_no_duplicate(Comment::WARNING, &self.baseaddr, ad, &msg);
    }
}

pub type InlineRecursion = Rc<RefCell<BTreeSet<Address>>>;

pub struct FlowInfo {
    unprocessed: Vec<Address>,
    addrlist: Vec<Address>,
    tablelist: Vec<OpId>,
    injectlist: Vec<Option<OpId>>,
    visited: BTreeMap<Address, VisitStat>,
    block_edge1: Vec<OpId>,
    block_edge2: Vec<OpId>,
    insn_count: u32,
    insn_max: u32,
    baddr: Address,
    eaddr: Address,
    minaddr: Address,
    maxaddr: Address,
    pcode_override_present: bool,
    flags: u32,
    baddata_count: u32,
    inline_head: Option<Rc<InlineHead>>,
    inline_recursion: Option<InlineRecursion>,
    inline_base: InlineRecursion,
}

fn space_and_raw(addr: &Address) -> String {
    let mut text = String::new();
    text.push_str(addr.get_space().map_or("", |spc| spc.get_name()));
    text.push(',');
    addr.print_raw(&mut text);
    text
}

fn dead_next(data: &Funcdata, op: OpId) -> Option<OpId> {
    data.obank.deadlist.next(&data.obank.ops, op)
}

fn dead_prev(data: &Funcdata, pos: Option<OpId>) -> Option<OpId> {
    match pos {
        Some(op) => data.obank.deadlist.prev(&data.obank.ops, op),
        None => data.obank.deadlist.back(),
    }
}

fn clone_foreign_varnode(data: &mut Funcdata, source: &Funcdata, vn: VarnodeId) -> VarnodeId {
    let original = source.vn(vn);
    let is_foreign_call_spec = original.get_space().map(|spc| spc.get_type()) == Some(SpaceType::Fspec);
    let address = if is_foreign_call_spec {
        let foreign_spec = FuncCallSpecs::get_fspec_from_const(original.get_addr());
        source.call_spec(foreign_spec).get_entry_address().clone()
    } else {
        original.get_addr().clone()
    };
    let newvn = data.vbank.create(original.get_size(), &address, original.get_type());
    let vflags = original.get_flags()
        & (Varnode::ANNOTATION
            | Varnode::EXTERNREF
            | Varnode::READONLY
            | Varnode::PERSIST
            | Varnode::ADDRTIED
            | Varnode::ADDRFORCE
            | Varnode::INDIRECT_CREATION
            | Varnode::INCIDENTAL_COPY
            | Varnode::VOLATIL
            | Varnode::MAPPED);
    let highs = &mut data.highs;
    data.vbank.varnodes.get_mut(newvn).set_flags(vflags, highs);
    newvn
}

fn clone_foreign_op(
    data: &mut Funcdata,
    source: &Funcdata,
    op: OpId,
    seq: &SeqNum,
    glb: &mut Architecture,
) -> Result<OpId> {
    let original = source.op(op);
    let num_input = original.num_input();
    let newop = data.new_op_seq(num_input, seq);
    data.op_set_opcode(newop, original.code(), glb);
    let fl = original.flags & (PcodeOp::STARTMARK | PcodeOp::STARTBASIC);
    data.op_mut(newop).set_flag(fl);
    if let Some(out) = original.get_out() {
        let newout = clone_foreign_varnode(data, source, out);
        data.op_set_output(newop, newout, glb)?;
    }
    for slot in 0..num_input {
        let input = source.op(op).get_in(slot);
        let newin = clone_foreign_varnode(data, source, input);
        data.op_set_input(newop, newin, slot)?;
    }
    Ok(newop)
}

impl FlowInfo {
    pub fn new(data: &mut Funcdata) -> FlowInfo {
        let space = data.get_address().get_space().cloned();
        FlowInfo {
            unprocessed: Vec::new(),
            addrlist: Vec::new(),
            tablelist: Vec::new(),
            injectlist: Vec::new(),
            visited: BTreeMap::new(),
            block_edge1: Vec::new(),
            block_edge2: Vec::new(),
            insn_count: 0,
            insn_max: u32::MAX,
            baddr: Address::from_parts(space.clone(), 0),
            eaddr: Address::from_parts(space, u64::MAX),
            minaddr: data.get_address().clone(),
            maxaddr: data.get_address().clone(),
            pcode_override_present: data.get_override().has_pcode_override(),
            flags: 0,
            baddata_count: 0,
            inline_head: None,
            inline_recursion: None,
            inline_base: Rc::new(RefCell::new(BTreeSet::new())),
        }
    }

    pub fn new_clone(data: &mut Funcdata, op2: &FlowInfo) -> FlowInfo {
        let inline_base: InlineRecursion = Rc::new(RefCell::new(BTreeSet::new()));
        let inline_recursion = if op2.inline_head.is_some() {
            *inline_base.borrow_mut() = op2.inline_base.borrow().clone();
            Some(inline_base.clone())
        } else {
            None
        };
        FlowInfo {
            unprocessed: op2.unprocessed.clone(),
            addrlist: op2.addrlist.clone(),
            tablelist: Vec::new(),
            injectlist: Vec::new(),
            visited: op2.visited.clone(),
            block_edge1: Vec::new(),
            block_edge2: Vec::new(),
            insn_count: op2.insn_count,
            insn_max: op2.insn_max,
            baddr: op2.baddr.clone(),
            eaddr: op2.eaddr.clone(),
            minaddr: data.get_address().clone(),
            maxaddr: data.get_address().clone(),
            pcode_override_present: data.get_override().has_pcode_override(),
            flags: op2.flags,
            baddata_count: op2.baddata_count,
            inline_head: op2.inline_head.clone(),
            inline_recursion,
            inline_base,
        }
    }

    fn has_possible_unreachable(&self) -> bool {
        (self.flags & POSSIBLE_UNREACHABLE) != 0
    }

    fn set_possible_unreachable(&mut self) {
        self.flags |= POSSIBLE_UNREACHABLE;
    }

    fn clear_properties(&mut self) {
        self.flags &= !(UNIMPLEMENTED_PRESENT | BADDATA_PRESENT | OUTOFBOUNDS_PRESENT);
        self.insn_count = 0;
        self.baddata_count = 0;
    }

    fn seen_instruction(&self, addr: &Address) -> bool {
        self.visited.contains_key(addr)
    }

    fn last_visited_at_or_before(&self, addr: &Address) -> Option<(&Address, &VisitStat)> {
        self.visited.range(..=addr.clone()).next_back()
    }

    fn fallthru_op(&self, op: OpId, data: &Funcdata) -> Result<Option<OpId>> {
        if let Some(retop) = dead_next(data, op)
            && !data.op(retop).is_instruction_start()
        {
            return Ok(Some(retop));
        }
        let opaddr = data.op(op).get_addr();
        let Some((first, stat)) = self.last_visited_at_or_before(opaddr) else {
            return Ok(None);
        };
        let endaddr = first.add(stat.size as i64);
        if endaddr <= *opaddr {
            return Ok(None);
        }
        Ok(Some(self.target(&endaddr, data)?))
    }

    fn new_address(&mut self, from: OpId, to: &Address, data: &mut Funcdata, glb: &mut Architecture) -> Result<()> {
        if *to < self.baddr || self.eaddr < *to {
            let fromaddr = data.op(from).get_addr().clone();
            self.handle_out_of_bounds(&fromaddr, to, data, glb)?;
            self.unprocessed.push(to.clone());
            return Ok(());
        }
        if self.seen_instruction(to) {
            let op = self.target(to, data)?;
            data.op_mark_start_basic(op);
            return Ok(());
        }
        self.addrlist.push(to.clone());
        Ok(())
    }

    fn delete_remaining_ops(&mut self, oiter: Option<OpId>, data: &mut Funcdata) -> Result<()> {
        let mut current = oiter;
        while let Some(op) = current {
            current = dead_next(data, op);
            data.op_destroy_raw(op)?;
        }
        Ok(())
    }

    fn xref_control_flow(
        &mut self,
        oiter: Option<OpId>,
        startbasic: &mut bool,
        isfallthru: &mut bool,
        fc: Option<CallSpecId>,
        data: &mut Funcdata,
        glb: &mut Architecture,
    ) -> Result<Option<OpId>> {
        let mut last_op: Option<OpId> = None;
        let mut position = oiter;
        *isfallthru = false;
        let mut maxtime: u32 = 0;
        while let Some(op) = position {
            position = dead_next(data, op);
            last_op = Some(op);
            if *startbasic {
                data.op_mark_start_basic(op);
                *startbasic = false;
            }
            match data.op(op).code() {
                OpCode::Cbranch | OpCode::Branch => {
                    let is_branch = data.op(op).code() == OpCode::Branch;
                    let destaddr = data.vn(data.op(op).get_in(0)).get_addr().clone();
                    if destaddr.is_constant() {
                        let mut fall_thru_addr = Address::invalid();
                        let destop = self.find_rel_target(op, &mut fall_thru_addr, data)?;
                        if let Some(destop) = destop {
                            data.op_mark_start_basic(destop);
                            let newtime = data.op(destop).get_time();
                            if newtime > maxtime {
                                maxtime = newtime;
                            }
                        } else {
                            *isfallthru = true;
                        }
                    } else {
                        self.new_address(op, &destaddr, data, glb)?;
                    }
                    if is_branch && data.op(op).get_time() >= maxtime {
                        self.delete_remaining_ops(position, data)?;
                        position = None;
                    }
                    *startbasic = true;
                }
                OpCode::Branchind => {
                    self.tablelist.push(op);
                    if data.op(op).get_time() >= maxtime {
                        self.delete_remaining_ops(position, data)?;
                        position = None;
                    }
                    *startbasic = true;
                }
                OpCode::Return => {
                    if data.op(op).get_time() >= maxtime {
                        self.delete_remaining_ops(position, data)?;
                        position = None;
                    }
                    *startbasic = true;
                }
                OpCode::Call if self.setup_call_specs(op, fc, data, glb)? => {
                    position = dead_prev(data, position);
                }
                OpCode::Callind if self.setup_callind_specs(op, fc, data, glb)? => {
                    position = dead_prev(data, position);
                }
                OpCode::Callother => {
                    let index = data.vn(data.op(op).get_in(0)).get_offset();
                    let injected = glb
                        .userops
                        .get_op(index as u32)
                        .is_some_and(|userop| userop.get_type() == UserOpType::Injected);
                    if injected {
                        self.injectlist.push(Some(op));
                    }
                }
                _ => {}
            }
        }
        if *isfallthru {
            *startbasic = true;
        } else {
            match last_op {
                None => *isfallthru = true,
                Some(op) => match data.op(op).code() {
                    OpCode::Branch | OpCode::Branchind | OpCode::Return => {}
                    _ => *isfallthru = true,
                },
            }
        }
        Ok(last_op)
    }

    fn process_instruction(
        &mut self,
        curaddr: &Address,
        startbasic: &mut bool,
        data: &mut Funcdata,
        glb: &mut Architecture,
    ) -> Result<bool> {
        let mut isfallthru = true;
        if self.insn_count >= self.insn_max {
            if (self.flags & ERROR_TOOMANYINSTRUCTIONS) != 0 {
                return Err(Error::Lowlevel(
                    "Flow exceeded maximum allowable instructions".to_string(),
                ));
            }
            self.artificial_halt(curaddr, PcodeOp::BADINSTRUCTION, data, glb)?;
            data.warning("Too many instructions -- Truncating flow here", curaddr, glb);
            if !self.has_too_many_instructions() {
                self.flags |= TOOMANYINSTRUCTIONS_PRESENT;
                data.warning_header("Exceeded maximum allowable instructions: Some flow is truncated", glb);
            }
        }
        self.insn_count += 1;

        let emptyflag = data.obank.empty();
        let before_last = if emptyflag { None } else { data.obank.deadlist.back() };
        let pcode_override = if self.pcode_override_present {
            data.get_override().get_pcode_override(curaddr).cloned()
        } else {
            None
        };

        let translate = glb.translate.take().expect("translator is missing");
        let result = {
            let mut emitter = PcodeEmitFd::new(data, glb);
            translate.one_instruction(&mut emitter, curaddr)
        };
        glb.translate = Some(translate);
        let step = match result {
            Ok(length) => length,
            Err(Error::Unimpl {
                message,
                instruction_length,
            }) => {
                if (self.flags & IGNORE_UNIMPLEMENTED) != 0 {
                    if !self.has_unimplemented() {
                        self.flags |= UNIMPLEMENTED_PRESENT;
                        data.warning_header("Control flow ignored unimplemented instructions", glb);
                    }
                    instruction_length
                } else if (self.flags & ERROR_UNIMPLEMENTED) != 0 {
                    return Err(Error::Unimpl {
                        message,
                        instruction_length,
                    });
                } else {
                    self.artificial_halt(curaddr, PcodeOp::UNIMPLEMENTED, data, glb)?;
                    data.warning("Unimplemented instruction - Truncating control flow here", curaddr, glb);
                    if !self.has_unimplemented() {
                        self.flags |= UNIMPLEMENTED_PRESENT;
                        data.warning_header("Control flow encountered unimplemented instructions", glb);
                    }
                    1
                }
            }
            Err(Error::BadData(message)) => {
                if (self.flags & ERROR_BADDATA) != 0 {
                    return Err(Error::BadData(message));
                }
                self.count_bad_data(&message, glb)?;
                self.artificial_halt(curaddr, PcodeOp::BADINSTRUCTION, data, glb)?;
                data.warning("Bad instruction - Truncating control flow here", curaddr, glb);
                if !self.has_bad_data() {
                    self.flags |= BADDATA_PRESENT;
                    data.warning_header("Control flow encountered bad instruction data", glb);
                }
                1
            }
            Err(other) => return Err(other),
        };
        self.visited.entry(curaddr.clone()).or_default().size = step;

        if *curaddr < self.minaddr {
            self.minaddr = curaddr.clone();
        }
        let endaddr = curaddr.add(step as i64);
        if self.maxaddr < endaddr {
            self.maxaddr = endaddr.clone();
        }

        let oiter = if emptyflag {
            data.obank.begin_dead()
        } else {
            before_last.and_then(|last| dead_next(data, last))
        };

        if let Some(first) = oiter {
            let seqnum = data.op(first).get_seq_num().clone();
            self.visited
                .get_mut(curaddr)
                .expect("visited instruction is missing")
                .seqnum = seqnum;
            data.op_mark_start_instruction(first);
            if let Some(record) = &pcode_override {
                record.perform_override(curaddr, data, glb)?;
            }
            self.xref_control_flow(oiter, startbasic, &mut isfallthru, None, data, glb)?;
        }

        if isfallthru {
            self.addrlist.push(endaddr);
        }
        Ok(isfallthru)
    }

    fn fallthru(&mut self, data: &mut Funcdata, glb: &mut Architecture) -> Result<()> {
        let mut bound = Address::invalid();
        if !self.set_fallthru_bound(&mut bound, data, glb)? {
            return Ok(());
        }
        let mut startbasic = true;
        loop {
            let curaddr = self.addrlist.pop().expect("flow address list is empty");
            let fallthruflag = self.process_instruction(&curaddr, &mut startbasic, data, glb)?;
            if !fallthruflag {
                break;
            }
            let Some(back) = self.addrlist.last().cloned() else {
                break;
            };
            if bound <= back {
                if bound == self.eaddr {
                    let eaddr = self.eaddr.clone();
                    self.handle_out_of_bounds(&eaddr, &back, data, glb)?;
                    self.unprocessed.push(back);
                    self.addrlist.pop();
                    return Ok(());
                }
                if bound == back {
                    if startbasic {
                        let op = self.target(&back, data)?;
                        data.op_mark_start_basic(op);
                    }
                    self.addrlist.pop();
                    break;
                }
                if !self.set_fallthru_bound(&mut bound, data, glb)? {
                    return Ok(());
                }
            }
        }
        Ok(())
    }

    fn find_rel_target(&self, op: OpId, res: &mut Address, data: &Funcdata) -> Result<Option<OpId>> {
        let pcop = data.op(op);
        let addr = data.vn(pcop.get_in(0)).get_addr();
        let id = pcop.get_time().wrapping_add(addr.get_offset() as u32);
        let seqnum = SeqNum::new(pcop.get_addr().clone(), id);
        if let Some(retop) = data.obank.find_op(&seqnum) {
            return Ok(Some(retop));
        }
        if let Some(retop) = data.obank.find_last_op(pcop.get_addr())
            && data.op(retop).get_time() < id
            && let Some((first, stat)) = self.last_visited_at_or_before(data.op(retop).get_addr())
        {
            *res = first.add(stat.size as i64);
            if *pcop.get_addr() < *res {
                return Ok(None);
            }
        }
        Err(Error::Lowlevel(format!(
            "Bad relative branch at instruction : ({})",
            space_and_raw(pcop.get_addr())
        )))
    }

    fn find_unprocessed(&mut self, data: &mut Funcdata) -> Result<()> {
        for index in 0..self.addrlist.len() {
            let addr = self.addrlist[index].clone();
            if self.seen_instruction(&addr) {
                let op = self.target(&addr, data)?;
                data.op_mark_start_basic(op);
            } else {
                self.unprocessed.push(addr);
            }
        }
        Ok(())
    }

    fn dedup_unprocessed(&mut self) {
        if self.unprocessed.is_empty() {
            return;
        }
        self.unprocessed.sort();
        self.unprocessed.dedup();
    }

    fn fillin_branch_stubs(&mut self, data: &mut Funcdata, glb: &mut Architecture) -> Result<()> {
        self.find_unprocessed(data)?;
        self.dedup_unprocessed();
        for index in 0..self.unprocessed.len() {
            let addr = self.unprocessed[index].clone();
            let op = self.artificial_halt(&addr, PcodeOp::MISSING, data, glb)?;
            data.op_mark_start_basic(op);
            data.op_mark_start_instruction(op);
        }
        Ok(())
    }

    fn fallthru_op_expect(&self, op: OpId, data: &Funcdata) -> Result<OpId> {
        self.fallthru_op(op, data)?.ok_or_else(|| {
            Error::Lowlevel(format!(
                "no fall-through op after instruction: ({})",
                space_and_raw(data.op(op).get_addr())
            ))
        })
    }

    fn collect_edges(&mut self, data: &mut Funcdata) -> Result<()> {
        if data.block(data.bblocks).get_size() != 0 {
            return Err(Error::Recov("Basic blocks already calculated\n".to_string()));
        }
        let mut position = data.obank.begin_dead();
        while let Some(op) = position {
            position = dead_next(data, op);
            let nextstart = match position {
                None => true,
                Some(next) => data.op(next).is_block_start(),
            };
            match data.op(op).code() {
                OpCode::Branch => {
                    let targ_op = self.branch_target(op, data)?;
                    self.block_edge1.push(op);
                    self.block_edge2.push(targ_op);
                }
                OpCode::Branchind => {
                    let Some(jt) = data.find_jump_table(op) else {
                        continue;
                    };
                    let num = data.jump_table(jt).num_entries();
                    for index in 0..num {
                        let addr = data.jump_table(jt).get_address_by_index(index);
                        let targ_op = self.target(&addr, data)?;
                        if data.op(targ_op).is_mark() {
                            continue;
                        }
                        data.op_mut(targ_op).set_mark();
                        self.block_edge1.push(op);
                        self.block_edge2.push(targ_op);
                    }
                    let mut index = self.block_edge1.len();
                    while index > 0 {
                        index -= 1;
                        if self.block_edge1[index] == op {
                            let targ_op = self.block_edge2[index];
                            data.op_mut(targ_op).clear_mark();
                        } else {
                            break;
                        }
                    }
                }
                OpCode::Return => {}
                OpCode::Cbranch => {
                    let targ_op = self.fallthru_op_expect(op, data)?;
                    self.block_edge1.push(op);
                    self.block_edge2.push(targ_op);
                    let targ_op = self.branch_target(op, data)?;
                    self.block_edge1.push(op);
                    self.block_edge2.push(targ_op);
                }
                _ => {
                    if nextstart {
                        let targ_op = self.fallthru_op_expect(op, data)?;
                        self.block_edge1.push(op);
                        self.block_edge2.push(targ_op);
                    }
                }
            }
        }
        Ok(())
    }

    fn split_basic(&mut self, data: &mut Funcdata) -> Result<()> {
        let Some(first) = data.obank.begin_dead() else {
            return Ok(());
        };
        let mut position = dead_next(data, first);
        if !data.op(first).is_block_start() {
            return Err(Error::Lowlevel("First op not marked as entry point".to_string()));
        }
        let graph = data.bblocks;
        let mut cur = data.block_new_block_basic(graph);
        data.op_insert(first, cur, None);
        data.block_set_start_block(graph, cur)?;
        let mut start = data.op(first).get_addr().clone();
        let mut stop = start.clone();
        while let Some(op) = position {
            position = dead_next(data, op);
            if data.op(op).is_block_start() {
                data.set_basic_block_range(cur, &start, &stop);
                cur = data.block_new_block_basic(graph);
                start = data.op(op).get_seq_num().get_addr().clone();
                stop = start.clone();
            } else {
                let next_addr = data.op(op).get_addr();
                if stop < *next_addr {
                    stop = next_addr.clone();
                }
            }
            data.op_insert(op, cur, None);
        }
        data.set_basic_block_range(cur, &start, &stop);
        Ok(())
    }

    fn connect_basic(&mut self, data: &mut Funcdata) -> Result<()> {
        let graph = data.bblocks;
        for index in 0..self.block_edge1.len() {
            let op = self.block_edge1[index];
            let targ_op = self.block_edge2[index];
            let bs = data.op(op).get_parent().expect("op is not in a basic block");
            let targ_bs = data.op(targ_op).get_parent().expect("op is not in a basic block");
            data.block_add_edge(graph, bs, targ_bs)?;
        }
        Ok(())
    }

    fn set_fallthru_bound(&mut self, bound: &mut Address, data: &mut Funcdata, glb: &mut Architecture) -> Result<bool> {
        let addr = self.addrlist.last().expect("flow address list is empty").clone();
        if let Some((first, stat)) = self.last_visited_at_or_before(&addr) {
            if addr == *first {
                let op = self.target(&addr, data)?;
                data.op_mark_start_basic(op);
                self.addrlist.pop();
                return Ok(false);
            }
            if addr < first.add(stat.size as i64) {
                self.reinterpreted(&addr, data, glb)?;
            }
        }
        match self.visited.range((Bound::Excluded(addr), Bound::Unbounded)).next() {
            Some((first, _)) => *bound = first.clone(),
            None => *bound = self.eaddr.clone(),
        }
        Ok(true)
    }

    fn handle_out_of_bounds(
        &mut self,
        fromaddr: &Address,
        toaddr: &Address,
        data: &mut Funcdata,
        glb: &mut Architecture,
    ) -> Result<()> {
        if (self.flags & IGNORE_OUTOFBOUNDS) == 0 {
            let mut errmsg = String::from("Function flow out of bounds: ");
            errmsg.push(fromaddr.get_shortcut());
            fromaddr.print_raw(&mut errmsg);
            errmsg.push_str(" flows to ");
            errmsg.push(toaddr.get_shortcut());
            toaddr.print_raw(&mut errmsg);
            if (self.flags & ERROR_OUTOFBOUNDS) == 0 {
                data.warning(&errmsg, toaddr, glb);
                if !self.has_out_of_bounds() {
                    self.flags |= OUTOFBOUNDS_PRESENT;
                    data.warning_header("Function flows out of bounds", glb);
                }
            } else {
                return Err(Error::Lowlevel(errmsg));
            }
        }
        Ok(())
    }

    fn count_bad_data(&mut self, err_msg: &str, glb: &Architecture) -> Result<()> {
        if self.baddata_count >= glb.max_baddata {
            return Err(Error::BadData(format!(
                "Bad instruction count exceeded:\n    ...\n    {}",
                err_msg
            )));
        }
        self.baddata_count += 1;
        Ok(())
    }

    fn artificial_halt(
        &mut self,
        addr: &Address,
        flag: u32,
        data: &mut Funcdata,
        glb: &mut Architecture,
    ) -> Result<OpId> {
        let haltop = data.new_op(1, addr);
        data.op_set_opcode(haltop, OpCode::Return, glb);
        let constant = data.new_constant(4, 1, glb);
        data.op_set_input(haltop, constant, 0)?;
        if flag != 0 {
            data.op_mark_halt(haltop, flag)?;
        }
        Ok(haltop)
    }

    fn reinterpreted(&mut self, addr: &Address, data: &mut Funcdata, glb: &mut Architecture) -> Result<()> {
        let Some((addr2, _)) = self.last_visited_at_or_before(addr) else {
            return Ok(());
        };
        let text = format!(
            "Instruction at ({}) overlaps instruction at ({})\n",
            space_and_raw(addr),
            space_and_raw(addr2)
        );
        if (self.flags & ERROR_REINTERPRETED) != 0 {
            return Err(Error::Lowlevel(text));
        }
        self.count_bad_data(&text, glb)?;
        if (self.flags & REINTERPRETED_PRESENT) == 0 {
            self.flags |= REINTERPRETED_PRESENT;
            data.warning_header(&text, glb);
        }
        Ok(())
    }

    fn check_for_flow_modification(
        &mut self,
        fspecs: CallSpecId,
        data: &mut Funcdata,
        glb: &mut Architecture,
    ) -> Result<bool> {
        let op = data.call_spec(fspecs).get_op();
        if data.call_spec(fspecs).is_inline() {
            self.injectlist.push(Some(op));
        }
        if data.call_spec(fspecs).is_no_return() {
            let opaddr = data.op(op).get_addr().clone();
            let haltop = self.artificial_halt(&opaddr, PcodeOp::NORETURN, data, glb)?;
            data.op_dead_insert_after(haltop, op)?;
            if !data.call_spec(fspecs).is_inline() {
                data.warning("Subroutine does not return", &opaddr, glb);
            }
            return Ok(true);
        }
        Ok(false)
    }

    fn query_call(&mut self, fspecs: CallSpecId, data: &mut Funcdata, glb: &mut Architecture) -> Result<()> {
        let entry = data.call_spec(fspecs).get_entry_address().clone();
        if entry.is_invalid() {
            return Ok(());
        }
        let otherfunc = {
            let db = glb.symboltab.as_ref().expect("symbol table is missing");
            let parent = data.get_scope_local().and_then(|local| db.scope(local).get_parent());
            parent.and_then(|scope| db.scope_query_function(scope, &entry))
        };
        let Some(sym) = otherfunc else {
            return Ok(());
        };
        data.call_spec_mut(fspecs).set_funcdata(sym, glb)?;
        if entry == *data.get_address() {
            let proto_is_inline = data.funcp.is_inline();
            if !data.call_spec(fspecs).has_model() || proto_is_inline {
                let funcp = &data.funcp;
                data.callspecs.get_mut(fspecs).proto.copy_flow_effects(funcp);
            }
            return Ok(());
        }
        let has_model = data.call_spec(fspecs).has_model();
        if let Some(other) = Database::symbol_get_function(glb, sym)? {
            let proto = other.get_func_proto();
            if !has_model || proto.is_inline() {
                data.call_spec_mut(fspecs).copy_flow_effects(proto);
            }
        }
        Ok(())
    }

    fn setup_call_specs(
        &mut self,
        op: OpId,
        fc: Option<CallSpecId>,
        data: &mut Funcdata,
        glb: &mut Architecture,
    ) -> Result<bool> {
        let spec = FuncCallSpecs::new(op, data);
        let res = data.callspecs.alloc(spec);
        data.qlst.push(res);
        let vn = data.new_varnode_call_specs(res, glb);
        data.op_set_input(op, vn, 0)?;

        Override::apply_prototype(data, glb, res)?;
        self.query_call(res, data, glb)?;
        if let Some(fc) = fc
            && data.call_spec(fc).get_entry_address() == data.call_spec(res).get_entry_address()
        {
            data.call_spec_mut(res).cancel_inject_id();
        }
        self.check_for_flow_modification(res, data, glb)
    }

    fn setup_callind_specs(
        &mut self,
        op: OpId,
        fc: Option<CallSpecId>,
        data: &mut Funcdata,
        glb: &mut Architecture,
    ) -> Result<bool> {
        let spec = FuncCallSpecs::new(op, data);
        let res = data.callspecs.alloc(spec);
        data.qlst.push(res);

        Override::apply_indirect(data, glb, res)?;
        if let Some(fc) = fc
            && data.call_spec(fc).get_entry_address() == data.call_spec(res).get_entry_address()
        {
            data.call_spec_mut(res).set_address(&Address::invalid());
        }
        Override::apply_prototype(data, glb, res)?;
        self.query_call(res, data, glb)?;

        if !data.call_spec(res).get_entry_address().is_invalid() {
            data.op_set_opcode(op, OpCode::Call, glb);
            let vn = data.new_varnode_call_specs(res, glb);
            data.op_set_input(op, vn, 0)?;
        }
        self.check_for_flow_modification(res, data, glb)
    }

    fn xref_inlined_branch(&mut self, op: OpId, data: &mut Funcdata, glb: &mut Architecture) -> Result<()> {
        match data.op(op).code() {
            OpCode::Call => {
                self.setup_call_specs(op, None, data, glb)?;
            }
            OpCode::Callind => {
                self.setup_callind_specs(op, None, data, glb)?;
            }
            OpCode::Branchind => {
                let jt = data.link_jump_table(op);
                if jt.is_none_or(|jt| data.jump_table(jt).num_entries() == 0) {
                    self.tablelist.push(op);
                }
            }
            _ => {}
        }
        Ok(())
    }

    fn do_injection(
        &mut self,
        inject_id: i32,
        op: OpId,
        fc: Option<CallSpecId>,
        data: &mut Funcdata,
        glb: &mut Architecture,
    ) -> Result<()> {
        let marker = data.obank.deadlist.back().expect("dead op list is empty");

        let mut library = glb.pcodeinjectlib.take().expect("pcode injection library is missing");
        let payload = library.take_payload(inject_id);
        let inject_result = {
            let icontext = library.get_cached_context();
            let mut emitter = PcodeEmitFd::new(data, glb);
            payload.inject(icontext, &mut emitter)
        };
        let payload_name = payload.get_name();
        let incidental_copy = payload.is_incidental_copy();
        library.restore_payload(inject_id, payload);
        glb.pcodeinjectlib = Some(library);
        inject_result?;

        let mut startbasic = data.op(op).is_block_start();
        let Some(firstop) = dead_next(data, marker) else {
            return Err(Error::Lowlevel(format!("Empty injection: {}", payload_name)));
        };
        let mut isfallthru = true;
        let lastop = self
            .xref_control_flow(Some(firstop), &mut startbasic, &mut isfallthru, fc, data, glb)?
            .expect("injection produced no ops");

        if startbasic && let Some(next) = dead_next(data, op) {
            data.op_mark_start_basic(next);
        }

        if incidental_copy {
            data.obank.mark_incidental_copy(firstop, lastop);
        }
        data.obank.move_sequence_dead(firstop, lastop, op);

        self.update_target(op, firstop, data);
        data.op_destroy_raw(op)?;
        Ok(())
    }

    fn inject_user_op(&mut self, op: OpId, data: &mut Funcdata, glb: &mut Architecture) -> Result<()> {
        let index = data.vn(data.op(op).get_in(0)).get_offset() as i32;
        let inject_id = glb
            .userops
            .get_op(index as u32)
            .expect("user op is missing")
            .get_inject_id() as i32;
        let icontext = glb
            .pcodeinjectlib
            .as_mut()
            .expect("pcode injection library is missing")
            .get_cached_context();
        icontext.clear();
        let base = icontext.base_mut();
        base.baseaddr = data.op(op).get_addr().clone();
        base.nextaddr = base.baseaddr.clone();
        for slot in 1..data.op(op).num_input() {
            let vn = data.vn(data.op(op).get_in(slot));
            base.inputlist.push(VarnodeData {
                space: vn.get_space().cloned(),
                offset: vn.get_offset(),
                size: vn.get_size() as u32,
            });
        }
        if let Some(outvn) = data.op(op).get_out() {
            let vn = data.vn(outvn);
            base.output.push(VarnodeData {
                space: vn.get_space().cloned(),
                offset: vn.get_offset(),
                size: vn.get_size() as u32,
            });
        }
        self.do_injection(inject_id, op, None, data, glb)
    }

    fn inline_sub_function(&mut self, fc: CallSpecId, data: &mut Funcdata, glb: &mut Architecture) -> Result<bool> {
        let Some(sym) = data.call_spec(fc).get_funcdata() else {
            return Ok(false);
        };

        if self.inline_head.is_none() {
            self.inline_head = Some(Rc::new(InlineHead::new(data)));
            self.inline_recursion = Some(self.inline_base.clone());
        }
        let recursion = self.inline_recursion.clone().expect("inline recursion set is missing");
        recursion.borrow_mut().insert(data.get_address().clone());
        let fd_address = data.call_spec(fc).get_entry_address().clone();
        if recursion.borrow().contains(&fd_address) {
            let opaddr = data.op(data.call_spec(fc).get_op()).get_addr().clone();
            self.inline_head
                .as_ref()
                .expect("inline head is missing")
                .warning("Could not inline here", &opaddr, glb);
            return Ok(false);
        }

        if Database::symbol_get_function(glb, sym)?.is_none() {
            return Ok(false);
        }
        let taken = glb
            .symboltab
            .as_mut()
            .expect("symbol table is missing")
            .symbol_take_function(sym);
        let Some(mut inlinefd) = taken else {
            return Ok(false);
        };
        let fd_address = inlinefd.get_address().clone();
        let callop = data.call_spec(fc).get_op();
        let result = data.inline_flow(&mut inlinefd, self, callop, glb);
        if let Some(head) = self.inline_head.clone() {
            head.flush_warnings(glb);
        }
        glb.symboltab
            .as_mut()
            .expect("symbol table is missing")
            .symbol_restore_function(sym, inlinefd);
        let res = result?;
        if res < 0 {
            return Ok(false);
        } else if res == 0 {
            recursion.borrow_mut().remove(&fd_address);
        } else if res == 1 {
            recursion.borrow_mut().insert(fd_address);
        }

        self.set_possible_unreachable();
        Ok(true)
    }

    fn inject_sub_function(&mut self, fc: CallSpecId, data: &mut Funcdata, glb: &mut Architecture) -> Result<bool> {
        let op = data.call_spec(fc).get_op();
        let inject_id = data.call_spec(fc).get_inject_id();
        {
            let icontext = glb
                .pcodeinjectlib
                .as_mut()
                .expect("pcode injection library is missing")
                .get_cached_context();
            icontext.clear();
            let base = icontext.base_mut();
            base.baseaddr = data.op(op).get_addr().clone();
            base.nextaddr = base.baseaddr.clone();
            base.calladdr = data.call_spec(fc).get_entry_address().clone();
        }
        self.do_injection(inject_id, op, Some(fc), data, glb)?;
        let paramshift = glb
            .pcodeinjectlib
            .as_ref()
            .expect("pcode injection library is missing")
            .get_payload(inject_id)
            .get_param_shift();
        if paramshift != 0 {
            let last = *data.qlst.last().expect("call specification list is empty");
            data.call_spec_mut(last).set_paramshift(paramshift);
        }
        Ok(true)
    }

    fn check_contained_call(&mut self, data: &mut Funcdata, glb: &mut Architecture) -> Result<()> {
        let mut index = 0;
        while index < data.qlst.len() {
            let fc = data.qlst[index];
            if data.call_spec(fc).get_funcdata().is_some() {
                index += 1;
                continue;
            }
            let op = data.call_spec(fc).get_op();
            if data.op(op).code() != OpCode::Call {
                index += 1;
                continue;
            }
            let addr = data.call_spec(fc).get_entry_address().clone();
            let Some((first, stat)) = self.last_visited_at_or_before(&addr) else {
                index += 1;
                continue;
            };
            if first.add(stat.size as i64) <= addr {
                index += 1;
                continue;
            }
            if *first == addr {
                let mut text = String::from("Possible PIC construction at ");
                data.op(op).get_addr().print_raw(&mut text);
                text.push_str(": Changing call to branch");
                data.warning_header(&text, glb);
                data.op_set_opcode(op, OpCode::Branch, glb);
                let targ = self.target(&addr, data)?;
                data.op_mark_start_basic(targ);
                if let Some(next) = dead_next(data, op) {
                    data.op_mark_start_basic(next);
                }
                let vn = data.new_code_ref(&addr, glb);
                data.op_set_input(op, vn, 0)?;
                data.qlst.remove(index);
                data.callspecs.remove(fc);
                if index == data.qlst.len() {
                    break;
                }
            } else {
                let opaddr = data.op(op).get_addr().clone();
                data.warning("Call to offcut address within same function", &opaddr, glb);
            }
            index += 1;
        }
        Ok(())
    }

    fn check_multistage_jumptables(&mut self, data: &mut Funcdata, glb: &mut Architecture) -> Result<()> {
        let num = data.num_jump_tables();
        for index in 0..num {
            let jt = data.get_jump_table(index);
            let mut table = std::mem::take(data.jump_table_mut(jt));
            let result = table.check_for_multistage(data, glb);
            let indirect = table.get_indirect_op();
            *data.jump_table_mut(jt) = table;
            if result? {
                self.tablelist.push(indirect.expect("jump table has no indirect op"));
            }
        }
        Ok(())
    }

    fn recover_jump_tables(
        &mut self,
        new_tables: &mut Vec<Option<JumpTableId>>,
        notreached: &mut Vec<OpId>,
        data: &mut Funcdata,
        glb: &mut Architecture,
    ) -> Result<()> {
        let op = self.tablelist[0];
        let mut name = String::from(data.get_name());
        name.push_str("@@jump@");
        data.op(op).get_addr().print_raw(&mut name);

        let parent = {
            let db = glb.symboltab.as_ref().expect("symbol table is missing");
            data.get_scope_local().and_then(|local| db.scope(local).get_parent())
        };
        let address = data.get_address().clone();
        let mut partial = Funcdata::new(&name, &name, parent, &address, None, 0, glb)?;
        let mut recover_all = || -> Result<()> {
            for index in 0..self.tablelist.len() {
                let op = self.tablelist[index];
                let mut mode = RecoveryMode::Success;
                let jt = data.recover_jump_table(&mut partial, op, self, &mut mode, glb)?;
                match jt {
                    None => {
                        if !self.is_flow_for_inline() {
                            self.truncate_indirect_jump(op, mode, data, glb)?;
                        }
                    }
                    Some(jt) => {
                        if data.jump_table(jt).is_partial() {
                            if self.tablelist.len() > 1 && data.jump_table(jt).get_recover_count() <= 1 {
                                notreached.push(op);
                            } else {
                                data.jump_table_mut(jt).mark_complete();
                            }
                        }
                    }
                }
                new_tables.push(jt);
            }
            Ok(())
        };
        let result = recover_all();
        partial.destroy(glb);
        result
    }

    fn delete_call_spec(&mut self, fc: CallSpecId, data: &mut Funcdata) -> Result<()> {
        let Some(index) = data.qlst.iter().position(|&entry| entry == fc) else {
            return Err(Error::Lowlevel("Misplaced callspec".to_string()));
        };
        data.callspecs.remove(fc);
        data.qlst.remove(index);
        Ok(())
    }

    fn truncate_indirect_jump(
        &mut self,
        op: OpId,
        mode: RecoveryMode,
        data: &mut Funcdata,
        glb: &mut Architecture,
    ) -> Result<()> {
        let opaddr = data.op(op).get_addr().clone();
        if mode == RecoveryMode::FailReturn {
            data.op_set_opcode(op, OpCode::Return, glb);
            data.warning("Treating indirect jump as return", &opaddr, glb);
            return Ok(());
        }
        data.op_set_opcode(op, OpCode::Callind, glb);
        self.setup_callind_specs(op, None, data, glb)?;
        let fc = data.get_call_specs_op(op).expect("call specification is missing");
        let return_type;
        let no_params;
        if mode == RecoveryMode::FailThunk {
            return_type = 0;
            no_params = false;
        } else if mode == RecoveryMode::FailCallother {
            return_type = PcodeOp::NORETURN;
            data.call_spec_mut(fc).set_no_return(true);
            data.warning("Does not return", &opaddr, glb);
            no_params = true;
        } else {
            return_type = 0;
            no_params = false;
            data.call_spec_mut(fc).set_bad_jump_table(true);
            data.warning("Treating indirect jump as call", &opaddr, glb);
        }
        if no_params && !data.call_spec(fc).has_model() {
            let void_type = glb.types.as_mut().expect("type factory is missing").get_type_void()?;
            let model = glb.defaultfp.expect("default prototype model is missing");
            data.call_spec_mut(fc).set_internal(model, void_type, glb);
            data.call_spec_mut(fc).set_input_lock(true, glb);
            data.call_spec_mut(fc).set_output_lock(true, glb);
        }

        let truncop = self.artificial_halt(&opaddr, return_type, data, glb)?;
        data.op_dead_insert_after(truncop, op)?;
        Ok(())
    }

    pub fn set_range(&mut self, start_address: &Address, end_address: &Address) {
        self.baddr = start_address.clone();
        self.eaddr = end_address.clone();
    }

    pub fn set_maximum_instructions(&mut self, max: u32) {
        self.insn_max = max;
    }

    pub fn set_flags(&mut self, val: u32) {
        self.flags |= val;
    }

    pub fn clear_flags(&mut self, val: u32) {
        self.flags &= !val;
    }

    pub fn target(&self, addr: &Address, data: &Funcdata) -> Result<OpId> {
        let mut current = self.visited.get_key_value(addr);
        while let Some((key, stat)) = current {
            let seq = &stat.seqnum;
            if !seq.get_addr().is_invalid() {
                if let Some(retop) = data.obank.find_op(seq) {
                    return Ok(retop);
                }
                break;
            }
            current = self.visited.get_key_value(&key.add(stat.size as i64));
        }
        Err(Error::Lowlevel(format!(
            "Could not find op at target address: ({})",
            space_and_raw(addr)
        )))
    }

    pub fn branch_target(&self, op: OpId, data: &Funcdata) -> Result<OpId> {
        let addr = data.vn(data.op(op).get_in(0)).get_addr().clone();
        if addr.is_constant() {
            let mut res = Address::invalid();
            if let Some(retop) = self.find_rel_target(op, &mut res, data)? {
                return Ok(retop);
            }
            return self.target(&res, data);
        }
        self.target(&addr, data)
    }

    pub fn update_target(&mut self, old_op: OpId, new_op: OpId, data: &Funcdata) {
        if let Some(stat) = self.visited.get_mut(data.op(old_op).get_addr())
            && stat.seqnum == *data.op(old_op).get_seq_num()
        {
            stat.seqnum = data.op(new_op).get_seq_num().clone();
        }
    }

    pub fn generate_ops(&mut self, data: &mut Funcdata, glb: &mut Architecture) -> Result<()> {
        let mut notreached: Vec<OpId> = Vec::new();
        self.clear_properties();
        self.addrlist.push(data.get_address().clone());
        while !self.addrlist.is_empty() {
            self.fallthru(data, glb)?;
        }
        if self.has_inject() {
            self.inject_pcode(data, glb)?;
        }
        loop {
            while !self.tablelist.is_empty() {
                let mut new_tables: Vec<Option<JumpTableId>> = Vec::new();
                self.recover_jump_tables(&mut new_tables, &mut notreached, data, glb)?;
                self.tablelist.clear();
                for entry in new_tables {
                    let Some(jt) = entry else {
                        continue;
                    };
                    let num = data.jump_table(jt).num_entries();
                    for index in 0..num {
                        let indirect = data
                            .jump_table(jt)
                            .get_indirect_op()
                            .expect("jump table has no indirect op");
                        let addr = data.jump_table(jt).get_address_by_index(index);
                        self.new_address(indirect, &addr, data, glb)?;
                    }
                    while !self.addrlist.is_empty() {
                        self.fallthru(data, glb)?;
                    }
                }
            }

            self.check_contained_call(data, glb)?;
            self.check_multistage_jumptables(data, glb)?;
            self.tablelist.append(&mut notreached);
            if self.has_inject() {
                self.inject_pcode(data, glb)?;
            }
            if self.tablelist.is_empty() {
                break;
            }
        }
        Ok(())
    }

    pub fn generate_blocks(&mut self, data: &mut Funcdata, glb: &mut Architecture) -> Result<()> {
        self.fillin_branch_stubs(data, glb)?;
        self.collect_edges(data)?;
        self.split_basic(data)?;
        self.connect_basic(data)?;
        let graph = data.bblocks;
        if data.block(graph).get_size() != 0 {
            let startblock = data.block(graph).get_block(0);
            if data.block(startblock).size_in() != 0 {
                let newfront = data.block_new_block_basic(graph);
                data.block_add_edge(graph, newfront, startblock)?;
                data.block_set_start_block(graph, newfront)?;
                let address = data.get_address().clone();
                data.set_basic_block_range(newfront, &address, &address);
            }
        }

        if self.has_possible_unreachable() {
            data.remove_unreachable_blocks(false, true, glb)?;
        }
        Ok(())
    }

    pub fn test_hard_inline_restrictions(
        &mut self,
        inlinefd: &Funcdata,
        op: OpId,
        retaddr: &mut Address,
        data: &mut Funcdata,
    ) -> bool {
        if !inlinefd.get_func_proto().is_no_return() {
            let opaddr = data.op(op).get_addr().clone();
            let head = self.inline_head.clone().expect("inline head is missing");
            let Some(nextop) = dead_next(data, op) else {
                head.defer_warning("No fallthrough prevents inlining here", &opaddr);
                return false;
            };
            *retaddr = data.op(nextop).get_addr().clone();
            if opaddr == *retaddr {
                head.defer_warning("Return address prevents inlining here", &opaddr);
                return false;
            }
            data.op_mark_start_basic(nextop);
        }
        true
    }

    pub fn check_ez_model(&self, data: &Funcdata) -> bool {
        let mut position = data.obank.begin_dead();
        while let Some(op) = position {
            if data.op(op).is_call_or_branch() {
                return false;
            }
            position = dead_next(data, op);
        }
        true
    }

    pub fn inject_pcode(&mut self, data: &mut Funcdata, glb: &mut Architecture) -> Result<()> {
        let mut index = 0;
        while index < self.injectlist.len() {
            let entry = self.injectlist[index];
            self.injectlist[index] = None;
            index += 1;
            let Some(op) = entry else {
                continue;
            };
            if data.op(op).code() == OpCode::Callother {
                self.inject_user_op(op, data, glb)?;
            } else {
                let fc = FuncCallSpecs::get_fspec_from_const(data.vn(data.op(op).get_in(0)).get_addr());
                if data.call_spec(fc).is_inline() {
                    let inject_id = data.call_spec(fc).get_inject_id();
                    if inject_id >= 0 {
                        if self.inject_sub_function(fc, data, glb)? {
                            let fixup_name = glb
                                .pcodeinjectlib
                                .as_ref()
                                .expect("pcode injection library is missing")
                                .get_call_fixup_name(inject_id);
                            let text = format!(
                                "Function: {} replaced with injection: {}",
                                data.call_spec(fc).get_name(),
                                fixup_name
                            );
                            data.warning_header(&text, glb);
                            self.delete_call_spec(fc, data)?;
                        }
                    } else if self.inline_sub_function(fc, data, glb)? {
                        let text = format!("Inlined function: {}", data.call_spec(fc).get_name());
                        data.warning_header(&text, glb);
                        self.delete_call_spec(fc, data)?;
                    }
                }
            }
        }
        self.injectlist.clear();
        Ok(())
    }

    pub fn forward_recursion(&mut self, op2: &FlowInfo) {
        self.inline_recursion = op2.inline_recursion.clone();
        self.inline_head = op2.inline_head.clone();
    }

    pub fn inline_clone(
        &mut self,
        inlineflow: &FlowInfo,
        inline_data: &Funcdata,
        retaddr: &Address,
        data: &mut Funcdata,
        glb: &mut Architecture,
    ) -> Result<()> {
        let mut position = inline_data.obank.begin_dead();
        while let Some(op) = position {
            position = dead_next(inline_data, op);
            let seq = inline_data.op(op).get_seq_num().clone();
            let cloneop = if inline_data.op(op).code() == OpCode::Return && !retaddr.is_invalid() {
                let cloneop = data.new_op_seq(1, &seq);
                data.op_set_opcode(cloneop, OpCode::Branch, glb);
                let vn = data.new_code_ref(retaddr, glb);
                data.op_set_input(cloneop, vn, 0)?;
                cloneop
            } else {
                clone_foreign_op(data, inline_data, op, &seq, glb)?
            };
            if data.op(cloneop).is_call_or_branch() {
                self.xref_inlined_branch(cloneop, data, glb)?;
            }
        }
        self.unprocessed.extend(inlineflow.unprocessed.iter().cloned());
        self.addrlist.extend(inlineflow.addrlist.iter().cloned());
        for (key, stat) in inlineflow.visited.iter() {
            self.visited.entry(key.clone()).or_insert_with(|| stat.clone());
        }
        Ok(())
    }

    pub fn inline_ez_clone(
        &mut self,
        inlineflow: &FlowInfo,
        inline_data: &Funcdata,
        calladdr: &Address,
        data: &mut Funcdata,
        glb: &mut Architecture,
    ) -> Result<()> {
        let _ = inlineflow;
        let mut position = inline_data.obank.begin_dead();
        while let Some(op) = position {
            position = dead_next(inline_data, op);
            if inline_data.op(op).code() == OpCode::Return {
                break;
            }
            let myseq = SeqNum::new(calladdr.clone(), inline_data.op(op).get_seq_num().get_time());
            clone_foreign_op(data, inline_data, op, &myseq, glb)?;
        }
        Ok(())
    }

    pub fn get_size(&self) -> i32 {
        self.maxaddr.get_offset().wrapping_sub(self.minaddr.get_offset()) as i32
    }

    pub fn has_inject(&self) -> bool {
        !self.injectlist.is_empty()
    }

    pub fn has_unimplemented(&self) -> bool {
        (self.flags & UNIMPLEMENTED_PRESENT) != 0
    }

    pub fn has_bad_data(&self) -> bool {
        (self.flags & BADDATA_PRESENT) != 0
    }

    pub fn has_out_of_bounds(&self) -> bool {
        (self.flags & OUTOFBOUNDS_PRESENT) != 0
    }

    pub fn has_reinterpreted(&self) -> bool {
        (self.flags & REINTERPRETED_PRESENT) != 0
    }

    pub fn has_too_many_instructions(&self) -> bool {
        (self.flags & TOOMANYINSTRUCTIONS_PRESENT) != 0
    }

    pub fn is_flow_for_inline(&self) -> bool {
        (self.flags & FLOW_FORINLINE) != 0
    }

    pub fn does_jump_record(&self) -> bool {
        (self.flags & RECORD_JUMPLOADS) != 0
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn empty_flow() -> FlowInfo {
        FlowInfo {
            unprocessed: Vec::new(),
            addrlist: Vec::new(),
            tablelist: Vec::new(),
            injectlist: Vec::new(),
            visited: BTreeMap::new(),
            block_edge1: Vec::new(),
            block_edge2: Vec::new(),
            insn_count: 0,
            insn_max: u32::MAX,
            baddr: Address::invalid(),
            eaddr: Address::invalid(),
            minaddr: Address::invalid(),
            maxaddr: Address::invalid(),
            pcode_override_present: false,
            flags: 0,
            baddata_count: 0,
            inline_head: None,
            inline_recursion: None,
            inline_base: Rc::new(RefCell::new(BTreeSet::new())),
        }
    }

    #[test]
    fn dedup_unprocessed_sorts_and_removes_duplicates() {
        let mut flow = empty_flow();
        for offset in [5u64, 1, 5, 3, 1, 9, 3] {
            flow.unprocessed.push(Address::from_parts(None, offset));
        }
        flow.dedup_unprocessed();
        let offsets: Vec<u64> = flow.unprocessed.iter().map(|addr| addr.get_offset()).collect();
        assert_eq!(offsets, vec![1, 3, 5, 9]);
    }

    #[test]
    fn clear_properties_keeps_other_flags() {
        let mut flow = empty_flow();
        flow.flags = UNIMPLEMENTED_PRESENT | BADDATA_PRESENT | OUTOFBOUNDS_PRESENT | REINTERPRETED_PRESENT;
        flow.insn_count = 7;
        flow.baddata_count = 2;
        flow.clear_properties();
        assert_eq!(flow.flags, REINTERPRETED_PRESENT);
        assert_eq!(flow.insn_count, 0);
        assert_eq!(flow.baddata_count, 0);
    }
}
