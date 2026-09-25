use std::collections::BTreeMap;
use std::ops::Bound;
use std::sync::Arc;

use crate::address::{Address, AddressKey, RangeList};
use crate::architecture::Architecture;
use crate::block::BlockId;
use crate::error::{Error, Result};
use crate::fspec::{CallSpecId, EffectRecord, FuncCallSpecs, ParamEntry};
use crate::funcdata::Funcdata;
use crate::op::{OpId, PcodeOp};
use crate::opcodes::OpCode;
use crate::pcoderaw::VarnodeData;
use crate::prefersplit::PreferSplitManager;
use crate::rangeutil::{ValueSetRead, ValueSetSolver, WidenerFull, WidenerNone};
use crate::space::{SpaceRef, SpaceType, same_space};
use crate::translate::JoinRecord;
use crate::types::TypeFactory;
use crate::varnode::VarnodeId;

pub type VariableStack = std::collections::HashMap<AddressKey, Vec<VarnodeId>>;

fn space_matches(candidate: Option<&SpaceRef>, spc: &SpaceRef) -> bool {
    match candidate {
        Some(space) => space.get_index() == spc.get_index(),
        None => false,
    }
}

fn space_type_of(candidate: Option<&SpaceRef>) -> Option<SpaceType> {
    candidate.map(|space| space.get_type())
}

fn type_factory(glb: &Architecture) -> &TypeFactory {
    glb.types.as_deref().expect("type factory is not initialized")
}

fn next_basic_op(data: &Funcdata, op: OpId) -> Option<OpId> {
    data.obank.next_in_list(op, PcodeOp::BASIC_LIST)
}

fn next_code_op(data: &Funcdata, op: OpId) -> Option<OpId> {
    data.obank.next_in_list(op, PcodeOp::CODE_LIST)
}

fn signed_offset(value: i32) -> u64 {
    value as i64 as u64
}

fn address_space(addr: &Address) -> SpaceRef {
    addr.get_space().expect("address without space").clone()
}

fn def_op(data: &Funcdata, vn: VarnodeId) -> OpId {
    data.vn(vn).get_def().expect("varnode is not written")
}

fn out_vn(data: &Funcdata, op: OpId) -> VarnodeId {
    data.op(op).get_out().expect("op without output")
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct SizePass {
    pub size: i32,
    pub pass: i32,
}

#[derive(Clone, Debug, Default)]
pub struct LocationMap {
    themap: BTreeMap<AddressKey, (Address, SizePass)>,
}

impl LocationMap {
    pub fn new() -> LocationMap {
        LocationMap {
            themap: BTreeMap::new(),
        }
    }

    pub fn add(&mut self, addr: Address, size: i32, pass: i32, intersect: &mut i32) -> Address {
        let mut addr = addr;
        let mut size = size;
        let mut pass = pass;
        *intersect = 0;
        let first_key = match self.themap.range(..addr.ordering_key()).next_back() {
            Some((key, _)) => Some(*key),
            None => self.themap.keys().next().copied(),
        };
        let mut merged_keys: Vec<AddressKey> = Vec::new();
        if let Some(first_key) = first_key {
            let mut entries = self.themap.range(first_key..).peekable();
            if let Some(&(_, (start, entry))) = entries.peek()
                && addr.overlap(0, start, entry.size) == -1
            {
                entries.next();
            }
            if let Some(&(key, (start, entry))) = entries.peek() {
                let position = addr.overlap(0, start, entry.size);
                if position != -1 {
                    if position + size <= entry.size {
                        *intersect = if entry.pass < pass { 2 } else { 0 };
                        return start.clone();
                    }
                    addr = start.clone();
                    size += position;
                    if entry.pass < pass {
                        *intersect = 1;
                        pass = entry.pass;
                    }
                    merged_keys.push(*key);
                    entries.next();
                }
            }
            for (key, (start, entry)) in entries {
                let position = start.overlap(0, &addr, size);
                if position == -1 {
                    break;
                }
                if position + entry.size > size {
                    size = position + entry.size;
                }
                if entry.pass < pass {
                    *intersect = 1;
                    pass = entry.pass;
                }
                merged_keys.push(*key);
            }
        }
        for key in &merged_keys {
            self.themap.remove(key);
        }
        self.themap
            .insert(addr.ordering_key(), (addr.clone(), SizePass { size, pass }));
        addr
    }

    fn next_key(&self, key: &AddressKey) -> Option<AddressKey> {
        self.themap
            .range((Bound::Excluded(*key), Bound::Unbounded))
            .next()
            .map(|(found, _)| *found)
    }

    pub fn find(&self, addr: &Address) -> Option<Address> {
        let (_, (start, entry)) = self.themap.range(..=addr.ordering_key()).next_back()?;
        if addr.overlap(0, start, entry.size) != -1 {
            return Some(start.clone());
        }
        None
    }

    pub fn find_pass(&self, addr: &Address) -> i32 {
        let Some((_, (start, entry))) = self.themap.range(..=addr.ordering_key()).next_back() else {
            return -1;
        };
        if addr.overlap(0, start, entry.size) != -1 {
            return entry.pass;
        }
        -1
    }

    pub fn erase(&mut self, iter: &Address) -> Option<Address> {
        let key = iter.ordering_key();
        self.themap.remove(&key);
        self.next_key(&key).map(|found| self.themap[&found].0.clone())
    }

    pub fn begin(&self) -> Option<Address> {
        self.themap.values().next().map(|(start, _)| start.clone())
    }

    pub fn get(&self, iter: &Address) -> &SizePass {
        &self
            .themap
            .get(&iter.ordering_key())
            .expect("LocationMap key not present")
            .1
    }

    pub fn get_mut(&mut self, iter: &Address) -> &mut SizePass {
        &mut self
            .themap
            .get_mut(&iter.ordering_key())
            .expect("LocationMap key not present")
            .1
    }

    pub fn next(&self, iter: &Address) -> Option<Address> {
        self.next_key(&iter.ordering_key())
            .map(|found| self.themap[&found].0.clone())
    }

    pub fn iter(&self) -> impl Iterator<Item = (&Address, &SizePass)> {
        self.themap.values().map(|(start, entry)| (start, entry))
    }

    pub fn clear(&mut self) {
        self.themap.clear();
    }
}

#[derive(Clone, Debug)]
pub struct MemRange {
    pub addr: Address,
    pub size: i32,
    pub flags: u32,
}

impl MemRange {
    pub const NEW_ADDRESSES: u32 = 1;
    pub const OLD_ADDRESSES: u32 = 2;

    pub fn new(ad: &Address, sz: i32, fl: u32) -> MemRange {
        MemRange {
            addr: ad.clone(),
            size: sz,
            flags: fl,
        }
    }

    pub fn new_addresses(&self) -> bool {
        (self.flags & MemRange::NEW_ADDRESSES) != 0
    }

    pub fn old_addresses(&self) -> bool {
        (self.flags & MemRange::OLD_ADDRESSES) != 0
    }

    pub fn clear_property(&mut self, val: u32) {
        self.flags &= !val;
    }
}

#[derive(Clone, Debug, Default)]
pub struct TaskList {
    tasklist: Vec<MemRange>,
}

impl TaskList {
    pub fn new() -> TaskList {
        TaskList { tasklist: Vec::new() }
    }

    pub fn add(&mut self, addr: Address, size: i32, fl: u32) {
        if let Some(entry) = self.tasklist.last_mut() {
            let over = addr.overlap(0, &entry.addr, entry.size);
            if over >= 0 {
                let relsize = size + over;
                if relsize > entry.size {
                    entry.size = relsize;
                }
                entry.flags |= fl;
                return;
            }
        }
        self.tasklist.push(MemRange::new(&addr, size, fl));
    }

    pub fn insert(&mut self, pos: usize, addr: Address, size: i32, fl: u32) -> usize {
        self.tasklist.insert(pos, MemRange::new(&addr, size, fl));
        pos
    }

    pub fn erase(&mut self, iter: usize) -> usize {
        self.tasklist.remove(iter);
        iter
    }

    pub fn begin(&self) -> usize {
        0
    }

    pub fn end(&self) -> usize {
        self.tasklist.len()
    }

    pub fn get(&self, iter: usize) -> &MemRange {
        &self.tasklist[iter]
    }

    pub fn get_mut(&mut self, iter: usize) -> &mut MemRange {
        &mut self.tasklist[iter]
    }

    pub fn clear(&mut self) {
        self.tasklist.clear();
    }

    pub fn empty(&self) -> bool {
        self.tasklist.is_empty()
    }
}

#[derive(Clone, Debug)]
pub struct PriorityQueue {
    queue: Vec<Vec<BlockId>>,
    curdepth: i32,
}

impl Default for PriorityQueue {
    fn default() -> PriorityQueue {
        PriorityQueue::new()
    }
}

impl PriorityQueue {
    pub fn new() -> PriorityQueue {
        PriorityQueue {
            queue: Vec::new(),
            curdepth: -2,
        }
    }

    pub fn reset(&mut self, maxdepth: i32) {
        if self.curdepth == -1 && (maxdepth as i64 as u64) == (self.queue.len() as u64).wrapping_sub(1) {
            return;
        }
        self.queue.clear();
        self.queue.resize((maxdepth + 1) as usize, Vec::new());
        self.curdepth = -1;
    }

    pub fn insert(&mut self, bl: BlockId, depth: i32) {
        self.queue[depth as usize].push(bl);
        if depth > self.curdepth {
            self.curdepth = depth;
        }
    }

    pub fn extract(&mut self) -> BlockId {
        let res = self.queue[self.curdepth as usize]
            .pop()
            .expect("extract from an empty priority queue");
        while self.queue[self.curdepth as usize].is_empty() {
            self.curdepth -= 1;
            if self.curdepth < 0 {
                break;
            }
        }
        res
    }

    pub fn empty(&self) -> bool {
        self.curdepth == -1
    }
}

#[derive(Clone, Debug)]
pub struct HeritageInfo {
    space: Option<SpaceRef>,
    delay: i32,
    deadcodedelay: i32,
    deadremoved: i32,
    load_guard_search: bool,
    warningissued: bool,
    has_call_placeholders: bool,
}

impl HeritageInfo {
    pub fn new(spc: Option<SpaceRef>) -> HeritageInfo {
        let (space, delay, deadcodedelay, has_call_placeholders) = match spc {
            None => (None, 0, 0, false),
            Some(spc) => {
                if !spc.is_heritaged() {
                    (None, spc.get_delay(), spc.get_deadcode_delay(), false)
                } else {
                    let delay = spc.get_delay();
                    let deadcodedelay = spc.get_deadcode_delay();
                    let placeholders = spc.get_type() == SpaceType::Spacebase;
                    (Some(spc), delay, deadcodedelay, placeholders)
                }
            }
        };
        HeritageInfo {
            space,
            delay,
            deadcodedelay,
            deadremoved: 0,
            load_guard_search: false,
            warningissued: false,
            has_call_placeholders,
        }
    }

    fn is_heritaged(&self) -> bool {
        self.space.is_some()
    }

    fn reset(&mut self) {
        self.deadremoved = 0;
        if let Some(space) = &self.space {
            self.has_call_placeholders = space.get_type() == SpaceType::Spacebase;
        }
        self.warningissued = false;
        self.load_guard_search = false;
    }
}

#[derive(Clone, Debug, Default)]
pub struct LoadGuard {
    op: Option<OpId>,
    spc: Option<SpaceRef>,
    pointer_base: u64,
    minimum_offset: u64,
    maximum_offset: u64,
    step: i32,
    analysis_state: i32,
}

impl LoadGuard {
    fn guard_space(&self) -> &SpaceRef {
        self.spc.as_ref().expect("load guard without space")
    }

    fn establish_range(&mut self, value_set: &ValueSetRead) {
        let range = value_set.get_range();
        let range_size = range.get_size();
        let mut size: u64;
        if range.is_empty() {
            self.minimum_offset = self.pointer_base;
            size = 0x1000;
        } else if range.is_full() || range_size > 0xffffff {
            self.minimum_offset = self.pointer_base;
            size = 0x1000;
            self.analysis_state = 1;
        } else {
            self.step = if range_size == 3 { range.get_step() } else { 0 };
            size = 0x1000;
            if value_set.is_left_stable() {
                self.minimum_offset = range.get_min();
            } else if value_set.is_right_stable() {
                if self.pointer_base < range.get_end() {
                    self.minimum_offset = self.pointer_base;
                    size = range.get_end().wrapping_sub(self.pointer_base);
                } else {
                    self.minimum_offset = range.get_min();
                    size = range_size.wrapping_mul(range.get_step() as i64 as u64);
                }
            } else {
                self.minimum_offset = self.pointer_base;
            }
        }
        let max = self.guard_space().get_highest();
        if self.minimum_offset > max {
            self.minimum_offset = max;
            self.maximum_offset = self.minimum_offset;
        } else {
            let max_size = (max - self.minimum_offset).wrapping_add(1);
            if size > max_size {
                size = max_size;
            }
            self.maximum_offset = self.minimum_offset.wrapping_add(size).wrapping_sub(1);
        }
    }

    fn finalize_range(&mut self, value_set: &ValueSetRead) {
        self.analysis_state = 1;
        let range = value_set.get_range();
        let mut range_size = range.get_size();
        if (range_size == 0x100 || range_size == 0x10000) && self.step == 0 {
            range_size = 0;
        }
        if range_size > 1 && range_size < 0xffffff {
            self.analysis_state = 2;
            if range_size > 2 {
                self.step = range.get_step();
            }
            self.minimum_offset = range.get_min();
            self.maximum_offset = range.get_end().wrapping_sub(1) & range.get_mask();
            if self.maximum_offset < self.minimum_offset {
                self.maximum_offset = self.guard_space().get_highest();
                self.analysis_state = 1;
            }
        }
        let highest = self.guard_space().get_highest();
        if self.minimum_offset > highest {
            self.minimum_offset = highest;
        }
        if self.maximum_offset > highest {
            self.maximum_offset = highest;
        }
    }

    fn set(&mut self, op: OpId, space: SpaceRef, off: u64) {
        self.op = Some(op);
        self.maximum_offset = space.get_highest();
        self.spc = Some(space);
        self.pointer_base = off;
        self.minimum_offset = 0;
        self.step = 0;
        self.analysis_state = 0;
    }

    pub fn get_op(&self) -> Option<OpId> {
        self.op
    }

    pub fn get_minimum(&self) -> u64 {
        self.minimum_offset
    }

    pub fn get_maximum(&self) -> u64 {
        self.maximum_offset
    }

    pub fn get_step(&self) -> i32 {
        self.step
    }

    pub fn is_guarded(&self, addr: &Address) -> bool {
        if !same_space(&addr.get_space().cloned(), &self.spc) {
            return false;
        }
        if addr.get_offset() < self.minimum_offset {
            return false;
        }
        if addr.get_offset() > self.maximum_offset {
            return false;
        }
        true
    }

    pub fn is_range_locked(&self) -> bool {
        self.analysis_state == 2
    }

    pub fn is_valid(&self, opc: OpCode, data: &Funcdata) -> bool {
        let op = data.op(self.op.expect("load guard without op"));
        !op.is_dead() && op.code() == opc
    }
}

#[derive(Clone, Debug)]
pub struct StackNode {
    pub vn: VarnodeId,
    pub offset: u64,
    pub traversals: u32,
    pub iter: usize,
}

impl StackNode {
    pub const NONCONSTANT_INDEX: u32 = 1;
    pub const MULTIEQUAL: u32 = 2;

    pub fn new(varnode: VarnodeId, offset_2: u64, trav: u32) -> StackNode {
        StackNode {
            vn: varnode,
            offset: offset_2,
            iter: 0,
            traversals: trav,
        }
    }
}

#[derive(Clone, Debug)]
pub struct Heritage {
    globaldisjoint: LocationMap,
    disjoint: TaskList,
    domchild: Vec<Vec<BlockId>>,
    augment: Vec<Vec<BlockId>>,
    flags: Vec<u32>,
    depth: Vec<i32>,
    maxdepth: i32,
    pass: i32,
    pq: PriorityQueue,
    merge: Vec<BlockId>,
    infolist: Vec<HeritageInfo>,
    load_guard: Vec<LoadGuard>,
    store_guard: Vec<LoadGuard>,
    load_copy_ops: Vec<OpId>,
}

impl Default for Heritage {
    fn default() -> Heritage {
        Heritage::new()
    }
}

impl Heritage {
    pub const BOUNDARY_NODE: u32 = 1;
    pub const MARK_NODE: u32 = 2;
    pub const MERGED_NODE: u32 = 4;

    pub fn new() -> Heritage {
        Heritage {
            globaldisjoint: LocationMap::new(),
            disjoint: TaskList::new(),
            domchild: Vec::new(),
            augment: Vec::new(),
            flags: Vec::new(),
            depth: Vec::new(),
            maxdepth: -1,
            pass: 0,
            pq: PriorityQueue::new(),
            merge: Vec::new(),
            infolist: Vec::new(),
            load_guard: Vec::new(),
            store_guard: Vec::new(),
            load_copy_ops: Vec::new(),
        }
    }

    fn clear_info_list(&mut self) {
        for info in self.infolist.iter_mut() {
            info.reset();
        }
    }

    fn get_info(&self, spc: &SpaceRef) -> &HeritageInfo {
        &self.infolist[spc.get_index() as usize]
    }

    fn get_info_mut(&mut self, spc: &SpaceRef) -> &mut HeritageInfo {
        &mut self.infolist[spc.get_index() as usize]
    }

    fn clear_stack_placeholders(data: &mut Funcdata, glb: &mut Architecture, spc: &SpaceRef) -> Result<()> {
        let num_calls = data.num_calls();
        for index in 0..num_calls {
            let fc = data.get_call_specs(index);
            FuncCallSpecs::abort_spacebase_relative(data, fc, glb)?;
        }
        data.heritage.get_info_mut(spc).has_call_placeholders = false;
        Ok(())
    }

    fn split_join_level(
        data: &mut Funcdata,
        glb: &mut Architecture,
        lastcombo: &[VarnodeId],
        nextlev: &mut Vec<Option<VarnodeId>>,
        joinrec: &Arc<JoinRecord>,
    ) -> Result<()> {
        let numpieces = joinrec.num_pieces();
        let mut recnum = 0;
        for &curvn in lastcombo {
            let cursize = data.vn(curvn).get_size();
            if cursize == joinrec.get_piece(recnum).size as i32 {
                nextlev.push(Some(curvn));
                nextlev.push(None);
                recnum += 1;
            } else {
                let mut sizeaccum = 0;
                let mut last = recnum;
                while last < numpieces {
                    sizeaccum += joinrec.get_piece(last).size as i32;
                    if sizeaccum == cursize {
                        last += 1;
                        break;
                    }
                    last += 1;
                }
                let numinhalf = (last - recnum) / 2;
                sizeaccum = 0;
                for piece in 0..numinhalf {
                    sizeaccum += joinrec.get_piece(recnum + piece).size as i32;
                }
                let mosthalf = if numinhalf == 1 {
                    let vdata = joinrec.get_piece(recnum);
                    let space = vdata.space.clone().expect("join piece without space");
                    data.new_varnode_space_offset(sizeaccum, &space, vdata.offset, glb)?
                } else {
                    data.new_unique(sizeaccum, None, glb)
                };
                let leasthalf = if (last - recnum) == 2 {
                    let vdata = joinrec.get_piece(recnum + 1);
                    let space = vdata.space.clone().expect("join piece without space");
                    data.new_varnode_space_offset(vdata.size as i32, &space, vdata.offset, glb)?
                } else {
                    data.new_unique(cursize - sizeaccum, None, glb)
                };
                nextlev.push(Some(mosthalf));
                nextlev.push(Some(leasthalf));
                recnum = last;
            }
        }
        Ok(())
    }

    fn is_primitive_join(data: &Funcdata, glb: &Architecture, vn: VarnodeId) -> bool {
        if data.vn(vn).is_type_lock() {
            let types = type_factory(glb);
            return types.get(data.vn(vn).get_type()).is_primitive_whole(types);
        }
        true
    }

    fn split_join_read(
        data: &mut Funcdata,
        glb: &mut Architecture,
        vn: VarnodeId,
        joinrec: &Arc<JoinRecord>,
    ) -> Result<()> {
        let mut op = data
            .vn(vn)
            .lone_descend()
            .ok_or_else(|| Error::Lowlevel("Free join varnode with multiple descendants".to_string()))?;
        let is_primitive = Heritage::is_primitive_join(data, glb, vn);
        let mut lastcombo: Vec<VarnodeId> = vec![vn];
        let mut nextlev: Vec<Option<VarnodeId>> = Vec::new();
        while (lastcombo.len() as i32) < joinrec.num_pieces() {
            nextlev.clear();
            Heritage::split_join_level(data, glb, &lastcombo, &mut nextlev, joinrec)?;
            for (index, &curvn) in lastcombo.iter().enumerate() {
                let mosthalf = nextlev[2 * index].expect("missing most significant join piece");
                let Some(leasthalf) = nextlev[2 * index + 1] else {
                    continue;
                };
                let addr = data.op(op).get_addr().clone();
                let concat = data.new_op(2, &addr);
                data.op_set_opcode(concat, OpCode::Piece, glb);
                data.op_set_output(concat, curvn, glb)?;
                data.op_set_input(concat, mosthalf, 0)?;
                data.op_set_input(concat, leasthalf, 1)?;
                data.op_insert_before(concat, op);
                if is_primitive {
                    data.vbank.get_mut(mosthalf).set_precis_hi(&mut data.highs);
                    data.vbank.get_mut(leasthalf).set_precis_lo(&mut data.highs);
                } else {
                    data.op_mark_no_collapse(concat);
                }
                op = concat;
            }
            lastcombo = nextlev.iter().flatten().copied().collect();
        }
        Ok(())
    }

    fn split_join_write(
        data: &mut Funcdata,
        glb: &mut Architecture,
        vn: VarnodeId,
        joinrec: &Arc<JoinRecord>,
    ) -> Result<()> {
        let mut op = data.vn(vn).get_def();
        let bb = data.block(data.bblocks).get_block(0);
        let is_primitive = Heritage::is_primitive_join(data, glb, vn);
        let mut lastcombo: Vec<VarnodeId> = vec![vn];
        let mut nextlev: Vec<Option<VarnodeId>> = Vec::new();
        while (lastcombo.len() as i32) < joinrec.num_pieces() {
            nextlev.clear();
            Heritage::split_join_level(data, glb, &lastcombo, &mut nextlev, joinrec)?;
            for (index, &curvn) in lastcombo.iter().enumerate() {
                let mosthalf = nextlev[2 * index].expect("missing most significant join piece");
                let Some(leasthalf) = nextlev[2 * index + 1] else {
                    continue;
                };
                let split_addr = if data.vn(vn).is_input() {
                    data.block(bb).get_start()
                } else {
                    data.op(op.expect("written join varnode without def"))
                        .get_addr()
                        .clone()
                };
                let split = data.new_op(2, &split_addr);
                data.op_set_opcode(split, OpCode::Subpiece, glb);
                data.op_set_output(split, mosthalf, glb)?;
                data.op_set_input(split, curvn, 0)?;
                let least_size = data.vn(leasthalf).get_size();
                let constant = data.new_constant(4, signed_offset(least_size), glb);
                data.op_set_input(split, constant, 1)?;
                match op {
                    None => data.op_insert_begin(split, bb),
                    Some(prev) => data.op_insert_after(split, prev),
                }
                op = Some(split);

                let split_addr = data.op(split).get_addr().clone();
                let split = data.new_op(2, &split_addr);
                data.op_set_opcode(split, OpCode::Subpiece, glb);
                data.op_set_output(split, leasthalf, glb)?;
                data.op_set_input(split, curvn, 0)?;
                let constant = data.new_constant(4, 0, glb);
                data.op_set_input(split, constant, 1)?;
                data.op_insert_after(split, op.expect("split op"));
                if is_primitive {
                    data.vbank.get_mut(mosthalf).set_precis_hi(&mut data.highs);
                    data.vbank.get_mut(leasthalf).set_precis_lo(&mut data.highs);
                }
                op = Some(split);
            }
            lastcombo = nextlev.iter().flatten().copied().collect();
        }
        Ok(())
    }

    fn float_extension_read(
        data: &mut Funcdata,
        glb: &mut Architecture,
        vn: VarnodeId,
        joinrec: &Arc<JoinRecord>,
    ) -> Result<()> {
        let op = data
            .vn(vn)
            .lone_descend()
            .ok_or_else(|| Error::Lowlevel("Free join varnode with multiple descendants".to_string()))?;
        let addr = data.op(op).get_addr().clone();
        let trunc = data.new_op(1, &addr);
        let vdata = joinrec.get_piece(0).clone();
        let space = vdata.space.clone().expect("join piece without space");
        let bigvn = data.new_varnode_space_offset(vdata.size as i32, &space, vdata.offset, glb)?;
        data.op_set_opcode(trunc, OpCode::FloatFloat2float, glb);
        data.op_set_output(trunc, vn, glb)?;
        data.op_set_input(trunc, bigvn, 0)?;
        data.op_insert_before(trunc, op);
        Ok(())
    }

    fn float_extension_write(
        data: &mut Funcdata,
        glb: &mut Architecture,
        vn: VarnodeId,
        joinrec: &Arc<JoinRecord>,
    ) -> Result<()> {
        let op = data.vn(vn).get_def();
        let bb = data.block(data.bblocks).get_block(0);
        let ext_addr = if data.vn(vn).is_input() {
            data.block(bb).get_start()
        } else {
            data.op(op.expect("written join varnode without def"))
                .get_addr()
                .clone()
        };
        let ext = data.new_op(1, &ext_addr);
        let vdata = joinrec.get_piece(0).clone();
        data.op_set_opcode(ext, OpCode::FloatFloat2float, glb);
        data.new_varnode_out(vdata.size as i32, &vdata.get_addr(), ext, glb)?;
        data.op_set_input(ext, vn, 0)?;
        match op {
            None => data.op_insert_begin(ext, bb),
            Some(prev) => data.op_insert_after(ext, prev),
        }
        Ok(())
    }

    fn process_joins(data: &mut Funcdata, glb: &mut Architecture) -> Result<()> {
        let joinspace = glb.manager.get_join_space().expect("missing join space");
        let mut iter = data.begin_loc_space(&joinspace);
        while let Some(vn) = data.vbank.loc_at(&iter) {
            if !space_matches(data.vn(vn).get_space(), &joinspace) {
                break;
            }
            iter = data.vbank.loc_next(&iter);
            let joinrec = glb.manager.find_join(data.vn(vn).get_offset())?;
            let piecespace = joinrec.get_piece(0).space.clone().expect("join piece without space");
            if joinrec.get_unified().size as i32 != data.vn(vn).get_size() {
                return Err(Error::Lowlevel(
                    "Joined varnode does not match size of record".to_string(),
                ));
            }
            if data.vn(vn).is_free() {
                if data.vn(vn).has_no_descend() {
                    data.delete_varnode(vn)?;
                    continue;
                }
                if joinrec.is_float_extension() {
                    Heritage::float_extension_read(data, glb, vn, &joinrec)?;
                } else {
                    Heritage::split_join_read(data, glb, vn, &joinrec)?;
                }
            }
            if data.heritage.pass != data.heritage.get_info(&piecespace).delay {
                continue;
            }
            if joinrec.is_float_extension() {
                Heritage::float_extension_write(data, glb, vn, &joinrec)?;
            } else {
                Heritage::split_join_write(data, glb, vn, &joinrec)?;
            }
        }
        Ok(())
    }

    fn build_adt(data: &mut Funcdata) {
        let graph = data.bblocks;
        let size = data.block(graph).get_size() as usize;
        let mut acount: Vec<i32> = vec![0; size];
        let mut bcount: Vec<i32> = vec![0; size];
        let mut tcount: Vec<i32> = vec![0; size];
        let mut zlink: Vec<i32> = vec![0; size];
        let mut upstart: Vec<BlockId> = Vec::new();
        let mut upend: Vec<BlockId> = Vec::new();

        data.heritage.augment.clear();
        data.heritage.augment.resize(size, Vec::new());
        data.heritage.flags.clear();
        data.heritage.flags.resize(size, 0);

        let mut domchild: Vec<Vec<BlockId>> = Vec::new();
        data.block_build_dom_tree(graph, &mut domchild);
        let mut depth: Vec<i32> = Vec::new();
        data.heritage.maxdepth = data.block_build_dom_depth(graph, &mut depth);
        data.heritage.depth = depth;
        for index in 0..size {
            let xblock = data.block(graph).get_block(index as i32);
            let xindex = data.block(xblock).get_index() as usize;
            for &child in domchild[index].iter() {
                let child_block = data.block(child);
                for slot in 0..child_block.size_in() {
                    let upblock = child_block.get_in(slot);
                    if Some(upblock) != child_block.get_immed_dom() {
                        upstart.push(upblock);
                        upend.push(child);
                        bcount[data.block(upblock).get_index() as usize] += 1;
                        tcount[xindex] += 1;
                    }
                }
            }
        }
        for index in (0..size).rev() {
            let mut ksum = 0;
            let mut lsum = 0;
            for &child in domchild[index].iter() {
                let child_index = data.block(child).get_index() as usize;
                ksum += acount[child_index];
                lsum += zlink[child_index];
            }
            acount[index] = bcount[index] - tcount[index] + ksum;
            zlink[index] = 1 + lsum;
            if domchild[index].is_empty() || zlink[index] > acount[index] + 1 {
                data.heritage.flags[index] |= Heritage::BOUNDARY_NODE;
                zlink[index] = 1;
            }
        }
        if size > 0 {
            zlink[0] = -1;
        }
        for index in 1..size {
            let block = data.block(graph).get_block(index as i32);
            let idom = data
                .block(block)
                .get_immed_dom()
                .expect("block without immediate dominator");
            let dom_index = data.block(idom).get_index() as usize;
            if (data.heritage.flags[dom_index] & Heritage::BOUNDARY_NODE) != 0 {
                zlink[index] = dom_index as i32;
            } else {
                zlink[index] = zlink[dom_index];
            }
        }
        for edge in 0..upstart.len() {
            let vblock = upend[edge];
            let idom = data
                .block(vblock)
                .get_immed_dom()
                .expect("block without immediate dominator");
            let dom_index = data.block(idom).get_index();
            let mut kindex = data.block(upstart[edge]).get_index();
            while dom_index < kindex {
                data.heritage.augment[kindex as usize].push(vblock);
                kindex = zlink[kindex as usize];
            }
        }
        data.heritage.domchild = domchild;
    }

    fn remove_revisited_markers(
        data: &mut Funcdata,
        glb: &mut Architecture,
        remove: &[VarnodeId],
        addr: &Address,
        size: i32,
    ) -> Result<()> {
        let spc = address_space(addr);
        if data.heritage.get_info(&spc).deadremoved > 0 {
            Heritage::bump_deadcode_delay(data, &spc);
            if !data.heritage.get_info(&spc).warningissued {
                data.heritage.get_info_mut(&spc).warningissued = true;
                let mut errmsg = String::from("Heritage AFTER dead removal. Revisit: ");
                addr.print_raw(&mut errmsg);
                data.warning_header(&errmsg, glb);
            }
        }

        for &vn in remove {
            let op = def_op(data, vn);
            let bl = data.op(op).get_parent().expect("op without parent block");
            let pos: Option<OpId>;
            match data.op(op).code() {
                OpCode::Indirect => {
                    let iop_vn = data.op(op).get_in(1);
                    let target_op = PcodeOp::get_op_from_const(data.vn(iop_vn).get_addr());
                    if data.op(target_op).is_dead() {
                        pos = next_basic_op(data, op);
                    } else {
                        pos = next_basic_op(data, target_op);
                    }
                    data.vbank.get_mut(vn).clear_addr_force(&mut data.highs);
                }
                OpCode::Multiequal => {
                    let mut cursor = next_basic_op(data, op);
                    while let Some(current) = cursor {
                        if data.op(current).code() != OpCode::Multiequal {
                            break;
                        }
                        cursor = next_basic_op(data, current);
                    }
                    pos = cursor;
                }
                _ => {
                    data.op_unlink(op)?;
                    continue;
                }
            }
            let offset = data.vn(vn).overlap_addr(addr, size);
            data.op_uninsert(op);
            let big = data.new_varnode(size, addr, None, glb)?;
            data.vn_mut(big).set_active_heritage();
            let constant = data.new_constant(4, signed_offset(offset), glb);
            let new_inputs = vec![big, constant];
            data.op_set_opcode(op, OpCode::Subpiece, glb);
            data.op_set_all_input(op, &new_inputs)?;
            data.op_insert(op, bl, pos);
            data.vn_mut(vn).set_write_mask();
        }
        Ok(())
    }

    fn collect(
        data: &Funcdata,
        glb: &Architecture,
        memrange: &mut MemRange,
        read: &mut Vec<VarnodeId>,
        write: &mut Vec<VarnodeId>,
        input: &mut Vec<VarnodeId>,
        remove: &mut Vec<VarnodeId>,
    ) -> i32 {
        read.clear();
        write.clear();
        input.clear();
        remove.clear();
        let start = memrange.addr.get_offset();
        let endaddr = &memrange.addr + memrange.size as i64;
        let enditer = if endaddr.get_offset() < start {
            let spc = address_space(&endaddr);
            let tmp = Address::new(spc.clone(), spc.get_highest());
            data.end_loc_addr(&tmp, glb)
        } else {
            data.begin_loc_addr(&endaddr)
        };
        let begin = data.begin_loc_addr(&memrange.addr);
        let mut maxsize = 0;
        for vn in data.vbank.loc_range(&begin, &enditer) {
            let varnode = data.vn(vn);
            if varnode.is_write_mask() {
                continue;
            }
            if varnode.is_written() {
                let op = data.op(varnode.get_def().expect("written varnode without def"));
                if op.is_marker() || op.is_return_copy() {
                    if varnode.get_size() < memrange.size {
                        remove.push(vn);
                        continue;
                    }
                    memrange.clear_property(MemRange::NEW_ADDRESSES);
                }
                if varnode.get_size() > maxsize {
                    maxsize = varnode.get_size();
                }
                write.push(vn);
            } else if !varnode.is_heritage_known() && !varnode.has_no_descend() {
                read.push(vn);
            } else if varnode.is_input() {
                input.push(vn);
            }
        }
        maxsize
    }

    fn call_op_indirect_effect(data: &Funcdata, glb: &Architecture, addr: &Address, size: i32, op: OpId) -> bool {
        let opc = data.op(op).code();
        if opc == OpCode::Call || opc == OpCode::Callind {
            let Some(fc) = data.get_call_specs_op(op) else {
                return true;
            };
            return data.call_spec(fc).has_effect_translate(addr, size, glb) != EffectRecord::UNAFFECTED;
        }
        false
    }

    fn normalize_read_size(
        data: &mut Funcdata,
        glb: &mut Architecture,
        vn: VarnodeId,
        op: OpId,
        addr: &Address,
        size: i32,
    ) -> Result<VarnodeId> {
        let op_addr = data.op(op).get_addr().clone();
        let newop = data.new_op(2, &op_addr);
        data.op_set_opcode(newop, OpCode::Subpiece, glb);
        let vn1 = data.new_varnode(size, addr, None, glb)?;
        let overlap = data.vn(vn).overlap_addr(addr, size);
        let vn2 = data.new_constant(addr.get_addr_size(), signed_offset(overlap), glb);
        data.op_set_input(newop, vn1, 0)?;
        data.op_set_input(newop, vn2, 1)?;
        data.op_set_output(newop, vn, glb)?;
        let out = out_vn(data, newop);
        data.vn_mut(out).set_write_mask();
        data.op_insert_before(newop, op);
        Ok(vn1)
    }

    fn normalize_write_size(
        data: &mut Funcdata,
        glb: &mut Architecture,
        vn: VarnodeId,
        addr: &Address,
        size: i32,
    ) -> Result<VarnodeId> {
        let mut mostvn: Option<VarnodeId> = None;
        let mut leastvn: Option<VarnodeId> = None;
        let op = def_op(data, vn);
        let op_addr = data.op(op).get_addr().clone();
        let vnsize = data.vn(vn).get_size();
        let overlap = data.vn(vn).overlap_addr(addr, size);
        let mostsigsize = size - (overlap + vnsize);
        if mostsigsize != 0 {
            let pieceaddr = if addr.is_big_endian() {
                addr.clone()
            } else {
                addr + (overlap + vnsize) as i64
            };
            if data.op(op).is_call() && Heritage::call_op_indirect_effect(data, glb, &pieceaddr, mostsigsize, op) {
                let newop = data.new_indirect_creation(op, &pieceaddr, mostsigsize, false, glb)?;
                mostvn = Some(out_vn(data, newop));
            } else {
                let newop = data.new_op(2, &op_addr);
                mostvn = Some(data.new_varnode_out(mostsigsize, &pieceaddr, newop, glb)?);
                let big = data.new_varnode(size, addr, None, glb)?;
                data.vn_mut(big).set_active_heritage();
                data.op_set_opcode(newop, OpCode::Subpiece, glb);
                data.op_set_input(newop, big, 0)?;
                let constant = data.new_constant(
                    addr.get_addr_size(),
                    signed_offset(overlap).wrapping_add(signed_offset(vnsize)),
                    glb,
                );
                data.op_set_input(newop, constant, 1)?;
                data.op_insert_before(newop, op);
            }
        }
        if overlap != 0 {
            let pieceaddr = if addr.is_big_endian() {
                addr + (size - overlap) as i64
            } else {
                addr.clone()
            };
            if data.op(op).is_call() && Heritage::call_op_indirect_effect(data, glb, &pieceaddr, overlap, op) {
                let newop = data.new_indirect_creation(op, &pieceaddr, overlap, false, glb)?;
                leastvn = Some(out_vn(data, newop));
            } else {
                let newop = data.new_op(2, &op_addr);
                leastvn = Some(data.new_varnode_out(overlap, &pieceaddr, newop, glb)?);
                let big = data.new_varnode(size, addr, None, glb)?;
                data.vn_mut(big).set_active_heritage();
                data.op_set_opcode(newop, OpCode::Subpiece, glb);
                data.op_set_input(newop, big, 0)?;
                let constant = data.new_constant(addr.get_addr_size(), 0, glb);
                data.op_set_input(newop, constant, 1)?;
                data.op_insert_before(newop, op);
            }
        }
        let midvn = if overlap != 0 {
            let newop = data.new_op(2, &op_addr);
            let midvn = if addr.is_big_endian() {
                let vn_addr = data.vn(vn).get_addr().clone();
                data.new_varnode_out(overlap + vnsize, &vn_addr, newop, glb)?
            } else {
                data.new_varnode_out(overlap + vnsize, addr, newop, glb)?
            };
            data.op_set_opcode(newop, OpCode::Piece, glb);
            data.op_set_input(newop, vn, 0)?;
            data.op_set_input(newop, leastvn.expect("missing least significant piece"), 1)?;
            data.op_insert_after(newop, op);
            midvn
        } else {
            vn
        };
        let bigout = if mostsigsize != 0 {
            let newop = data.new_op(2, &op_addr);
            let bigout = data.new_varnode_out(size, addr, newop, glb)?;
            data.op_set_opcode(newop, OpCode::Piece, glb);
            data.op_set_input(newop, mostvn.expect("missing most significant piece"), 0)?;
            data.op_set_input(newop, midvn, 1)?;
            let mid_def = def_op(data, midvn);
            data.op_insert_after(newop, mid_def);
            bigout
        } else {
            midvn
        };
        data.vn_mut(vn).set_write_mask();
        Ok(bigout)
    }

    fn concat_pieces(
        data: &mut Funcdata,
        glb: &mut Architecture,
        vnlist: &[VarnodeId],
        insertop: Option<OpId>,
        finalvn: VarnodeId,
    ) -> Result<VarnodeId> {
        let mut preexist = vnlist[0];
        let isbigendian = data.vn(preexist).get_addr().is_big_endian();
        let bl: BlockId;
        let insertiter: Option<OpId>;
        let opaddress: Address;
        match insertop {
            None => {
                bl = data.block_get_start_block(data.bblocks)?;
                insertiter = data.block(bl).get_op_list().front();
                opaddress = data.get_address().clone();
            }
            Some(insert) => {
                bl = data.op(insert).get_parent().expect("op without parent block");
                insertiter = Some(insert);
                opaddress = data.op(insert).get_addr().clone();
            }
        }
        for index in 1..vnlist.len() {
            let vn = vnlist[index];
            let newop = data.new_op(2, &opaddress);
            data.op_set_opcode(newop, OpCode::Piece, glb);
            let newvn = if index == vnlist.len() - 1 {
                data.op_set_output(newop, finalvn, glb)?;
                finalvn
            } else {
                let newsize = data.vn(preexist).get_size() + data.vn(vn).get_size();
                data.new_unique_out(newsize, newop, glb)?
            };
            if isbigendian {
                data.op_set_input(newop, preexist, 0)?;
                data.op_set_input(newop, vn, 1)?;
            } else {
                data.op_set_input(newop, vn, 0)?;
                data.op_set_input(newop, preexist, 1)?;
            }
            data.op_insert(newop, bl, insertiter);
            preexist = newvn;
        }
        Ok(preexist)
    }

    fn split_pieces(
        data: &mut Funcdata,
        glb: &mut Architecture,
        vnlist: &[VarnodeId],
        insertop: Option<OpId>,
        addr: &Address,
        size: i32,
        startvn: VarnodeId,
    ) -> Result<()> {
        let isbigendian = addr.is_big_endian();
        let baseoff = if isbigendian {
            addr.get_offset().wrapping_add(signed_offset(size))
        } else {
            addr.get_offset()
        };
        let bl: BlockId;
        let insertiter: Option<OpId>;
        let opaddress: Address;
        match insertop {
            None => {
                bl = data.block_get_start_block(data.bblocks)?;
                insertiter = data.block(bl).get_op_list().front();
                opaddress = data.get_address().clone();
            }
            Some(insert) => {
                bl = data.op(insert).get_parent().expect("op without parent block");
                insertiter = next_basic_op(data, insert);
                opaddress = data.op(insert).get_addr().clone();
            }
        }
        for &vn in vnlist {
            let newop = data.new_op(2, &opaddress);
            data.op_set_opcode(newop, OpCode::Subpiece, glb);
            let piece = data.vn(vn);
            let diff = if isbigendian {
                baseoff.wrapping_sub(piece.get_offset().wrapping_add(signed_offset(piece.get_size())))
            } else {
                piece.get_offset().wrapping_sub(baseoff)
            };
            data.op_set_input(newop, startvn, 0)?;
            let constant = data.new_constant(4, diff, glb);
            data.op_set_input(newop, constant, 1)?;
            data.op_set_output(newop, vn, glb)?;
            data.op_insert(newop, bl, insertiter);
        }
        Ok(())
    }

    fn find_address_forces(data: &mut Funcdata, copy_sinks: &mut Vec<OpId>, forces: &mut Vec<OpId>) {
        for &op in copy_sinks.iter() {
            data.op_mut(op).set_mark();
        }

        let mut pos = 0;
        while pos < copy_sinks.len() {
            let op = copy_sinks[pos];
            let addr = data.vn(out_vn(data, op)).get_addr().clone();
            pos += 1;
            let max_in = data.op(op).num_input();
            for slot in 0..max_in {
                let vn = data.op(op).get_in(slot);
                if !data.vn(vn).is_written() {
                    continue;
                }
                if data.vn(vn).is_addr_force() {
                    continue;
                }
                let new_op = def_op(data, vn);
                if data.op(new_op).is_mark() {
                    continue;
                }
                data.op_mut(new_op).set_mark();
                let opc = data.op(new_op).code();
                let mut is_artificial = false;
                if opc == OpCode::Copy || opc == OpCode::Multiequal {
                    is_artificial = true;
                    let max_in_new = data.op(new_op).num_input();
                    for new_slot in 0..max_in_new {
                        let in_vn = data.op(new_op).get_in(new_slot);
                        if addr != *data.vn(in_vn).get_addr() {
                            is_artificial = false;
                            break;
                        }
                    }
                } else if opc == OpCode::Indirect && data.op(new_op).is_indirect_store() {
                    let in_vn = data.op(new_op).get_in(0);
                    if addr == *data.vn(in_vn).get_addr() {
                        is_artificial = true;
                    }
                }
                if is_artificial {
                    copy_sinks.push(new_op);
                } else {
                    forces.push(new_op);
                }
            }
        }
    }

    fn propagate_copy_away(data: &mut Funcdata, op: OpId) -> Result<()> {
        let mut in_vn = data.op(op).get_in(0);
        while data.vn(in_vn).is_written() {
            let next_op = def_op(data, in_vn);
            if data.op(next_op).code() != OpCode::Copy {
                break;
            }
            let next_in = data.op(next_op).get_in(0);
            if data.vn(next_in).get_addr() != data.vn(in_vn).get_addr() {
                break;
            }
            in_vn = next_in;
        }
        let out = out_vn(data, op);
        data.total_replace(out, in_vn)?;
        data.op_destroy(op)?;
        Ok(())
    }

    fn handle_new_load_copies(data: &mut Funcdata) -> Result<()> {
        if data.heritage.load_copy_ops.is_empty() {
            return Ok(());
        }
        let mut load_copy_ops = std::mem::take(&mut data.heritage.load_copy_ops);
        let mut forces: Vec<OpId> = Vec::new();
        let copy_sink_size = load_copy_ops.len();
        Heritage::find_address_forces(data, &mut load_copy_ops, &mut forces);

        if !forces.is_empty() {
            let mut load_ranges = RangeList::new();
            for guard in data.heritage.load_guard.iter() {
                load_ranges.insert_range(guard.guard_space(), guard.minimum_offset, guard.maximum_offset);
            }
            for &op in forces.iter() {
                let vn = out_vn(data, op);
                if load_ranges.in_range(data.vn(vn).get_addr(), 1) {
                    data.vbank.get_mut(vn).set_addr_force(&mut data.highs);
                }
                data.op_mut(op).clear_mark();
            }
        }

        for &op in load_copy_ops[..copy_sink_size].iter() {
            Heritage::propagate_copy_away(data, op)?;
        }
        for &op in load_copy_ops[copy_sink_size..].iter() {
            data.op_mut(op).clear_mark();
        }
        data.heritage.load_copy_ops.clear();
        Ok(())
    }

    fn analyze_new_load_guards(data: &mut Funcdata, glb: &mut Architecture) -> Result<()> {
        let mut nothing_to_do = true;
        if let Some(last) = data.heritage.load_guard.last()
            && last.analysis_state == 0
        {
            nothing_to_do = false;
        }
        if let Some(last) = data.heritage.store_guard.last()
            && last.analysis_state == 0
        {
            nothing_to_do = false;
        }
        if nothing_to_do {
            return Ok(());
        }

        let mut sinks: Vec<VarnodeId> = Vec::new();
        let mut reads: Vec<OpId> = Vec::new();
        let mut load_start = data.heritage.load_guard.len();
        while load_start > 0 {
            let guard = &data.heritage.load_guard[load_start - 1];
            if guard.analysis_state != 0 {
                break;
            }
            load_start -= 1;
            let op = guard.op.expect("load guard without op");
            reads.push(op);
            sinks.push(data.op(op).get_in(1));
        }
        let mut store_start = data.heritage.store_guard.len();
        while store_start > 0 {
            let guard = &data.heritage.store_guard[store_start - 1];
            if guard.analysis_state != 0 {
                break;
            }
            store_start -= 1;
            let op = guard.op.expect("store guard without op");
            reads.push(op);
            sinks.push(data.op(op).get_in(1));
        }
        let stack_spc = glb.manager.get_stack_space();
        let mut stack_reg: Option<VarnodeId> = None;
        if let Some(stack_spc) = &stack_spc
            && stack_spc.num_spacebase() > 0
        {
            stack_reg = data.find_spacebase_input(stack_spc)?;
        }
        let mut vs_solver = ValueSetSolver::default();
        vs_solver.establish_value_sets(&sinks, &reads, stack_reg, false, data);
        let mut widener = WidenerNone::new();
        vs_solver.solve(10000, &mut widener, data);
        let mut run_full_analysis = false;
        for index in load_start..data.heritage.load_guard.len() {
            let op = data.heritage.load_guard[index].op.expect("load guard without op");
            let seq = data.op(op).get_seq_num().clone();
            let guard = &mut data.heritage.load_guard[index];
            guard.establish_range(vs_solver.get_value_set_read(&seq));
            if guard.analysis_state == 0 {
                run_full_analysis = true;
            }
        }
        for index in store_start..data.heritage.store_guard.len() {
            let op = data.heritage.store_guard[index].op.expect("store guard without op");
            let seq = data.op(op).get_seq_num().clone();
            data.heritage.store_guard[index].establish_range(vs_solver.get_value_set_read(&seq));
            data.op_mut(op).set_alias_update();
            if data.heritage.store_guard[index].analysis_state == 0 {
                run_full_analysis = true;
            }
        }
        if run_full_analysis {
            let mut full_widener = WidenerFull::new();
            vs_solver.solve(10000, &mut full_widener, data);
            for index in load_start..data.heritage.load_guard.len() {
                let op = data.heritage.load_guard[index].op.expect("load guard without op");
                let seq = data.op(op).get_seq_num().clone();
                data.heritage.load_guard[index].finalize_range(vs_solver.get_value_set_read(&seq));
            }
            for index in store_start..data.heritage.store_guard.len() {
                let op = data.heritage.store_guard[index].op.expect("store guard without op");
                let seq = data.op(op).get_seq_num().clone();
                data.heritage.store_guard[index].finalize_range(vs_solver.get_value_set_read(&seq));
            }
        }
        Ok(())
    }

    fn generate_load_guard(data: &mut Funcdata, node: &StackNode, op: OpId, spc: &SpaceRef) {
        if !data.op(op).uses_spacebase_ptr() {
            let mut guard = LoadGuard::default();
            guard.set(op, spc.clone(), node.offset);
            data.heritage.load_guard.push(guard);
            data.op_mark_spacebase_ptr(op);
        }
    }

    fn generate_store_guard(data: &mut Funcdata, node: &StackNode, op: OpId, spc: &SpaceRef) {
        if !data.op(op).uses_spacebase_ptr() {
            let mut guard = LoadGuard::default();
            guard.set(op, spc.clone(), node.offset);
            data.heritage.store_guard.push(guard);
            data.op_mark_spacebase_ptr(op);
        }
    }

    fn protect_free_stores(data: &mut Funcdata, spc: &SpaceRef, free_stores: &mut Vec<OpId>) -> bool {
        let mut iter = data.begin_op(OpCode::Store);
        let mut has_new = false;
        while let Some(op) = iter {
            iter = next_code_op(data, op);
            if data.op(op).is_dead() {
                continue;
            }
            let mut vn = data.op(op).get_in(1);
            while data.vn(vn).is_written() {
                let def = def_op(data, vn);
                let opc = data.op(def).code();
                if opc == OpCode::Copy {
                    vn = data.op(def).get_in(0);
                } else if opc == OpCode::IntAdd && data.vn(data.op(def).get_in(1)).is_constant() {
                    vn = data.op(def).get_in(0);
                } else {
                    break;
                }
            }
            if data.vn(vn).is_free() && space_matches(data.vn(vn).get_space(), spc) {
                data.op_mark_spacebase_ptr(op);
                free_stores.push(op);
                has_new = true;
            }
        }
        has_new
    }

    fn push_stack_node(
        data: &mut Funcdata,
        out: VarnodeId,
        offset: u64,
        traversals: u32,
        path: &mut Vec<StackNode>,
        marked_vn: &mut Vec<VarnodeId>,
        unknown_stack_storage: &mut bool,
    ) {
        if !data.vn(out).has_no_descend() {
            data.vn_mut(out).set_mark();
            path.push(StackNode::new(out, offset, traversals));
            marked_vn.push(out);
        } else if space_type_of(data.vn(out).get_space()) == Some(SpaceType::Spacebase) {
            *unknown_stack_storage = true;
        }
    }

    fn discover_indexed_stack_pointers(
        data: &mut Funcdata,
        spc: &SpaceRef,
        free_stores: &mut Vec<OpId>,
        check_free_stores: bool,
    ) -> Result<bool> {
        let mut marked_vn: Vec<VarnodeId> = Vec::new();
        let mut path: Vec<StackNode> = Vec::new();
        let mut unknown_stack_storage = false;
        for index in 0..spc.num_spacebase() {
            let stack_pointer = spc.get_spacebase(index)?;
            let Some(sp_input) = data.find_varnode_input(stack_pointer.size as i32, &stack_pointer.get_addr()) else {
                continue;
            };
            path.push(StackNode::new(sp_input, 0, 0));
            while let Some(cur_node) = path.last_mut() {
                let descend = data.vbank.get(cur_node.vn).descend();
                if cur_node.iter >= descend.len() {
                    path.pop();
                    continue;
                }
                let op = descend[cur_node.iter];
                cur_node.iter += 1;
                let cur_node = cur_node.clone();
                let out = data.op(op).get_out();
                if let Some(out) = out
                    && data.vn(out).is_mark()
                {
                    continue;
                }
                match data.op(op).code() {
                    OpCode::IntAdd => {
                        let out = out.expect("INT_ADD without output");
                        let slot = data.op(op).get_slot(cur_node.vn);
                        let other_vn = data.op(op).get_in(1 - slot);
                        if data.vn(other_vn).is_constant() {
                            let new_offset =
                                spc.wrap_offset(cur_node.offset.wrapping_add(data.vn(other_vn).get_offset()));
                            Heritage::push_stack_node(
                                data,
                                out,
                                new_offset,
                                cur_node.traversals,
                                &mut path,
                                &mut marked_vn,
                                &mut unknown_stack_storage,
                            );
                        } else {
                            Heritage::push_stack_node(
                                data,
                                out,
                                cur_node.offset,
                                cur_node.traversals | StackNode::NONCONSTANT_INDEX,
                                &mut path,
                                &mut marked_vn,
                                &mut unknown_stack_storage,
                            );
                        }
                    }
                    OpCode::Segmentop | OpCode::Indirect | OpCode::Copy => {
                        if data.op(op).code() == OpCode::Segmentop && data.op(op).get_in(2) != cur_node.vn {
                            continue;
                        }
                        let out = out.expect("op without output");
                        Heritage::push_stack_node(
                            data,
                            out,
                            cur_node.offset,
                            cur_node.traversals,
                            &mut path,
                            &mut marked_vn,
                            &mut unknown_stack_storage,
                        );
                    }
                    OpCode::Multiequal => {
                        let out = out.expect("MULTIEQUAL without output");
                        Heritage::push_stack_node(
                            data,
                            out,
                            cur_node.offset,
                            cur_node.traversals | StackNode::MULTIEQUAL,
                            &mut path,
                            &mut marked_vn,
                            &mut unknown_stack_storage,
                        );
                    }
                    OpCode::Load if cur_node.traversals != 0 => {
                        Heritage::generate_load_guard(data, &cur_node, op, spc);
                    }
                    OpCode::Store if data.op(op).get_in(1) == cur_node.vn => {
                        if cur_node.traversals != 0 {
                            Heritage::generate_store_guard(data, &cur_node, op, spc);
                        } else {
                            data.op_mark_spacebase_ptr(op);
                        }
                    }
                    _ => {}
                }
            }
        }
        for &vn in marked_vn.iter() {
            data.vn_mut(vn).clear_mark();
        }
        if unknown_stack_storage && check_free_stores {
            return Ok(Heritage::protect_free_stores(data, spc, free_stores));
        }
        Ok(false)
    }

    fn reprocess_free_stores(data: &mut Funcdata, spc: &SpaceRef, free_stores: &mut Vec<OpId>) -> Result<()> {
        for &op in free_stores.iter() {
            data.op_clear_spacebase_ptr(op);
        }

        Heritage::discover_indexed_stack_pointers(data, spc, free_stores, false)?;

        for &op in free_stores.iter() {
            if data.op(op).uses_spacebase_ptr() {
                continue;
            }
            let mut ind_op = data.op_previous_op(op);
            while let Some(indirect) = ind_op {
                if data.op(indirect).code() != OpCode::Indirect {
                    break;
                }
                let iop_vn = data.op(indirect).get_in(1);
                if space_type_of(data.vn(iop_vn).get_space()) != Some(SpaceType::Iop) {
                    break;
                }
                if op != PcodeOp::get_op_from_const(data.vn(iop_vn).get_addr()) {
                    break;
                }
                let next_op = data.op_previous_op(indirect);
                let out = out_vn(data, indirect);
                if space_matches(data.vn(out).get_space(), spc) {
                    let input = data.op(indirect).get_in(0);
                    data.total_replace(out, input)?;
                    data.op_destroy(indirect)?;
                }
                ind_op = next_op;
            }
        }
        Ok(())
    }

    fn guard(
        data: &mut Funcdata,
        glb: &mut Architecture,
        addr: &Address,
        size: i32,
        guard_performed: bool,
        read: &mut [VarnodeId],
        write: &mut Vec<VarnodeId>,
    ) -> Result<()> {
        for index in 0..read.len() {
            let mut vn = read[index];
            let descend = data.vn(vn).descend();
            if descend.is_empty() {
                continue;
            }
            let op = descend[0];
            if descend.len() > 1 {
                return Err(Error::Lowlevel("Free varnode with multiple reads".to_string()));
            }
            if data.vn(vn).get_size() < size {
                vn = Heritage::normalize_read_size(data, glb, vn, op, addr, size)?;
                read[index] = vn;
            }
            data.vn_mut(vn).set_active_heritage();
        }

        for index in 0..write.len() {
            let mut vn = write[index];
            if data.vn(vn).get_size() < size {
                vn = Heritage::normalize_write_size(data, glb, vn, addr, size)?;
                write[index] = vn;
            }
            data.vn_mut(vn).set_active_heritage();
        }

        if guard_performed {
            let mut fl: u32 = 0;
            let scope = data.get_scope_local().expect("function without local scope");
            glb.symboltab
                .as_deref()
                .expect("symbol table is not initialized")
                .scope_query_properties(scope, addr, size, &Address::invalid(), &mut fl);
            Heritage::guard_calls(data, glb, fl, addr, size, write)?;
            Heritage::guard_returns(data, glb, fl, addr, size)?;
            if addr.high_ptr_possible(size, &glb.manager) {
                Heritage::guard_stores(data, glb, addr, size, write)?;
                Heritage::guard_loads(data, glb, fl, addr, size)?;
            }
        }
        Ok(())
    }

    fn guard_input(
        data: &mut Funcdata,
        glb: &mut Architecture,
        addr: &Address,
        size: i32,
        input: &mut [VarnodeId],
    ) -> Result<()> {
        if input.is_empty() {
            return Ok(());
        }
        if input.len() == 1 && data.vn(input[0]).get_size() == size {
            return Ok(());
        }

        let spc = address_space(addr);
        let mut index = 0;
        let mut cur = addr.get_offset();
        let end = cur.wrapping_add(signed_offset(size));
        let mut newinput: Vec<VarnodeId> = Vec::new();

        while cur < end {
            let mut vn;
            if index < input.len() {
                vn = input[index];
                if data.vn(vn).get_offset() > cur {
                    let sz = data.vn(vn).get_offset().wrapping_sub(cur) as i32;
                    vn = data.new_varnode(sz, &Address::new(spc.clone(), cur), None, glb)?;
                    vn = data.set_input_varnode(vn, glb)?;
                } else {
                    index += 1;
                }
            } else {
                let sz = end.wrapping_sub(cur) as i32;
                vn = data.new_varnode(sz, &Address::new(spc.clone(), cur), None, glb)?;
                vn = data.set_input_varnode(vn, glb)?;
            }
            newinput.push(vn);
            cur = cur.wrapping_add(signed_offset(data.vn(vn).get_size()));
        }

        if newinput.len() == 1 {
            return Ok(());
        }
        let newout = data.new_varnode(size, addr, None, glb)?;
        let unified = Heritage::concat_pieces(data, glb, &newinput, None, newout)?;
        data.vn_mut(unified).set_active_heritage();
        Ok(())
    }

    fn guard_call_overlapping_input(
        data: &mut Funcdata,
        glb: &mut Architecture,
        fc: CallSpecId,
        addr: &Address,
        trans_addr: &Address,
        size: i32,
    ) -> Result<()> {
        let mut v_data = VarnodeData::default();

        if data
            .call_spec_mut(fc)
            .get_biggest_contained_input_param(trans_addr, size, &mut v_data, glb)
        {
            let mut trunc_addr = v_data.get_addr();
            let diff = trunc_addr.get_offset().wrapping_sub(trans_addr.get_offset()) as i32;
            trunc_addr = addr + diff as i64;
            if data.call_spec_mut(fc).get_active_input().which_trial(&trunc_addr, size) < 0 {
                let truncate_amount = addr.justified_contain(size, &trunc_addr, v_data.size as i32, false);
                let op = data.call_spec(fc).get_op();
                let op_addr = data.op(op).get_addr().clone();
                let subpiece_op = data.new_op(2, &op_addr);
                data.op_set_opcode(subpiece_op, OpCode::Subpiece, glb);
                let whole_vn = data.new_varnode(size, addr, None, glb)?;
                data.vn_mut(whole_vn).set_active_heritage();
                data.op_set_input(subpiece_op, whole_vn, 0)?;
                let constant = data.new_constant(4, signed_offset(truncate_amount), glb);
                data.op_set_input(subpiece_op, constant, 1)?;
                let vn = data.new_varnode_out(v_data.size as i32, &trunc_addr, subpiece_op, glb)?;
                data.op_insert_before(subpiece_op, op);
                data.call_spec_mut(fc)
                    .get_active_input()
                    .register_trial(&trunc_addr, v_data.size as i32);
                let num_input = data.op(op).num_input();
                data.op_insert_input(op, vn, num_input)?;
            }
        }
        Ok(())
    }

    fn guard_output_overlap(
        data: &mut Funcdata,
        glb: &mut Architecture,
        call_op: OpId,
        addr: &Address,
        size: i32,
        ret_addr: &Address,
        ret_size: i32,
        write: &mut Vec<VarnodeId>,
    ) -> Result<()> {
        let size_front = ret_addr.get_offset().wrapping_sub(addr.get_offset()) as i32;
        let size_back = size - ret_size - size_front;
        let ind_op = data.new_indirect_creation(call_op, ret_addr, ret_size, true, glb)?;
        let mut vn_collect = out_vn(data, ind_op);
        let mut insert_point = call_op;
        let ind_addr = data.op(ind_op).get_addr().clone();
        if size_front != 0 {
            let ind_op_front = data.new_indirect_creation(ind_op, addr, size_front, false, glb)?;
            let new_front = out_vn(data, ind_op_front);
            let concat_front = data.new_op(2, &ind_addr);
            let slot_new = if ret_addr.is_big_endian() { 0 } else { 1 };
            data.op_set_opcode(concat_front, OpCode::Piece, glb);
            data.op_set_input(concat_front, new_front, slot_new)?;
            data.op_set_input(concat_front, vn_collect, 1 - slot_new)?;
            vn_collect = data.new_varnode_out(size_front + ret_size, addr, concat_front, glb)?;
            data.op_insert_after(concat_front, insert_point);
            insert_point = concat_front;
        }
        if size_back != 0 {
            let addr_back = ret_addr + ret_size as i64;
            let ind_op_back = data.new_indirect_creation(call_op, &addr_back, size_back, false, glb)?;
            let new_back = out_vn(data, ind_op_back);
            let concat_back = data.new_op(2, &ind_addr);
            let slot_new = if ret_addr.is_big_endian() { 1 } else { 0 };
            data.op_set_opcode(concat_back, OpCode::Piece, glb);
            data.op_set_input(concat_back, new_back, slot_new)?;
            data.op_set_input(concat_back, vn_collect, 1 - slot_new)?;
            vn_collect = data.new_varnode_out(size, addr, concat_back, glb)?;
            data.op_insert_after(concat_back, insert_point);
        }
        data.vn_mut(vn_collect).set_active_heritage();
        write.push(vn_collect);
        Ok(())
    }

    fn try_output_overlap_guard(
        data: &mut Funcdata,
        glb: &mut Architecture,
        fc: CallSpecId,
        addr: &Address,
        trans_addr: &Address,
        size: i32,
        write: &mut Vec<VarnodeId>,
    ) -> Result<bool> {
        let mut v_data = VarnodeData::default();

        if !data
            .call_spec_mut(fc)
            .get_biggest_contained_output(trans_addr, size, &mut v_data, glb)
        {
            return Ok(false);
        }
        let mut trunc_addr = v_data.get_addr();
        let diff = trunc_addr.get_offset().wrapping_sub(trans_addr.get_offset()) as i32;
        trunc_addr = addr + diff as i64;
        if data
            .call_spec_mut(fc)
            .get_active_output()
            .which_trial(&trunc_addr, size)
            >= 0
        {
            return Ok(false);
        }
        let call_op = data.call_spec(fc).get_op();
        Heritage::guard_output_overlap(data, glb, call_op, addr, size, &trunc_addr, v_data.size as i32, write)?;
        data.call_spec_mut(fc)
            .get_active_output()
            .register_trial(&trunc_addr, v_data.size as i32);
        Ok(true)
    }

    fn try_output_stack_guard(
        data: &mut Funcdata,
        glb: &mut Architecture,
        fc: CallSpecId,
        addr: &Address,
        trans_addr: &Address,
        size: i32,
        output_character: i32,
        write: &mut Vec<VarnodeId>,
    ) -> Result<bool> {
        let call_op = data.call_spec(fc).get_op();
        if output_character == ParamEntry::CONTAINED_BY {
            let mut v_data = VarnodeData::default();

            if !data
                .call_spec_mut(fc)
                .get_biggest_contained_output(trans_addr, size, &mut v_data, glb)
            {
                return Ok(false);
            }
            let mut trunc_addr = v_data.get_addr();
            let diff = trunc_addr.get_offset().wrapping_sub(trans_addr.get_offset()) as i32;
            trunc_addr = addr + diff as i64;
            Heritage::guard_output_overlap_stack(
                data,
                glb,
                call_op,
                addr,
                size,
                &trunc_addr,
                v_data.size as i32,
                write,
            )?;
            return Ok(true);
        }
        let output = data
            .call_spec(fc)
            .get_output_ref()
            .expect("call specification without output");
        let mut ret_addr = output.get_address(glb);
        let ret_size = output.get_size(glb);
        let diff = addr.get_offset().wrapping_sub(trans_addr.get_offset()) as i32;
        ret_addr = &ret_addr + diff as i64;
        let mut outvn = data.op(call_op).get_out();
        let mut vn_final: Option<VarnodeId> = None;
        if outvn.is_none() {
            let created = data.new_varnode_out(ret_size, &ret_addr, call_op, glb)?;
            outvn = Some(created);
            vn_final = Some(created);
        }
        if size < ret_size {
            let call_addr = data.op(call_op).get_addr().clone();
            let sub_piece = data.new_op(2, &call_addr);
            data.op_set_opcode(sub_piece, OpCode::Subpiece, glb);
            let truncate_amount = ret_addr.justified_contain(ret_size, addr, size, false);
            let constant = data.new_constant(4, signed_offset(truncate_amount), glb);
            data.op_set_input(sub_piece, constant, 1)?;
            data.op_set_input(sub_piece, outvn.expect("call output"), 0)?;
            vn_final = Some(data.new_varnode_out(size, addr, sub_piece, glb)?);
            data.op_insert_after(sub_piece, call_op);
        }
        if let Some(vn_final) = vn_final {
            data.vn_mut(vn_final).set_active_heritage();
            write.push(vn_final);
        }
        Ok(true)
    }

    fn guard_output_overlap_stack(
        data: &mut Funcdata,
        glb: &mut Architecture,
        call_op: OpId,
        addr: &Address,
        size: i32,
        ret_addr: &Address,
        ret_size: i32,
        write: &mut Vec<VarnodeId>,
    ) -> Result<()> {
        let size_front = ret_addr.get_offset().wrapping_sub(addr.get_offset()) as i32;
        let size_back = size - ret_size - size_front;
        let mut insert_point = call_op;
        let call_addr = data.op(call_op).get_addr().clone();
        let mut vn_collect = match data.op(call_op).get_out() {
            Some(out) => out,
            None => data.new_varnode_out(ret_size, ret_addr, call_op, glb)?,
        };
        if size_front != 0 {
            let new_input = data.new_varnode(size, addr, None, glb)?;
            data.vn_mut(new_input).set_active_heritage();
            let sub_piece = data.new_op(2, &call_addr);
            data.op_set_opcode(sub_piece, OpCode::Subpiece, glb);
            let truncate_amount = addr.justified_contain(size, addr, size_front, false);
            let constant = data.new_constant(4, signed_offset(truncate_amount), glb);
            data.op_set_input(sub_piece, constant, 1)?;
            data.op_set_input(sub_piece, new_input, 0)?;
            let ind_op_front = data.new_indirect_op(call_op, addr, size_front, 0, glb)?;
            let ind_in = data.op(ind_op_front).get_in(0);
            data.op_set_output(sub_piece, ind_in, glb)?;
            data.op_insert_before(sub_piece, call_op);
            let new_front = out_vn(data, ind_op_front);
            let concat_front = data.new_op(2, &call_addr);
            let slot_new = if ret_addr.is_big_endian() { 0 } else { 1 };
            data.op_set_opcode(concat_front, OpCode::Piece, glb);
            data.op_set_input(concat_front, new_front, slot_new)?;
            data.op_set_input(concat_front, vn_collect, 1 - slot_new)?;
            vn_collect = data.new_varnode_out(size_front + ret_size, addr, concat_front, glb)?;
            data.op_insert_after(concat_front, insert_point);
            insert_point = concat_front;
        }
        if size_back != 0 {
            let new_input = data.new_varnode(size, addr, None, glb)?;
            data.vn_mut(new_input).set_active_heritage();
            let addr_back = ret_addr + ret_size as i64;
            let sub_piece = data.new_op(2, &call_addr);
            data.op_set_opcode(sub_piece, OpCode::Subpiece, glb);
            let truncate_amount = addr.justified_contain(size, &addr_back, size_back, false);
            let constant = data.new_constant(4, signed_offset(truncate_amount), glb);
            data.op_set_input(sub_piece, constant, 1)?;
            data.op_set_input(sub_piece, new_input, 0)?;
            let ind_op_back = data.new_indirect_op(call_op, &addr_back, size_back, 0, glb)?;
            let ind_in = data.op(ind_op_back).get_in(0);
            data.op_set_output(sub_piece, ind_in, glb)?;
            data.op_insert_before(sub_piece, call_op);
            let new_back = out_vn(data, ind_op_back);
            let concat_back = data.new_op(2, &call_addr);
            let slot_new = if ret_addr.is_big_endian() { 1 } else { 0 };
            data.op_set_opcode(concat_back, OpCode::Piece, glb);
            data.op_set_input(concat_back, new_back, slot_new)?;
            data.op_set_input(concat_back, vn_collect, 1 - slot_new)?;
            vn_collect = data.new_varnode_out(size, addr, concat_back, glb)?;
            data.op_insert_after(concat_back, insert_point);
        }
        data.vn_mut(vn_collect).set_active_heritage();
        write.push(vn_collect);
        Ok(())
    }

    fn guard_calls(
        data: &mut Funcdata,
        glb: &mut Architecture,
        fl: u32,
        addr: &Address,
        size: i32,
        write: &mut Vec<VarnodeId>,
    ) -> Result<()> {
        let holdind = (fl & crate::varnode::Varnode::ADDRTIED) != 0;
        for index in 0..data.num_calls() {
            let fc = data.get_call_specs(index);
            let call_op = data.call_spec(fc).get_op();
            if data.op(call_op).is_assignment() {
                let vn = out_vn(data, call_op);
                if data.vn(vn).get_addr() == addr && data.vn(vn).get_size() == size {
                    continue;
                }
            }
            let spc = address_space(addr);
            let mut off = addr.get_offset();
            let mut tryregister = true;
            if spc.get_type() == SpaceType::Spacebase {
                let spacebase_offset = data.call_spec(fc).get_spacebase_offset();
                if spacebase_offset != FuncCallSpecs::OFFSET_UNKNOWN {
                    off = spc.wrap_offset(off.wrapping_sub(spacebase_offset));
                } else {
                    tryregister = false;
                }
            }
            let trans_addr = Address::new(spc.clone(), off);
            let mut effecttype = data.call_spec(fc).has_effect(&trans_addr, size, glb);
            let mut possibleoutput = false;
            if data.call_spec(fc).is_output_active() && tryregister {
                let output_character = data.call_spec_mut(fc).characterize_as_output(&trans_addr, size, glb);
                if output_character != ParamEntry::NO_CONTAINMENT {
                    if effecttype != EffectRecord::KILLEDBYCALL && data.call_spec(fc).is_auto_killed_by_call(glb) {
                        effecttype = EffectRecord::KILLEDBYCALL;
                    }
                    if output_character == ParamEntry::CONTAINED_BY {
                        if Heritage::try_output_overlap_guard(data, glb, fc, addr, &trans_addr, size, write)? {
                            effecttype = EffectRecord::UNAFFECTED;
                        }
                    } else {
                        let active = data.call_spec_mut(fc).get_active_output();
                        if active.which_trial(&trans_addr, size) < 0 {
                            active.register_trial(&trans_addr, size);
                            possibleoutput = true;
                        }
                    }
                }
            } else if data.call_spec(fc).is_stack_output_lock() && tryregister {
                let output_character = data.call_spec_mut(fc).characterize_as_output(&trans_addr, size, glb);
                if output_character != ParamEntry::NO_CONTAINMENT {
                    effecttype = EffectRecord::UNKNOWN_EFFECT;
                    if Heritage::try_output_stack_guard(
                        data,
                        glb,
                        fc,
                        addr,
                        &trans_addr,
                        size,
                        output_character,
                        write,
                    )? {
                        effecttype = EffectRecord::UNAFFECTED;
                    }
                }
            }
            if data.call_spec(fc).is_input_active() && tryregister {
                let input_character = data
                    .call_spec_mut(fc)
                    .characterize_as_input_param(&trans_addr, size, glb);
                if input_character == ParamEntry::CONTAINS_JUSTIFIED {
                    if data.call_spec_mut(fc).get_active_input().which_trial(&trans_addr, size) < 0 {
                        let op = data.call_spec(fc).get_op();
                        data.call_spec_mut(fc)
                            .get_active_input()
                            .register_trial(&trans_addr, size);
                        let vn = data.new_varnode(size, addr, None, glb)?;
                        data.vn_mut(vn).set_active_heritage();
                        let num_input = data.op(op).num_input();
                        data.op_insert_input(op, vn, num_input)?;
                    }
                } else if input_character == ParamEntry::CONTAINED_BY {
                    Heritage::guard_call_overlapping_input(data, glb, fc, addr, &trans_addr, size)?;
                }
            }
            if effecttype == EffectRecord::UNKNOWN_EFFECT || effecttype == EffectRecord::RETURN_ADDRESS {
                let call_op = data.call_spec(fc).get_op();
                let indop = data.new_indirect_op(call_op, addr, size, 0, glb)?;
                let ind_in = data.op(indop).get_in(0);
                data.vn_mut(ind_in).set_active_heritage();
                let ind_out = out_vn(data, indop);
                data.vn_mut(ind_out).set_active_heritage();
                write.push(ind_out);
                if holdind {
                    data.vbank.get_mut(ind_out).set_addr_force(&mut data.highs);
                }
                if effecttype == EffectRecord::RETURN_ADDRESS {
                    data.vn_mut(ind_out).set_return_address();
                }
            } else if effecttype == EffectRecord::KILLEDBYCALL {
                let call_op = data.call_spec(fc).get_op();
                let indop = data.new_indirect_creation(call_op, addr, size, possibleoutput, glb)?;
                let ind_out = out_vn(data, indop);
                data.vn_mut(ind_out).set_active_heritage();
                write.push(ind_out);
            }
        }
        Ok(())
    }

    fn guard_stores(
        data: &mut Funcdata,
        glb: &mut Architecture,
        addr: &Address,
        size: i32,
        write: &mut Vec<VarnodeId>,
    ) -> Result<()> {
        let spc = address_space(addr);
        let container = spc.get_contain();
        let spc_option = Some(spc.clone());

        let mut iter = data.begin_op(OpCode::Store);
        while let Some(op) = iter {
            iter = next_code_op(data, op);
            if data.op(op).is_dead() {
                continue;
            }
            let store_space = data.vn(data.op(op).get_in(0)).get_space_from_const(&glb.manager);
            if (same_space(&container, &store_space) && data.op(op).uses_spacebase_ptr())
                || same_space(&spc_option, &store_space)
            {
                let indop = data.new_indirect_op(op, addr, size, PcodeOp::INDIRECT_STORE, glb)?;
                let ind_in = data.op(indop).get_in(0);
                data.vn_mut(ind_in).set_active_heritage();
                let ind_out = out_vn(data, indop);
                data.vn_mut(ind_out).set_active_heritage();
                write.push(ind_out);
            }
        }
        Ok(())
    }

    fn guard_loads(data: &mut Funcdata, glb: &mut Architecture, fl: u32, addr: &Address, size: i32) -> Result<()> {
        if (fl & crate::varnode::Varnode::ADDRTIED) == 0 {
            return Ok(());
        }
        let mut index = 0;
        while index < data.heritage.load_guard.len() {
            if !data.heritage.load_guard[index].is_valid(OpCode::Load, data) {
                data.heritage.load_guard.remove(index);
                continue;
            }
            let guard_rec = data.heritage.load_guard[index].clone();
            index += 1;
            if !same_space(&guard_rec.spc, &addr.get_space().cloned()) {
                continue;
            }
            if addr.get_offset() < guard_rec.minimum_offset {
                continue;
            }
            if addr.get_offset() > guard_rec.maximum_offset {
                continue;
            }
            let guard_op = guard_rec.op.expect("load guard without op");
            let guard_addr = data.op(guard_op).get_addr().clone();
            let copyop = data.new_op(1, &guard_addr);
            let vn = data.new_varnode_out(size, addr, copyop, glb)?;
            data.vn_mut(vn).set_active_heritage();
            data.vbank.get_mut(vn).set_addr_force(&mut data.highs);
            data.op_set_opcode(copyop, OpCode::Copy, glb);
            let invn = data.new_varnode(size, addr, None, glb)?;
            data.vn_mut(invn).set_active_heritage();
            data.op_set_input(copyop, invn, 0)?;
            data.op_insert_before(copyop, guard_op);
            data.heritage.load_copy_ops.push(copyop);
        }
        Ok(())
    }

    fn guard_returns_overlapping(data: &mut Funcdata, glb: &mut Architecture, addr: &Address, size: i32) -> Result<()> {
        let mut v_data = VarnodeData::default();

        if !data
            .get_func_proto_mut()
            .get_biggest_contained_output(addr, size, &mut v_data, glb)
        {
            return Ok(());
        }
        let trunc_addr = v_data.get_addr();
        data.get_active_output_mut()
            .expect("function without active output")
            .register_trial(&trunc_addr, v_data.size as i32);
        let mut offset = v_data.offset.wrapping_sub(addr.get_offset()) as i32;
        if v_data
            .space
            .as_ref()
            .expect("output storage without space")
            .is_big_endian()
        {
            offset = (size - v_data.size as i32) - offset;
        }
        let mut iter = data.begin_op(OpCode::Return);
        while let Some(op) = iter {
            iter = next_code_op(data, op);
            if data.op(op).is_dead() {
                continue;
            }
            if data.op(op).get_halt_type() != 0 {
                continue;
            }
            let invn = data.new_varnode(size, addr, None, glb)?;
            let op_addr = data.op(op).get_addr().clone();
            let sub_op = data.new_op(2, &op_addr);
            data.op_set_opcode(sub_op, OpCode::Subpiece, glb);
            data.op_set_input(sub_op, invn, 0)?;
            let constant = data.new_constant(4, signed_offset(offset), glb);
            data.op_set_input(sub_op, constant, 1)?;
            data.op_insert_before(sub_op, op);
            let ret_val = data.new_varnode_out(v_data.size as i32, &trunc_addr, sub_op, glb)?;
            data.vn_mut(invn).set_active_heritage();
            let num_input = data.op(op).num_input();
            data.op_insert_input(op, ret_val, num_input)?;
        }
        Ok(())
    }

    fn guard_returns(data: &mut Funcdata, glb: &mut Architecture, fl: u32, addr: &Address, size: i32) -> Result<()> {
        if data.get_active_output().is_some() {
            let output_character = data.get_func_proto_mut().characterize_as_output(addr, size, glb);
            if output_character == ParamEntry::CONTAINED_BY {
                Heritage::guard_returns_overlapping(data, glb, addr, size)?;
            } else if output_character != ParamEntry::NO_CONTAINMENT {
                data.get_active_output_mut()
                    .expect("function without active output")
                    .register_trial(addr, size);
                let mut iter = data.begin_op(OpCode::Return);
                while let Some(op) = iter {
                    iter = next_code_op(data, op);
                    if data.op(op).is_dead() {
                        continue;
                    }
                    if data.op(op).get_halt_type() != 0 {
                        continue;
                    }
                    let invn = data.new_varnode(size, addr, None, glb)?;
                    data.vn_mut(invn).set_active_heritage();
                    let num_input = data.op(op).num_input();
                    data.op_insert_input(op, invn, num_input)?;
                }
            }
        }
        if (fl & crate::varnode::Varnode::PERSIST) == 0 {
            return Ok(());
        }
        let mut iter = data.begin_op(OpCode::Return);
        while let Some(op) = iter {
            iter = next_code_op(data, op);
            if data.op(op).is_dead() {
                continue;
            }
            let op_addr = data.op(op).get_addr().clone();
            let copyop = data.new_op(1, &op_addr);
            let vn = data.new_varnode_out(size, addr, copyop, glb)?;
            data.vbank.get_mut(vn).set_addr_force(&mut data.highs);
            data.vn_mut(vn).set_active_heritage();
            data.op_set_opcode(copyop, OpCode::Copy, glb);
            data.mark_return_copy(copyop);
            let invn = data.new_varnode(size, addr, None, glb)?;
            data.vn_mut(invn).set_active_heritage();
            data.op_set_input(copyop, invn, 0)?;
            data.op_insert_before(copyop, op);
        }
        Ok(())
    }

    fn build_refinement(refine: &mut [i32], addr: &Address, vnlist: &[VarnodeId], data: &Funcdata) {
        for &vn in vnlist {
            let curaddr = data.vn(vn).get_addr();
            let sz = data.vn(vn).get_size();
            let diff = curaddr.get_offset().wrapping_sub(addr.get_offset()) as u32 as usize;
            refine[diff] = 1;
            refine[diff + sz as usize] = 1;
        }
    }

    fn split_by_refinement(
        data: &mut Funcdata,
        glb: &mut Architecture,
        vn: VarnodeId,
        addr: &Address,
        refine: &[i32],
        split: &mut Vec<VarnodeId>,
    ) -> Result<()> {
        let mut curaddr = data.vn(vn).get_addr().clone();
        let mut sz = data.vn(vn).get_size();
        let spc = address_space(&curaddr);
        let mut diff = spc.wrap_offset(curaddr.get_offset().wrapping_sub(addr.get_offset())) as u32;
        let mut cutsz = refine[diff as usize];
        if sz <= cutsz {
            return Ok(());
        }
        split.push(data.new_varnode(cutsz, &curaddr, None, glb)?);
        sz -= cutsz;
        while sz > 0 {
            curaddr = &curaddr + cutsz as i64;
            diff = spc.wrap_offset(curaddr.get_offset().wrapping_sub(addr.get_offset())) as u32;
            cutsz = refine[diff as usize];
            if cutsz > sz {
                cutsz = sz;
            }
            split.push(data.new_varnode(cutsz, &curaddr, None, glb)?);
            sz -= cutsz;
        }
        Ok(())
    }

    fn refine_read(
        data: &mut Funcdata,
        glb: &mut Architecture,
        vn: VarnodeId,
        addr: &Address,
        refine: &[i32],
        newvn: &mut Vec<VarnodeId>,
    ) -> Result<()> {
        newvn.clear();
        Heritage::split_by_refinement(data, glb, vn, addr, refine, newvn)?;
        if newvn.is_empty() {
            return Ok(());
        }
        let vnsize = data.vn(vn).get_size();
        let replacevn = data.new_unique(vnsize, None, glb);
        let op = data
            .vn(vn)
            .lone_descend()
            .expect("free varnode without single descendant");
        let slot = data.op(op).get_slot(vn);
        Heritage::concat_pieces(data, glb, newvn, Some(op), replacevn)?;
        data.op_set_input(op, replacevn, slot)?;
        if data.vn(vn).has_no_descend() {
            data.delete_varnode(vn)?;
        } else {
            return Err(Error::Lowlevel("Refining non-free varnode".to_string()));
        }
        Ok(())
    }

    fn refine_write(
        data: &mut Funcdata,
        glb: &mut Architecture,
        vn: VarnodeId,
        addr: &Address,
        refine: &[i32],
        newvn: &mut Vec<VarnodeId>,
    ) -> Result<()> {
        newvn.clear();
        Heritage::split_by_refinement(data, glb, vn, addr, refine, newvn)?;
        if newvn.is_empty() {
            return Ok(());
        }
        let vnsize = data.vn(vn).get_size();
        let vnaddr = data.vn(vn).get_addr().clone();
        let replacevn = data.new_unique(vnsize, None, glb);
        let def = def_op(data, vn);
        data.op_set_output(def, replacevn, glb)?;
        Heritage::split_pieces(data, glb, newvn, Some(def), &vnaddr, vnsize, replacevn)?;
        data.total_replace(vn, replacevn)?;
        data.delete_varnode(vn)?;
        Ok(())
    }

    fn refine_input(
        data: &mut Funcdata,
        glb: &mut Architecture,
        vn: VarnodeId,
        addr: &Address,
        refine: &[i32],
        newvn: &mut Vec<VarnodeId>,
    ) -> Result<()> {
        newvn.clear();
        Heritage::split_by_refinement(data, glb, vn, addr, refine, newvn)?;
        if newvn.is_empty() {
            return Ok(());
        }
        let vnaddr = data.vn(vn).get_addr().clone();
        let vnsize = data.vn(vn).get_size();
        Heritage::split_pieces(data, glb, newvn, None, &vnaddr, vnsize, vn)?;
        data.vn_mut(vn).set_write_mask();
        Ok(())
    }

    fn remove13_refinement(refine: &mut [i32]) {
        if refine.is_empty() {
            return;
        }
        let mut pos: i32 = 0;
        let mut lastsize = refine[pos as usize];
        pos += lastsize;
        while (pos as usize) < refine.len() {
            let cursize = refine[pos as usize];
            if cursize == 0 {
                break;
            }
            if (lastsize == 1 && cursize == 3) || (lastsize == 3 && cursize == 1) {
                refine[(pos - lastsize) as usize] = 4;
                lastsize = 4;
                pos += cursize;
            } else {
                lastsize = cursize;
                pos += lastsize;
            }
        }
    }

    fn refinement(
        data: &mut Funcdata,
        glb: &mut Architecture,
        memiter: usize,
        readvars: &[VarnodeId],
        writevars: &[VarnodeId],
        inputvars: &[VarnodeId],
    ) -> Result<Option<usize>> {
        let size = data.heritage.disjoint.get(memiter).size;
        if size > 1024 {
            return Ok(None);
        }
        let mut addr = data.heritage.disjoint.get(memiter).addr.clone();
        let mut refine: Vec<i32> = vec![0; (size + 1) as usize];
        Heritage::build_refinement(&mut refine, &addr, readvars, data);
        Heritage::build_refinement(&mut refine, &addr, writevars, data);
        Heritage::build_refinement(&mut refine, &addr, inputvars, data);
        refine.pop();
        let mut lastpos = 0;
        for curpos in 1..size {
            if refine[curpos as usize] != 0 {
                refine[lastpos as usize] = curpos - lastpos;
                lastpos = curpos;
            }
        }
        if lastpos == 0 {
            return Ok(None);
        }
        refine[lastpos as usize] = size - lastpos;
        Heritage::remove13_refinement(&mut refine);
        let mut newvn: Vec<VarnodeId> = Vec::new();
        for &vn in readvars {
            Heritage::refine_read(data, glb, vn, &addr, &refine, &mut newvn)?;
        }
        for &vn in writevars {
            Heritage::refine_write(data, glb, vn, &addr, &refine, &mut newvn)?;
        }
        for &vn in inputvars {
            Heritage::refine_input(data, glb, vn, &addr, &refine, &mut newvn)?;
        }

        let heritage = &mut data.heritage;
        let flags = heritage.disjoint.get(memiter).flags;
        let mut insert_pos = heritage.disjoint.erase(memiter);
        let iter = heritage
            .globaldisjoint
            .find(&addr)
            .expect("refined range missing from global disjoint cover");
        let cur_pass = heritage.globaldisjoint.get(&iter).pass;
        heritage.globaldisjoint.erase(&iter);
        let mut cut = 0;
        let mut sz = refine[cut as usize];
        let mut intersect = 0;
        let resiter = heritage.disjoint.insert(insert_pos, addr.clone(), sz, flags);
        insert_pos += 1;
        heritage.globaldisjoint.add(addr.clone(), sz, cur_pass, &mut intersect);
        cut += sz;
        addr = &addr + sz as i64;
        while cut < size {
            sz = refine[cut as usize];
            heritage.disjoint.insert(insert_pos, addr.clone(), sz, flags);
            insert_pos += 1;
            heritage.globaldisjoint.add(addr.clone(), sz, cur_pass, &mut intersect);
            cut += sz;
            addr = &addr + sz as i64;
        }
        Ok(Some(resiter))
    }

    fn visit_incr(data: &mut Funcdata, qnode: BlockId, vnode: BlockId) {
        let vindex = data.block(vnode).get_index() as usize;
        let qindex = data.block(qnode).get_index();
        let augment = data.heritage.augment[vindex].clone();
        for vblock in augment {
            let idom = data
                .block(vblock)
                .get_immed_dom()
                .expect("block without immediate dominator");
            if data.block(idom).get_index() < qindex {
                let kindex = data.block(vblock).get_index() as usize;
                let heritage = &mut data.heritage;
                if (heritage.flags[kindex] & Heritage::MERGED_NODE) == 0 {
                    heritage.merge.push(vblock);
                    heritage.flags[kindex] |= Heritage::MERGED_NODE;
                }
                if (heritage.flags[kindex] & Heritage::MARK_NODE) == 0 {
                    heritage.flags[kindex] |= Heritage::MARK_NODE;
                    let depth = heritage.depth[kindex];
                    heritage.pq.insert(vblock, depth);
                }
            } else {
                break;
            }
        }
        if (data.heritage.flags[vindex] & Heritage::BOUNDARY_NODE) == 0 {
            let children = data.heritage.domchild[vindex].clone();
            for child in children {
                let child_index = data.block(child).get_index() as usize;
                if (data.heritage.flags[child_index] & Heritage::MARK_NODE) == 0 {
                    Heritage::visit_incr(data, qnode, child);
                }
            }
        }
    }

    fn calc_multiequals(data: &mut Funcdata, write: &[VarnodeId]) {
        let maxdepth = data.heritage.maxdepth;
        data.heritage.pq.reset(maxdepth);
        data.heritage.merge.clear();

        for &vn in write {
            let bl = data.op(def_op(data, vn)).get_parent().expect("op without parent block");
            let index = data.block(bl).get_index() as usize;
            let heritage = &mut data.heritage;
            if (heritage.flags[index] & Heritage::MARK_NODE) != 0 {
                continue;
            }
            let depth = heritage.depth[index];
            heritage.pq.insert(bl, depth);
            heritage.flags[index] |= Heritage::MARK_NODE;
        }
        if (data.heritage.flags[0] & Heritage::MARK_NODE) == 0 {
            let start = data.block(data.bblocks).get_block(0);
            let heritage = &mut data.heritage;
            let depth = heritage.depth[0];
            heritage.pq.insert(start, depth);
            heritage.flags[0] |= Heritage::MARK_NODE;
        }

        while !data.heritage.pq.empty() {
            let bl = data.heritage.pq.extract();
            Heritage::visit_incr(data, bl, bl);
        }
        for flag in data.heritage.flags.iter_mut() {
            *flag &= !(Heritage::MARK_NODE | Heritage::MERGED_NODE);
        }
    }

    fn rename_recurse(
        data: &mut Funcdata,
        glb: &mut Architecture,
        bl: BlockId,
        varstack: &mut VariableStack,
    ) -> Result<()> {
        let mut writelist: Vec<VarnodeId> = Vec::new();

        let mut oiter = data.block(bl).get_op_list().front();
        while let Some(op) = oiter {
            if data.op(op).code() != OpCode::Multiequal {
                let mut slot = 0;
                while slot < data.op(op).num_input() {
                    let vnin = data.op(op).get_in(slot);
                    if data.vn(vnin).is_heritage_known() || !data.vn(vnin).is_active_heritage() {
                        slot += 1;
                        continue;
                    }
                    data.vn_mut(vnin).clear_active_heritage();
                    let vnin_addr = data.vn(vnin).get_addr().clone();
                    let vnin_size = data.vn(vnin).get_size();
                    let stack = varstack.entry(vnin_addr.ordering_key()).or_default();
                    let mut vnnew = match stack.last() {
                        Some(top) => *top,
                        None => {
                            let created = data.new_varnode(vnin_size, &vnin_addr, None, glb)?;
                            let input = data.set_input_varnode(created, glb)?;
                            stack.push(input);
                            input
                        }
                    };
                    if data.vn(vnnew).is_written() {
                        let newdef = def_op(data, vnnew);
                        if data.op(newdef).code() == OpCode::Indirect {
                            let iop_vn = data.op(newdef).get_in(1);
                            if PcodeOp::get_op_from_const(data.vn(iop_vn).get_addr()) == op {
                                let stack = varstack.get_mut(&vnin_addr.ordering_key()).expect("variable stack");
                                if stack.len() == 1 {
                                    vnnew = data.new_varnode(vnin_size, &vnin_addr, None, glb)?;
                                    vnnew = data.set_input_varnode(vnnew, glb)?;
                                    stack.insert(0, vnnew);
                                } else {
                                    vnnew = stack[stack.len() - 2];
                                }
                            }
                        }
                    }
                    data.op_set_input(op, vnnew, slot)?;
                    if data.vn(vnin).has_no_descend() {
                        data.delete_varnode(vnin)?;
                    }
                    slot += 1;
                }
            }
            if let Some(vnout) = data.op(op).get_out()
                && data.vn(vnout).is_active_heritage()
            {
                data.vn_mut(vnout).clear_active_heritage();
                let vnout_key = data.vn(vnout).get_addr().ordering_key();
                varstack.entry(vnout_key).or_default().push(vnout);
                writelist.push(vnout);
            }
            oiter = next_basic_op(data, op);
        }
        let size_out = data.block(bl).size_out();
        for index in 0..size_out {
            let subbl = data.block(bl).get_out(index);
            let slot = data.block(bl).get_out_rev_index(index);
            let mut suboiter = data.block(subbl).get_op_list().front();
            while let Some(multiop) = suboiter {
                if data.op(multiop).code() != OpCode::Multiequal {
                    break;
                }
                let vnin = data.op(multiop).get_in(slot);
                if !data.vn(vnin).is_heritage_known() {
                    let vnin_addr = data.vn(vnin).get_addr().clone();
                    let vnin_size = data.vn(vnin).get_size();
                    let stack = varstack.entry(vnin_addr.ordering_key()).or_default();
                    let vnnew = match stack.last() {
                        Some(top) => *top,
                        None => {
                            let created = data.new_varnode(vnin_size, &vnin_addr, None, glb)?;
                            let input = data.set_input_varnode(created, glb)?;
                            stack.push(input);
                            input
                        }
                    };
                    data.op_set_input(multiop, vnnew, slot)?;
                    if data.vn(vnin).has_no_descend() {
                        data.delete_varnode(vnin)?;
                    }
                }
                suboiter = next_basic_op(data, multiop);
            }
        }
        let index = data.block(bl).get_index() as usize;
        let children = data.heritage.domchild[index].clone();
        for child in children {
            Heritage::rename_recurse(data, glb, child, varstack)?;
        }
        for &vnout in writelist.iter() {
            let vnout_key = data.vn(vnout).get_addr().ordering_key();
            varstack.entry(vnout_key).or_default().pop();
        }
        Ok(())
    }

    fn bump_deadcode_delay(data: &mut Funcdata, spc: &SpaceRef) {
        if spc.get_type() != SpaceType::Processor && spc.get_type() != SpaceType::Spacebase {
            return;
        }
        if spc.get_delay() != spc.get_deadcode_delay() {
            return;
        }
        if data.get_override().has_deadcode_delay(spc) {
            return;
        }
        data.get_override()
            .insert_deadcode_delay(spc, spc.get_deadcode_delay() + 1);
        data.set_restart_pending(true);
    }

    fn place_multiequals(data: &mut Funcdata, glb: &mut Architecture) -> Result<()> {
        let mut readvars: Vec<VarnodeId> = Vec::new();
        let mut writevars: Vec<VarnodeId> = Vec::new();
        let mut inputvars: Vec<VarnodeId> = Vec::new();
        let mut removevars: Vec<VarnodeId> = Vec::new();

        let mut next_index = 0;
        while next_index < data.heritage.disjoint.end() {
            let mut current = next_index;
            next_index += 1;
            let mut memrange = data.heritage.disjoint.get(current).clone();
            let max = Heritage::collect(
                data,
                glb,
                &mut memrange,
                &mut readvars,
                &mut writevars,
                &mut inputvars,
                &mut removevars,
            );
            *data.heritage.disjoint.get_mut(current) = memrange.clone();
            if memrange.size > 4
                && max < memrange.size
                && let Some(refiter) = Heritage::refinement(data, glb, current, &readvars, &writevars, &inputvars)?
            {
                current = refiter;
                next_index = refiter + 1;
                let mut refined = data.heritage.disjoint.get(current).clone();
                Heritage::collect(
                    data,
                    glb,
                    &mut refined,
                    &mut readvars,
                    &mut writevars,
                    &mut inputvars,
                    &mut removevars,
                );
                *data.heritage.disjoint.get_mut(current) = refined;
            }
            let memrange = data.heritage.disjoint.get(current).clone();
            let size = memrange.size;
            if readvars.is_empty() {
                if writevars.is_empty() && inputvars.is_empty() {
                    continue;
                }
                if space_type_of(memrange.addr.get_space()) == Some(SpaceType::Internal) || memrange.old_addresses() {
                    continue;
                }
            }
            if !removevars.is_empty() {
                Heritage::remove_revisited_markers(data, glb, &removevars, &memrange.addr, size)?;
            }
            Heritage::guard_input(data, glb, &memrange.addr, size, &mut inputvars)?;
            Heritage::guard(
                data,
                glb,
                &memrange.addr,
                size,
                memrange.new_addresses(),
                &mut readvars,
                &mut writevars,
            )?;
            Heritage::calc_multiequals(data, &writevars);
            let merge = data.heritage.merge.clone();
            for bl in merge {
                let size_in = data.block(bl).size_in();
                let start = data.block(bl).get_start();
                let multiop = data.new_op(size_in, &start);
                let vnout = data.new_varnode_out(size, &memrange.addr, multiop, glb)?;
                data.vn_mut(vnout).set_active_heritage();
                data.op_set_opcode(multiop, OpCode::Multiequal, glb);
                for slot in 0..size_in {
                    let vnin = data.new_varnode(size, &memrange.addr, None, glb)?;
                    data.op_set_input(multiop, vnin, slot)?;
                }
                data.op_insert_begin(multiop, bl);
            }
        }
        data.heritage.merge.clear();
        Ok(())
    }

    fn rename(data: &mut Funcdata, glb: &mut Architecture) -> Result<()> {
        let mut varstack = VariableStack::new();
        let start = data.block(data.bblocks).get_block(0);
        Heritage::rename_recurse(data, glb, start, &mut varstack)?;
        data.heritage.disjoint.clear();
        Ok(())
    }

    pub fn get_pass(&self) -> i32 {
        self.pass
    }

    pub fn heritage_pass(&self, addr: &Address) -> i32 {
        self.globaldisjoint.find_pass(addr)
    }

    pub fn num_heritage_passes(&self, spc: &SpaceRef) -> Result<i32> {
        let info = self.get_info(spc);
        if !info.is_heritaged() {
            return Err(Error::Lowlevel(
                "Trying to calculate passes for non-heritaged space".to_string(),
            ));
        }
        Ok(self.pass - info.delay)
    }

    pub fn seen_dead_code(&mut self, spc: &SpaceRef) {
        self.get_info_mut(spc).deadremoved = 1;
    }

    pub fn get_dead_code_delay(&self, spc: &SpaceRef) -> i32 {
        self.get_info(spc).deadcodedelay
    }

    pub fn set_dead_code_delay(&mut self, spc: &SpaceRef, delay: i32) -> Result<()> {
        let info = self.get_info_mut(spc);
        if delay < info.delay {
            return Err(Error::Lowlevel("Illegal deadcode delay setting".to_string()));
        }
        info.deadcodedelay = delay;
        Ok(())
    }

    pub fn dead_removal_allowed(&self, spc: &SpaceRef) -> bool {
        self.pass > self.get_info(spc).deadcodedelay
    }

    pub fn dead_removal_allowed_seen(&mut self, spc: &SpaceRef) -> bool {
        let pass = self.pass;
        let info = self.get_info_mut(spc);
        let res = pass > info.deadcodedelay;
        if res {
            info.deadremoved = 1;
        }
        res
    }

    pub fn mark_range_heritaged(&mut self, addr: &Address, sz: i32) {
        let mut intersect = 0;
        if self.pass > 0 {
            self.globaldisjoint.add(addr.clone(), sz, self.pass - 1, &mut intersect);
        }
    }

    pub fn build_info_list(data: &mut Funcdata, glb: &Architecture) {
        let heritage = &mut data.heritage;
        if !heritage.infolist.is_empty() {
            return;
        }
        let num_spaces = glb.manager.num_spaces();
        heritage.infolist.reserve(num_spaces as usize);
        for index in 0..num_spaces {
            heritage.infolist.push(HeritageInfo::new(glb.manager.get_space(index)));
        }
    }

    pub fn force_restructure(&mut self) {
        self.maxdepth = -1;
    }

    pub fn clear(&mut self) {
        self.disjoint.clear();
        self.globaldisjoint.clear();
        self.domchild.clear();
        self.augment.clear();
        self.flags.clear();
        self.depth.clear();
        self.merge.clear();
        self.clear_info_list();
        self.load_guard.clear();
        self.store_guard.clear();
        self.maxdepth = -1;
        self.pass = 0;
    }

    pub fn heritage(data: &mut Funcdata, glb: &mut Architecture) -> Result<()> {
        let mut warnvn: Option<VarnodeId> = None;
        let mut reprocess_stack_count = 0;
        let mut stack_space: Option<SpaceRef> = None;
        let mut free_stores: Vec<OpId> = Vec::new();
        let mut splitmanage = PreferSplitManager::default();

        if data.heritage.maxdepth == -1 {
            Heritage::build_adt(data);
        }

        Heritage::process_joins(data, glb)?;
        if data.heritage.pass == 0 {
            splitmanage.init();
            splitmanage.split(data, glb)?;
        }
        for index in 0..data.heritage.infolist.len() {
            let info = data.heritage.infolist[index].clone();
            if !info.is_heritaged() {
                continue;
            }
            if data.heritage.pass < info.delay {
                continue;
            }
            let space = info.space.clone().expect("heritaged info without space");
            if info.has_call_placeholders {
                Heritage::clear_stack_placeholders(data, glb, &space)?;
            }

            if !data.heritage.infolist[index].load_guard_search {
                data.heritage.infolist[index].load_guard_search = true;
                if Heritage::discover_indexed_stack_pointers(data, &space, &mut free_stores, true)? {
                    reprocess_stack_count += 1;
                    stack_space = Some(space.clone());
                }
            }
            let mut needwarning = false;
            let begin = data.begin_loc_space(&space);
            let end = data.end_loc_space(&space, glb);
            let varnodes = data.vbank.loc_range(&begin, &end);

            for vn in varnodes {
                let varnode = data.vn(vn);
                if !varnode.is_written() && varnode.has_no_descend() && !varnode.is_unaffected() && !varnode.is_input()
                {
                    continue;
                }
                if varnode.is_write_mask() {
                    continue;
                }
                let vn_addr = varnode.get_addr().clone();
                let vn_size = varnode.get_size();
                let mut prev = 0;
                let pass = data.heritage.pass;
                let liter = data.heritage.globaldisjoint.add(vn_addr, vn_size, pass, &mut prev);
                let range_size = data.heritage.globaldisjoint.get(&liter).size;
                if prev == 0 {
                    data.heritage.disjoint.add(liter, range_size, MemRange::NEW_ADDRESSES);
                } else if prev == 2 {
                    if data.vn(vn).is_heritage_known() {
                        continue;
                    }
                    if data.vn(vn).has_no_descend() {
                        continue;
                    }
                    if !needwarning && data.heritage.infolist[index].deadremoved > 0 && !data.is_jumptable_recovery_on()
                    {
                        needwarning = true;
                        let vn_space = data.vn(vn).get_space().expect("varnode without space").clone();
                        Heritage::bump_deadcode_delay(data, &vn_space);
                        warnvn = Some(vn);
                    }
                    data.heritage.disjoint.add(liter, range_size, MemRange::OLD_ADDRESSES);
                } else {
                    data.heritage
                        .disjoint
                        .add(liter, range_size, MemRange::OLD_ADDRESSES | MemRange::NEW_ADDRESSES);
                    if !needwarning && data.heritage.infolist[index].deadremoved > 0 && !data.is_jumptable_recovery_on()
                    {
                        if data.vn(vn).is_heritage_known() {
                            continue;
                        }
                        needwarning = true;
                        let vn_space = data.vn(vn).get_space().expect("varnode without space").clone();
                        Heritage::bump_deadcode_delay(data, &vn_space);
                        warnvn = Some(vn);
                    }
                }
            }

            if needwarning && !data.heritage.infolist[index].warningissued {
                data.heritage.infolist[index].warningissued = true;
                let warn = warnvn.expect("warning varnode");
                let mut errmsg = String::from("Heritage AFTER dead removal. Example location: ");
                {
                    let trans = glb.translate.as_deref().expect("translator is not initialized");
                    data.vn(warn).print_raw_no_markup(&mut errmsg, trans, data);
                }
                if !data.vn(warn).has_no_descend() {
                    let warnop = data.vn(warn).descend()[0];
                    errmsg.push_str(" : ");
                    data.op(warnop).get_addr().print_raw(&mut errmsg);
                }
                data.warning_header(&errmsg, glb);
            }
        }
        if !data.heritage.disjoint.empty() {
            Heritage::place_multiequals(data, glb)?;
            Heritage::rename(data, glb)?;
        }
        if reprocess_stack_count > 0 {
            let stack_space = stack_space.expect("stack space for free stores");
            Heritage::reprocess_free_stores(data, &stack_space, &mut free_stores)?;
        }
        Heritage::analyze_new_load_guards(data, glb)?;
        Heritage::handle_new_load_copies(data)?;
        if data.heritage.pass == 0 {
            splitmanage.split_additional(data, glb)?;
        }
        data.heritage.pass += 1;
        Ok(())
    }

    pub fn get_load_guards(&self) -> &[LoadGuard] {
        &self.load_guard
    }

    pub fn get_store_guards(&self) -> &[LoadGuard] {
        &self.store_guard
    }

    pub fn get_store_guard(&self, op: OpId) -> Option<&LoadGuard> {
        self.store_guard.iter().find(|guard| guard.op == Some(op))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::space::AddrSpace;

    fn ram() -> SpaceRef {
        Arc::new(AddrSpace::new_processor("ram", false, 4, 1, 3, 0, 0, 0))
    }

    fn at(spc: &SpaceRef, offset: u64) -> Address {
        Address::new(spc.clone(), offset)
    }

    #[test]
    fn location_map_merges_and_reports_intersections() {
        let spc = ram();
        let mut map = LocationMap::new();
        let mut intersect = -1;
        let key = map.add(at(&spc, 0x10), 4, 0, &mut intersect);
        assert_eq!(key, at(&spc, 0x10));
        assert_eq!(intersect, 0);

        let key = map.add(at(&spc, 0x12), 2, 1, &mut intersect);
        assert_eq!(key, at(&spc, 0x10));
        assert_eq!(intersect, 2);

        let key = map.add(at(&spc, 0x12), 4, 1, &mut intersect);
        assert_eq!(key, at(&spc, 0x10));
        assert_eq!(intersect, 1);
        assert_eq!(*map.get(&key), SizePass { size: 6, pass: 0 });

        map.add(at(&spc, 0x20), 4, 1, &mut intersect);
        let key = map.add(at(&spc, 0x18), 0x10, 1, &mut intersect);
        assert_eq!(key, at(&spc, 0x18));
        assert_eq!(intersect, 0);
        assert_eq!(*map.get(&key), SizePass { size: 0x10, pass: 1 });
        assert_eq!(map.iter().count(), 2);

        assert_eq!(map.find(&at(&spc, 0x21)), Some(at(&spc, 0x18)));
        assert_eq!(map.find(&at(&spc, 0x0f)), None);
        assert_eq!(map.find_pass(&at(&spc, 0x15)), 0);
        assert_eq!(map.find_pass(&at(&spc, 0x16)), -1);
        assert_eq!(map.find_pass(&at(&spc, 0x27)), 1);
        assert_eq!(map.find_pass(&at(&spc, 0x28)), -1);
    }

    #[test]
    fn location_map_absorbs_following_ranges_with_older_pass() {
        let spc = ram();
        let mut map = LocationMap::new();
        let mut intersect = 0;
        map.add(at(&spc, 0x0f0), 4, 1, &mut intersect);
        map.add(at(&spc, 0x104), 4, 0, &mut intersect);
        map.add(at(&spc, 0x10c), 8, 2, &mut intersect);
        let key = map.add(at(&spc, 0x100), 0x10, 3, &mut intersect);
        assert_eq!(key, at(&spc, 0x100));
        assert_eq!(intersect, 1);
        assert_eq!(*map.get(&key), SizePass { size: 0x14, pass: 0 });
        assert_eq!(map.iter().count(), 2);
    }

    #[test]
    fn location_map_skips_first_entry_without_predecessor() {
        let spc = ram();
        let mut map = LocationMap::new();
        let mut intersect = 0;
        map.add(at(&spc, 0x104), 4, 0, &mut intersect);
        map.add(at(&spc, 0x10c), 8, 2, &mut intersect);
        let key = map.add(at(&spc, 0x100), 0x10, 3, &mut intersect);
        assert_eq!(key, at(&spc, 0x100));
        assert_eq!(intersect, 1);
        assert_eq!(*map.get(&key), SizePass { size: 0x14, pass: 2 });
        assert_eq!(*map.get(&at(&spc, 0x104)), SizePass { size: 4, pass: 0 });
        assert_eq!(map.iter().count(), 2);
    }

    #[test]
    fn task_list_extends_last_range() {
        let spc = ram();
        let mut list = TaskList::new();
        list.add(at(&spc, 0x10), 4, MemRange::NEW_ADDRESSES);
        list.add(at(&spc, 0x12), 4, MemRange::OLD_ADDRESSES);
        list.add(at(&spc, 0x13), 1, 0);
        assert_eq!(list.end(), 1);
        assert_eq!(list.get(0).size, 6);
        assert!(list.get(0).new_addresses() && list.get(0).old_addresses());
        list.add(at(&spc, 0x16), 2, 0);
        assert_eq!(list.end(), 2);
        let pos = list.insert(1, at(&spc, 0x20), 2, MemRange::OLD_ADDRESSES);
        assert_eq!(pos, 1);
        assert_eq!(list.get(1).addr, at(&spc, 0x20));
        assert_eq!(list.get(2).addr, at(&spc, 0x16));
        assert_eq!(list.erase(1), 1);
        assert_eq!(list.get(1).addr, at(&spc, 0x16));
    }

    #[test]
    fn priority_queue_extracts_deepest_last_in_first() {
        let mut queue = PriorityQueue::new();
        queue.reset(3);
        assert!(queue.empty());
        queue.insert(BlockId(1), 1);
        queue.insert(BlockId(2), 3);
        queue.insert(BlockId(3), 3);
        queue.insert(BlockId(4), 0);
        assert_eq!(queue.extract(), BlockId(3));
        assert_eq!(queue.extract(), BlockId(2));
        assert_eq!(queue.extract(), BlockId(1));
        assert!(!queue.empty());
        assert_eq!(queue.extract(), BlockId(4));
        assert!(queue.empty());
    }

    #[test]
    fn remove13_refinement_merges_one_three_pairs() {
        let mut refine = vec![1, 3, 0, 0, 4, 0, 0, 0, 3, 0, 0, 1];
        Heritage::remove13_refinement(&mut refine);
        assert_eq!(refine, vec![4, 3, 0, 0, 4, 0, 0, 0, 4, 0, 0, 1]);
        let mut refine = vec![2, 0, 2, 0];
        Heritage::remove13_refinement(&mut refine);
        assert_eq!(refine, vec![2, 0, 2, 0]);
    }
}
