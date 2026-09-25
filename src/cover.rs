use crate::stdsort::std_sort;
use std::collections::BTreeMap;
use std::fmt::Write;

use crate::block::BlockId;
use crate::funcdata::Funcdata;
use crate::op::{OpId, PcodeOp};
use crate::opcodes::OpCode;
use crate::varnode::VarnodeId;

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub enum CoverPoint {
    Begin,
    End,
    Input,
    Op(OpId),
}

#[derive(Clone, Debug, Default)]
pub struct PcodeOpSetBase {
    pub op_list: Vec<OpId>,
    pub block_start: Vec<i32>,
    pub is_pop: bool,
}

impl PcodeOpSetBase {
    pub fn new() -> PcodeOpSetBase {
        PcodeOpSetBase {
            op_list: Vec::new(),
            block_start: Vec::new(),
            is_pop: false,
        }
    }
}

pub trait PcodeOpSet {
    fn base(&self) -> &PcodeOpSetBase;

    fn base_mut(&mut self) -> &mut PcodeOpSetBase;

    fn populate(&mut self, data: &Funcdata);

    fn affects_test(&self, op: OpId, vn: VarnodeId, data: &Funcdata) -> bool;

    fn add_op(&mut self, op: OpId) {
        self.base_mut().op_list.push(op);
    }

    fn finalize(&mut self, data: &Funcdata) {
        let base = self.base_mut();
        std_sort(&mut base.op_list, |first, second| {
            pcode_op_set_compare_by_block(*first, *second, data)
        });
        let mut block_num = -1;
        for index in 0..base.op_list.len() {
            let new_block_num = op_block_index(data, base.op_list[index]);
            if new_block_num > block_num {
                base.block_start.push(index as i32);
                block_num = new_block_num;
            }
        }
        base.is_pop = true;
    }

    fn is_populated(&self) -> bool {
        self.base().is_pop
    }

    fn clear(&mut self) {
        let base = self.base_mut();
        base.is_pop = false;
        base.op_list.clear();
        base.block_start.clear();
    }
}

pub fn pcode_op_set_compare_by_block(first: OpId, second: OpId, data: &Funcdata) -> bool {
    let first_op = data.op(first);
    let second_op = data.op(second);
    if first_op.get_parent() != second_op.get_parent() {
        return op_block_index(data, first) < op_block_index(data, second);
    }
    first_op.get_seq_num().get_order() < second_op.get_seq_num().get_order()
}

fn op_block_index(data: &Funcdata, op: OpId) -> i32 {
    let parent = data.op(op).get_parent().expect("p-code op has no parent block");
    data.block(parent).get_index()
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct CoverBlock {
    start: CoverPoint,
    stop: CoverPoint,
}

impl Default for CoverBlock {
    fn default() -> CoverBlock {
        CoverBlock::new()
    }
}

impl CoverBlock {
    pub const fn new() -> CoverBlock {
        CoverBlock {
            start: CoverPoint::Begin,
            stop: CoverPoint::Begin,
        }
    }

    pub fn get_u_index(op: CoverPoint, data: &Funcdata) -> u32 {
        let op = match op {
            CoverPoint::Begin => return 0,
            CoverPoint::End => return u32::MAX,
            CoverPoint::Input => return 0,
            CoverPoint::Op(op) => op,
        };
        let pcode_op = data.op(op);
        if pcode_op.is_marker() {
            if pcode_op.code() == OpCode::Multiequal {
                return 0;
            } else if pcode_op.code() == OpCode::Indirect {
                let iop = PcodeOp::get_op_from_const(data.vn(pcode_op.get_in(1)).get_addr());
                return data.op(iop).get_seq_num().get_order();
            }
        }
        pcode_op.get_seq_num().get_order()
    }

    pub fn get_start(&self) -> CoverPoint {
        self.start
    }

    pub fn get_stop(&self) -> CoverPoint {
        self.stop
    }

    pub fn clear(&mut self) {
        self.start = CoverPoint::Begin;
        self.stop = CoverPoint::Begin;
    }

    pub fn set_all(&mut self) {
        self.start = CoverPoint::Begin;
        self.stop = CoverPoint::End;
    }

    pub fn set_begin(&mut self, begin: CoverPoint) {
        self.start = begin;
        if self.stop == CoverPoint::Begin {
            self.stop = CoverPoint::End;
        }
    }

    pub fn set_end(&mut self, end: CoverPoint) {
        self.stop = end;
    }

    pub fn intersect(&self, op2: &CoverBlock, data: &Funcdata) -> i32 {
        if self.empty() {
            return 0;
        }
        if op2.empty() {
            return 0;
        }
        let ustart = CoverBlock::get_u_index(self.start, data);
        let ustop = CoverBlock::get_u_index(self.stop, data);
        let u2start = CoverBlock::get_u_index(op2.start, data);
        let u2stop = CoverBlock::get_u_index(op2.stop, data);
        CoverBlock::intersect_indices(ustart, ustop, u2start, u2stop)
    }

    fn intersect_indices(ustart: u32, ustop: u32, u2start: u32, u2stop: u32) -> i32 {
        if ustart <= ustop {
            if u2start <= u2stop {
                if ustop <= u2start || u2stop <= ustart {
                    if ustart == u2stop || ustop == u2start {
                        return 1;
                    } else {
                        return 0;
                    }
                }
            } else if ustart >= u2stop && ustop <= u2start {
                if ustart == u2stop || ustop == u2start {
                    return 1;
                } else {
                    return 0;
                }
            }
        } else if u2start <= u2stop && u2start >= ustop && u2stop <= ustart {
            if u2start == ustop || u2stop == ustart {
                return 1;
            } else {
                return 0;
            }
        }
        2
    }

    pub fn empty(&self) -> bool {
        self.start == CoverPoint::Begin && self.stop == CoverPoint::Begin
    }

    pub fn contain(&self, point: CoverPoint, data: &Funcdata) -> bool {
        if self.empty() {
            return false;
        }
        let upoint = CoverBlock::get_u_index(point, data);
        let ustart = CoverBlock::get_u_index(self.start, data);
        let ustop = CoverBlock::get_u_index(self.stop, data);
        if ustart <= ustop {
            return upoint >= ustart && upoint <= ustop;
        }
        upoint <= ustop || upoint >= ustart
    }

    pub fn boundary(&self, point: CoverPoint, data: &Funcdata) -> i32 {
        if self.empty() {
            return 0;
        }
        let val = CoverBlock::get_u_index(point, data);
        if CoverBlock::get_u_index(self.start, data) == val && self.start != CoverPoint::Begin {
            return 2;
        }
        if CoverBlock::get_u_index(self.stop, data) == val {
            return 1;
        }
        0
    }

    pub fn merge(&mut self, op2: &CoverBlock, data: &Funcdata) {
        if op2.empty() {
            return;
        }
        if self.empty() {
            self.start = op2.start;
            self.stop = op2.stop;
            return;
        }
        let ustart = CoverBlock::get_u_index(self.start, data);
        let u2start = CoverBlock::get_u_index(op2.start, data);
        let internal4 = ustart == 0 && op2.stop == CoverPoint::End;
        let internal1 = internal4 || op2.contain(self.start, data);
        let internal3 = u2start == 0 && self.stop == CoverPoint::End;
        let internal2 = internal3 || self.contain(op2.start, data);
        if internal1 && internal2 && (ustart != u2start || internal3 || internal4) {
            self.set_all();
            return;
        }
        if internal1 {
            self.start = op2.start;
        } else if !internal2 {
            if ustart < u2start {
                self.stop = op2.stop;
            } else {
                self.start = op2.start;
            }
            return;
        }
        if internal3 || op2.contain(self.stop, data) {
            self.stop = op2.stop;
        }
    }

    pub fn print(&self, out: &mut String, data: &Funcdata) {
        if self.empty() {
            out.push_str("empty");
            return;
        }
        let ustart = CoverBlock::get_u_index(self.start, data);
        let ustop = CoverBlock::get_u_index(self.stop, data);
        CoverBlock::print_point(out, self.start, ustart, data);
        out.push('-');
        CoverBlock::print_point(out, self.stop, ustop, data);
    }

    fn print_point(out: &mut String, point: CoverPoint, uindex: u32, data: &Funcdata) {
        if uindex == 0 {
            out.push_str("begin");
        } else if uindex == u32::MAX {
            out.push_str("end");
        } else if let CoverPoint::Op(op) = point {
            let _ = write!(out, "{}", data.op(op).get_seq_num());
        }
    }
}

pub const EMPTY_BLOCK: CoverBlock = CoverBlock::new();

#[derive(Clone, Debug, Default)]
pub struct Cover {
    cover: BTreeMap<i32, CoverBlock>,
}

impl Cover {
    pub fn new() -> Cover {
        Cover { cover: BTreeMap::new() }
    }

    fn add_ref_recurse(&mut self, bl: BlockId, data: &Funcdata) {
        let flow = data.block(bl);
        let block = self.cover.entry(flow.get_index()).or_default();
        if block.empty() {
            block.set_all();
            for slot in 0..flow.size_in() {
                self.add_ref_recurse(flow.get_in(slot), data);
            }
        } else {
            let op = block.get_stop();
            let ustart = CoverBlock::get_u_index(block.get_start(), data);
            let ustop = CoverBlock::get_u_index(op, data);
            if ustop != u32::MAX && ustop >= ustart {
                block.set_end(CoverPoint::End);
            }
            if ustop == 0
                && block.get_start() == CoverPoint::Begin
                && let CoverPoint::Op(stop_op) = op
                && data.op(stop_op).code() == OpCode::Multiequal
            {
                for slot in 0..flow.size_in() {
                    self.add_ref_recurse(flow.get_in(slot), data);
                }
            }
        }
    }

    pub fn clear(&mut self) {
        self.cover.clear();
    }

    pub fn compare_to(&self, op2: &Cover) -> i32 {
        let first = self.cover.keys().next().copied().unwrap_or(1000000);
        let second = op2.cover.keys().next().copied().unwrap_or(1000000);
        if first < second {
            return -1;
        } else if first == second {
            return 0;
        }
        1
    }

    pub fn get_cover_block(&self, index: i32) -> &CoverBlock {
        self.cover.get(&index).unwrap_or(&EMPTY_BLOCK)
    }

    pub fn intersect(&self, op2: &Cover, data: &Funcdata) -> i32 {
        let mut res = 0;
        let mut iter = self.cover.iter().peekable();
        let mut iter2 = op2.cover.iter().peekable();
        loop {
            let (Some((key, block)), Some((key2, block2))) = (iter.peek(), iter2.peek()) else {
                return res;
            };
            if key < key2 {
                iter.next();
            } else if key > key2 {
                iter2.next();
            } else {
                let newres = block.intersect(block2, data);
                if newres == 2 {
                    return 2;
                }
                if newres == 1 {
                    res = 1;
                }
                iter.next();
                iter2.next();
            }
        }
    }

    pub fn intersect_by_block(&self, blk: i32, op2: &Cover, data: &Funcdata) -> i32 {
        let Some(block) = self.cover.get(&blk) else {
            return 0;
        };
        let Some(block2) = op2.cover.get(&blk) else {
            return 0;
        };
        block.intersect(block2, data)
    }

    pub fn intersect_list(&self, listout: &mut Vec<i32>, op2: &Cover, level: i32, data: &Funcdata) {
        listout.clear();
        let mut iter = self.cover.iter().peekable();
        let mut iter2 = op2.cover.iter().peekable();
        loop {
            let (Some((key, block)), Some((key2, block2))) = (iter.peek(), iter2.peek()) else {
                return;
            };
            let key = **key;
            if key < **key2 {
                iter.next();
            } else if key > **key2 {
                iter2.next();
            } else {
                let val = block.intersect(block2, data);
                if val >= level {
                    listout.push(key);
                }
                iter.next();
                iter2.next();
            }
        }
    }

    pub fn intersect_op_set(&self, op_set: &dyn PcodeOpSet, rep: VarnodeId, data: &Funcdata) -> bool {
        let op_set_base = op_set.base();
        if op_set_base.op_list.is_empty() {
            return false;
        }
        let mut set_block = 0usize;
        let mut op_index = op_set_base.block_start[set_block] as usize;
        let mut set_index = op_block_index(data, op_set_base.op_list[op_index]);
        let first_index = op_block_index(data, op_set_base.op_list[0]);
        let mut cover_iter = self.cover.range(first_index..).peekable();
        while let Some((cover_index, cover_block)) = cover_iter.peek() {
            let cover_index = **cover_index;
            if cover_index < set_index {
                cover_iter.next();
            } else if cover_index > set_index {
                set_block += 1;
                if set_block >= op_set_base.block_start.len() {
                    break;
                }
                op_index = op_set_base.block_start[set_block] as usize;
                set_index = op_block_index(data, op_set_base.op_list[op_index]);
            } else {
                let cover_block = **cover_block;
                cover_iter.next();
                let mut op_max = op_set_base.op_list.len();
                set_block += 1;
                if set_block < op_set_base.block_start.len() {
                    op_max = op_set_base.block_start[set_block] as usize;
                }
                loop {
                    let op = op_set_base.op_list[op_index];
                    if cover_block.contain(CoverPoint::Op(op), data)
                        && cover_block.boundary(CoverPoint::Op(op), data) == 0
                        && op_set.affects_test(op, rep, data)
                    {
                        return true;
                    }
                    op_index += 1;
                    if op_index >= op_max {
                        break;
                    }
                }
                if set_block >= op_set_base.block_start.len() {
                    break;
                }
            }
        }
        false
    }

    pub fn contain(&self, op: OpId, max: i32, data: &Funcdata) -> bool {
        let Some(block) = self.cover.get(&op_block_index(data, op)) else {
            return false;
        };
        if block.contain(CoverPoint::Op(op), data) {
            if max == 1 {
                return true;
            }
            if block.boundary(CoverPoint::Op(op), data) == 0 {
                return true;
            }
        }
        false
    }

    pub fn contain_varnode_def(&self, vn: VarnodeId, data: &Funcdata) -> i32 {
        let (point, blk) = match data.vn(vn).get_def() {
            None => (CoverPoint::Input, 0),
            Some(op) => (CoverPoint::Op(op), op_block_index(data, op)),
        };
        let Some(block) = self.cover.get(&blk) else {
            return 0;
        };
        if block.contain(point, data) {
            let boundtype = block.boundary(point, data);
            if boundtype == 0 {
                return 1;
            }
            if boundtype == 2 {
                return 2;
            }
            return 3;
        }
        0
    }

    pub fn merge(&mut self, op2: &Cover, data: &Funcdata) {
        for (key, block) in op2.cover.iter() {
            self.cover.entry(*key).or_default().merge(block, data);
        }
    }

    pub fn rebuild(&mut self, vn: VarnodeId, data: &Funcdata) {
        let mut path = vec![vn];
        let mut pos = 0;
        self.add_def_point(vn, data);
        loop {
            let cur_vn = path[pos];
            pos += 1;
            for op in data.vn(cur_vn).descend().iter() {
                self.add_ref_point(*op, vn, data);
                if let Some(out_vn) = data.op(*op).get_out()
                    && data.vn(out_vn).is_implied()
                {
                    path.push(out_vn);
                }
            }
            if pos >= path.len() {
                break;
            }
        }
    }

    pub fn add_def_point(&mut self, vn: VarnodeId, data: &Funcdata) {
        self.cover.clear();
        let varnode = data.vn(vn);
        if let Some(def) = varnode.get_def() {
            let block = self.cover.entry(op_block_index(data, def)).or_default();
            block.set_begin(CoverPoint::Op(def));
            block.set_end(CoverPoint::Op(def));
        } else if varnode.is_input() {
            let block = self.cover.entry(0).or_default();
            block.set_begin(CoverPoint::Input);
            block.set_end(CoverPoint::Input);
        }
    }

    pub fn add_ref_point(&mut self, reference: OpId, vn: VarnodeId, data: &Funcdata) {
        let ref_op = data.op(reference);
        let bl = ref_op.get_parent().expect("p-code op has no parent block");
        let flow = data.block(bl);
        let block = self.cover.entry(flow.get_index()).or_default();
        if block.empty() {
            block.set_end(CoverPoint::Op(reference));
        } else if block.contain(CoverPoint::Op(reference), data) {
            if ref_op.code() != OpCode::Multiequal {
                return;
            }
        } else {
            let op = block.get_stop();
            let startop = block.get_start();
            block.set_end(CoverPoint::Op(reference));
            let ustop = CoverBlock::get_u_index(block.get_stop(), data);
            if ustop >= CoverBlock::get_u_index(startop, data) {
                if let CoverPoint::Op(stop_op) = op
                    && data.op(stop_op).code() == OpCode::Multiequal
                    && startop == CoverPoint::Begin
                {
                    for slot in 0..flow.size_in() {
                        self.add_ref_recurse(flow.get_in(slot), data);
                    }
                }
                return;
            }
        }
        if ref_op.code() == OpCode::Multiequal {
            for slot in 0..ref_op.num_input() {
                if ref_op.get_in(slot) == vn {
                    self.add_ref_recurse(flow.get_in(slot), data);
                }
            }
        } else {
            for slot in 0..flow.size_in() {
                self.add_ref_recurse(flow.get_in(slot), data);
            }
        }
    }

    pub fn print(&self, out: &mut String, data: &Funcdata) {
        for (key, block) in self.cover.iter() {
            let _ = write!(out, "{}: ", key);
            block.print(out, data);
            out.push('\n');
        }
    }

    pub fn iter(&self) -> impl DoubleEndedIterator<Item = (&i32, &CoverBlock)> {
        self.cover.iter()
    }

    pub fn blocks(&self) -> &BTreeMap<i32, CoverBlock> {
        &self.cover
    }

    pub fn blocks_mut(&mut self) -> &mut BTreeMap<i32, CoverBlock> {
        &mut self.cover
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn one_piece_intervals() {
        assert_eq!(CoverBlock::intersect_indices(1, 5, 5, 9), 1);
        assert_eq!(CoverBlock::intersect_indices(1, 5, 6, 9), 0);
        assert_eq!(CoverBlock::intersect_indices(1, 5, 3, 9), 2);
        assert_eq!(CoverBlock::intersect_indices(6, 9, 1, 6), 1);
    }

    #[test]
    fn two_piece_intervals() {
        assert_eq!(CoverBlock::intersect_indices(8, 2, 3, 7), 0);
        assert_eq!(CoverBlock::intersect_indices(8, 2, 2, 7), 1);
        assert_eq!(CoverBlock::intersect_indices(8, 2, 1, 7), 2);
        assert_eq!(CoverBlock::intersect_indices(3, 7, 8, 2), 0);
        assert_eq!(CoverBlock::intersect_indices(3, 7, 7, 2), 1);
        assert_eq!(CoverBlock::intersect_indices(8, 2, 9, 1), 2);
    }

    #[test]
    fn cover_block_points() {
        let mut block = CoverBlock::new();
        assert!(block.empty());
        block.set_begin(CoverPoint::Input);
        assert_eq!(block.get_stop(), CoverPoint::End);
        block.set_all();
        assert_eq!(block.get_start(), CoverPoint::Begin);
        assert_eq!(block.get_stop(), CoverPoint::End);
        let cover = Cover::new();
        assert!(cover.get_cover_block(3).empty());
        assert_eq!(cover.compare_to(&Cover::new()), 0);
    }
}
