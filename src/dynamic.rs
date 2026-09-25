use crate::stdsort::std_sort;
use std::cmp::Ordering;

use crate::address::Address;
use crate::crc32::crc_update;
use crate::funcdata::Funcdata;
use crate::op::OpId;
use crate::opcodes::OpCode;
use crate::varnode::VarnodeId;

#[derive(Copy, Clone, Debug)]
pub struct ToOpEdge {
    op: OpId,
    slot: i32,
}

impl ToOpEdge {
    pub fn new(op: OpId, slot: i32) -> ToOpEdge {
        ToOpEdge { op, slot }
    }

    pub fn get_op(&self) -> OpId {
        self.op
    }

    pub fn get_slot(&self) -> i32 {
        self.slot
    }

    pub fn less_than(&self, op2: &ToOpEdge, data: &Funcdata) -> bool {
        let seq1 = data.op(self.op).get_seq_num();
        let seq2 = data.op(op2.op).get_seq_num();
        let addr1 = seq1.get_addr();
        let addr2 = seq2.get_addr();
        if addr1 != addr2 {
            return addr1 < addr2;
        }
        let ord1 = seq1.get_order();
        let ord2 = seq2.get_order();
        if ord1 != ord2 {
            return ord1 < ord2;
        }
        self.slot < op2.slot
    }

    pub fn compare(&self, op2: &ToOpEdge, data: &Funcdata) -> Ordering {
        if self.less_than(op2, data) {
            Ordering::Less
        } else if op2.less_than(self, data) {
            Ordering::Greater
        } else {
            Ordering::Equal
        }
    }

    pub fn hash(&self, reg: u32, data: &Funcdata) -> u32 {
        let mut reg = crc_update(reg, self.slot as u32);
        let pcode_op = data.op(self.op);
        reg = crc_update(reg, TRANSTABLE[pcode_op.code().index()]);
        let addr = pcode_op.get_seq_num().get_addr();
        let mut val = addr.get_offset();
        let size = addr.get_addr_size();
        for _ in 0..size {
            reg = crc_update(reg, val as u32);
            val >>= 8;
        }
        reg
    }
}

pub struct DynamicHash {
    vnproc: u32,
    opproc: u32,
    opedgeproc: u32,
    markop: Vec<OpId>,
    markvn: Vec<VarnodeId>,
    vnedge: Vec<VarnodeId>,
    opedge: Vec<ToOpEdge>,
    addrresult: Address,
    hash: u64,
}

pub const TRANSTABLE: [u32; 75] = [
    0,
    OpCode::Copy as u32,
    OpCode::Load as u32,
    OpCode::Store as u32,
    OpCode::Branch as u32,
    OpCode::Cbranch as u32,
    OpCode::Branchind as u32,
    OpCode::Call as u32,
    OpCode::Callind as u32,
    OpCode::Callother as u32,
    OpCode::Return as u32,
    OpCode::IntEqual as u32,
    OpCode::IntEqual as u32,
    OpCode::IntSless as u32,
    OpCode::IntSless as u32,
    OpCode::IntLess as u32,
    OpCode::IntLess as u32,
    OpCode::IntZext as u32,
    OpCode::IntSext as u32,
    OpCode::IntAdd as u32,
    OpCode::IntAdd as u32,
    OpCode::IntCarry as u32,
    OpCode::IntScarry as u32,
    OpCode::IntSborrow as u32,
    OpCode::Int2comp as u32,
    OpCode::IntNegate as u32,
    OpCode::IntXor as u32,
    OpCode::IntAnd as u32,
    OpCode::IntOr as u32,
    OpCode::IntMult as u32,
    OpCode::IntRight as u32,
    OpCode::IntSright as u32,
    OpCode::IntMult as u32,
    OpCode::IntDiv as u32,
    OpCode::IntSdiv as u32,
    OpCode::IntRem as u32,
    OpCode::IntSrem as u32,
    OpCode::BoolNegate as u32,
    OpCode::BoolXor as u32,
    OpCode::BoolAnd as u32,
    OpCode::BoolOr as u32,
    OpCode::FloatEqual as u32,
    OpCode::FloatEqual as u32,
    OpCode::FloatLess as u32,
    OpCode::FloatLess as u32,
    0,
    OpCode::FloatNan as u32,
    OpCode::FloatAdd as u32,
    OpCode::FloatDiv as u32,
    OpCode::FloatMult as u32,
    OpCode::FloatAdd as u32,
    OpCode::FloatNeg as u32,
    OpCode::FloatAbs as u32,
    OpCode::FloatSqrt as u32,
    OpCode::FloatInt2float as u32,
    OpCode::FloatFloat2float as u32,
    OpCode::FloatTrunc as u32,
    OpCode::FloatCeil as u32,
    OpCode::FloatFloor as u32,
    OpCode::FloatRound as u32,
    OpCode::Multiequal as u32,
    OpCode::Indirect as u32,
    OpCode::Piece as u32,
    OpCode::Subpiece as u32,
    0,
    OpCode::IntAdd as u32,
    OpCode::IntAdd as u32,
    OpCode::Segmentop as u32,
    OpCode::Cpoolref as u32,
    OpCode::New as u32,
    OpCode::Insert as u32,
    OpCode::Zpull as u32,
    OpCode::Popcount as u32,
    OpCode::Lzcount as u32,
    OpCode::Spull as u32,
];

impl Default for DynamicHash {
    fn default() -> DynamicHash {
        DynamicHash::new()
    }
}

impl DynamicHash {
    pub fn new() -> DynamicHash {
        DynamicHash {
            vnproc: 0,
            opproc: 0,
            opedgeproc: 0,
            markop: Vec::new(),
            markvn: Vec::new(),
            vnedge: Vec::new(),
            opedge: Vec::new(),
            addrresult: Address::invalid(),
            hash: 0,
        }
    }

    fn trans(data: &Funcdata, op: OpId) -> u32 {
        TRANSTABLE[data.op(op).code().index()]
    }

    fn build_vn_up(&mut self, vn: VarnodeId, data: &mut Funcdata) {
        let mut cur = vn;
        let op;
        loop {
            let varnode = data.vn(cur);
            if !varnode.is_written() {
                return;
            }
            let def = varnode.get_def().expect("written varnode without defining op");
            if Self::trans(data, def) != 0 {
                op = def;
                break;
            }
            cur = data.op(def).get_in(0);
        }
        self.opedge.push(ToOpEdge::new(op, -1));
    }

    fn build_vn_down(&mut self, vn: VarnodeId, data: &mut Funcdata) {
        let insize = self.opedge.len();
        let descend: Vec<OpId> = data.vn(vn).descend().to_vec();
        for first in descend {
            let mut op = Some(first);
            let mut tmpvn = vn;
            while let Some(cur) = op {
                if Self::trans(data, cur) != 0 {
                    break;
                }
                match data.op(cur).get_out() {
                    None => {
                        op = None;
                        break;
                    }
                    Some(out) => {
                        tmpvn = out;
                        op = data.vn(out).lone_descend();
                    }
                }
            }
            let Some(cur) = op else {
                continue;
            };
            let slot = data.op(cur).get_slot(tmpvn);
            self.opedge.push(ToOpEdge::new(cur, slot));
        }
        if self.opedge.len() - insize > 1 {
            let data_ref: &Funcdata = data;
            std_sort(&mut self.opedge[insize..], |edge1, edge2| {
                edge1.compare(edge2, data_ref) == std::cmp::Ordering::Less
            });
        }
    }

    fn build_op_up(&mut self, op: OpId, data: &mut Funcdata) {
        let pcode_op = data.op(op);
        for index in 0..pcode_op.num_input() {
            self.vnedge.push(pcode_op.get_in(index));
        }
    }

    fn build_op_down(&mut self, op: OpId, data: &mut Funcdata) {
        if let Some(vn) = data.op(op).get_out() {
            self.vnedge.push(vn);
        }
    }

    fn gather_unmarked_vn(&mut self, data: &mut Funcdata) {
        for index in 0..self.vnedge.len() {
            let vn = self.vnedge[index];
            if data.vn(vn).is_mark() {
                continue;
            }
            self.markvn.push(vn);
            data.vn_mut(vn).set_mark();
        }
        self.vnedge.clear();
    }

    fn gather_unmarked_op(&mut self, data: &mut Funcdata) {
        while (self.opedgeproc as usize) < self.opedge.len() {
            let op = self.opedge[self.opedgeproc as usize].get_op();
            self.opedgeproc += 1;
            if data.op(op).is_mark() {
                continue;
            }
            self.markop.push(op);
            data.op_mut(op).set_mark();
        }
    }

    fn build_vn_up_pending(&mut self, data: &mut Funcdata) {
        while (self.vnproc as usize) < self.markvn.len() {
            let vn = self.markvn[self.vnproc as usize];
            self.build_vn_up(vn, data);
            self.vnproc += 1;
        }
    }

    fn build_vn_down_pending(&mut self, data: &mut Funcdata) {
        while (self.vnproc as usize) < self.markvn.len() {
            let vn = self.markvn[self.vnproc as usize];
            self.build_vn_down(vn, data);
            self.vnproc += 1;
        }
    }

    fn build_op_up_pending(&mut self, data: &mut Funcdata) {
        while (self.opproc as usize) < self.markop.len() {
            let op = self.markop[self.opproc as usize];
            self.build_op_up(op, data);
            self.opproc += 1;
        }
    }

    fn build_op_down_pending(&mut self, data: &mut Funcdata) {
        while (self.opproc as usize) < self.markop.len() {
            let op = self.markop[self.opproc as usize];
            self.build_op_down(op, data);
            self.opproc += 1;
        }
    }

    fn piece_together_hash(&mut self, root: VarnodeId, method: u32, data: &mut Funcdata) {
        for &vn in self.markvn.iter() {
            data.vn_mut(vn).clear_mark();
        }
        for &op in self.markop.iter() {
            data.op_mut(op).clear_mark();
        }

        if self.opedge.is_empty() {
            self.hash = 0;
            self.addrresult = Address::invalid();
            return;
        }

        let mut reg: u32 = 0x3ba0fe06;

        let root_vn = data.vn(root);
        reg = crc_update(reg, root_vn.get_size() as u32);
        if root_vn.is_constant() {
            let mut val = root_vn.get_offset();
            for _ in 0..root_vn.get_size() {
                reg = crc_update(reg, val as u32);
                val >>= 8;
            }
        }

        for edge in self.opedge.iter() {
            reg = edge.hash(reg, data);
        }

        let mut op = self.opedge[0].get_op();
        let mut slot = 0;
        let mut attachedop = true;
        let mut found = false;
        for edge in self.opedge.iter() {
            op = edge.get_op();
            slot = edge.get_slot();
            let pcode_op = data.op(op);
            if slot < 0 && pcode_op.get_out() == Some(root) {
                found = true;
                break;
            }
            if slot >= 0 && pcode_op.get_in(slot) == root {
                found = true;
                break;
            }
        }
        if !found {
            op = self.opedge[0].get_op();
            slot = self.opedge[0].get_slot();
            attachedop = false;
        }

        let mut hash: u64 = if attachedop { 0 } else { 1 };
        hash <<= 4;
        hash |= method as u64;
        hash <<= 7;
        hash |= Self::trans(data, op) as u64;
        hash <<= 5;
        hash |= (slot & 0x1f) as u64;

        hash <<= 32;
        hash |= reg as u64;
        self.hash = hash;
        self.addrresult = data.op(op).get_seq_num().get_addr().clone();
    }

    fn move_off_skip(op: &mut Option<OpId>, slot: &mut i32, data: &Funcdata) {
        while let Some(cur) = *op {
            if Self::trans(data, cur) != 0 {
                return;
            }
            if *slot >= 0 {
                let vn = data.op(cur).get_out().expect("skipped op without output");
                *op = data.vn(vn).lone_descend();
                match *op {
                    None => return,
                    Some(next) => *slot = data.op(next).get_slot(vn),
                }
            } else {
                let varnode = data.vn(data.op(cur).get_in(0));
                if !varnode.is_written() {
                    return;
                }
                *op = varnode.get_def();
            }
        }
    }

    fn dedup_varnodes(varlist: &mut Vec<VarnodeId>, data: &mut Funcdata) {
        if varlist.len() < 2 {
            return;
        }
        let mut res_list = Vec::new();
        for &vn in varlist.iter() {
            if !data.vn(vn).is_mark() {
                data.vn_mut(vn).set_mark();
                res_list.push(vn);
            }
        }
        for &vn in res_list.iter() {
            data.vn_mut(vn).clear_mark();
        }
        std::mem::swap(varlist, &mut res_list);
    }

    pub fn clear(&mut self) {
        self.markop.clear();
        self.markvn.clear();
        self.vnedge.clear();
        self.opedge.clear();
    }

    pub fn calc_hash_varnode(&mut self, root: VarnodeId, method: u32, data: &mut Funcdata) {
        self.vnproc = 0;
        self.opproc = 0;
        self.opedgeproc = 0;

        self.vnedge.push(root);
        self.gather_unmarked_vn(data);
        for index in (self.vnproc as usize)..self.markvn.len() {
            let vn = self.markvn[index];
            self.build_vn_up(vn, data);
        }
        self.build_vn_down_pending(data);

        match method {
            1 => {
                self.gather_unmarked_op(data);
                self.build_op_up_pending(data);
                self.gather_unmarked_vn(data);
                self.build_vn_up_pending(data);
            }
            2 => {
                self.gather_unmarked_op(data);
                self.build_op_down_pending(data);
                self.gather_unmarked_vn(data);
                self.build_vn_down_pending(data);
            }
            3 => {
                self.gather_unmarked_op(data);
                self.build_op_up_pending(data);
                self.gather_unmarked_vn(data);
                self.build_vn_down_pending(data);
            }
            _ => {}
        }
        self.piece_together_hash(root, method, data);
    }

    pub fn calc_hash_op(&mut self, op: OpId, slot: i32, method: u32, data: &mut Funcdata) {
        let root = if slot < 0 {
            match data.op(op).get_out() {
                Some(out) => out,
                None => {
                    self.hash = 0;
                    self.addrresult = Address::invalid();
                    return;
                }
            }
        } else {
            if slot >= data.op(op).num_input() {
                self.hash = 0;
                self.addrresult = Address::invalid();
                return;
            }
            data.op(op).get_in(slot)
        };
        self.vnproc = 0;
        self.opproc = 0;
        self.opedgeproc = 0;

        self.opedge.push(ToOpEdge::new(op, slot));
        match method {
            5 => {
                self.gather_unmarked_op(data);
                self.build_op_up_pending(data);
                self.gather_unmarked_vn(data);
                self.build_vn_up_pending(data);
            }
            6 => {
                self.gather_unmarked_op(data);
                self.build_op_down_pending(data);
                self.gather_unmarked_vn(data);
                self.build_vn_down_pending(data);
            }
            _ => {}
        }
        self.piece_together_hash(root, method, data);
    }

    pub fn unique_hash_varnode(&mut self, root: VarnodeId, fd: &mut Funcdata) {
        let mut vnlist: Vec<VarnodeId> = Vec::new();
        let mut vnlist2: Vec<VarnodeId> = Vec::new();
        let mut champion: Vec<VarnodeId> = Vec::new();
        let mut tmphash: u64 = 0;
        let mut tmpaddr = Address::invalid();
        let maxduplicates: usize = 8;

        for method in 0..4 {
            self.clear();
            self.calc_hash_varnode(root, method, fd);
            if self.hash == 0 {
                return;
            }
            tmphash = self.hash;
            tmpaddr = self.addrresult.clone();
            vnlist.clear();
            vnlist2.clear();
            DynamicHash::gather_first_level_vars(&mut vnlist, fd, &tmpaddr, tmphash);
            for &tmpvn in vnlist.iter() {
                self.clear();
                self.calc_hash_varnode(tmpvn, method, fd);
                if DynamicHash::get_comparable(self.hash) == DynamicHash::get_comparable(tmphash) {
                    vnlist2.push(tmpvn);
                    if vnlist2.len() > maxduplicates {
                        break;
                    }
                }
            }
            if vnlist2.len() <= maxduplicates && (champion.is_empty() || vnlist2.len() < champion.len()) {
                champion = vnlist2.clone();
                if champion.len() == 1 {
                    break;
                }
            }
        }
        if champion.is_empty() {
            self.hash = 0;
            self.addrresult = Address::invalid();
            return;
        }
        let total = champion.len() as u64 - 1;
        let Some(pos) = champion.iter().position(|&vn| vn == root) else {
            self.hash = 0;
            self.addrresult = Address::invalid();
            return;
        };
        self.hash = tmphash | ((pos as u64) << 49);
        self.hash |= total << 52;
        self.addrresult = tmpaddr;
    }

    pub fn unique_hash_op(&mut self, op: OpId, slot: i32, fd: &mut Funcdata) {
        let mut oplist: Vec<OpId> = Vec::new();
        let mut oplist2: Vec<OpId> = Vec::new();
        let mut champion: Vec<OpId> = Vec::new();
        let mut tmphash: u64 = 0;
        let mut tmpaddr = Address::invalid();
        let maxduplicates: usize = 8;

        let mut current = Some(op);
        let mut slot = slot;
        DynamicHash::move_off_skip(&mut current, &mut slot, fd);
        let Some(op) = current else {
            self.hash = 0;
            self.addrresult = Address::invalid();
            return;
        };
        let op_addr = fd.op(op).get_addr().clone();
        fd.list_ops(&mut oplist, &op_addr);
        for method in 4..7 {
            self.clear();
            self.calc_hash_op(op, slot, method, fd);
            if self.hash == 0 {
                return;
            }
            tmphash = self.hash;
            tmpaddr = self.addrresult.clone();
            oplist.clear();
            oplist2.clear();
            for &tmpop in oplist.iter() {
                if slot >= fd.op(tmpop).num_input() {
                    continue;
                }
                self.clear();
                self.calc_hash_op(tmpop, slot, method, fd);
                if DynamicHash::get_comparable(self.hash) == DynamicHash::get_comparable(tmphash) {
                    oplist2.push(tmpop);
                    if oplist2.len() > maxduplicates {
                        break;
                    }
                }
            }
            if oplist2.len() <= maxduplicates && (champion.is_empty() || oplist2.len() < champion.len()) {
                champion = oplist2.clone();
                if champion.len() == 1 {
                    break;
                }
            }
        }
        if champion.is_empty() {
            self.hash = 0;
            self.addrresult = Address::invalid();
            return;
        }
        let total = champion.len() as u64 - 1;
        let Some(pos) = champion.iter().position(|&candidate| candidate == op) else {
            self.hash = 0;
            self.addrresult = Address::invalid();
            return;
        };
        self.hash = tmphash | ((pos as u64) << 49);
        self.hash |= total << 52;
        self.addrresult = tmpaddr;
    }

    pub fn find_varnode(&mut self, fd: &mut Funcdata, addr: &Address, hash_value: u64) -> Option<VarnodeId> {
        let method = DynamicHash::get_method_from_hash(hash_value);
        let total = DynamicHash::get_total_from_hash(hash_value);
        let pos = DynamicHash::get_position_from_hash(hash_value);
        let mut hash_value = hash_value;
        DynamicHash::clear_total_position(&mut hash_value);
        let mut vnlist: Vec<VarnodeId> = Vec::new();
        let mut vnlist2: Vec<VarnodeId> = Vec::new();
        DynamicHash::gather_first_level_vars(&mut vnlist, fd, addr, hash_value);
        for &tmpvn in vnlist.iter() {
            self.clear();
            self.calc_hash_varnode(tmpvn, method, fd);
            if DynamicHash::get_comparable(self.hash) == DynamicHash::get_comparable(hash_value) {
                vnlist2.push(tmpvn);
            }
        }
        if total as usize != vnlist2.len() {
            return None;
        }
        vnlist2.get(pos as usize).copied()
    }

    pub fn find_op(&mut self, fd: &mut Funcdata, addr: &Address, hash_value: u64) -> Option<OpId> {
        let method = DynamicHash::get_method_from_hash(hash_value);
        let slot = DynamicHash::get_slot_from_hash(hash_value);
        let total = DynamicHash::get_total_from_hash(hash_value);
        let pos = DynamicHash::get_position_from_hash(hash_value);
        let mut hash_value = hash_value;
        DynamicHash::clear_total_position(&mut hash_value);
        let mut oplist: Vec<OpId> = Vec::new();
        let mut oplist2: Vec<OpId> = Vec::new();
        fd.list_ops(&mut oplist, addr);
        for &tmpop in oplist.iter() {
            if slot >= fd.op(tmpop).num_input() {
                continue;
            }
            self.clear();
            self.calc_hash_op(tmpop, slot, method, fd);
            if DynamicHash::get_comparable(self.hash) == DynamicHash::get_comparable(hash_value) {
                oplist2.push(tmpop);
            }
        }
        if total as usize != oplist2.len() {
            return None;
        }
        oplist2.get(pos as usize).copied()
    }

    pub fn get_hash(&self) -> u64 {
        self.hash
    }

    pub fn get_address(&self) -> &Address {
        &self.addrresult
    }

    pub fn gather_first_level_vars(varlist: &mut Vec<VarnodeId>, fd: &mut Funcdata, addr: &Address, hash_value: u64) {
        let opc_val = DynamicHash::get_op_code_from_hash(hash_value);
        let slot = DynamicHash::get_slot_from_hash(hash_value);
        let isnotattached = DynamicHash::get_is_not_attached(hash_value);
        let mut op_list: Vec<OpId> = Vec::new();
        fd.list_ops(&mut op_list, addr);

        for &listed in op_list.iter() {
            let pcode_op = fd.op(listed);
            if pcode_op.is_dead() {
                continue;
            }
            if Self::trans(fd, listed) != opc_val {
                continue;
            }
            if slot < 0 {
                if let Some(mut vn) = pcode_op.get_out() {
                    if isnotattached
                        && let Some(next) = fd.vn(vn).lone_descend()
                        && Self::trans(fd, next) == 0
                    {
                        match fd.op(next).get_out() {
                            Some(out) => vn = out,
                            None => continue,
                        }
                    }
                    varlist.push(vn);
                }
            } else if slot < pcode_op.num_input() {
                let mut vn = pcode_op.get_in(slot);
                if isnotattached
                    && let Some(def) = fd.vn(vn).get_def()
                    && Self::trans(fd, def) == 0
                {
                    vn = fd.op(def).get_in(0);
                }
                varlist.push(vn);
            }
        }
        DynamicHash::dedup_varnodes(varlist, fd);
    }

    pub fn get_slot_from_hash(hash_value: u64) -> i32 {
        let res = ((hash_value >> 32) & 0x1f) as i32;
        if res == 31 { -1 } else { res }
    }

    pub fn get_method_from_hash(hash_value: u64) -> u32 {
        ((hash_value >> 44) & 0xf) as u32
    }

    pub fn get_op_code_from_hash(hash_value: u64) -> u32 {
        ((hash_value >> 37) & 0x7f) as u32
    }

    pub fn get_position_from_hash(hash_value: u64) -> u32 {
        ((hash_value >> 49) & 7) as u32
    }

    pub fn get_total_from_hash(hash_value: u64) -> u32 {
        ((hash_value >> 52) & 7) as u32 + 1
    }

    pub fn get_is_not_attached(hash_value: u64) -> bool {
        ((hash_value >> 48) & 1) != 0
    }

    pub fn clear_total_position(hash_value: &mut u64) {
        let mut val: u64 = 0x3f;
        val <<= 49;
        val = !val;
        *hash_value &= val;
    }

    pub fn get_comparable(hash_value: u64) -> u32 {
        hash_value as u32
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn hash_field_extraction() {
        let mut hash_value: u64 = 1u64 << 48;
        hash_value |= 3u64 << 44;
        hash_value |= (OpCode::IntAdd as u64) << 37;
        hash_value |= 0x1fu64 << 32;
        hash_value |= 0xdeadbeef;
        hash_value |= 5u64 << 49;
        hash_value |= 6u64 << 52;
        assert!(DynamicHash::get_is_not_attached(hash_value));
        assert_eq!(DynamicHash::get_method_from_hash(hash_value), 3);
        assert_eq!(DynamicHash::get_op_code_from_hash(hash_value), OpCode::IntAdd as u32);
        assert_eq!(DynamicHash::get_slot_from_hash(hash_value), -1);
        assert_eq!(DynamicHash::get_position_from_hash(hash_value), 5);
        assert_eq!(DynamicHash::get_total_from_hash(hash_value), 7);
        assert_eq!(DynamicHash::get_comparable(hash_value), 0xdeadbeef);
        DynamicHash::clear_total_position(&mut hash_value);
        assert_eq!(DynamicHash::get_position_from_hash(hash_value), 0);
        assert_eq!(DynamicHash::get_total_from_hash(hash_value), 1);
        assert!(DynamicHash::get_is_not_attached(hash_value));
        assert_eq!(DynamicHash::get_method_from_hash(hash_value), 3);
    }

    #[test]
    fn transtable_lumps_variants() {
        assert_eq!(TRANSTABLE[OpCode::IntSub.index()], OpCode::IntAdd as u32);
        assert_eq!(TRANSTABLE[OpCode::Ptradd.index()], OpCode::IntAdd as u32);
        assert_eq!(TRANSTABLE[OpCode::Ptrsub.index()], OpCode::IntAdd as u32);
        assert_eq!(TRANSTABLE[OpCode::IntLeft.index()], OpCode::IntMult as u32);
        assert_eq!(TRANSTABLE[OpCode::Cast.index()], 0);
        assert_eq!(TRANSTABLE[OpCode::Spull.index()], OpCode::Spull as u32);
    }
}
