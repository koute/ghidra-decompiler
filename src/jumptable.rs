use crate::stdsort::std_sort;
use std::cell::Cell;
use std::collections::{BTreeMap, BTreeSet};

use crate::address::{Address, calc_mask, minimalmask, mostsigbit_set, signbit_negative, uintb_negate};
use crate::architecture::Architecture;
use crate::block::BlockId;
use crate::define_id;
use crate::dynamic::DynamicHash;
use crate::emulate::Emulate;
use crate::emulateutil::{EmulatePcodeOp, EmulatePcodeOpBase, PcodeOpContext};
use crate::error::{Error, Result};
use crate::expression::PcodeOpNode;
use crate::flow::FlowInfo;
use crate::funcdata::Funcdata;
use crate::marshal::{ATTRIB_CONTENT, ATTRIB_FORMAT, ATTRIB_SIZE, AttributeId, Decoder, ElementId, Encoder};
use crate::memstate::{MemoryBank, MemoryImage};
use crate::op::{OpId, PcodeOp};
use crate::opcodes::OpCode;
use crate::pcodeinject::evaluate_executable;
use crate::pcoderaw::VarnodeData;
use crate::rangeutil::CircleRange;
use crate::space::AddrSpace;
use crate::userop::{UserOpId, UserOpType};
use crate::varnode::VarnodeId;

pub const ATTRIB_LABEL: AttributeId = AttributeId::new("label", 131);
pub const ATTRIB_NUM: AttributeId = AttributeId::new("num", 132);
pub const ELEM_BASICOVERRIDE: ElementId = ElementId::new("basicoverride", 211);
pub const ELEM_DEST: ElementId = ElementId::new("dest", 212);
pub const ELEM_JUMPTABLE: ElementId = ElementId::new("jumptable", 213);
pub const ELEM_LOADTABLE: ElementId = ElementId::new("loadtable", 214);
pub const ELEM_NORMADDR: ElementId = ElementId::new("normaddr", 215);
pub const ELEM_NORMHASH: ElementId = ElementId::new("normhash", 216);
pub const ELEM_STARTVAL: ElementId = ElementId::new("startval", 217);

define_id!(JumpTableId);

fn last_op_of(data: &Funcdata, bl: BlockId) -> Option<OpId> {
    data.block_last_op(bl)
}

fn parent_of(data: &Funcdata, op: OpId) -> BlockId {
    data.op(op).get_parent().expect("p-code op is not in a basic block")
}

#[derive(Clone, Debug)]
pub struct LoadTable {
    pub addr: Address,
    pub size: i32,
    pub num: i32,
}

impl Default for LoadTable {
    fn default() -> LoadTable {
        LoadTable {
            addr: Address::invalid(),
            size: 0,
            num: 0,
        }
    }
}

impl LoadTable {
    pub fn new(ad: &Address, sz: i32) -> LoadTable {
        LoadTable {
            addr: ad.clone(),
            size: sz,
            num: 1,
        }
    }

    pub fn with_count(ad: &Address, sz: i32, nm: i32) -> LoadTable {
        LoadTable {
            addr: ad.clone(),
            size: sz,
            num: nm,
        }
    }

    pub fn less_than(&self, op2: &LoadTable) -> bool {
        self.addr < op2.addr
    }

    pub fn encode(&self, encoder: &mut dyn Encoder) -> Result<()> {
        encoder.open_element(ELEM_LOADTABLE);
        encoder.write_signed_integer(ATTRIB_SIZE, self.size as i64);
        encoder.write_signed_integer(ATTRIB_NUM, self.num as i64);
        self.addr.encode(encoder)?;
        encoder.close_element(ELEM_LOADTABLE);
        Ok(())
    }

    pub fn decode(&mut self, decoder: &mut dyn Decoder) -> Result<()> {
        let elem_id = decoder.open_element_expect(ELEM_LOADTABLE)?;
        self.size = decoder.read_signed_integer_attr(ATTRIB_SIZE)? as i32;
        self.num = decoder.read_signed_integer_attr(ATTRIB_NUM)? as i32;
        self.addr = Address::decode(decoder)?;
        decoder.close_element(elem_id)?;
        Ok(())
    }

    pub fn collapse_table(table: &mut Vec<LoadTable>) {
        if table.is_empty() {
            return;
        }
        let mut issorted = true;
        let mut num = table[0].num;
        let size = table[0].size;
        let mut nextaddr = table[0].addr.add(size as i64);
        for entry in table.iter().skip(1) {
            if entry.addr == nextaddr && entry.size == size {
                num += entry.num;
                nextaddr = entry.addr.add(entry.size as i64);
            } else {
                issorted = false;
                break;
            }
        }
        if issorted {
            table.truncate(1);
            table[0].num = num;
            return;
        }
        std_sort(table, |first, second| first.addr < second.addr);
        let mut count = 1;
        let mut lastiter = 0;
        nextaddr = table[0].addr.add((table[0].size * table[0].num) as i64);
        for index in 1..table.len() {
            let current = table[index].clone();
            if current.addr == nextaddr && current.size == table[lastiter].size {
                table[lastiter].num += current.num;
                nextaddr = current.addr.add((current.size * current.num) as i64);
            } else if nextaddr < current.addr || current.size != table[lastiter].size {
                lastiter += 1;
                table[lastiter] = current.clone();
                nextaddr = current.addr.add((current.size * current.num) as i64);
                count += 1;
            }
        }
        table.resize(count, LoadTable::with_count(&nextaddr, 0, 1));
    }
}

#[derive(Clone, Copy, Debug)]
pub struct RootedOp {
    pub op: Option<OpId>,
    pub root_vn: i32,
}

impl RootedOp {
    pub fn new(op: OpId, root: i32) -> RootedOp {
        RootedOp {
            op: Some(op),
            root_vn: root,
        }
    }
}

#[derive(Clone, Debug, Default)]
pub struct PathMeld {
    pub common_vn: Vec<VarnodeId>,
    pub op_meld: Vec<RootedOp>,
}

impl PathMeld {
    pub fn internal_intersect(&mut self, data: &mut Funcdata, parent_map: &mut Vec<i32>) {
        let mut new_vn: Vec<VarnodeId> = Vec::new();
        for &vn in self.common_vn.iter() {
            if data.vn(vn).is_mark() {
                parent_map.push(new_vn.len() as i32);
                new_vn.push(vn);
                data.vn_mut(vn).clear_mark();
            } else {
                parent_map.push(-1);
            }
        }
        self.common_vn = new_vn;
        let mut last_intersect = -1;
        for index in (0..parent_map.len()).rev() {
            let val = parent_map[index];
            if val == -1 {
                parent_map[index] = last_intersect;
            } else {
                last_intersect = val;
            }
        }
    }

    pub fn meld_ops(&mut self, data: &Funcdata, path: &[PcodeOpNode], cut_off: i32, parent_map: &[i32]) -> i32 {
        for rooted in self.op_meld.iter_mut() {
            let pos = parent_map[rooted.root_vn as usize];
            if pos == -1 {
                rooted.op = None;
            } else {
                rooted.root_vn = pos;
            }
        }
        let mut new_meld: Vec<RootedOp> = Vec::new();
        let mut cur_root = -1;
        let mut meld_pos = 0;
        let mut last_block: Option<BlockId> = None;
        for index in 0..cut_off.max(0) as usize {
            let op = path[index].op.expect("path edge without op");
            let op_parent = data.op(op).get_parent();
            let mut cur_op: Option<OpId> = None;
            while meld_pos < self.op_meld.len() {
                let trial_op = match self.op_meld[meld_pos].op {
                    Some(trial_op) => trial_op,
                    None => {
                        meld_pos += 1;
                        continue;
                    }
                };
                let trial_parent = data.op(trial_op).get_parent();
                if trial_parent != op_parent {
                    if op_parent == last_block {
                        cur_op = None;
                        break;
                    } else if trial_parent != last_block {
                        let res = self.op_meld[meld_pos].root_vn;
                        self.op_meld = new_meld;
                        return res;
                    }
                } else if data.op(trial_op).get_seq_num().get_order() <= data.op(op).get_seq_num().get_order() {
                    cur_op = Some(trial_op);
                    break;
                }
                last_block = trial_parent;
                new_meld.push(self.op_meld[meld_pos]);
                cur_root = self.op_meld[meld_pos].root_vn;
                meld_pos += 1;
            }
            if cur_op == Some(op) {
                new_meld.push(self.op_meld[meld_pos]);
                cur_root = self.op_meld[meld_pos].root_vn;
                meld_pos += 1;
            } else {
                new_meld.push(RootedOp::new(op, cur_root));
            }
            last_block = op_parent;
        }
        self.op_meld = new_meld;
        -1
    }

    pub fn truncate_paths(&mut self, cut_point: i32) {
        while self.op_meld.len() > 1 {
            if self.op_meld.last().expect("op meld is empty").root_vn < cut_point {
                break;
            }
            self.op_meld.pop();
        }
        self.common_vn.truncate(cut_point as usize);
    }

    pub fn set(&mut self, op2: &PathMeld) {
        self.common_vn = op2.common_vn.clone();
        self.op_meld = op2.op_meld.clone();
    }

    pub fn set_path(&mut self, data: &Funcdata, path: &[PcodeOpNode]) {
        for (index, node) in path.iter().enumerate() {
            let op = node.op.expect("path edge without op");
            let vn = data.op(op).get_in(node.slot);
            self.op_meld.push(RootedOp::new(op, index as i32));
            self.common_vn.push(vn);
        }
    }

    pub fn set_op(&mut self, op: OpId, vn: VarnodeId) {
        self.common_vn.push(vn);
        self.op_meld.push(RootedOp::new(op, 0));
    }

    pub fn append(&mut self, op2: &PathMeld) {
        let mut common = op2.common_vn.clone();
        common.extend(self.common_vn.iter().copied());
        self.common_vn = common;
        let mut ops = op2.op_meld.clone();
        ops.extend(self.op_meld.iter().copied());
        self.op_meld = ops;
        for index in op2.op_meld.len()..self.op_meld.len() {
            self.op_meld[index].root_vn += op2.common_vn.len() as i32;
        }
    }

    pub fn clear(&mut self) {
        self.common_vn.clear();
        self.op_meld.clear();
    }

    pub fn meld(&mut self, data: &mut Funcdata, path: &mut Vec<PcodeOpNode>) {
        let mut parent_map: Vec<i32> = Vec::new();
        for node in path.iter() {
            let vn = data.op(node.op.expect("path edge without op")).get_in(node.slot);
            data.vn_mut(vn).set_mark();
        }
        self.internal_intersect(data, &mut parent_map);
        let mut cut_off = -1;
        for (index, node) in path.iter().enumerate() {
            let vn = data.op(node.op.expect("path edge without op")).get_in(node.slot);
            if !data.vn(vn).is_mark() {
                cut_off = index as i32 + 1;
            } else {
                data.vn_mut(vn).clear_mark();
            }
        }
        let new_cutoff = self.meld_ops(data, path, cut_off, &parent_map);
        if new_cutoff >= 0 {
            self.truncate_paths(new_cutoff);
        }
        path.truncate(cut_off.max(0) as usize);
    }

    pub fn mark_paths(&self, data: &mut Funcdata, val: bool, start_varnode: i32) {
        let mut start_op = self.op_meld.len() as i32 - 1;
        while start_op >= 0 {
            if self.op_meld[start_op as usize].root_vn == start_varnode {
                break;
            }
            start_op -= 1;
        }
        if start_op < 0 {
            return;
        }
        for index in 0..=start_op as usize {
            let op = self.op_meld[index].op.expect("melded path has no op");
            if val {
                data.op_mut(op).set_mark();
            } else {
                data.op_mut(op).clear_mark();
            }
        }
    }

    pub fn num_common_varnode(&self) -> i32 {
        self.common_vn.len() as i32
    }

    pub fn num_ops(&self) -> i32 {
        self.op_meld.len() as i32
    }

    pub fn get_varnode(&self, index: i32) -> VarnodeId {
        self.common_vn[index as usize]
    }

    pub fn get_op_parent(&self, index: i32) -> VarnodeId {
        self.common_vn[self.op_meld[index as usize].root_vn as usize]
    }

    pub fn get_op(&self, index: i32) -> OpId {
        self.op_meld[index as usize].op.expect("melded path has no op")
    }

    pub fn get_earliest_op(&self, pos: i32) -> Option<OpId> {
        for rooted in self.op_meld.iter().rev() {
            if rooted.root_vn == pos {
                return rooted.op;
            }
        }
        None
    }

    pub fn is_load_in_path(&self, data: &Funcdata, index: i32) -> bool {
        let mut index = index;
        while index > 0 {
            index -= 1;
            let vn = self.common_vn[index as usize];
            if !data.vn(vn).is_written() {
                continue;
            }
            let def = data.vn(vn).get_def().expect("written varnode has no defining op");
            if data.op(def).code() == OpCode::Load {
                return true;
            }
        }
        false
    }

    pub fn empty(&self) -> bool {
        self.common_vn.is_empty()
    }
}

pub struct EmulateFunction {
    pub base: EmulatePcodeOpBase,
    pub varnode_map: BTreeMap<VarnodeId, u64>,
    pub loadpoints: Option<Vec<LoadTable>>,
}

impl EmulateFunction {
    pub fn new() -> EmulateFunction {
        EmulateFunction {
            base: EmulatePcodeOpBase::new(),
            varnode_map: BTreeMap::new(),
            loadpoints: None,
        }
    }

    pub fn execute_load(&mut self, ctx: &mut PcodeOpContext<'_>) -> Result<()> {
        if self.loadpoints.is_some() {
            let op = self.base.current_op.expect("no current p-code op");
            let ptrvn = ctx.data.op(op).get_in(1);
            let mut off = self.get_varnode_value(ctx.data, ctx.glb, ptrvn)?;
            let spc = ctx
                .data
                .vn(ctx.data.op(op).get_in(0))
                .get_space_from_const(&ctx.glb.manager)
                .expect("LOAD space operand is invalid");
            off = AddrSpace::address_to_byte(off, spc.get_word_size());
            let outvn = ctx.data.op(op).get_out().expect("LOAD has no output");
            let size = ctx.data.vn(outvn).get_size();
            self.loadpoints
                .as_mut()
                .expect("load collection is disabled")
                .push(LoadTable::new(&Address::new(spc, off), size));
        }
        EmulatePcodeOp::pcode_execute_load(self, ctx)
    }

    pub fn execute_branch(&mut self, _ctx: &mut PcodeOpContext<'_>) -> Result<()> {
        Err(Error::Lowlevel(
            "Branch encountered emulating jumptable calculation".to_string(),
        ))
    }

    pub fn execute_branchind(&mut self, _ctx: &mut PcodeOpContext<'_>) -> Result<()> {
        Err(Error::Lowlevel(
            "Indirect branch encountered emulating jumptable calculation".to_string(),
        ))
    }

    pub fn execute_call(&mut self, ctx: &mut PcodeOpContext<'_>) -> Result<()> {
        self.fallthru_op(ctx)
    }

    pub fn execute_callind(&mut self, ctx: &mut PcodeOpContext<'_>) -> Result<()> {
        self.fallthru_op(ctx)
    }

    pub fn execute_callother(&mut self, ctx: &mut PcodeOpContext<'_>) -> Result<()> {
        self.fallthru_op(ctx)
    }

    pub fn fallthru_op(&mut self, _ctx: &mut PcodeOpContext<'_>) -> Result<()> {
        self.base.last_op = self.base.current_op;
        Ok(())
    }

    pub fn set_load_collect(&mut self, val: Option<Vec<LoadTable>>) {
        self.loadpoints = val;
    }

    pub fn set_execute_address(&mut self, ctx: &mut PcodeOpContext<'_>, addr: &Address) -> Result<()> {
        let has_physical = addr.get_space().map(|spc| spc.has_physical()).unwrap_or(false);
        if !has_physical {
            return Err(Error::Lowlevel("Bad execute address".to_string()));
        }
        let op = ctx
            .data
            .target(addr)
            .ok_or_else(|| Error::Lowlevel("Could not set execute address".to_string()))?;
        let opc = ctx.data.op(op).code();
        self.base.current_op = Some(op);
        self.base.emulate.current_behave = Some(opc);
        Ok(())
    }

    pub fn get_varnode_value(&self, data: &Funcdata, glb: &Architecture, vn: VarnodeId) -> Result<u64> {
        if data.vn(vn).is_constant() {
            return Ok(data.vn(vn).get_offset());
        }
        if let Some(val) = self.varnode_map.get(&vn) {
            return Ok(*val);
        }
        let spc = data.vn(vn).get_space().expect("varnode has no space").clone();
        EmulatePcodeOp::get_load_image_value(self, glb, &spc, data.vn(vn).get_offset(), data.vn(vn).get_size())
    }

    pub fn set_varnode_value(&mut self, vn: VarnodeId, val: u64) {
        self.varnode_map.insert(vn, val);
    }

    pub fn emulate_path(
        &mut self,
        data: &mut Funcdata,
        glb: &mut Architecture,
        val: u64,
        path_meld: &PathMeld,
        startop: OpId,
        startvn: VarnodeId,
    ) -> Result<u64> {
        let mut startop = startop;
        let mut startvn = startvn;
        let mut index = 0;
        while index < path_meld.num_ops() {
            if path_meld.get_op(index) == startop {
                break;
            }
            index += 1;
        }
        if data.op(startop).code() == OpCode::Multiequal {
            let mut slot = 0;
            while slot < data.op(startop).num_input() {
                if data.op(startop).get_in(slot) == startvn {
                    break;
                }
                slot += 1;
            }
            if slot == data.op(startop).num_input() || index == 0 {
                return Err(Error::Lowlevel(
                    "Cannot start jumptable emulation with unresolved MULTIEQUAL".to_string(),
                ));
            }
            startvn = data.op(startop).get_out().expect("MULTIEQUAL has no output");
            index -= 1;
            startop = path_meld.get_op(index);
        }
        if index == path_meld.num_ops() {
            return Err(Error::Lowlevel("Bad jumptable emulation".to_string()));
        }
        if !data.vn(startvn).is_constant() {
            self.set_varnode_value(startvn, val);
        }
        let _ = startop;
        let mut ctx = PcodeOpContext::new(&mut *data, &mut *glb);
        while index > 0 {
            let curop = path_meld.get_op(index);
            index -= 1;
            EmulatePcodeOp::set_current_op(self, ctx.data, curop);
            if let Err(err) = self.execute_current_op(&mut ctx) {
                if let Error::DataUnavail(_) = err {
                    let message = format!(
                        "Could not emulate address calculation at {}",
                        ctx.data.op(curop).get_addr()
                    );
                    return Err(Error::Lowlevel(message));
                }
                return Err(err);
            }
        }
        let invn = ctx.data.op(path_meld.get_op(0)).get_in(0);
        self.get_varnode_value(ctx.data, ctx.glb, invn)
    }
}

impl Default for EmulateFunction {
    fn default() -> EmulateFunction {
        EmulateFunction::new()
    }
}

pub struct GuardRecord {
    pub cbranch: Option<OpId>,
    pub read_op: OpId,
    pub vn: VarnodeId,
    pub base_vn: VarnodeId,
    pub indpath: i32,
    pub bits_preserved: i32,
    pub range: CircleRange,
    pub unrolled: bool,
}

impl GuardRecord {
    pub fn new(
        data: &Funcdata,
        b_op: OpId,
        r_op: OpId,
        path: i32,
        rng: &CircleRange,
        vn: VarnodeId,
        unr: bool,
    ) -> GuardRecord {
        let mut bits_preserved = 0;
        let base_vn = GuardRecord::quasi_copy(data, vn, &mut bits_preserved);
        GuardRecord {
            cbranch: Some(b_op),
            read_op: r_op,
            vn,
            base_vn,
            indpath: path,
            bits_preserved,
            range: rng.clone(),
            unrolled: unr,
        }
    }

    pub fn is_unrolled(&self) -> bool {
        self.unrolled
    }

    pub fn get_branch(&self) -> Option<OpId> {
        self.cbranch
    }

    pub fn get_read_op(&self) -> OpId {
        self.read_op
    }

    pub fn get_path(&self) -> i32 {
        self.indpath
    }

    pub fn get_range(&self) -> &CircleRange {
        &self.range
    }

    pub fn clear(&mut self) {
        self.cbranch = None;
    }

    pub fn value_match(&self, data: &Funcdata, vn2: VarnodeId, base_vn2: VarnodeId, bits_preserved2: i32) -> i32 {
        if self.vn == vn2 {
            return 1;
        }
        let load_op;
        let load_op2;
        if self.bits_preserved == bits_preserved2 {
            if self.base_vn == base_vn2 {
                return 1;
            }
            load_op = data.vn(self.base_vn).get_def();
            load_op2 = data.vn(base_vn2).get_def();
        } else {
            load_op = data.vn(self.vn).get_def();
            load_op2 = data.vn(vn2).get_def();
        }
        let load_op = match load_op {
            Some(load_op) => load_op,
            None => return 0,
        };
        let load_op2 = match load_op2 {
            Some(load_op2) => load_op2,
            None => return 0,
        };
        if GuardRecord::one_off_match(data, load_op, load_op2) == 1 {
            return 1;
        }
        if data.op(load_op).code() != OpCode::Load {
            return 0;
        }
        if data.op(load_op2).code() != OpCode::Load {
            return 0;
        }
        if data.vn(data.op(load_op).get_in(0)).get_offset() != data.vn(data.op(load_op2).get_in(0)).get_offset() {
            return 0;
        }
        let ptr = data.op(load_op).get_in(1);
        let ptr2 = data.op(load_op2).get_in(1);
        if ptr == ptr2 {
            return 2;
        }
        if !data.vn(ptr).is_written() {
            return 0;
        }
        if !data.vn(ptr2).is_written() {
            return 0;
        }
        let addop = data.vn(ptr).get_def().expect("written varnode has no defining op");
        if data.op(addop).code() != OpCode::IntAdd {
            return 0;
        }
        let constvn = data.op(addop).get_in(1);
        if !data.vn(constvn).is_constant() {
            return 0;
        }
        let addop2 = data.vn(ptr2).get_def().expect("written varnode has no defining op");
        if data.op(addop2).code() != OpCode::IntAdd {
            return 0;
        }
        let constvn2 = data.op(addop2).get_in(1);
        if !data.vn(constvn2).is_constant() {
            return 0;
        }
        if data.op(addop).get_in(0) != data.op(addop2).get_in(0) {
            return 0;
        }
        if data.vn(constvn).get_offset() != data.vn(constvn2).get_offset() {
            return 0;
        }
        2
    }

    fn matching_constants(data: &Funcdata, vn1: VarnodeId, vn2: VarnodeId) -> bool {
        if !data.vn(vn1).is_constant() {
            return false;
        }
        if !data.vn(vn2).is_constant() {
            return false;
        }
        data.vn(vn1).get_offset() == data.vn(vn2).get_offset()
    }

    pub fn one_off_match(data: &Funcdata, op1: OpId, op2: OpId) -> i32 {
        if data.op(op1).code() != data.op(op2).code() {
            return 0;
        }
        match data.op(op1).code() {
            OpCode::IntAnd
            | OpCode::IntAdd
            | OpCode::IntXor
            | OpCode::IntOr
            | OpCode::IntLeft
            | OpCode::IntRight
            | OpCode::IntSright
            | OpCode::IntMult
            | OpCode::Subpiece => {
                if data.op(op2).get_in(0) != data.op(op1).get_in(0) {
                    return 0;
                }
                if GuardRecord::matching_constants(data, data.op(op2).get_in(1), data.op(op1).get_in(1)) {
                    return 1;
                }
            }
            _ => {}
        }
        0
    }

    pub fn quasi_copy(data: &Funcdata, vn: VarnodeId, bits_preserved: &mut i32) -> VarnodeId {
        *bits_preserved = mostsigbit_set(data.vn(vn).get_nz_mask()) + 1;
        if *bits_preserved == 0 {
            return vn;
        }
        let mut mask: u64 = 1 << 1;
        mask = mask.wrapping_shl((*bits_preserved - 1) as u32);
        mask = mask.wrapping_sub(1);
        let mut vn = vn;
        let mut op = data.vn(vn).get_def();
        while let Some(cur) = op {
            match data.op(cur).code() {
                OpCode::Copy => {
                    vn = data.op(cur).get_in(0);
                    op = data.vn(vn).get_def();
                }
                OpCode::IntAnd => {
                    let const_vn = data.op(cur).get_in(1);
                    if data.vn(const_vn).is_constant() && data.vn(const_vn).get_offset() == mask {
                        vn = data.op(cur).get_in(0);
                        op = data.vn(vn).get_def();
                    } else {
                        op = None;
                    }
                }
                OpCode::IntOr => {
                    let const_vn = data.op(cur).get_in(1);
                    let offset = data.vn(const_vn).get_offset();
                    if data.vn(const_vn).is_constant() && (offset | mask) == (offset ^ mask) {
                        vn = data.op(cur).get_in(0);
                        op = data.vn(vn).get_def();
                    } else {
                        op = None;
                    }
                }
                OpCode::IntSext | OpCode::IntZext
                    if data.vn(data.op(cur).get_in(0)).get_size() * 8 >= *bits_preserved =>
                {
                    vn = data.op(cur).get_in(0);
                    op = data.vn(vn).get_def();
                }
                OpCode::Piece if data.vn(data.op(cur).get_in(1)).get_size() * 8 >= *bits_preserved => {
                    vn = data.op(cur).get_in(1);
                    op = data.vn(vn).get_def();
                }
                OpCode::Subpiece => {
                    let const_vn = data.op(cur).get_in(1);
                    if data.vn(const_vn).is_constant() && data.vn(const_vn).get_offset() == 0 {
                        vn = data.op(cur).get_in(0);
                        op = data.vn(vn).get_def();
                    } else {
                        op = None;
                    }
                }
                _ => {
                    op = None;
                }
            }
        }
        vn
    }
}

pub const NO_LABEL: u64 = 0xBAD1ABE1BAD1ABE1;

pub trait JumpValues: Send {
    fn truncate(&mut self, nm: i32);

    fn get_size(&self) -> u64;

    fn contains(&self, val: u64) -> bool;

    fn initialize_for_reading(&self) -> bool;

    fn next(&self) -> bool;

    fn get_value(&self) -> u64;

    fn get_start_varnode(&self) -> Option<VarnodeId>;

    fn get_start_op(&self) -> Option<OpId>;

    fn is_reversible(&self) -> bool;

    fn clone_values(&self) -> Box<dyn JumpValues>;

    fn as_values_range(&self) -> Option<&JumpValuesRange> {
        None
    }

    fn as_values_range_mut(&mut self) -> Option<&mut JumpValuesRange> {
        None
    }
}

pub struct JumpValuesRange {
    pub range: CircleRange,
    pub normqvn: Option<VarnodeId>,
    pub startop: Option<OpId>,
    pub curval: Cell<u64>,
}

impl Default for JumpValuesRange {
    fn default() -> JumpValuesRange {
        JumpValuesRange::new()
    }
}

impl JumpValuesRange {
    pub fn new() -> JumpValuesRange {
        JumpValuesRange {
            range: CircleRange::new(),
            normqvn: None,
            startop: None,
            curval: Cell::new(0),
        }
    }

    pub fn set_range(&mut self, rng: &CircleRange, vn: VarnodeId, op: Option<OpId>) {
        self.range = rng.clone();
        self.normqvn = Some(vn);
        self.startop = op;
    }

    pub fn get_range(&self) -> &CircleRange {
        &self.range
    }
}

impl JumpValues for JumpValuesRange {
    fn truncate(&mut self, nm: i32) {
        let mut range_size = 64 - self.range.get_mask().leading_zeros() as i32;
        range_size >>= 3;
        let left = self.range.get_min();
        let step = self.range.get_step();
        let right = left.wrapping_add(step.wrapping_mul(nm) as i64 as u64) & self.range.get_mask();
        self.range.set_range(left, right, range_size, step);
    }

    fn get_size(&self) -> u64 {
        self.range.get_size()
    }

    fn contains(&self, val: u64) -> bool {
        self.range.contains(val)
    }

    fn initialize_for_reading(&self) -> bool {
        if self.range.get_size() == 0 {
            return false;
        }
        self.curval.set(self.range.get_min());
        true
    }

    fn next(&self) -> bool {
        let mut val = self.curval.get();
        let res = self.range.get_next(&mut val);
        self.curval.set(val);
        res
    }

    fn get_value(&self) -> u64 {
        self.curval.get()
    }

    fn get_start_varnode(&self) -> Option<VarnodeId> {
        self.normqvn
    }

    fn get_start_op(&self) -> Option<OpId> {
        self.startop
    }

    fn is_reversible(&self) -> bool {
        true
    }

    fn clone_values(&self) -> Box<dyn JumpValues> {
        let mut res = JumpValuesRange::new();
        res.range = self.range.clone();
        res.normqvn = self.normqvn;
        res.startop = self.startop;
        Box::new(res)
    }

    fn as_values_range(&self) -> Option<&JumpValuesRange> {
        Some(self)
    }

    fn as_values_range_mut(&mut self) -> Option<&mut JumpValuesRange> {
        Some(self)
    }
}

pub struct JumpValuesRangeDefault {
    pub base: JumpValuesRange,
    pub extravalue: u64,
    pub extravn: Option<VarnodeId>,
    pub extraop: Option<OpId>,
    pub lastvalue: Cell<bool>,
}

impl Default for JumpValuesRangeDefault {
    fn default() -> JumpValuesRangeDefault {
        JumpValuesRangeDefault::new()
    }
}

impl JumpValuesRangeDefault {
    pub fn new() -> JumpValuesRangeDefault {
        JumpValuesRangeDefault {
            base: JumpValuesRange::new(),
            extravalue: 0,
            extravn: None,
            extraop: None,
            lastvalue: Cell::new(false),
        }
    }

    pub fn set_extra_value(&mut self, val: u64) {
        self.extravalue = val;
    }

    pub fn set_default_vn(&mut self, vn: VarnodeId) {
        self.extravn = Some(vn);
    }

    pub fn set_default_op(&mut self, op: OpId) {
        self.extraop = Some(op);
    }
}

impl JumpValues for JumpValuesRangeDefault {
    fn truncate(&mut self, nm: i32) {
        self.base.truncate(nm);
    }

    fn get_size(&self) -> u64 {
        self.base.range.get_size().wrapping_add(1)
    }

    fn contains(&self, val: u64) -> bool {
        if self.extravalue == val {
            return true;
        }
        self.base.range.contains(val)
    }

    fn initialize_for_reading(&self) -> bool {
        if self.base.range.get_size() == 0 {
            self.base.curval.set(self.extravalue);
            self.lastvalue.set(true);
        } else {
            self.base.curval.set(self.base.range.get_min());
            self.lastvalue.set(false);
        }
        true
    }

    fn next(&self) -> bool {
        if self.lastvalue.get() {
            return false;
        }
        let mut val = self.base.curval.get();
        if self.base.range.get_next(&mut val) {
            self.base.curval.set(val);
            return true;
        }
        self.base.curval.set(val);
        self.lastvalue.set(true);
        self.base.curval.set(self.extravalue);
        true
    }

    fn get_value(&self) -> u64 {
        self.base.get_value()
    }

    fn get_start_varnode(&self) -> Option<VarnodeId> {
        if self.lastvalue.get() {
            self.extravn
        } else {
            self.base.normqvn
        }
    }

    fn get_start_op(&self) -> Option<OpId> {
        if self.lastvalue.get() {
            self.extraop
        } else {
            self.base.startop
        }
    }

    fn is_reversible(&self) -> bool {
        !self.lastvalue.get()
    }

    fn clone_values(&self) -> Box<dyn JumpValues> {
        let mut res = JumpValuesRangeDefault::new();
        res.base.range = self.base.range.clone();
        res.base.normqvn = self.base.normqvn;
        res.base.startop = self.base.startop;
        res.extravalue = self.extravalue;
        res.extravn = self.extravn;
        res.extraop = self.extraop;
        Box::new(res)
    }

    fn as_values_range(&self) -> Option<&JumpValuesRange> {
        Some(&self.base)
    }

    fn as_values_range_mut(&mut self) -> Option<&mut JumpValuesRange> {
        Some(&mut self.base)
    }
}

pub trait JumpModel: Send {
    fn is_override(&self) -> bool;

    fn get_table_size(&self) -> i32;

    fn recover_model(
        &mut self,
        jt: &JumpTable,
        data: &mut Funcdata,
        glb: &mut Architecture,
        indop: OpId,
        previous: Option<&dyn JumpModel>,
        maxtablesize: u32,
    ) -> Result<bool>;

    fn build_addresses(
        &self,
        data: &mut Funcdata,
        glb: &mut Architecture,
        indop: OpId,
        addresstable: &mut Vec<Address>,
        loadpoints: Option<&mut Vec<LoadTable>>,
        loadcounts: Option<&mut Vec<i32>>,
    ) -> Result<()>;

    fn find_unnormalized(&mut self, data: &mut Funcdata, maxaddsub: u32, maxleftright: u32, maxext: u32) -> Result<()>;

    fn build_labels(
        &self,
        data: &mut Funcdata,
        glb: &mut Architecture,
        addresstable: &mut Vec<Address>,
        label: &mut Vec<u64>,
        orig: &dyn JumpModel,
    ) -> Result<()>;

    fn fold_in_normalization(
        &mut self,
        data: &mut Funcdata,
        glb: &mut Architecture,
        indop: OpId,
    ) -> Result<Option<VarnodeId>>;

    fn fold_in_guards(&mut self, data: &mut Funcdata, glb: &mut Architecture, jump: &mut JumpTable) -> Result<bool>;

    fn sanity_check(
        &mut self,
        data: &mut Funcdata,
        glb: &mut Architecture,
        indop: OpId,
        addresstable: &mut Vec<Address>,
        loadpoints: &mut Vec<LoadTable>,
        loadcounts: Option<&mut Vec<i32>>,
    ) -> Result<bool>;

    fn clone_model(&self) -> Box<dyn JumpModel>;

    fn clear(&mut self) {}

    fn encode(&self, _encoder: &mut dyn Encoder) -> Result<()> {
        Ok(())
    }

    fn decode(&mut self, _decoder: &mut dyn Decoder) -> Result<()> {
        Ok(())
    }

    fn as_jump_basic(&self) -> Option<&JumpBasic> {
        None
    }

    fn as_jump_assisted(&self) -> Option<&JumpAssisted> {
        None
    }
}

#[derive(Clone, Debug, Default)]
pub struct JumpModelTrivial {
    pub size: u32,
}

impl JumpModelTrivial {
    pub fn new() -> JumpModelTrivial {
        JumpModelTrivial { size: 0 }
    }
}

impl JumpModel for JumpModelTrivial {
    fn is_override(&self) -> bool {
        false
    }

    fn get_table_size(&self) -> i32 {
        self.size as i32
    }

    fn recover_model(
        &mut self,
        jt: &JumpTable,
        data: &mut Funcdata,
        _glb: &mut Architecture,
        indop: OpId,
        _previous: Option<&dyn JumpModel>,
        _maxtablesize: u32,
    ) -> Result<bool> {
        self.size = data.block(parent_of(data, indop)).size_out() as u32;
        Ok(self.size != 0 && self.size as i32 <= jt.num_entries())
    }

    fn build_addresses(
        &self,
        data: &mut Funcdata,
        _glb: &mut Architecture,
        indop: OpId,
        addresstable: &mut Vec<Address>,
        _loadpoints: Option<&mut Vec<LoadTable>>,
        _loadcounts: Option<&mut Vec<i32>>,
    ) -> Result<()> {
        addresstable.clear();
        let bl = parent_of(data, indop);
        for slot in 0..data.block(bl).size_out() {
            let outbl = data.block(bl).get_out(slot);
            addresstable.push(data.block(outbl).get_start());
        }
        Ok(())
    }

    fn find_unnormalized(
        &mut self,
        _data: &mut Funcdata,
        _maxaddsub: u32,
        _maxleftright: u32,
        _maxext: u32,
    ) -> Result<()> {
        Ok(())
    }

    fn build_labels(
        &self,
        _data: &mut Funcdata,
        _glb: &mut Architecture,
        addresstable: &mut Vec<Address>,
        label: &mut Vec<u64>,
        _orig: &dyn JumpModel,
    ) -> Result<()> {
        for addr in addresstable.iter() {
            label.push(addr.get_offset());
        }
        Ok(())
    }

    fn fold_in_normalization(
        &mut self,
        _data: &mut Funcdata,
        _glb: &mut Architecture,
        _indop: OpId,
    ) -> Result<Option<VarnodeId>> {
        Ok(None)
    }

    fn fold_in_guards(&mut self, _data: &mut Funcdata, _glb: &mut Architecture, _jump: &mut JumpTable) -> Result<bool> {
        Ok(false)
    }

    fn sanity_check(
        &mut self,
        _data: &mut Funcdata,
        _glb: &mut Architecture,
        _indop: OpId,
        _addresstable: &mut Vec<Address>,
        _loadpoints: &mut Vec<LoadTable>,
        _loadcounts: Option<&mut Vec<i32>>,
    ) -> Result<bool> {
        Ok(true)
    }

    fn clone_model(&self) -> Box<dyn JumpModel> {
        let mut res = JumpModelTrivial::new();
        res.size = self.size;
        Box::new(res)
    }
}

pub trait JumpBasicModel {
    fn jump_basic(&self) -> &JumpBasic;

    fn jump_basic_mut(&mut self) -> &mut JumpBasic;

    fn fold_in_one_guard(
        &mut self,
        data: &mut Funcdata,
        glb: &mut Architecture,
        guard: usize,
        jump: &mut JumpTable,
    ) -> Result<bool>;
}

pub struct JumpBasic {
    pub jrange: Option<Box<dyn JumpValues>>,
    pub path_meld: PathMeld,
    pub selectguards: Vec<GuardRecord>,
    pub varnode_index: i32,
    pub normalvn: Option<VarnodeId>,
    pub switchvn: Option<VarnodeId>,
}

impl Default for JumpBasic {
    fn default() -> JumpBasic {
        JumpBasic::new()
    }
}

impl JumpBasic {
    pub fn new() -> JumpBasic {
        JumpBasic {
            jrange: None,
            path_meld: PathMeld::default(),
            selectguards: Vec::new(),
            varnode_index: 0,
            normalvn: None,
            switchvn: None,
        }
    }

    fn range_values(&self) -> &JumpValuesRange {
        self.jrange
            .as_ref()
            .and_then(|jrange| jrange.as_values_range())
            .expect("jump table range is not recovered")
    }

    fn range_values_mut(&mut self) -> &mut JumpValuesRange {
        self.jrange
            .as_mut()
            .and_then(|jrange| jrange.as_values_range_mut())
            .expect("jump table range is not recovered")
    }

    fn jrange_ref(&self) -> &dyn JumpValues {
        self.jrange.as_deref().expect("jump table range is not recovered")
    }

    pub fn is_prune(data: &Funcdata, vn: VarnodeId) -> bool {
        if !data.vn(vn).is_written() {
            return true;
        }
        let op = data.vn(vn).get_def().expect("written varnode has no defining op");
        if data.op(op).is_call() || data.op(op).is_marker() {
            return true;
        }
        if data.op(op).num_input() == 0 {
            return true;
        }
        false
    }

    pub fn is_point(data: &Funcdata, vn: VarnodeId) -> bool {
        if data.vn(vn).is_constant() {
            return false;
        }
        if data.vn(vn).is_annotation() {
            return false;
        }
        if data.vn(vn).is_read_only() {
            return false;
        }
        true
    }

    pub fn get_stride(data: &Funcdata, vn: VarnodeId) -> i32 {
        let mut mask = data.vn(vn).get_nz_mask();
        if (mask & 0x3f) == 0 {
            return 32;
        }
        let mut stride = 1;
        while (mask & 1) == 0 {
            mask >>= 1;
            stride <<= 1;
        }
        stride
    }

    pub fn backup2_switch(
        data: &mut Funcdata,
        glb: &Architecture,
        output: u64,
        outvn: VarnodeId,
        invn: VarnodeId,
    ) -> Result<u64> {
        let mut output = output;
        let mut curvn = outvn;
        while curvn != invn {
            let op = data
                .vn(curvn)
                .get_def()
                .expect("switch normalization varnode has no defining op");
            let behave = glb.inst[data.op(op).code().index()]
                .as_ref()
                .expect("no TypeOp registered for opcode")
                .base()
                .behave
                .clone();
            let mut slot = 0;
            while slot < data.op(op).num_input() {
                if !data.vn(data.op(op).get_in(slot)).is_constant() {
                    break;
                }
                slot += 1;
            }
            let outsize = data.vn(data.op(op).get_out().expect("op has no output")).get_size();
            if data.op(op).get_eval_type() == PcodeOp::BINARY {
                let othervn = data.op(op).get_in(1 - slot);
                let addr = data.vn(othervn).get_addr().clone();
                let otherval = if !addr.is_constant() {
                    let loader = glb.loader.as_ref().expect("missing load image").clone();
                    let spc = addr.get_space().expect("address has no space").clone();
                    let mut mem = MemoryImage::new(spc, 4, 1024, loader.as_ref());
                    mem.get_value(addr.get_offset(), data.vn(othervn).get_size())?
                } else {
                    addr.get_offset()
                };
                let insize = data.vn(data.op(op).get_in(slot)).get_size();
                output = behave
                    .expect("op has no behavior")
                    .recover_input_binary(slot, outsize, output, insize, otherval)?;
                curvn = data.op(op).get_in(slot);
            } else if data.op(op).get_eval_type() == PcodeOp::UNARY {
                let insize = data.vn(data.op(op).get_in(slot)).get_size();
                output = behave
                    .expect("op has no behavior")
                    .recover_input_unary(outsize, output, insize)?;
                curvn = data.op(op).get_in(slot);
            } else {
                return Err(Error::Lowlevel("Bad switch normalization op".to_string()));
            }
        }
        Ok(output)
    }

    pub fn duplicate_varnodes(arr: &[VarnodeId]) -> bool {
        let vn = arr[0];
        for &other in arr.iter().skip(1) {
            if other != vn {
                return false;
            }
        }
        true
    }

    pub fn get_initial_range(&self, jt: &JumpTable, data: &Funcdata, vn: VarnodeId, rng: &mut CircleRange) {
        if data.vn(vn).is_constant() {
            *rng = CircleRange::new_single(data.vn(vn).get_offset(), data.vn(vn).get_size());
            return;
        }
        if data.vn(vn).is_written() {
            let def = data.vn(vn).get_def().expect("written varnode has no defining op");
            if data.op(def).is_bool_output() {
                *rng = CircleRange::new_range(0, 2, 1, 1);
                return;
            }
        }
        let step = JumpBasic::get_stride(data, vn);
        let size = data.vn(vn).get_size();
        if !data.vn(vn).is_written() {
            *rng = CircleRange::new_range(0, 0, size, step);
            return;
        }
        if jt.is_partial() {
            rng.set_range(0, 0, size, step);
        } else {
            rng.set_range(
                0,
                data.vn(vn).get_nz_mask().wrapping_add(step as i64 as u64),
                size,
                step,
            );
        }
        let op = data.vn(vn).get_def().expect("written varnode has no defining op");
        let opc = data.op(op).code();
        if opc == OpCode::IntAnd {
            let cvn = data.op(op).get_in(1);
            if data.vn(cvn).is_constant() {
                let tmprange = CircleRange::new_range(
                    0,
                    data.vn(cvn).get_offset().wrapping_add(step as i64 as u64),
                    size,
                    step,
                );
                if tmprange.get_size() < rng.get_size() {
                    *rng = tmprange;
                }
            }
        } else if opc == OpCode::IntRem {
            let cvn = data.op(op).get_in(1);
            if data.vn(cvn).is_constant() {
                let tmprange = CircleRange::new_range(0, data.vn(cvn).get_offset(), size, step);
                if tmprange.get_size() < rng.get_size() {
                    *rng = tmprange;
                }
            }
        } else if opc == OpCode::IntSrem {
            let cvn = data.op(op).get_in(1);
            if data.vn(cvn).is_constant() {
                let mut val = data.vn(cvn).get_offset();
                let csize = data.vn(cvn).get_size();
                if signbit_negative(val, csize) {
                    val = uintb_negate(val, csize);
                    val = val.wrapping_add(1);
                }
                let tmprange =
                    CircleRange::new_range(val.wrapping_neg().wrapping_add(step as i64 as u64), val, size, step);
                if tmprange.get_size() < rng.get_size() {
                    *rng = tmprange;
                }
            }
        }
    }

    pub fn find_determining_varnodes(&mut self, data: &mut Funcdata, op: OpId, slot: i32) {
        let mut path: Vec<PcodeOpNode> = Vec::new();
        let mut firstpoint = false;
        path.push(PcodeOpNode::new(op, slot));
        loop {
            let node = *path.last().expect("path is empty");
            let nodeop = node.op.expect("path edge without op");
            let curvn = data.op(nodeop).get_in(node.slot);
            if JumpBasic::is_prune(data, curvn) {
                if JumpBasic::is_point(data, curvn) {
                    if !firstpoint {
                        self.path_meld.set_path(data, &path);
                        firstpoint = true;
                    } else {
                        self.path_meld.meld(data, &mut path);
                    }
                }
                path.last_mut().expect("path is empty").slot += 1;
                loop {
                    let back = *path.last().expect("path is empty");
                    if back.slot < data.op(back.op.expect("path edge without op")).num_input() {
                        break;
                    }
                    path.pop();
                    if path.is_empty() {
                        break;
                    }
                    path.last_mut().expect("path is empty").slot += 1;
                }
            } else {
                let def = data.vn(curvn).get_def().expect("written varnode has no defining op");
                path.push(PcodeOpNode::new(def, 0));
            }
            if path.len() <= 1 {
                break;
            }
        }
        if self.path_meld.empty() {
            let invn = data.op(op).get_in(slot);
            self.path_meld.set_op(op, invn);
        }
    }

    pub fn analyze_guards(&mut self, jt: &JumpTable, data: &mut Funcdata, bl: BlockId, pathout: i32) {
        let maxbranch = 2;
        let maxpullback = 2;
        let usenzmask = !jt.is_partial();
        let mut bl = bl;
        let mut pathout = pathout;
        self.selectguards.clear();
        for index in 0..maxbranch {
            let prevbl;
            let indpath;
            if pathout >= 0 && data.block(bl).size_out() == 2 {
                prevbl = bl;
                indpath = pathout;
                pathout = -1;
            } else {
                pathout = -1;
                let mut found;
                loop {
                    if data.block(bl).size_in() != 1 {
                        if data.block(bl).size_in() > 1 {
                            self.check_unrolled_guard(jt, data, bl, maxpullback, usenzmask);
                        }
                        return;
                    }
                    found = data.block(bl).get_in(0);
                    if data.block(found).size_out() != 1 {
                        break;
                    }
                    bl = found;
                }
                prevbl = found;
                indpath = data.block(bl).get_in_rev_index(0);
            }
            let cbranch = match last_op_of(data, prevbl) {
                Some(cbranch) if data.op(cbranch).code() == OpCode::Cbranch => cbranch,
                _ => break,
            };
            if index != 0 {
                let otherbl = data.block(prevbl).get_out(1 - indpath);
                if let Some(otherop) = last_op_of(data, otherbl)
                    && data.op(otherop).code() == OpCode::Branchind
                    && Some(otherop) != jt.get_indirect_op()
                {
                    break;
                }
            }
            let mut toswitchval = indpath == 1;
            if data.op(cbranch).is_boolean_flip() {
                toswitchval = !toswitchval;
            }
            bl = prevbl;
            let mut vn = data.op(cbranch).get_in(1);
            let mut rng = CircleRange::new_bool(toswitchval);
            let indpathstore = if data.block(prevbl).get_flip_path() {
                1 - indpath
            } else {
                indpath
            };
            self.selectguards
                .push(GuardRecord::new(data, cbranch, cbranch, indpathstore, &rng, vn, false));
            for _ in 0..maxpullback {
                if !data.vn(vn).is_written() {
                    break;
                }
                let read_op = data.vn(vn).get_def().expect("written varnode has no defining op");
                let mut markup: Option<VarnodeId> = None;
                vn = match rng.pull_back(read_op, Some(&mut markup), usenzmask, data) {
                    Some(next) => next,
                    None => break,
                };
                if rng.is_empty() {
                    break;
                }
                self.selectguards
                    .push(GuardRecord::new(data, cbranch, read_op, indpathstore, &rng, vn, false));
            }
        }
    }

    pub fn calc_range(&self, jt: &JumpTable, data: &Funcdata, vn: VarnodeId, rng: &mut CircleRange) {
        self.get_initial_range(jt, data, vn, rng);
        let mut bits_preserved = 0;
        let base_vn = GuardRecord::quasi_copy(data, vn, &mut bits_preserved);
        for guard in self.selectguards.iter() {
            let matchval = guard.value_match(data, vn, base_vn, bits_preserved);
            if matchval == 0 {
                continue;
            }
            if rng.intersect(guard.get_range()) != 0 {
                continue;
            }
        }
        if rng.get_size() > 0x10000 {
            let mut positive = CircleRange::new_range(
                0,
                (rng.get_mask() >> 1).wrapping_add(1),
                data.vn(vn).get_size(),
                rng.get_step(),
            );
            positive.intersect(rng);
            if !positive.is_empty() {
                *rng = positive;
            }
        }
    }

    pub fn is_preferred_range(&self, data: &Funcdata, pos: i32, new_range: &CircleRange) -> bool {
        let old_range = self.range_values().get_range();
        if old_range.get_step() != new_range.get_step() {
            return new_range.get_step() < old_range.get_step();
        }
        if old_range.get_min() != new_range.get_min() {
            return new_range.get_min() < old_range.get_min();
        }
        let old_size = data.vn(self.path_meld.get_varnode(self.varnode_index)).get_size();
        let new_size = data.vn(self.path_meld.get_varnode(pos)).get_size();
        new_size < old_size
    }

    pub fn find_smallest_normal(&mut self, jt: &JumpTable, data: &Funcdata, previous: Option<&JumpBasic>) {
        let mut rng = CircleRange::new();
        let mut expected_range = CircleRange::new();
        if let Some(previous) = previous
            && let Some(prevrange) = previous.jrange.as_ref().and_then(|jrange| jrange.as_values_range())
        {
            expected_range = prevrange.get_range().clone();
        }
        self.varnode_index = 0;
        self.calc_range(jt, data, self.path_meld.get_varnode(0), &mut rng);
        let vn0 = self.path_meld.get_varnode(0);
        let op0 = self.path_meld.get_op(0);
        self.range_values_mut().set_range(&rng, vn0, Some(op0));
        let mut maxsize = rng.get_size();
        for index in 1..self.path_meld.num_common_varnode() {
            if rng == expected_range {
                return;
            }
            self.calc_range(jt, data, self.path_meld.get_varnode(index), &mut rng);
            let size = rng.get_size();
            if size > maxsize {
                continue;
            }
            if size == maxsize && !self.is_preferred_range(data, index, &rng) {
                continue;
            }
            self.varnode_index = index;
            maxsize = size;
            let vn = self.path_meld.get_varnode(index);
            let op = self.path_meld.get_earliest_op(index);
            self.range_values_mut().set_range(&rng, vn, op);
        }
        let selected = self.path_meld.get_varnode(self.varnode_index);
        if maxsize == 256
            && data.vn(selected).get_size() == 1
            && !self.path_meld.is_load_in_path(data, self.varnode_index)
        {
            let vn0 = self.path_meld.get_varnode(0);
            rng.set_full(data.vn(vn0).get_size());
            let op0 = self.path_meld.get_op(0);
            self.range_values_mut().set_range(&rng, vn0, Some(op0));
        }
    }

    pub fn find_normalized(
        &mut self,
        jt: &JumpTable,
        data: &mut Funcdata,
        glb: &mut Architecture,
        rootbl: BlockId,
        pathout: i32,
        previous: Option<&dyn JumpModel>,
        maxtablesize: u32,
    ) -> Result<()> {
        self.analyze_guards(jt, data, rootbl, pathout);
        self.find_smallest_normal(jt, data, previous.and_then(|model| model.as_jump_basic()));
        let size = self.jrange_ref().get_size();
        if size > maxtablesize as u64 && self.path_meld.num_common_varnode() == 1 {
            let vn = self.path_meld.get_varnode(0);
            if data.vn(vn).is_read_only() {
                let loader = glb.loader.as_ref().expect("missing load image").clone();
                let spc = data.vn(vn).get_space().expect("varnode has no space").clone();
                let mut mem = MemoryImage::new(spc, 4, 16, loader.as_ref());
                let val = mem.get_value(data.vn(vn).get_offset(), data.vn(vn).get_size())?;
                self.varnode_index = 0;
                let rng = CircleRange::new_single(val, data.vn(vn).get_size());
                let op0 = self.path_meld.get_op(0);
                self.range_values_mut().set_range(&rng, vn, Some(op0));
            }
        }
        Ok(())
    }

    pub fn mark_foldable_guards(&mut self, data: &mut Funcdata) {
        let vn = self.path_meld.get_varnode(self.varnode_index);
        let mut bits_preserved = 0;
        let base_vn = GuardRecord::quasi_copy(data, vn, &mut bits_preserved);
        for guard in self.selectguards.iter_mut() {
            if guard.value_match(data, vn, base_vn, bits_preserved) == 0 || guard.is_unrolled() {
                guard.clear();
            }
        }
    }

    pub fn mark_model(&self, data: &mut Funcdata, val: bool) {
        self.path_meld.mark_paths(data, val, self.varnode_index);
        for guard in self.selectguards.iter() {
            if guard.get_branch().is_none() {
                continue;
            }
            let read_op = guard.get_read_op();
            if val {
                data.op_mut(read_op).set_mark();
            } else {
                data.op_mut(read_op).clear_mark();
            }
        }
    }

    pub fn flows_only_to_model(&self, data: &Funcdata, vn: VarnodeId, trail_op: Option<OpId>) -> bool {
        for &op in data.vn(vn).descend() {
            if Some(op) == trail_op {
                continue;
            }
            if !data.op(op).is_mark() {
                return false;
            }
        }
        true
    }

    pub fn check_common_cbranch(&self, data: &Funcdata, var_array: &mut Vec<VarnodeId>, bl: BlockId) -> bool {
        let cur_block = data.block(bl).get_in(0);
        let op = match last_op_of(data, cur_block) {
            Some(op) if data.op(op).code() == OpCode::Cbranch => op,
            _ => return false,
        };
        let outslot = data.block(bl).get_in_rev_index(0);
        let is_op_flip = data.op(op).is_boolean_flip();
        var_array.push(data.op(op).get_in(1));
        for index in 1..data.block(bl).size_in() {
            let cur_block = data.block(bl).get_in(index);
            let op = match last_op_of(data, cur_block) {
                Some(op) if data.op(op).code() == OpCode::Cbranch => op,
                _ => return false,
            };
            if data.op(op).is_boolean_flip() != is_op_flip {
                return false;
            }
            if outslot != data.block(bl).get_in_rev_index(index) {
                return false;
            }
            var_array.push(data.op(op).get_in(1));
        }
        true
    }

    pub fn check_unrolled_guard(
        &mut self,
        _jt: &JumpTable,
        data: &mut Funcdata,
        bl: BlockId,
        maxpullback: i32,
        usenzmask: bool,
    ) {
        let mut var_array: Vec<VarnodeId> = Vec::new();
        if !self.check_common_cbranch(data, &mut var_array, bl) {
            return;
        }
        let indpath = data.block(bl).get_in_rev_index(0);
        let mut toswitchval = indpath == 1;
        let inbl = data.block(bl).get_in(0);
        let cbranch = last_op_of(data, inbl).expect("guard block has no CBRANCH");
        if data.op(cbranch).is_boolean_flip() {
            toswitchval = !toswitchval;
        }
        let mut rng = CircleRange::new_bool(toswitchval);
        let indpathstore = if data.block(inbl).get_flip_path() {
            1 - indpath
        } else {
            indpath
        };
        let read_op = cbranch;
        for _ in 0..maxpullback {
            if JumpBasic::duplicate_varnodes(&var_array) {
                self.selectguards.push(GuardRecord::new(
                    data,
                    cbranch,
                    read_op,
                    indpathstore,
                    &rng,
                    var_array[0],
                    true,
                ));
            } else if let Some(multi_op) = data.block_find_multiequal(bl, &var_array) {
                let outvn = data.op(multi_op).get_out().expect("MULTIEQUAL has no output");
                self.selectguards.push(GuardRecord::new(
                    data,
                    cbranch,
                    read_op,
                    indpathstore,
                    &rng,
                    outvn,
                    true,
                ));
            }
            let vn = var_array[0];
            if !data.vn(vn).is_written() {
                break;
            }
            let read_op = data.vn(vn).get_def().expect("written varnode has no defining op");
            let mut markup: Option<VarnodeId> = None;
            let vn = match rng.pull_back(read_op, Some(&mut markup), usenzmask, data) {
                Some(next) => next,
                None => break,
            };
            if rng.is_empty() {
                break;
            }
            let slot = data.op(read_op).get_slot(vn);
            if !data.block_lift_verify_unroll(&mut var_array, slot) {
                break;
            }
        }
    }

    pub fn fold_in_one_guard_basic(
        &mut self,
        data: &mut Funcdata,
        glb: &mut Architecture,
        guard: usize,
        jump: &mut JumpTable,
    ) -> Result<bool> {
        let cbranch = self.selectguards[guard].get_branch().expect("guard has no branch");
        let cbranchblock = parent_of(data, cbranch);
        if data.block(cbranchblock).size_out() != 2 {
            return Ok(false);
        }
        let mut indpath = self.selectguards[guard].get_path();
        if data.block(cbranchblock).get_flip_path() {
            indpath = 1 - indpath;
        }
        let switchbl = parent_of(data, jump.get_indirect_op().expect("jump table has no indirect op"));
        if data.block(cbranchblock).get_out(indpath) != switchbl {
            return Ok(false);
        }
        let guardtarget = data.block(cbranchblock).get_out(1 - indpath);
        let mut pos = 0;
        while pos < data.block(switchbl).size_out() {
            if data.block(switchbl).get_out(pos) == guardtarget {
                break;
            }
            pos += 1;
        }
        if jump.has_folded_default() && jump.get_default_block() != pos {
            return Ok(false);
        }
        if !data.block_no_intervening_statement(switchbl) {
            return Ok(false);
        }
        if pos == data.block(switchbl).size_out() {
            jump.add_block_to_switch(data, guardtarget, NO_LABEL);
            jump.set_last_as_default();
            data.push_branch(cbranchblock, 1 - indpath, switchbl, glb)?;
        } else {
            let val = if (indpath == 0) != data.op(cbranch).is_boolean_flip() {
                0
            } else {
                1
            };
            let size = data.vn(data.op(cbranch).get_in(0)).get_size();
            let constvn = data.new_constant(size, val, glb);
            data.op_set_input(cbranch, constvn, 1)?;
            jump.set_default_block(pos);
        }
        jump.set_folded_default();
        self.selectguards[guard].clear();
        Ok(true)
    }

    pub fn fold_in_guards_generic(
        model: &mut dyn JumpBasicModel,
        data: &mut Funcdata,
        glb: &mut Architecture,
        jump: &mut JumpTable,
    ) -> Result<bool> {
        let mut change = false;
        for index in 0..model.jump_basic().selectguards.len() {
            let cbranch = match model.jump_basic().selectguards[index].get_branch() {
                Some(cbranch) => cbranch,
                None => continue,
            };
            if data.op(cbranch).is_dead() {
                model.jump_basic_mut().selectguards[index].clear();
                continue;
            }
            if model.fold_in_one_guard(data, glb, index, jump)? {
                change = true;
            }
        }
        Ok(change)
    }

    pub fn get_path_meld(&self) -> &PathMeld {
        &self.path_meld
    }

    pub fn get_value_range(&self) -> Option<&JumpValuesRange> {
        self.jrange.as_ref().and_then(|jrange| jrange.as_values_range())
    }

    pub fn recover_model_basic(
        &mut self,
        jt: &JumpTable,
        data: &mut Funcdata,
        glb: &mut Architecture,
        indop: OpId,
        previous: Option<&dyn JumpModel>,
        maxtablesize: u32,
    ) -> Result<bool> {
        self.jrange = Some(Box::new(JumpValuesRange::new()));
        self.find_determining_varnodes(data, indop, 0);
        let rootbl = parent_of(data, indop);
        self.find_normalized(jt, data, glb, rootbl, -1, previous, maxtablesize)?;
        if self.jrange_ref().get_size() > maxtablesize as u64 {
            return Ok(false);
        }
        self.mark_foldable_guards(data);
        Ok(true)
    }

    pub fn build_addresses_basic(
        &self,
        data: &mut Funcdata,
        glb: &mut Architecture,
        indop: OpId,
        addresstable: &mut Vec<Address>,
        loadpoints: Option<&mut Vec<LoadTable>>,
        loadcounts: Option<&mut Vec<i32>>,
    ) -> Result<()> {
        addresstable.clear();
        let mut emul = EmulateFunction::new();
        let mut loadpoints = loadpoints;
        let mut loadcounts = loadcounts;
        if loadpoints.is_some() {
            emul.set_load_collect(Some(Vec::new()));
        }
        let mut mask = !0u64;
        let bit = glb.funcptr_align;
        if bit != 0 {
            mask = mask.wrapping_shr(bit as u32).wrapping_shl(bit as u32);
        }
        let spc = data
            .op(indop)
            .get_addr()
            .get_space()
            .expect("BRANCHIND address has no space")
            .clone();
        let jrange = self.jrange_ref();
        let mut notdone = jrange.initialize_for_reading();
        while notdone {
            let val = jrange.get_value();
            let startop = jrange.get_start_op().expect("jump table range has no start op");
            let startvn = jrange
                .get_start_varnode()
                .expect("jump table range has no start varnode");
            let result = emul.emulate_path(data, glb, val, &self.path_meld, startop, startvn);
            if let Some(external) = loadpoints.as_deref_mut()
                && let Some(collected) = emul.loadpoints.as_mut()
            {
                external.append(collected);
            }
            let mut addr = result?;
            addr = AddrSpace::address_to_byte(addr, spc.get_word_size());
            addr &= mask;
            addresstable.push(Address::new(spc.clone(), addr));
            if let Some(counts) = loadcounts.as_deref_mut() {
                let size = loadpoints.as_deref().map(|points| points.len()).unwrap_or(0);
                counts.push(size as i32);
            }
            notdone = jrange.next();
        }
        Ok(())
    }

    pub fn find_unnormalized_basic(
        &mut self,
        data: &mut Funcdata,
        maxaddsub: u32,
        _maxleftright: u32,
        maxext: u32,
    ) -> Result<()> {
        let mut index = self.varnode_index;
        self.normalvn = Some(self.path_meld.get_varnode(index));
        index += 1;
        self.switchvn = self.normalvn;
        self.mark_model(data, true);
        let mut countaddsub: u32 = 0;
        let mut countext: u32 = 0;
        let mut normop: Option<OpId> = None;
        while index < self.path_meld.num_common_varnode() {
            let switchvn = self.switchvn.expect("switch variable is missing");
            if !self.flows_only_to_model(data, switchvn, normop) {
                break;
            }
            let testvn = self.path_meld.get_varnode(index);
            if !data.vn(switchvn).is_written() {
                break;
            }
            let curop = data.vn(switchvn).get_def().expect("written varnode has no defining op");
            normop = Some(curop);
            let mut slot = 0;
            while slot < data.op(curop).num_input() {
                if data.op(curop).get_in(slot) == testvn {
                    break;
                }
                slot += 1;
            }
            if slot == data.op(curop).num_input() {
                break;
            }
            match data.op(curop).code() {
                OpCode::IntAdd | OpCode::IntSub => {
                    countaddsub += 1;
                    if countaddsub <= maxaddsub && data.vn(data.op(curop).get_in(1 - slot)).is_constant() {
                        self.switchvn = Some(testvn);
                    }
                }
                OpCode::IntZext | OpCode::IntSext => {
                    countext += 1;
                    if countext <= maxext {
                        self.switchvn = Some(testvn);
                    }
                }
                _ => {}
            }
            if self.switchvn != Some(testvn) {
                break;
            }
            index += 1;
        }
        self.mark_model(data, false);
        Ok(())
    }

    pub fn build_labels_basic(
        &self,
        data: &mut Funcdata,
        glb: &mut Architecture,
        addresstable: &mut [Address],
        label: &mut Vec<u64>,
        orig: &dyn JumpModel,
    ) -> Result<()> {
        let origrange: &dyn JumpValues = orig
            .as_jump_basic()
            .and_then(|basic| basic.jrange.as_deref())
            .expect("original jump model has no value range");
        let mut notdone = origrange.initialize_for_reading();
        while notdone {
            let val = origrange.get_value();
            let mut needswarning = 0;
            let switchval;
            if origrange.is_reversible() {
                if !self.jrange_ref().contains(val) {
                    needswarning = 1;
                }
                let normalvn = self.normalvn.expect("normalized switch variable is missing");
                let switchvn = self.switchvn.expect("switch variable is missing");
                switchval = match JumpBasic::backup2_switch(data, glb, val, normalvn, switchvn) {
                    Ok(switchval) => switchval,
                    Err(Error::Evaluation(_)) => {
                        needswarning = 2;
                        NO_LABEL
                    }
                    Err(err) => return Err(err),
                };
            } else {
                switchval = NO_LABEL;
            }
            if needswarning == 1 {
                data.warning(
                    "This code block may not be properly labeled as switch case",
                    &addresstable[label.len()],
                    glb,
                );
            } else if needswarning == 2 {
                data.warning("Calculation of case label failed", &addresstable[label.len()], glb);
            }
            label.push(switchval);
            if label.len() >= addresstable.len() {
                break;
            }
            notdone = origrange.next();
        }
        while label.len() < addresstable.len() {
            data.warning("Bad switch case", &addresstable[label.len()], glb);
            label.push(NO_LABEL);
        }
        Ok(())
    }

    pub fn fold_in_normalization_basic(
        &mut self,
        data: &mut Funcdata,
        _glb: &mut Architecture,
        indop: OpId,
    ) -> Result<Option<VarnodeId>> {
        let switchvn = self.switchvn.expect("switch variable is missing");
        data.op_set_input(indop, switchvn, 0)?;
        Ok(self.switchvn)
    }

    pub fn sanity_check_basic(
        &mut self,
        data: &mut Funcdata,
        glb: &mut Architecture,
        _indop: OpId,
        addresstable: &mut Vec<Address>,
        loadpoints: &mut Vec<LoadTable>,
        loadcounts: Option<&mut Vec<i32>>,
    ) -> Result<bool> {
        if addresstable.is_empty() {
            return Ok(true);
        }
        let addr = addresstable[0].clone();
        let mut index = 0;
        if addr.get_offset() != 0 {
            index = 1;
            while index < addresstable.len() {
                let offset = addresstable[index].get_offset();
                if offset == 0 {
                    break;
                }
                let diff = if addr.get_offset() < offset {
                    offset - addr.get_offset()
                } else {
                    addr.get_offset() - offset
                };
                if diff > 0xffff {
                    let mut buffer = [0u8; 8];
                    let loader = glb.loader.as_ref().expect("missing load image").clone();
                    let dataavail = match loader.load_fill(&mut buffer[..4], &addresstable[index]) {
                        Ok(()) => true,
                        Err(Error::DataUnavail(_)) => false,
                        Err(err) => return Err(err),
                    };
                    if !dataavail {
                        break;
                    }
                }
                index += 1;
            }
        }
        let _ = data;
        if index == 0 {
            return Ok(false);
        }
        if index != addresstable.len() {
            addresstable.truncate(index);
            self.jrange
                .as_mut()
                .expect("jump table range is not recovered")
                .truncate(index as i32);
            if let Some(counts) = loadcounts {
                loadpoints.resize(counts[index - 1] as usize, LoadTable::default());
            }
        }
        Ok(true)
    }

    pub fn clear_basic(&mut self) {
        self.jrange = None;
        self.path_meld.clear();
        self.selectguards.clear();
        self.normalvn = None;
        self.switchvn = None;
    }
}

impl JumpBasicModel for JumpBasic {
    fn jump_basic(&self) -> &JumpBasic {
        self
    }

    fn jump_basic_mut(&mut self) -> &mut JumpBasic {
        self
    }

    fn fold_in_one_guard(
        &mut self,
        data: &mut Funcdata,
        glb: &mut Architecture,
        guard: usize,
        jump: &mut JumpTable,
    ) -> Result<bool> {
        self.fold_in_one_guard_basic(data, glb, guard, jump)
    }
}

impl JumpModel for JumpBasic {
    fn is_override(&self) -> bool {
        false
    }

    fn get_table_size(&self) -> i32 {
        self.jrange_ref().get_size() as i32
    }

    fn recover_model(
        &mut self,
        jt: &JumpTable,
        data: &mut Funcdata,
        glb: &mut Architecture,
        indop: OpId,
        previous: Option<&dyn JumpModel>,
        maxtablesize: u32,
    ) -> Result<bool> {
        self.recover_model_basic(jt, data, glb, indop, previous, maxtablesize)
    }

    fn build_addresses(
        &self,
        data: &mut Funcdata,
        glb: &mut Architecture,
        indop: OpId,
        addresstable: &mut Vec<Address>,
        loadpoints: Option<&mut Vec<LoadTable>>,
        loadcounts: Option<&mut Vec<i32>>,
    ) -> Result<()> {
        self.build_addresses_basic(data, glb, indop, addresstable, loadpoints, loadcounts)
    }

    fn find_unnormalized(&mut self, data: &mut Funcdata, maxaddsub: u32, maxleftright: u32, maxext: u32) -> Result<()> {
        self.find_unnormalized_basic(data, maxaddsub, maxleftright, maxext)
    }

    fn build_labels(
        &self,
        data: &mut Funcdata,
        glb: &mut Architecture,
        addresstable: &mut Vec<Address>,
        label: &mut Vec<u64>,
        orig: &dyn JumpModel,
    ) -> Result<()> {
        self.build_labels_basic(data, glb, addresstable, label, orig)
    }

    fn fold_in_normalization(
        &mut self,
        data: &mut Funcdata,
        glb: &mut Architecture,
        indop: OpId,
    ) -> Result<Option<VarnodeId>> {
        self.fold_in_normalization_basic(data, glb, indop)
    }

    fn fold_in_guards(&mut self, data: &mut Funcdata, glb: &mut Architecture, jump: &mut JumpTable) -> Result<bool> {
        JumpBasic::fold_in_guards_generic(self, data, glb, jump)
    }

    fn sanity_check(
        &mut self,
        data: &mut Funcdata,
        glb: &mut Architecture,
        indop: OpId,
        addresstable: &mut Vec<Address>,
        loadpoints: &mut Vec<LoadTable>,
        loadcounts: Option<&mut Vec<i32>>,
    ) -> Result<bool> {
        self.sanity_check_basic(data, glb, indop, addresstable, loadpoints, loadcounts)
    }

    fn clone_model(&self) -> Box<dyn JumpModel> {
        let mut res = JumpBasic::new();
        res.jrange = self.jrange.as_ref().map(|jrange| jrange.clone_values());
        Box::new(res)
    }

    fn clear(&mut self) {
        self.clear_basic();
    }

    fn as_jump_basic(&self) -> Option<&JumpBasic> {
        Some(self)
    }
}

pub struct JumpBasic2 {
    pub basic: JumpBasic,
    pub extravn: Option<VarnodeId>,
    pub orig_path_meld: PathMeld,
}

impl Default for JumpBasic2 {
    fn default() -> JumpBasic2 {
        JumpBasic2::new()
    }
}

impl JumpBasic2 {
    pub fn new() -> JumpBasic2 {
        JumpBasic2 {
            basic: JumpBasic::new(),
            extravn: None,
            orig_path_meld: PathMeld::default(),
        }
    }

    pub fn check_normal_dominance(&self, data: &Funcdata) -> bool {
        let normalvn = self.basic.normalvn.expect("normalized switch variable is missing");
        if data.vn(normalvn).is_input() {
            return true;
        }
        let defblock = parent_of(
            data,
            data.vn(normalvn)
                .get_def()
                .expect("normalized switch variable has no def"),
        );
        let mut switchblock = data.op(self.basic.path_meld.get_op(0)).get_parent();
        while let Some(block) = switchblock {
            if block == defblock {
                return true;
            }
            switchblock = data.block(block).get_immed_dom();
        }
        false
    }

    pub fn initialize_start(&mut self, p_meld: &PathMeld) {
        if p_meld.empty() {
            self.extravn = None;
            return;
        }
        self.extravn = Some(p_meld.get_varnode(p_meld.num_common_varnode() - 1));
        self.orig_path_meld.set(p_meld);
    }
}

impl JumpBasicModel for JumpBasic2 {
    fn jump_basic(&self) -> &JumpBasic {
        &self.basic
    }

    fn jump_basic_mut(&mut self) -> &mut JumpBasic {
        &mut self.basic
    }

    fn fold_in_one_guard(
        &mut self,
        _data: &mut Funcdata,
        _glb: &mut Architecture,
        guard: usize,
        jump: &mut JumpTable,
    ) -> Result<bool> {
        jump.set_last_as_default();
        self.basic.selectguards[guard].clear();
        Ok(true)
    }
}

impl JumpModel for JumpBasic2 {
    fn is_override(&self) -> bool {
        false
    }

    fn get_table_size(&self) -> i32 {
        self.basic.get_table_size()
    }

    fn recover_model(
        &mut self,
        jt: &JumpTable,
        data: &mut Funcdata,
        glb: &mut Architecture,
        _indop: OpId,
        previous: Option<&dyn JumpModel>,
        maxtablesize: u32,
    ) -> Result<bool> {
        let mut extravalue: u64 = 0;
        let joinvn = match self.extravn {
            Some(joinvn) => joinvn,
            None => return Ok(false),
        };
        if !data.vn(joinvn).is_written() {
            return Ok(false);
        }
        let multiop = data.vn(joinvn).get_def().expect("written varnode has no defining op");
        if data.op(multiop).code() != OpCode::Multiequal {
            return Ok(false);
        }
        if data.op(multiop).num_input() != 2 {
            return Ok(false);
        }
        let mut path = 0;
        while path < 2 {
            let vn = data.op(multiop).get_in(path);
            if data.vn(vn).is_written() {
                let copyop = data.vn(vn).get_def().expect("written varnode has no defining op");
                if data.op(copyop).code() == OpCode::Copy {
                    let othervn = data.op(copyop).get_in(0);
                    if data.vn(othervn).is_constant() {
                        extravalue = data.vn(othervn).get_offset();
                        break;
                    }
                }
            }
            path += 1;
        }
        if path == 2 {
            return Ok(false);
        }
        let multibl = parent_of(data, multiop);
        let rootbl = data.block(multibl).get_in(1 - path);
        let pathout = data.block(multibl).get_in_rev_index(1 - path);
        let mut jdef = JumpValuesRangeDefault::new();
        jdef.set_extra_value(extravalue);
        jdef.set_default_vn(joinvn);
        jdef.set_default_op(self.orig_path_meld.get_op(self.orig_path_meld.num_ops() - 1));
        self.basic.jrange = Some(Box::new(jdef));
        self.basic.find_determining_varnodes(data, multiop, 1 - path);
        self.basic
            .find_normalized(jt, data, glb, rootbl, pathout, previous, maxtablesize)?;
        if self.basic.jrange_ref().get_size() > maxtablesize as u64 {
            return Ok(false);
        }
        self.basic.path_meld.append(&self.orig_path_meld);
        self.basic.varnode_index += self.orig_path_meld.num_common_varnode();
        Ok(true)
    }

    fn build_addresses(
        &self,
        data: &mut Funcdata,
        glb: &mut Architecture,
        indop: OpId,
        addresstable: &mut Vec<Address>,
        loadpoints: Option<&mut Vec<LoadTable>>,
        loadcounts: Option<&mut Vec<i32>>,
    ) -> Result<()> {
        self.basic
            .build_addresses_basic(data, glb, indop, addresstable, loadpoints, loadcounts)
    }

    fn find_unnormalized(&mut self, data: &mut Funcdata, maxaddsub: u32, maxleftright: u32, maxext: u32) -> Result<()> {
        self.basic.normalvn = Some(self.basic.path_meld.get_varnode(self.basic.varnode_index));
        if self.check_normal_dominance(data) {
            return self
                .basic
                .find_unnormalized_basic(data, maxaddsub, maxleftright, maxext);
        }
        let extravn = self.extravn.expect("join varnode is missing");
        self.basic.switchvn = Some(extravn);
        let multiop = data.vn(extravn).get_def().expect("join varnode has no defining op");
        let normalvn = self.basic.normalvn;
        if Some(data.op(multiop).get_in(0)) == normalvn || Some(data.op(multiop).get_in(1)) == normalvn {
            self.basic.normalvn = self.basic.switchvn;
            Ok(())
        } else {
            Err(Error::Lowlevel("Backward normalization not implemented".to_string()))
        }
    }

    fn build_labels(
        &self,
        data: &mut Funcdata,
        glb: &mut Architecture,
        addresstable: &mut Vec<Address>,
        label: &mut Vec<u64>,
        orig: &dyn JumpModel,
    ) -> Result<()> {
        self.basic.build_labels_basic(data, glb, addresstable, label, orig)
    }

    fn fold_in_normalization(
        &mut self,
        data: &mut Funcdata,
        glb: &mut Architecture,
        indop: OpId,
    ) -> Result<Option<VarnodeId>> {
        self.basic.fold_in_normalization_basic(data, glb, indop)
    }

    fn fold_in_guards(&mut self, data: &mut Funcdata, glb: &mut Architecture, jump: &mut JumpTable) -> Result<bool> {
        JumpBasic::fold_in_guards_generic(self, data, glb, jump)
    }

    fn sanity_check(
        &mut self,
        data: &mut Funcdata,
        glb: &mut Architecture,
        indop: OpId,
        addresstable: &mut Vec<Address>,
        loadpoints: &mut Vec<LoadTable>,
        loadcounts: Option<&mut Vec<i32>>,
    ) -> Result<bool> {
        self.basic
            .sanity_check_basic(data, glb, indop, addresstable, loadpoints, loadcounts)
    }

    fn clone_model(&self) -> Box<dyn JumpModel> {
        let mut res = JumpBasic2::new();
        res.basic.jrange = self.basic.jrange.as_ref().map(|jrange| jrange.clone_values());
        Box::new(res)
    }

    fn clear(&mut self) {
        self.extravn = None;
        self.orig_path_meld.clear();
        self.basic.clear_basic();
    }

    fn as_jump_basic(&self) -> Option<&JumpBasic> {
        Some(&self.basic)
    }
}

pub struct JumpBasicOverride {
    pub basic: JumpBasic,
    pub adset: BTreeSet<Address>,
    pub values: Vec<u64>,
    pub addrtable: Vec<Address>,
    pub startingvalue: u64,
    pub normaddress: Address,
    pub hash: u64,
    pub istrivial: bool,
}

impl Default for JumpBasicOverride {
    fn default() -> JumpBasicOverride {
        JumpBasicOverride::new()
    }
}

impl JumpBasicOverride {
    pub fn new() -> JumpBasicOverride {
        JumpBasicOverride {
            basic: JumpBasic::new(),
            adset: BTreeSet::new(),
            values: Vec::new(),
            addrtable: Vec::new(),
            startingvalue: 0,
            normaddress: Address::invalid(),
            hash: 0,
            istrivial: false,
        }
    }

    pub fn find_start_op(&mut self, data: &mut Funcdata, vn: VarnodeId) -> i32 {
        let descend = data.vn(vn).descend().to_vec();
        for &op in descend.iter() {
            data.op_mut(op).set_mark();
        }
        let mut res = -1;
        for index in 0..self.basic.path_meld.num_ops() {
            if data.op(self.basic.path_meld.get_op(index)).is_mark() {
                res = index;
                break;
            }
        }
        for &op in descend.iter() {
            data.op_mut(op).clear_mark();
        }
        res
    }

    pub fn trial_norm(
        &mut self,
        data: &mut Funcdata,
        glb: &mut Architecture,
        trialvn: VarnodeId,
        tolerance: u32,
    ) -> Result<i32> {
        let opi = self.find_start_op(data, trialvn);
        if opi < 0 {
            return Ok(-1);
        }
        let startop = self.basic.path_meld.get_op(opi);
        if !self.values.is_empty() {
            return Ok(opi);
        }
        let mut emul = EmulateFunction::new();
        let spc = data
            .op(startop)
            .get_addr()
            .get_space()
            .expect("op address has no space")
            .clone();
        let mut val = self.startingvalue;
        let mut total: u32 = 0;
        let mut miss: u32 = 0;
        let mut alreadyseen: BTreeSet<Address> = BTreeSet::new();
        while (total as usize) < self.adset.len() {
            let mut addr = match emul.emulate_path(data, glb, val, &self.basic.path_meld, startop, trialvn) {
                Ok(addr) => addr,
                Err(err) if err.is_lowlevel() => {
                    miss = tolerance;
                    0
                }
                Err(err) => return Err(err),
            };
            addr = AddrSpace::address_to_byte(addr, spc.get_word_size());
            let newaddr = Address::new(spc.clone(), addr);
            if self.adset.contains(&newaddr) {
                if alreadyseen.insert(newaddr.clone()) {
                    total += 1;
                }
                self.values.push(val);
                self.addrtable.push(newaddr);
                if self.values.len() > self.adset.len() + 100 {
                    break;
                }
                miss = 0;
            } else {
                miss += 1;
                if miss >= tolerance {
                    break;
                }
            }
            val = val.wrapping_add(1);
        }
        if total as usize == self.adset.len() {
            return Ok(opi);
        }
        self.values.clear();
        self.addrtable.clear();
        Ok(-1)
    }

    pub fn setup_trivial(&mut self) {
        if self.addrtable.is_empty() {
            for addr in self.adset.iter() {
                self.addrtable.push(addr.clone());
            }
        }
        self.values.clear();
        for addr in self.addrtable.iter() {
            self.values.push(addr.get_offset());
        }
        self.basic.varnode_index = 0;
        self.basic.normalvn = Some(self.basic.path_meld.get_varnode(0));
        self.istrivial = true;
    }

    pub fn find_likely_norm(&mut self, data: &Funcdata) -> Option<VarnodeId> {
        let meld = &self.basic.path_meld;
        let mut res: Option<VarnodeId> = None;
        let mut index = 0;
        while index < meld.num_ops() {
            let op = meld.get_op(index);
            if data.op(op).code() == OpCode::Load {
                res = Some(meld.get_op_parent(index));
                break;
            }
            index += 1;
        }
        res?;
        index += 1;
        while index < meld.num_ops() {
            let op = meld.get_op(index);
            if data.op(op).code() == OpCode::IntAdd {
                res = Some(meld.get_op_parent(index));
                break;
            }
            index += 1;
        }
        index += 1;
        while index < meld.num_ops() {
            let op = meld.get_op(index);
            if data.op(op).code() == OpCode::IntMult {
                res = Some(meld.get_op_parent(index));
                break;
            }
            index += 1;
        }
        res
    }

    pub fn clear_copy_specific(&mut self) {
        self.basic.selectguards.clear();
        self.basic.path_meld.clear();
        self.basic.normalvn = None;
        self.basic.switchvn = None;
    }

    pub fn set_addresses(&mut self, adtable: &[Address]) {
        for addr in adtable.iter() {
            self.adset.insert(addr.clone());
        }
    }

    pub fn set_norm(&mut self, addr: &Address, hash: u64) {
        self.normaddress = addr.clone();
        self.hash = hash;
    }

    pub fn set_starting_value(&mut self, val: u64) {
        self.startingvalue = val;
    }
}

impl JumpModel for JumpBasicOverride {
    fn is_override(&self) -> bool {
        true
    }

    fn get_table_size(&self) -> i32 {
        self.addrtable.len() as i32
    }

    fn recover_model(
        &mut self,
        _jt: &JumpTable,
        data: &mut Funcdata,
        glb: &mut Architecture,
        indop: OpId,
        _previous: Option<&dyn JumpModel>,
        _maxtablesize: u32,
    ) -> Result<bool> {
        self.clear_copy_specific();
        self.basic.find_determining_varnodes(data, indop, 0);
        if !self.istrivial {
            let mut trialvn: Option<VarnodeId> = None;
            if self.hash != 0 {
                let mut dyn_hash = DynamicHash::new();
                trialvn = dyn_hash.find_varnode(data, &self.normaddress, self.hash);
            }
            if trialvn.is_none() && (self.values.is_empty() || self.hash == 0) {
                trialvn = self.find_likely_norm(data);
            }
            if let Some(trialvn) = trialvn {
                let opi = self.trial_norm(data, glb, trialvn, 10)?;
                if opi >= 0 {
                    self.basic.varnode_index = opi;
                    self.basic.normalvn = Some(trialvn);
                    return Ok(true);
                }
            }
        }
        self.setup_trivial();
        Ok(true)
    }

    fn build_addresses(
        &self,
        _data: &mut Funcdata,
        _glb: &mut Architecture,
        _indop: OpId,
        addresstable: &mut Vec<Address>,
        _loadpoints: Option<&mut Vec<LoadTable>>,
        _loadcounts: Option<&mut Vec<i32>>,
    ) -> Result<()> {
        *addresstable = self.addrtable.clone();
        Ok(())
    }

    fn find_unnormalized(&mut self, data: &mut Funcdata, maxaddsub: u32, maxleftright: u32, maxext: u32) -> Result<()> {
        self.basic
            .find_unnormalized_basic(data, maxaddsub, maxleftright, maxext)
    }

    fn build_labels(
        &self,
        data: &mut Funcdata,
        glb: &mut Architecture,
        addresstable: &mut Vec<Address>,
        label: &mut Vec<u64>,
        _orig: &dyn JumpModel,
    ) -> Result<()> {
        for &value in self.values.iter() {
            let normalvn = self.basic.normalvn.expect("normalized switch variable is missing");
            let switchvn = self.basic.switchvn.expect("switch variable is missing");
            let addr = match JumpBasic::backup2_switch(data, glb, value, normalvn, switchvn) {
                Ok(addr) => addr,
                Err(Error::Evaluation(_)) => NO_LABEL,
                Err(err) => return Err(err),
            };
            label.push(addr);
            if label.len() >= addresstable.len() {
                break;
            }
        }
        while label.len() < addresstable.len() {
            data.warning("Bad switch case", &addresstable[label.len()], glb);
            label.push(NO_LABEL);
        }
        Ok(())
    }

    fn fold_in_normalization(
        &mut self,
        data: &mut Funcdata,
        glb: &mut Architecture,
        indop: OpId,
    ) -> Result<Option<VarnodeId>> {
        self.basic.fold_in_normalization_basic(data, glb, indop)
    }

    fn fold_in_guards(&mut self, _data: &mut Funcdata, _glb: &mut Architecture, _jump: &mut JumpTable) -> Result<bool> {
        Ok(false)
    }

    fn sanity_check(
        &mut self,
        _data: &mut Funcdata,
        _glb: &mut Architecture,
        _indop: OpId,
        _addresstable: &mut Vec<Address>,
        _loadpoints: &mut Vec<LoadTable>,
        _loadcounts: Option<&mut Vec<i32>>,
    ) -> Result<bool> {
        Ok(true)
    }

    fn clone_model(&self) -> Box<dyn JumpModel> {
        let mut res = JumpBasicOverride::new();
        res.adset = self.adset.clone();
        res.values = self.values.clone();
        res.addrtable = self.addrtable.clone();
        res.startingvalue = self.startingvalue;
        res.normaddress = self.normaddress.clone();
        res.hash = self.hash;
        Box::new(res)
    }

    fn clear(&mut self) {
        self.values.clear();
        self.addrtable.clear();
        self.istrivial = false;
    }

    fn encode(&self, encoder: &mut dyn Encoder) -> Result<()> {
        encoder.open_element(ELEM_BASICOVERRIDE);
        for addr in self.adset.iter() {
            encoder.open_element(ELEM_DEST);
            let spc = addr.get_space().expect("override address has no space");
            spc.encode_attributes(encoder, addr.get_offset())?;
            encoder.close_element(ELEM_DEST);
        }
        if self.hash != 0 {
            encoder.open_element(ELEM_NORMADDR);
            let spc = self.normaddress.get_space().expect("normalized address has no space");
            spc.encode_attributes(encoder, self.normaddress.get_offset())?;
            encoder.close_element(ELEM_NORMADDR);
            encoder.open_element(ELEM_NORMHASH);
            encoder.write_unsigned_integer(ATTRIB_CONTENT, self.hash);
            encoder.close_element(ELEM_NORMHASH);
        }
        if self.startingvalue != 0 {
            encoder.open_element(ELEM_STARTVAL);
            encoder.write_unsigned_integer(ATTRIB_CONTENT, self.startingvalue);
            encoder.close_element(ELEM_STARTVAL);
        }
        encoder.close_element(ELEM_BASICOVERRIDE);
        Ok(())
    }

    fn decode(&mut self, decoder: &mut dyn Decoder) -> Result<()> {
        let elem_id = decoder.open_element_expect(ELEM_BASICOVERRIDE)?;
        loop {
            let sub_id = decoder.open_element()?;
            if sub_id == 0 {
                break;
            }
            if sub_id == ELEM_DEST {
                let v_data = VarnodeData::decode_from_attributes(decoder)?;
                self.adset.insert(v_data.get_addr());
            } else if sub_id == ELEM_NORMADDR {
                let v_data = VarnodeData::decode_from_attributes(decoder)?;
                self.normaddress = v_data.get_addr();
            } else if sub_id == ELEM_NORMHASH {
                self.hash = decoder.read_unsigned_integer_attr(ATTRIB_CONTENT)?;
            } else if sub_id == ELEM_STARTVAL {
                self.startingvalue = decoder.read_unsigned_integer_attr(ATTRIB_CONTENT)?;
            }
            decoder.close_element(sub_id)?;
        }
        decoder.close_element(elem_id)?;
        if self.adset.is_empty() {
            return Err(Error::Lowlevel("Empty jumptable override".to_string()));
        }
        Ok(())
    }

    fn as_jump_basic(&self) -> Option<&JumpBasic> {
        Some(&self.basic)
    }
}

#[derive(Clone, Debug, Default)]
pub struct JumpAssisted {
    pub assist_op: Option<OpId>,
    pub userop: Option<UserOpId>,
    pub size_indices: i32,
    pub switchvn: Option<VarnodeId>,
}

impl JumpAssisted {
    pub fn new() -> JumpAssisted {
        JumpAssisted {
            assist_op: None,
            userop: None,
            size_indices: 0,
            switchvn: None,
        }
    }

    fn assist_script_inputs(&self, data: &Funcdata) -> Vec<u64> {
        let assist_op = self.assist_op.expect("jumpassist op is missing");
        let num_inputs = data.op(assist_op).num_input() - 1;
        let mut inputs: Vec<u64> = Vec::new();
        for index in 0..num_inputs {
            inputs.push(data.vn(data.op(assist_op).get_in(index + 1)).get_offset());
        }
        inputs
    }

    fn payload_size_input(glb: &Architecture, injectid: i32) -> i32 {
        glb.pcodeinjectlib
            .as_deref()
            .expect("missing p-code inject library")
            .get_payload(injectid)
            .size_input()
    }

    fn assist_data(glb: &Architecture, userop: UserOpId) -> (String, i32, i32, i32, i32) {
        let op = glb
            .userops
            .get_op(userop.0)
            .expect("jumpassist user op is missing")
            .clone();
        let assist = op.as_jump_assist().expect("user op is not a jumpassist");
        (
            op.name.clone(),
            assist.calcsize,
            assist.index2addr,
            assist.index2case,
            assist.defaultaddr,
        )
    }
}

impl JumpModel for JumpAssisted {
    fn is_override(&self) -> bool {
        false
    }

    fn get_table_size(&self) -> i32 {
        self.size_indices + 1
    }

    fn recover_model(
        &mut self,
        _jt: &JumpTable,
        data: &mut Funcdata,
        glb: &mut Architecture,
        indop: OpId,
        previous: Option<&dyn JumpModel>,
        maxtablesize: u32,
    ) -> Result<bool> {
        let addr_vn = data.op(indop).get_in(0);
        if !data.vn(addr_vn).is_written() {
            return Ok(false);
        }
        self.assist_op = data.vn(addr_vn).get_def();
        let assist_op = match self.assist_op {
            Some(assist_op) => assist_op,
            None => return Ok(false),
        };
        if data.op(assist_op).code() != OpCode::Callother {
            return Ok(false);
        }
        if data.op(assist_op).num_input() < 3 {
            return Ok(false);
        }
        let index = data.vn(data.op(assist_op).get_in(0)).get_offset() as i32;
        let tmp_op = glb.userops.get_op(index as u32).expect("user op is missing").clone();
        if tmp_op.get_type() != UserOpType::Jumpassist {
            return Ok(false);
        }
        self.userop = Some(UserOpId(index as u32));
        self.switchvn = Some(data.op(assist_op).get_in(1));
        for slot in 2..data.op(assist_op).num_input() {
            if !data.vn(data.op(assist_op).get_in(slot)).is_constant() {
                return Ok(false);
            }
        }
        let calcsize = tmp_op.as_jump_assist().expect("user op is not a jumpassist").calcsize;
        if calcsize == -1 {
            self.size_indices = data.vn(data.op(assist_op).get_in(2)).get_offset() as i32;
        } else {
            let inputs = self.assist_script_inputs(data);
            if JumpAssisted::payload_size_input(glb, calcsize) != inputs.len() as i32 {
                return Err(Error::Lowlevel(format!(
                    "{}: <size_pcode> has wrong number of parameters",
                    tmp_op.name
                )));
            }
            self.size_indices = evaluate_executable(glb, calcsize, &inputs)? as i32;
        }
        if let Some(previous) = previous
            && previous.get_table_size() - 1 != self.size_indices
        {
            return Ok(false);
        }
        if self.size_indices as u32 > maxtablesize {
            return Ok(false);
        }
        Ok(true)
    }

    fn build_addresses(
        &self,
        data: &mut Funcdata,
        glb: &mut Architecture,
        indop: OpId,
        addresstable: &mut Vec<Address>,
        _loadpoints: Option<&mut Vec<LoadTable>>,
        _loadcounts: Option<&mut Vec<i32>>,
    ) -> Result<()> {
        let (name, _, index2addr, _, defaultaddr) =
            JumpAssisted::assist_data(glb, self.userop.expect("jumpassist user op is missing"));
        if index2addr == -1 {
            return Err(Error::Lowlevel(
                "Final index2addr calculation outside of jumpassist".to_string(),
            ));
        }
        addresstable.clear();
        let spc = data
            .op(indop)
            .get_addr()
            .get_space()
            .expect("BRANCHIND address has no space")
            .clone();
        let mut inputs = self.assist_script_inputs(data);
        if JumpAssisted::payload_size_input(glb, index2addr) != inputs.len() as i32 {
            return Err(Error::Lowlevel(format!(
                "{}: <addr_pcode> has wrong number of parameters",
                name
            )));
        }
        let mut mask = !0u64;
        let bit = glb.funcptr_align;
        if bit != 0 {
            mask = mask.wrapping_shr(bit as u32).wrapping_shl(bit as u32);
        }
        for index in 0..self.size_indices {
            inputs[0] = index as i64 as u64;
            let mut output = evaluate_executable(glb, index2addr, &inputs)?;
            output &= mask;
            addresstable.push(Address::new(spc.clone(), output));
        }
        if JumpAssisted::payload_size_input(glb, defaultaddr) != inputs.len() as i32 {
            return Err(Error::Lowlevel(format!(
                "{}: <default_pcode> has wrong number of parameters",
                name
            )));
        }
        inputs[0] = 0;
        let default_address = evaluate_executable(glb, defaultaddr, &inputs)?;
        addresstable.push(Address::new(spc, default_address));
        Ok(())
    }

    fn find_unnormalized(
        &mut self,
        _data: &mut Funcdata,
        _maxaddsub: u32,
        _maxleftright: u32,
        _maxext: u32,
    ) -> Result<()> {
        Ok(())
    }

    fn build_labels(
        &self,
        data: &mut Funcdata,
        glb: &mut Architecture,
        _addresstable: &mut Vec<Address>,
        label: &mut Vec<u64>,
        orig: &dyn JumpModel,
    ) -> Result<()> {
        let orig_size = orig
            .as_jump_assisted()
            .expect("original model is not a jumpassist model")
            .size_indices;
        if orig_size != self.size_indices {
            return Err(Error::Lowlevel(
                "JumpAssisted table size changed during recovery".to_string(),
            ));
        }
        let (name, _, _, index2case, _) =
            JumpAssisted::assist_data(glb, self.userop.expect("jumpassist user op is missing"));
        if index2case == -1 {
            for index in 0..self.size_indices {
                label.push(index as i64 as u64);
            }
        } else {
            let mut inputs = self.assist_script_inputs(data);
            if inputs.len() as i32 != JumpAssisted::payload_size_input(glb, index2case) {
                return Err(Error::Lowlevel(format!(
                    "{}: <case_pcode> has wrong number of parameters",
                    name
                )));
            }
            for index in 0..self.size_indices {
                inputs[0] = index as i64 as u64;
                let output = evaluate_executable(glb, index2case, &inputs)?;
                label.push(output);
            }
        }
        label.push(NO_LABEL);
        Ok(())
    }

    fn fold_in_normalization(
        &mut self,
        data: &mut Funcdata,
        _glb: &mut Architecture,
        _indop: OpId,
    ) -> Result<Option<VarnodeId>> {
        let assist_op = self.assist_op.expect("jumpassist op is missing");
        let switchvn = self.switchvn.expect("switch variable is missing");
        let outvn = data.op(assist_op).get_out().expect("jumpassist op has no output");
        while let Some(&op) = data.vn(outvn).descend().first() {
            data.op_set_input(op, switchvn, 0)?;
        }
        data.op_destroy(assist_op)?;
        Ok(self.switchvn)
    }

    fn fold_in_guards(&mut self, _data: &mut Funcdata, _glb: &mut Architecture, jump: &mut JumpTable) -> Result<bool> {
        let orig_val = jump.get_default_block();
        jump.set_last_as_default();
        Ok(orig_val != jump.get_default_block())
    }

    fn sanity_check(
        &mut self,
        _data: &mut Funcdata,
        _glb: &mut Architecture,
        _indop: OpId,
        _addresstable: &mut Vec<Address>,
        _loadpoints: &mut Vec<LoadTable>,
        _loadcounts: Option<&mut Vec<i32>>,
    ) -> Result<bool> {
        Ok(true)
    }

    fn clone_model(&self) -> Box<dyn JumpModel> {
        let mut res = JumpAssisted::new();
        res.userop = self.userop;
        res.size_indices = self.size_indices;
        Box::new(res)
    }

    fn clear(&mut self) {
        self.assist_op = None;
        self.switchvn = None;
    }

    fn as_jump_assisted(&self) -> Option<&JumpAssisted> {
        Some(self)
    }
}

#[repr(i32)]
#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum RecoveryMode {
    Success = 0,
    FailNormal = 1,
    FailThunk = 2,
    FailReturn = 3,
    FailCallother = 4,
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct IndexPair {
    pub block_position: i32,
    pub address_index: i32,
}

impl IndexPair {
    pub fn new(pos: i32, index: i32) -> IndexPair {
        IndexPair {
            block_position: pos,
            address_index: index,
        }
    }

    pub fn less_than(&self, op2: &IndexPair) -> bool {
        if self.block_position != op2.block_position {
            return self.block_position < op2.block_position;
        }
        self.address_index < op2.address_index
    }

    pub fn compare_by_position(op1: &IndexPair, op2: &IndexPair) -> bool {
        op1.block_position < op2.block_position
    }
}

pub struct JumpTable {
    pub jmodel: Option<Box<dyn JumpModel>>,
    pub origmodel: Option<Box<dyn JumpModel>>,
    pub addresstable: Vec<Address>,
    pub block2addr: Vec<IndexPair>,
    pub label: Vec<u64>,
    pub loadpoints: Vec<LoadTable>,
    pub opaddress: Address,
    pub indirect: Option<OpId>,
    pub switch_var_consume: u64,
    pub default_block: i32,
    pub last_block: i32,
    pub recover_count: i32,
    pub display_format: u32,
    pub partial_table: bool,
    pub collectloads: bool,
    pub default_is_folded: bool,
}

impl Default for JumpTable {
    fn default() -> JumpTable {
        JumpTable::new(Address::invalid())
    }
}

impl JumpTable {
    pub const MAXADDSUB: u32 = 1;
    pub const MAXLEFTRIGHT: u32 = 1;
    pub const MAXEXT: u32 = 1;

    pub fn new(ad: Address) -> JumpTable {
        JumpTable {
            jmodel: None,
            origmodel: None,
            addresstable: Vec::new(),
            block2addr: Vec::new(),
            label: Vec::new(),
            loadpoints: Vec::new(),
            opaddress: ad,
            indirect: None,
            switch_var_consume: !0u64,
            default_block: -1,
            last_block: -1,
            recover_count: 0,
            display_format: 0,
            partial_table: false,
            collectloads: false,
            default_is_folded: false,
        }
    }

    pub fn identity_placeholder(&self) -> JumpTable {
        JumpTable {
            opaddress: self.opaddress.clone(),
            indirect: self.indirect,
            ..JumpTable::default()
        }
    }

    pub fn from_table(op2: &JumpTable) -> JumpTable {
        JumpTable {
            jmodel: op2.jmodel.as_ref().map(|model| model.clone_model()),
            origmodel: None,
            addresstable: op2.addresstable.clone(),
            block2addr: Vec::new(),
            label: Vec::new(),
            loadpoints: op2.loadpoints.clone(),
            opaddress: op2.opaddress.clone(),
            indirect: None,
            switch_var_consume: !0u64,
            default_block: -1,
            last_block: op2.last_block,
            recover_count: op2.recover_count,
            display_format: op2.display_format,
            partial_table: op2.partial_table,
            collectloads: op2.collectloads,
            default_is_folded: false,
        }
    }

    fn indirect_op(&self) -> OpId {
        self.indirect.expect("jump table has no indirect op")
    }

    pub fn save_model(&mut self) {
        self.origmodel = self.jmodel.take();
    }

    pub fn restore_saved_model(&mut self) {
        self.jmodel = self.origmodel.take();
    }

    pub fn clear_saved_model(&mut self) {
        self.origmodel = None;
    }

    pub fn recover_model(
        &mut self,
        data: &mut Funcdata,
        glb: &mut Architecture,
        match_model: Option<&dyn JumpModel>,
    ) -> Result<()> {
        let max_table_size = glb.max_jumptable_size;
        let indirect = self.indirect_op();
        if let Some(mut model) = self.jmodel.take()
            && model.is_override()
        {
            let result = model.recover_model(self, data, glb, indirect, None, max_table_size);
            self.jmodel = Some(model);
            result?;
            return Ok(());
        }
        let vn = data.op(indirect).get_in(0);
        if data.vn(vn).is_written() {
            let op = data.vn(vn).get_def().expect("written varnode has no defining op");
            if data.op(op).code() == OpCode::Callother {
                let mut jassisted: Box<dyn JumpModel> = Box::new(JumpAssisted::new());
                let recovered = jassisted.recover_model(self, data, glb, indirect, match_model, max_table_size);
                self.jmodel = Some(jassisted);
                if recovered? {
                    return Ok(());
                }
            }
        }
        let mut jbasic = JumpBasic::new();
        let recovered = jbasic.recover_model(self, data, glb, indirect, match_model, max_table_size);
        match recovered {
            Ok(true) => {
                self.jmodel = Some(Box::new(jbasic));
                return Ok(());
            }
            Ok(false) => {}
            Err(err) => {
                self.jmodel = Some(Box::new(jbasic));
                return Err(err);
            }
        }
        let mut jbasic2 = JumpBasic2::new();
        jbasic2.initialize_start(jbasic.get_path_meld());
        drop(jbasic);
        let recovered = jbasic2.recover_model(self, data, glb, indirect, match_model, max_table_size);
        match recovered {
            Ok(true) => {
                self.jmodel = Some(Box::new(jbasic2));
                Ok(())
            }
            Ok(false) => {
                self.jmodel = None;
                Ok(())
            }
            Err(err) => {
                self.jmodel = Some(Box::new(jbasic2));
                Err(err)
            }
        }
    }

    pub fn trivial_switch_over(&mut self, data: &Funcdata) -> Result<()> {
        self.block2addr.clear();
        self.block2addr.reserve(self.addresstable.len());
        let parent = parent_of(data, self.indirect_op());
        let size_out = data.block(parent).size_out();
        if size_out as usize != self.addresstable.len() {
            return Err(Error::Lowlevel(
                "Trivial addresstable and switch block size do not match".to_string(),
            ));
        }
        for index in 0..size_out {
            self.block2addr.push(IndexPair::new(index, index));
        }
        self.last_block = size_out - 1;
        self.default_block = -1;
        Ok(())
    }

    pub fn is_thunk(&self, data: &Funcdata) -> Result<bool> {
        if self.addresstable.len() != 1 {
            return Ok(false);
        }
        let addr = &self.addresstable[0];
        if addr.get_offset() == 0 {
            return Ok(true);
        }
        let mut iter = data.begin_op_alive();
        while let Some(op) = iter {
            iter = data.obank.next_in_list(op, PcodeOp::INSERT_LIST);
            let opc = data.op(op).code();
            if opc != OpCode::Branchind && opc != OpCode::Branch {
                return Ok(false);
            }
        }
        Ok(true)
    }

    pub fn sanity_check(
        &mut self,
        data: &mut Funcdata,
        glb: &mut Architecture,
        loadcounts: Option<&mut Vec<i32>>,
    ) -> Result<()> {
        if self.jmodel.as_ref().expect("jump table model is missing").is_override() {
            return Ok(());
        }
        let size = self.addresstable.len();
        if !JumpTable::is_reachable(data, self.indirect_op()) {
            self.partial_table = true;
        }
        if self.is_thunk(data)? {
            return Err(Error::JumptableThunk("Likely thunk".to_string()));
        }
        let indirect = self.indirect_op();
        let mut model = self.jmodel.take().expect("jump table model is missing");
        let mut addresstable = std::mem::take(&mut self.addresstable);
        let mut loadpoints = std::mem::take(&mut self.loadpoints);
        let result = model.sanity_check(data, glb, indirect, &mut addresstable, &mut loadpoints, loadcounts);
        self.addresstable = addresstable;
        self.loadpoints = loadpoints;
        self.jmodel = Some(model);
        if !result? {
            let message = format!("Jumptable at {} did not pass sanity check.", self.opaddress);
            return Err(Error::Lowlevel(message));
        }
        if size != self.addresstable.len() {
            data.warning("Sanity check requires truncation of jumptable", &self.opaddress, glb);
        }
        Ok(())
    }

    pub fn block2_position(&self, data: &Funcdata, bl: BlockId) -> Result<i32> {
        let parent = parent_of(data, self.indirect_op());
        let mut position = 0;
        while position < data.block(bl).size_in() {
            if data.block(bl).get_in(position) == parent {
                break;
            }
            position += 1;
        }
        if position == data.block(bl).size_in() {
            return Err(Error::Lowlevel("Requested block, not in jumptable".to_string()));
        }
        Ok(data.block(bl).get_in_rev_index(position))
    }

    pub fn is_reachable(data: &Funcdata, op: OpId) -> bool {
        let mut parent = parent_of(data, op);
        for _ in 0..2 {
            if data.block(parent).size_in() != 1 {
                return true;
            }
            let bl = data.block(parent).get_in(0);
            if data.block(bl).size_out() != 2 {
                continue;
            }
            let cbranch = match last_op_of(data, bl) {
                Some(cbranch) if data.op(cbranch).code() == OpCode::Cbranch => cbranch,
                _ => continue,
            };
            let vn = data.op(cbranch).get_in(1);
            if !data.vn(vn).is_constant() {
                continue;
            }
            let mut trueslot = if data.op(cbranch).is_boolean_flip() { 0 } else { 1 };
            if data.vn(vn).get_offset() == 0 {
                trueslot = 1 - trueslot;
            }
            if data.block(bl).get_out(trueslot) != parent {
                return false;
            }
            parent = bl;
        }
        true
    }

    pub fn is_recovered(&self) -> bool {
        !self.addresstable.is_empty()
    }

    pub fn is_labelled(&self) -> bool {
        !self.label.is_empty()
    }

    pub fn is_override(&self) -> bool {
        match &self.jmodel {
            Some(model) => model.is_override(),
            None => false,
        }
    }

    pub fn is_partial(&self) -> bool {
        self.partial_table
    }

    pub fn mark_complete(&mut self) {
        self.partial_table = false;
    }

    pub fn num_entries(&self) -> i32 {
        self.addresstable.len() as i32
    }

    pub fn get_switch_var_consume(&self) -> u64 {
        self.switch_var_consume
    }

    pub fn get_default_block(&self) -> i32 {
        self.default_block
    }

    pub fn get_op_address(&self) -> &Address {
        &self.opaddress
    }

    pub fn get_indirect_op(&self) -> Option<OpId> {
        self.indirect
    }

    pub fn set_indirect_op(&mut self, data: &Funcdata, ind: OpId) {
        self.opaddress = data.op(ind).get_addr().clone();
        self.indirect = Some(ind);
    }

    pub fn get_display_format(&self) -> u32 {
        self.display_format
    }

    pub fn set_display_format(&mut self, format: u32) {
        self.display_format = format;
    }

    pub fn set_override(&mut self, addrtable: &[Address], naddr: &Address, hash: u64, sv: u64) -> Result<()> {
        let mut jump_override = JumpBasicOverride::new();
        jump_override.set_addresses(addrtable);
        jump_override.set_norm(naddr, hash);
        jump_override.set_starting_value(sv);
        self.jmodel = Some(Box::new(jump_override));
        Ok(())
    }

    pub fn num_indices_by_block(&self, data: &Funcdata, bl: BlockId) -> i32 {
        let position = self
            .block2_position(data, bl)
            .expect("Requested block, not in jumptable");
        let start = self.block2addr.partition_point(|pair| pair.block_position < position);
        let end = self.block2addr.partition_point(|pair| pair.block_position <= position);
        (end - start) as i32
    }

    pub fn get_index_by_block(&self, data: &Funcdata, bl: BlockId, index: i32) -> Result<i32> {
        let position = self.block2_position(data, bl)?;
        let mut count = 0;
        let start = self.block2addr.partition_point(|pair| pair.block_position < position);
        for pair in self.block2addr[start..].iter() {
            if pair.block_position == position {
                if count == index {
                    return Ok(pair.address_index);
                }
                count += 1;
            }
        }
        Err(Error::Lowlevel("Could not get jumptable index for block".to_string()))
    }

    pub fn get_address_by_index(&self, index: i32) -> Address {
        self.addresstable[index as usize].clone()
    }

    pub fn get_recover_count(&self) -> i32 {
        self.recover_count
    }

    pub fn increment_recovery_count(&mut self) {
        self.recover_count += 1;
    }

    pub fn set_last_as_default(&mut self) {
        self.default_block = self.last_block;
    }

    pub fn set_default_block(&mut self, bl: i32) {
        self.default_block = bl;
    }

    pub fn set_load_collect(&mut self, val: bool) {
        self.collectloads = val;
    }

    pub fn set_folded_default(&mut self) {
        self.default_is_folded = true;
    }

    pub fn has_folded_default(&self) -> bool {
        self.default_is_folded
    }

    pub fn add_block_to_switch(&mut self, data: &Funcdata, bl: BlockId, lab: u64) {
        self.addresstable.push(data.block(bl).get_start());
        let parent = parent_of(data, self.indirect_op());
        self.last_block = data.block(parent).size_out();
        self.block2addr
            .push(IndexPair::new(self.last_block, self.addresstable.len() as i32 - 1));
        self.label.push(lab);
    }

    pub fn switch_over(&mut self, data: &Funcdata, flow: &FlowInfo) -> Result<()> {
        self.block2addr.clear();
        self.block2addr.reserve(self.addresstable.len());
        let parent = parent_of(data, self.indirect_op());
        for index in 0..self.addresstable.len() {
            let addr = self.addresstable[index].clone();
            let op = flow.target(&addr, data)?;
            let tmpbl = data.op(op).get_parent();
            let mut pos = 0;
            while pos < data.block(parent).size_out() {
                if Some(data.block(parent).get_out(pos)) == tmpbl {
                    break;
                }
                pos += 1;
            }
            if pos == data.block(parent).size_out() {
                return Err(Error::Lowlevel("Jumptable destination not linked".to_string()));
            }
            self.block2addr.push(IndexPair::new(pos, index as i32));
        }
        self.last_block = self
            .block2addr
            .last()
            .expect("jump table has no addresses")
            .block_position;
        self.block2addr.sort();
        self.default_block = -1;
        let mut maxcount = 1;
        let mut iter = 0;
        while iter < self.block2addr.len() {
            let cur_pos = self.block2addr[iter].block_position;
            let mut nextiter = iter;
            let mut count = 0;
            while nextiter < self.block2addr.len() && self.block2addr[nextiter].block_position == cur_pos {
                count += 1;
                nextiter += 1;
            }
            iter = nextiter;
            if count > maxcount {
                maxcount = count;
                self.default_block = cur_pos;
            }
        }
        Ok(())
    }

    pub fn get_label_by_index(&self, index: i32) -> u64 {
        self.label[index as usize]
    }

    pub fn fold_in_normalization(&mut self, data: &mut Funcdata, glb: &mut Architecture) -> Result<()> {
        let indirect = self.indirect_op();
        let mut model = self.jmodel.take().expect("jump table model is missing");
        let result = model.fold_in_normalization(data, glb, indirect);
        self.jmodel = Some(model);
        if let Some(switchvn) = result? {
            self.switch_var_consume = minimalmask(data.vn(switchvn).get_nz_mask());
            if self.switch_var_consume >= calc_mask(data.vn(switchvn).get_size()) && data.vn(switchvn).is_written() {
                let op = data.vn(switchvn).get_def().expect("written varnode has no defining op");
                if data.op(op).code() == OpCode::IntSext {
                    self.switch_var_consume = calc_mask(data.vn(data.op(op).get_in(0)).get_size());
                }
            }
        }
        Ok(())
    }

    pub fn fold_in_guards(&mut self, data: &mut Funcdata, glb: &mut Architecture) -> Result<bool> {
        let mut model = self.jmodel.take().expect("jump table model is missing");
        let result = model.fold_in_guards(data, glb, self);
        self.jmodel = Some(model);
        result
    }

    pub fn recover_addresses(&mut self, data: &mut Funcdata, glb: &mut Architecture) -> Result<()> {
        self.recover_model(data, glb, None)?;
        let table_size = match &self.jmodel {
            None => {
                let message = format!("Could not recover jumptable at {}. Too many branches", self.opaddress);
                return Err(Error::Lowlevel(message));
            }
            Some(model) => model.get_table_size(),
        };
        if table_size == 0 {
            let message = format!("Jumptable with 0 entries at {}", self.opaddress);
            return Err(Error::Lowlevel(message));
        }
        let indirect = self.indirect_op();
        let model = self.jmodel.take().expect("jump table model is missing");
        let mut addresstable = std::mem::take(&mut self.addresstable);
        if self.collectloads {
            let mut loadcounts: Vec<i32> = Vec::new();
            let mut loadpoints = std::mem::take(&mut self.loadpoints);
            let result = model.build_addresses(
                data,
                glb,
                indirect,
                &mut addresstable,
                Some(&mut loadpoints),
                Some(&mut loadcounts),
            );
            self.addresstable = addresstable;
            self.loadpoints = loadpoints;
            self.jmodel = Some(model);
            result?;
            self.sanity_check(data, glb, Some(&mut loadcounts))?;
            LoadTable::collapse_table(&mut self.loadpoints);
        } else {
            let result = model.build_addresses(data, glb, indirect, &mut addresstable, None, None);
            self.addresstable = addresstable;
            self.jmodel = Some(model);
            result?;
            self.sanity_check(data, glb, None)?;
        }
        Ok(())
    }

    pub fn recover_multistage(&mut self, data: &mut Funcdata, glb: &mut Architecture) -> Result<()> {
        self.save_model();
        let oldaddresstable = self.addresstable.clone();
        self.addresstable.clear();
        self.loadpoints.clear();
        if let Err(err) = self.recover_addresses(data, glb) {
            let caught = matches!(err, Error::JumptableThunk(_)) || err.is_lowlevel();
            if !caught {
                return Err(err);
            }
            self.restore_saved_model();
            self.addresstable = oldaddresstable;
            let addr = data.op(self.indirect_op()).get_addr().clone();
            data.warning("Second-stage recovery error", &addr, glb);
        }
        self.partial_table = false;
        self.clear_saved_model();
        Ok(())
    }

    pub fn match_model(&mut self, data: &mut Funcdata, glb: &mut Architecture) -> Result<()> {
        if !self.is_recovered() {
            return Err(Error::Lowlevel(
                "Trying to recover jumptable labels without addresses".to_string(),
            ));
        }
        if let Some(model) = &self.jmodel {
            if !model.is_override() {
                self.save_model();
            } else {
                self.clear_saved_model();
                data.warning("Switch is manually overridden", &self.opaddress, glb);
            }
        }
        let orig = self.origmodel.take();
        let result = self.recover_model(data, glb, orig.as_deref());
        self.origmodel = orig;
        result?;
        if let Some(model) = &self.jmodel {
            let table_size = model.get_table_size();
            if table_size as usize != self.addresstable.len() {
                if self.addresstable.len() == 1 && table_size > 1 {
                    data.get_override().insert_multistage_jump(&self.opaddress);
                    data.set_restart_pending(true);
                    return Ok(());
                }
                data.warning(
                    "Could not find normalized switch variable to match jumptable",
                    &self.opaddress,
                    glb,
                );
            }
        }
        Ok(())
    }

    pub fn recover_labels(&mut self, data: &mut Funcdata, glb: &mut Architecture) -> Result<()> {
        if let Some(mut model) = self.jmodel.take() {
            let mut addresstable = std::mem::take(&mut self.addresstable);
            let mut label = std::mem::take(&mut self.label);
            let use_orig = match &self.origmodel {
                None => false,
                Some(orig) => orig.get_table_size() != 0,
            };
            let result = model
                .find_unnormalized(data, JumpTable::MAXADDSUB, JumpTable::MAXLEFTRIGHT, JumpTable::MAXEXT)
                .and_then(|_| {
                    if use_orig {
                        let orig = self.origmodel.as_deref().expect("original jump model is missing");
                        model.build_labels(data, glb, &mut addresstable, &mut label, orig)
                    } else {
                        model.build_labels(data, glb, &mut addresstable, &mut label, model.as_ref())
                    }
                });
            self.addresstable = addresstable;
            self.label = label;
            self.jmodel = Some(model);
            result?;
        } else {
            let indirect = self.indirect_op();
            let mut model: Box<dyn JumpModel> = Box::new(JumpModelTrivial::new());
            let orig = self.origmodel.take();
            let recovered = model.recover_model(self, data, glb, indirect, orig.as_deref(), glb.max_jumptable_size);
            let mut addresstable = std::mem::take(&mut self.addresstable);
            let result =
                recovered.and_then(|_| model.build_addresses(data, glb, indirect, &mut addresstable, None, None));
            self.addresstable = addresstable;
            self.origmodel = orig;
            self.jmodel = Some(model);
            result?;
            self.trivial_switch_over(data)?;
            let model = self.jmodel.take().expect("jump table model is missing");
            let mut addresstable = std::mem::take(&mut self.addresstable);
            let mut label = std::mem::take(&mut self.label);
            let result = match self.origmodel.as_deref() {
                Some(orig) => model.build_labels(data, glb, &mut addresstable, &mut label, orig),
                None => model.build_labels(data, glb, &mut addresstable, &mut label, model.as_ref()),
            };
            self.addresstable = addresstable;
            self.label = label;
            self.jmodel = Some(model);
            result?;
        }
        self.clear_saved_model();
        Ok(())
    }

    pub fn check_for_multistage(&mut self, data: &mut Funcdata, _glb: &mut Architecture) -> Result<bool> {
        if self.addresstable.len() != 1 {
            return Ok(false);
        }
        if self.partial_table {
            return Ok(false);
        }
        let indirect = match self.indirect {
            Some(indirect) => indirect,
            None => return Ok(false),
        };
        if self.recover_count > 1 {
            return Ok(false);
        }
        let addr = data.op(indirect).get_addr().clone();
        if data.get_override().query_multistage_jumptable(&addr) {
            self.partial_table = true;
            return Ok(true);
        }
        Ok(false)
    }

    pub fn clear(&mut self) {
        self.clear_saved_model();
        let is_override = self.jmodel.as_ref().expect("jump table model is missing").is_override();
        if is_override {
            self.jmodel.as_mut().expect("jump table model is missing").clear();
        } else {
            self.jmodel = None;
        }
        self.addresstable.clear();
        self.block2addr.clear();
        self.last_block = -1;
        self.label.clear();
        self.loadpoints.clear();
        self.indirect = None;
        self.switch_var_consume = !0u64;
        self.default_block = -1;
        self.recover_count = 0;
        self.partial_table = false;
    }

    pub fn encode(&self, encoder: &mut dyn Encoder) -> Result<()> {
        if !self.is_recovered() {
            return Err(Error::Lowlevel("Trying to save unrecovered jumptable".to_string()));
        }
        encoder.open_element(ELEM_JUMPTABLE);
        if self.display_format != 0 {
            encoder.write_unsigned_integer(ATTRIB_FORMAT, self.display_format as u64);
        }
        self.opaddress.encode(encoder)?;
        for (index, addr) in self.addresstable.iter().enumerate() {
            encoder.open_element(ELEM_DEST);
            if let Some(spc) = addr.get_space() {
                spc.encode_attributes(encoder, addr.get_offset())?;
            }
            if index < self.label.len() && self.label[index] != NO_LABEL {
                encoder.write_unsigned_integer(ATTRIB_LABEL, self.label[index]);
            }
            encoder.close_element(ELEM_DEST);
        }
        for loadpoint in self.loadpoints.iter() {
            loadpoint.encode(encoder)?;
        }
        if let Some(model) = &self.jmodel
            && model.is_override()
        {
            model.encode(encoder)?;
        }
        encoder.close_element(ELEM_JUMPTABLE);
        Ok(())
    }

    pub fn decode(&mut self, decoder: &mut dyn Decoder) -> Result<()> {
        let elem_id = decoder.open_element_expect(ELEM_JUMPTABLE)?;
        if decoder.get_next_attribute_id()? == ATTRIB_FORMAT.get_id() {
            self.display_format = decoder.read_unsigned_integer()? as u32;
        }
        self.opaddress = Address::decode(decoder)?;
        let mut missedlabel = false;
        loop {
            let sub_id = decoder.peek_element()?;
            if sub_id == 0 {
                break;
            }
            if sub_id == ELEM_DEST.get_id() {
                decoder.open_element()?;
                let mut foundlabel = false;
                loop {
                    let attrib_id = decoder.get_next_attribute_id()?;
                    if attrib_id == 0 {
                        break;
                    }
                    if attrib_id == ATTRIB_LABEL.get_id() {
                        if missedlabel {
                            return Err(Error::Lowlevel("Jumptable entries are missing labels".to_string()));
                        }
                        let lab = decoder.read_unsigned_integer()?;
                        self.label.push(lab);
                        foundlabel = true;
                        break;
                    }
                }
                if !foundlabel {
                    missedlabel = true;
                }
                self.addresstable.push(Address::decode(decoder)?);
            } else if sub_id == ELEM_LOADTABLE.get_id() {
                let mut loadpoint = LoadTable::default();
                loadpoint.decode(decoder)?;
                self.loadpoints.push(loadpoint);
            } else if sub_id == ELEM_BASICOVERRIDE.get_id() {
                if self.jmodel.is_some() {
                    return Err(Error::Lowlevel("Duplicate jumptable override specs".to_string()));
                }
                let mut model: Box<dyn JumpModel> = Box::new(JumpBasicOverride::new());
                let result = model.decode(decoder);
                self.jmodel = Some(model);
                result?;
            }
        }
        decoder.close_element(elem_id)?;
        if !self.label.is_empty() {
            while self.label.len() < self.addresstable.len() {
                self.label.push(NO_LABEL);
            }
        }
        Ok(())
    }
}

impl<'c> Emulate<'c> for EmulateFunction {
    type Context = PcodeOpContext<'c>;

    fn base(&self) -> &crate::emulate::EmulateBase {
        &self.base.emulate
    }

    fn base_mut(&mut self) -> &mut crate::emulate::EmulateBase {
        &mut self.base.emulate
    }

    fn get_behavior(&self, ctx: &PcodeOpContext<'c>, opc: OpCode) -> Option<crate::opbehavior::OpBehaviorRef> {
        EmulatePcodeOp::pcode_get_behavior(self, ctx, opc)
    }

    fn execute_unary(&mut self, ctx: &mut PcodeOpContext<'c>) -> Result<()> {
        EmulatePcodeOp::pcode_execute_unary(self, ctx)
    }

    fn execute_binary(&mut self, ctx: &mut PcodeOpContext<'c>) -> Result<()> {
        EmulatePcodeOp::pcode_execute_binary(self, ctx)
    }

    fn execute_load(&mut self, ctx: &mut PcodeOpContext<'c>) -> Result<()> {
        EmulateFunction::execute_load(self, ctx)
    }

    fn execute_store(&mut self, ctx: &mut PcodeOpContext<'c>) -> Result<()> {
        EmulatePcodeOp::pcode_execute_store(self, ctx)
    }

    fn execute_branch(&mut self, ctx: &mut PcodeOpContext<'c>) -> Result<()> {
        EmulateFunction::execute_branch(self, ctx)
    }

    fn execute_cbranch(&mut self, ctx: &mut PcodeOpContext<'c>) -> Result<bool> {
        EmulatePcodeOp::pcode_execute_cbranch(self, ctx)
    }

    fn execute_branchind(&mut self, ctx: &mut PcodeOpContext<'c>) -> Result<()> {
        EmulateFunction::execute_branchind(self, ctx)
    }

    fn execute_call(&mut self, ctx: &mut PcodeOpContext<'c>) -> Result<()> {
        EmulateFunction::execute_call(self, ctx)
    }

    fn execute_callind(&mut self, ctx: &mut PcodeOpContext<'c>) -> Result<()> {
        EmulateFunction::execute_callind(self, ctx)
    }

    fn execute_callother(&mut self, ctx: &mut PcodeOpContext<'c>) -> Result<()> {
        EmulateFunction::execute_callother(self, ctx)
    }

    fn execute_multiequal(&mut self, ctx: &mut PcodeOpContext<'c>) -> Result<()> {
        EmulatePcodeOp::pcode_execute_multiequal(self, ctx)
    }

    fn execute_indirect(&mut self, ctx: &mut PcodeOpContext<'c>) -> Result<()> {
        EmulatePcodeOp::pcode_execute_indirect(self, ctx)
    }

    fn execute_segment_op(&mut self, ctx: &mut PcodeOpContext<'c>) -> Result<()> {
        EmulatePcodeOp::pcode_execute_segment_op(self, ctx)
    }

    fn execute_cpool_ref(&mut self, ctx: &mut PcodeOpContext<'c>) -> Result<()> {
        EmulatePcodeOp::pcode_execute_cpool_ref(self, ctx)
    }

    fn execute_new(&mut self, ctx: &mut PcodeOpContext<'c>) -> Result<()> {
        EmulatePcodeOp::pcode_execute_new(self, ctx)
    }

    fn fallthru_op(&mut self, ctx: &mut PcodeOpContext<'c>) -> Result<()> {
        EmulateFunction::fallthru_op(self, ctx)
    }

    fn set_execute_address(&mut self, ctx: &mut PcodeOpContext<'c>, addr: &Address) -> Result<()> {
        EmulateFunction::set_execute_address(self, ctx, addr)
    }

    fn get_execute_address(&self, ctx: &PcodeOpContext<'c>) -> Address {
        EmulatePcodeOp::pcode_get_execute_address(self, ctx.data)
    }
}

impl<'c> EmulatePcodeOp<'c> for EmulateFunction {
    fn pcode_base(&self) -> &EmulatePcodeOpBase {
        &self.base
    }

    fn pcode_base_mut(&mut self) -> &mut EmulatePcodeOpBase {
        &mut self.base
    }

    fn set_varnode_value(&mut self, vn: VarnodeId, val: u64) {
        EmulateFunction::set_varnode_value(self, vn, val)
    }

    fn get_varnode_value(&self, ctx: &PcodeOpContext<'c>, vn: VarnodeId) -> Result<u64> {
        EmulateFunction::get_varnode_value(self, ctx.data, ctx.glb, vn)
    }
}
