use std::collections::BTreeMap;

use crate::address::calc_mask;
use crate::architecture::Architecture;
use crate::error::{Error, Result};
use crate::funcdata::Funcdata;
use crate::istream::{Basefield, read_i32};
use crate::marshal::AttributeId;
use crate::op::{OpId, PcodeOp};
use crate::opcodes::OpCode;
use crate::space::SpaceType;
use crate::varnode::VarnodeId;

pub const ATTRIB_VECTOR_LANE_SIZES: AttributeId = AttributeId::new("vector_lane_sizes", 130);

#[derive(Clone, Debug, Default)]
pub struct TransformVar {
    pub vn: Option<VarnodeId>,
    pub replacement: Option<VarnodeId>,
    pub var_type: u32,
    pub flags: u32,
    pub byte_size: i32,
    pub bit_size: i32,
    pub val: u64,
    pub def: Option<usize>,
}

impl TransformVar {
    pub const PIECE: u32 = 1;
    pub const PREEXISTING: u32 = 2;
    pub const NORMAL_TEMP: u32 = 3;
    pub const PIECE_TEMP: u32 = 4;
    pub const CONSTANT: u32 = 5;

    pub const SPLIT_TERMINATOR: u32 = 1;
    pub const INPUT_DUPLICATE: u32 = 2;

    pub fn initialize(&mut self, tp: u32, original: Option<VarnodeId>, bits: i32, bytes: i32, value: u64) {
        self.var_type = tp;
        self.vn = original;
        self.val = value;
        self.bit_size = bits;
        self.byte_size = bytes;
        self.flags = 0;
        self.def = None;
        self.replacement = None;
    }

    pub fn get_original(&self) -> Option<VarnodeId> {
        self.vn
    }

    pub fn get_def(&self) -> Option<usize> {
        self.def
    }
}

#[derive(Clone, Debug)]
pub struct TransformOp {
    pub op: Option<OpId>,
    pub replacement: Option<OpId>,
    pub opc: OpCode,
    pub special: u32,
    pub output: Option<usize>,
    pub input: Vec<Option<usize>>,
    pub follow: Option<usize>,
}

impl TransformOp {
    pub const OP_REPLACEMENT: u32 = 1;
    pub const OP_PREEXISTING: u32 = 2;
    pub const OP_INDIRECT: u32 = 4;
    pub const INDIRECT_CREATION: u32 = 8;
    pub const INDIRECT_CREATION_POSSIBLE_OUT: u32 = 0x10;

    pub fn get_out(&self) -> Option<usize> {
        self.output
    }

    pub fn get_in(&self, index: i32) -> Option<usize> {
        self.input[index as usize]
    }
}

#[derive(Clone, Copy, Debug)]
pub struct LanedIterator {
    size: i32,
    mask: u32,
}

impl LanedIterator {
    pub fn new(laned_r: &LanedRegister) -> LanedIterator {
        let mut iterator = LanedIterator {
            size: 0,
            mask: laned_r.size_bit_mask,
        };
        iterator.normalize();
        iterator
    }

    pub fn end() -> LanedIterator {
        LanedIterator { size: -1, mask: 0 }
    }

    pub fn normalize(&mut self) {
        let mut flag: u32 = 1u32.wrapping_shl(self.size as u32);
        while flag <= self.mask {
            if (flag & self.mask) != 0 {
                return;
            }
            self.size += 1;
            flag = flag.wrapping_shl(1);
        }
        self.size = -1;
    }

    pub fn increment(&mut self) -> &mut LanedIterator {
        self.size += 1;
        self.normalize();
        self
    }

    pub fn get(&self) -> i32 {
        self.size
    }
}

impl PartialEq for LanedIterator {
    fn eq(&self, other: &LanedIterator) -> bool {
        self.size == other.size
    }
}

impl Eq for LanedIterator {}

impl PartialEq<i32> for LanedIterator {
    fn eq(&self, other: &i32) -> bool {
        self.size == *other
    }
}

impl Iterator for LanedIterator {
    type Item = i32;

    fn next(&mut self) -> Option<i32> {
        if self.size == -1 {
            return None;
        }
        let current = self.size;
        self.increment();
        Some(current)
    }
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct LanedRegister {
    whole_size: i32,
    size_bit_mask: u32,
}

impl LanedRegister {
    pub fn new() -> LanedRegister {
        LanedRegister {
            whole_size: 0,
            size_bit_mask: 0,
        }
    }

    pub fn with_mask(sz: i32, mask: u32) -> LanedRegister {
        LanedRegister {
            whole_size: sz,
            size_bit_mask: mask,
        }
    }

    pub fn parse_sizes(&mut self, register_size: i32, lane_sizes: &str) -> Result<()> {
        self.whole_size = register_size;
        self.size_bit_mask = 0;
        let mut pos: Option<usize> = Some(0);
        while let Some(start) = pos {
            let value: &str;
            match lane_sizes[start..].find(',') {
                None => {
                    value = &lane_sizes[start..];
                    pos = None;
                }
                Some(relative) => {
                    let next_pos = start + relative;
                    value = &lane_sizes[start..next_pos];
                    let after = next_pos + 1;
                    pos = if after >= lane_sizes.len() { None } else { Some(after) };
                }
            }
            let size = read_i32(value, Basefield::Auto, -1);
            if size <= 0 || size >= self.whole_size || size > 16 {
                return Err(Error::Lowlevel(format!("Bad lane size: {}", value)));
            }
            self.add_lane_size(size);
        }
        Ok(())
    }

    pub fn get_whole_size(&self) -> i32 {
        self.whole_size
    }

    pub fn get_size_bit_mask(&self) -> u32 {
        self.size_bit_mask
    }

    pub fn add_lane_size(&mut self, size: i32) {
        self.size_bit_mask |= 1u32.wrapping_shl(size as u32);
    }

    pub fn allowed_lane(&self, size: i32) -> bool {
        (self.size_bit_mask.wrapping_shr(size as u32) & 1) != 0
    }

    pub fn begin(&self) -> LanedIterator {
        LanedIterator::new(self)
    }

    pub fn end(&self) -> LanedIterator {
        LanedIterator::end()
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LaneDescription {
    whole_size: i32,
    lane_size: Vec<i32>,
    lane_position: Vec<i32>,
}

impl LaneDescription {
    pub fn new(orig_size: i32, sz: i32) -> LaneDescription {
        let num_lanes = orig_size / sz;
        let mut lane_size = Vec::with_capacity(num_lanes.max(0) as usize);
        let mut lane_position = Vec::with_capacity(num_lanes.max(0) as usize);
        let mut pos = 0;
        for _ in 0..num_lanes {
            lane_size.push(sz);
            lane_position.push(pos);
            pos += sz;
        }
        LaneDescription {
            whole_size: orig_size,
            lane_size,
            lane_position,
        }
    }

    pub fn new_lo_hi(orig_size: i32, lo: i32, hi: i32) -> LaneDescription {
        LaneDescription {
            whole_size: orig_size,
            lane_size: vec![lo, hi],
            lane_position: vec![0, lo],
        }
    }

    pub fn subset(&mut self, lsb_offset: i32, size: i32) -> bool {
        if lsb_offset == 0 && size == self.whole_size {
            return true;
        }
        let first_lane = self.get_boundary(lsb_offset);
        if first_lane < 0 {
            return false;
        }
        let last_lane = self.get_boundary(lsb_offset + size);
        if last_lane < 0 {
            return false;
        }
        let mut new_lane_size = Vec::new();
        self.lane_position.clear();
        let mut new_position = 0;
        for index in first_lane..last_lane {
            let lane = self.lane_size[index as usize];
            self.lane_position.push(new_position);
            new_lane_size.push(lane);
            new_position += lane;
        }
        self.whole_size = size;
        self.lane_size = new_lane_size;
        true
    }

    pub fn get_num_lanes(&self) -> i32 {
        self.lane_size.len() as i32
    }

    pub fn get_whole_size(&self) -> i32 {
        self.whole_size
    }

    pub fn get_size(&self, index: i32) -> i32 {
        self.lane_size[index as usize]
    }

    pub fn get_position(&self, index: i32) -> i32 {
        self.lane_position[index as usize]
    }

    pub fn get_boundary(&self, byte_pos: i32) -> i32 {
        if byte_pos < 0 || byte_pos > self.whole_size {
            return -1;
        }
        if byte_pos == self.whole_size {
            return self.lane_position.len() as i32;
        }
        let mut min = 0i32;
        let mut max = self.lane_position.len() as i32 - 1;
        while min <= max {
            let index = (min + max) / 2;
            let pos = self.lane_position[index as usize];
            if pos == byte_pos {
                return index;
            }
            if pos < byte_pos {
                min = index + 1;
            } else {
                max = index - 1;
            }
        }
        -1
    }

    pub fn restriction(
        &self,
        _num_lanes: i32,
        skip_lanes: i32,
        byte_pos: i32,
        size: i32,
        res_num_lanes: &mut i32,
        res_skip_lanes: &mut i32,
    ) -> bool {
        *res_skip_lanes = self.get_boundary(self.lane_position[skip_lanes as usize] + byte_pos);
        if *res_skip_lanes < 0 {
            return false;
        }
        let final_index = self.get_boundary(self.lane_position[skip_lanes as usize] + byte_pos + size);
        if final_index < 0 {
            return false;
        }
        *res_num_lanes = final_index - *res_skip_lanes;
        *res_num_lanes != 0
    }

    pub fn extension(
        &self,
        _num_lanes: i32,
        skip_lanes: i32,
        byte_pos: i32,
        size: i32,
        res_num_lanes: &mut i32,
        res_skip_lanes: &mut i32,
    ) -> bool {
        *res_skip_lanes = self.get_boundary(self.lane_position[skip_lanes as usize] - byte_pos);
        if *res_skip_lanes < 0 {
            return false;
        }
        let final_index = self.get_boundary(self.lane_position[skip_lanes as usize] - byte_pos + size);
        if final_index < 0 {
            return false;
        }
        *res_num_lanes = final_index - *res_skip_lanes;
        *res_num_lanes != 0
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum TransformFlavor {
    Standard,
    Subfloat,
}

#[derive(Clone, Debug)]
pub struct TransformManager {
    pub flavor: TransformFlavor,
    pub piece_map: BTreeMap<u32, usize>,
    pub new_varnodes: Vec<TransformVar>,
    pub new_ops: Vec<TransformOp>,
}

impl TransformManager {
    pub fn new() -> TransformManager {
        TransformManager {
            flavor: TransformFlavor::Standard,
            piece_map: BTreeMap::new(),
            new_varnodes: Vec::new(),
            new_ops: Vec::new(),
        }
    }

    pub fn with_flavor(flavor: TransformFlavor) -> TransformManager {
        TransformManager {
            flavor,
            piece_map: BTreeMap::new(),
            new_varnodes: Vec::new(),
            new_ops: Vec::new(),
        }
    }

    pub fn var(&self, index: usize) -> &TransformVar {
        &self.new_varnodes[index]
    }

    pub fn var_mut(&mut self, index: usize) -> &mut TransformVar {
        &mut self.new_varnodes[index]
    }

    pub fn op(&self, index: usize) -> &TransformOp {
        &self.new_ops[index]
    }

    pub fn op_mut(&mut self, index: usize) -> &mut TransformOp {
        &mut self.new_ops[index]
    }

    pub fn var_create_replacement(&mut self, rvn: usize, data: &mut Funcdata, glb: &mut Architecture) -> Result<()> {
        if self.new_varnodes[rvn].replacement.is_some() {
            return Ok(());
        }
        let var = self.new_varnodes[rvn].clone();
        let def_replacement = var
            .def
            .map(|def| self.new_ops[def].replacement.expect("missing replacement op"));
        let replacement = match var.var_type {
            TransformVar::PREEXISTING => var.vn.expect("missing preexisting varnode"),
            TransformVar::CONSTANT => data.new_constant(var.byte_size, var.val, glb),
            TransformVar::NORMAL_TEMP | TransformVar::PIECE_TEMP => match def_replacement {
                None => data.new_unique(var.byte_size, None, glb),
                Some(def_op) => data.new_unique_out(var.byte_size, def_op, glb)?,
            },
            TransformVar::PIECE => {
                let vn = var.vn.expect("missing piece varnode");
                let mut byte_pos = var.val as i32;
                if (byte_pos & 7) != 0 {
                    return Err(Error::Lowlevel("Varnode piece is not byte aligned".to_string()));
                }
                byte_pos >>= 3;
                let original = data.vn(vn);
                let big_endian = original.get_space().expect("varnode without space").is_big_endian();
                if big_endian {
                    byte_pos = original.get_size() - byte_pos - var.byte_size;
                }
                let mut addr = original.get_addr().add(byte_pos as i64);
                addr.renormalize(var.byte_size)?;
                let created = match def_replacement {
                    None => data.new_varnode(var.byte_size, &addr, None, glb)?,
                    Some(def_op) => data.new_varnode_out(var.byte_size, &addr, def_op, glb)?,
                };
                data.transfer_varnode_properties(vn, created, byte_pos, glb);
                created
            }
            _ => return Err(Error::Lowlevel("Bad TransformVar type".to_string())),
        };
        self.new_varnodes[rvn].replacement = Some(replacement);
        Ok(())
    }

    pub fn op_create_replacement(&mut self, rop: usize, data: &mut Funcdata, glb: &mut Architecture) -> Result<()> {
        let special = self.new_ops[rop].special;
        let op = self.new_ops[rop].op.expect("missing transform op anchor");
        let opc = self.new_ops[rop].opc;
        let input_count = self.new_ops[rop].input.len() as i32;
        if (special & TransformOp::OP_PREEXISTING) != 0 {
            self.new_ops[rop].replacement = Some(op);
            data.op_set_opcode(op, opc, glb);
            while input_count < data.op(op).num_input() {
                let last = data.op(op).num_input() - 1;
                data.op_remove_input(op, last);
            }
            for slot in 0..data.op(op).num_input() {
                data.op_unset_input(op, slot);
            }
            while data.op(op).num_input() < input_count {
                let slot = (data.op(op).num_input() - 1).max(0);
                data.op_mut(op).insert_input(slot);
            }
        } else if (special & TransformOp::OP_INDIRECT) != 0 {
            let target = PcodeOp::get_op_from_const(data.vn(data.op(op).get_in(1)).get_addr());
            let replacement = data.new_indirect(target, glb)?;
            self.new_ops[rop].replacement = Some(replacement);
            let output = self.new_ops[rop].output.expect("missing indirect output");
            self.var_create_replacement(output, data, glb)?;
            data.op_insert_before(replacement, op);
        } else {
            let addr = data.op(op).get_addr().clone();
            let replacement = data.new_op(input_count, &addr);
            data.op_set_opcode(replacement, opc, glb);
            self.new_ops[rop].replacement = Some(replacement);
            if let Some(output) = self.new_ops[rop].output {
                self.var_create_replacement(output, data, glb)?;
            }
            if self.new_ops[rop].follow.is_none() {
                if opc == OpCode::Multiequal {
                    let parent = data.op(op).get_parent().expect("op without parent block");
                    data.op_insert_begin(replacement, parent);
                } else {
                    data.op_insert_before(replacement, op);
                }
            }
        }
        Ok(())
    }

    pub fn op_attempt_insertion(&mut self, rop: usize, data: &mut Funcdata) -> bool {
        if let Some(follow) = self.new_ops[rop].follow {
            if self.new_ops[follow].follow.is_none() {
                let replacement = self.new_ops[rop].replacement.expect("missing replacement op");
                let follow_replacement = self.new_ops[follow].replacement.expect("missing follow replacement op");
                if self.new_ops[rop].opc == OpCode::Multiequal {
                    let parent = data
                        .op(follow_replacement)
                        .get_parent()
                        .expect("op without parent block");
                    data.op_insert_begin(replacement, parent);
                } else {
                    data.op_insert_before(replacement, follow_replacement);
                }
                self.new_ops[rop].follow = None;
                return true;
            }
            return false;
        }
        true
    }

    pub fn special_handling(&mut self, rop: usize, data: &mut Funcdata, glb: &mut Architecture) -> Result<()> {
        let special = self.new_ops[rop].special;
        if (special & TransformOp::INDIRECT_CREATION) != 0 {
            let replacement = self.new_ops[rop].replacement.expect("missing replacement op");
            data.mark_indirect_creation(replacement, false, glb)?;
        } else if (special & TransformOp::INDIRECT_CREATION_POSSIBLE_OUT) != 0 {
            let replacement = self.new_ops[rop].replacement.expect("missing replacement op");
            data.mark_indirect_creation(replacement, true, glb)?;
        }
        Ok(())
    }

    pub fn create_ops(&mut self, data: &mut Funcdata, glb: &mut Architecture) -> Result<()> {
        for rop in 0..self.new_ops.len() {
            self.op_create_replacement(rop, data, glb)?;
        }
        loop {
            let mut follow_count = 0;
            for rop in 0..self.new_ops.len() {
                if !self.op_attempt_insertion(rop, data) {
                    follow_count += 1;
                }
            }
            if follow_count == 0 {
                break;
            }
        }
        Ok(())
    }

    pub fn create_varnodes(
        &mut self,
        input_list: &mut Vec<usize>,
        data: &mut Funcdata,
        glb: &mut Architecture,
    ) -> Result<()> {
        let arrays: Vec<usize> = self.piece_map.values().copied().collect();
        for first in arrays {
            let mut rvn = first;
            loop {
                if self.new_varnodes[rvn].var_type == TransformVar::PIECE {
                    let vn = self.new_varnodes[rvn].vn.expect("missing piece varnode");
                    if data.vn(vn).is_input() {
                        input_list.push(rvn);
                        if data.vn(vn).is_mark() {
                            self.new_varnodes[rvn].flags |= TransformVar::INPUT_DUPLICATE;
                        } else {
                            data.vn_mut(vn).set_mark();
                        }
                    }
                }
                self.var_create_replacement(rvn, data, glb)?;
                if (self.new_varnodes[rvn].flags & TransformVar::SPLIT_TERMINATOR) != 0 {
                    break;
                }
                rvn += 1;
            }
        }
        for rvn in 0..self.new_varnodes.len() {
            self.var_create_replacement(rvn, data, glb)?;
        }
        Ok(())
    }

    pub fn remove_old(&mut self, data: &mut Funcdata) -> Result<()> {
        for rop in 0..self.new_ops.len() {
            if (self.new_ops[rop].special & TransformOp::OP_REPLACEMENT) != 0 {
                let op = self.new_ops[rop].op.expect("missing replaced op");
                if !data.op(op).is_dead() {
                    data.op_destroy(op)?;
                }
            }
        }
        Ok(())
    }

    pub fn transform_input_varnodes(
        &mut self,
        input_list: &[usize],
        data: &mut Funcdata,
        glb: &mut Architecture,
    ) -> Result<()> {
        for &rvn in input_list {
            if (self.new_varnodes[rvn].flags & TransformVar::INPUT_DUPLICATE) == 0 {
                let vn = self.new_varnodes[rvn].vn.expect("missing input varnode");
                data.delete_varnode(vn)?;
            }
            let replacement = self.new_varnodes[rvn].replacement.expect("missing replacement varnode");
            let input = data.set_input_varnode(replacement, glb)?;
            self.new_varnodes[rvn].replacement = Some(input);
        }
        Ok(())
    }

    pub fn place_inputs(&mut self, data: &mut Funcdata, glb: &mut Architecture) -> Result<()> {
        for rop in 0..self.new_ops.len() {
            let op = self.new_ops[rop].replacement.expect("missing replacement op");
            for slot in 0..self.new_ops[rop].input.len() {
                let rvn = self.new_ops[rop].input[slot].expect("missing transform input");
                let vn = self.new_varnodes[rvn].replacement.expect("missing replacement varnode");
                data.op_set_input(op, vn, slot as i32)?;
            }
            self.special_handling(rop, data, glb)?;
        }
        Ok(())
    }

    pub fn preserve_address(&self, vn: VarnodeId, _bit_size: i32, lsb_offset: i32, data: &Funcdata) -> bool {
        match self.flavor {
            TransformFlavor::Standard => {
                if (lsb_offset & 7) != 0 {
                    return false;
                }
                let space = data.vn(vn).get_space().expect("varnode without space");
                if space.get_type() == SpaceType::Internal {
                    return false;
                }
                true
            }
            TransformFlavor::Subfloat => data.vn(vn).is_input(),
        }
    }

    pub fn clear_varnode_marks(&mut self, data: &mut Funcdata) {
        for &rvn in self.piece_map.values() {
            if let Some(vn) = self.new_varnodes[rvn].vn {
                data.vn_mut(vn).clear_mark();
            }
        }
    }

    pub fn new_preexisting_varnode(&mut self, vn: VarnodeId, data: &Funcdata) -> usize {
        let res = self.new_varnodes.len();
        self.new_varnodes.push(TransformVar::default());
        let original = data.vn(vn);
        self.piece_map.insert(original.get_create_index(), res);
        let size = original.get_size();
        self.new_varnodes[res].initialize(TransformVar::PREEXISTING, Some(vn), size * 8, size, 0);
        self.new_varnodes[res].flags = TransformVar::SPLIT_TERMINATOR;
        res
    }

    pub fn new_unique(&mut self, size: i32) -> usize {
        let res = self.new_varnodes.len();
        self.new_varnodes.push(TransformVar::default());
        self.new_varnodes[res].initialize(TransformVar::NORMAL_TEMP, None, size * 8, size, 0);
        res
    }

    pub fn new_constant(&mut self, size: i32, lsb_offset: i32, val: u64) -> usize {
        let res = self.new_varnodes.len();
        self.new_varnodes.push(TransformVar::default());
        let value = val.wrapping_shr(lsb_offset as u32) & calc_mask(size);
        self.new_varnodes[res].initialize(TransformVar::CONSTANT, None, size * 8, size, value);
        res
    }

    pub fn new_piece(&mut self, vn: VarnodeId, bit_size: i32, lsb_offset: i32, data: &Funcdata) -> usize {
        let res = self.new_varnodes.len();
        self.new_varnodes.push(TransformVar::default());
        self.piece_map.insert(data.vn(vn).get_create_index(), res);
        let byte_size = (bit_size + 7) / 8;
        let var_type = if self.preserve_address(vn, bit_size, lsb_offset, data) {
            TransformVar::PIECE
        } else {
            TransformVar::PIECE_TEMP
        };
        self.new_varnodes[res].initialize(var_type, Some(vn), bit_size, byte_size, lsb_offset as i64 as u64);
        self.new_varnodes[res].flags = TransformVar::SPLIT_TERMINATOR;
        res
    }

    fn fill_split_lane(&mut self, slot: usize, vn: VarnodeId, bitpos: i32, byte_size: i32, data: &Funcdata) {
        let original = data.vn(vn);
        if original.is_constant() {
            let val = if bitpos < 64 {
                (original.get_offset() >> bitpos) & calc_mask(byte_size)
            } else {
                0
            };
            self.new_varnodes[slot].initialize(TransformVar::CONSTANT, Some(vn), byte_size * 8, byte_size, val);
        } else {
            let var_type = if self.preserve_address(vn, byte_size * 8, bitpos, data) {
                TransformVar::PIECE
            } else {
                TransformVar::PIECE_TEMP
            };
            self.new_varnodes[slot].initialize(var_type, Some(vn), byte_size * 8, byte_size, bitpos as i64 as u64);
        }
    }

    pub fn new_split(&mut self, vn: VarnodeId, description: &LaneDescription, data: &Funcdata) -> usize {
        let num = description.get_num_lanes();
        let res = self.new_varnodes.len();
        for _ in 0..num {
            self.new_varnodes.push(TransformVar::default());
        }
        self.piece_map.insert(data.vn(vn).get_create_index(), res);
        for index in 0..num {
            let bitpos = description.get_position(index) * 8;
            let byte_size = description.get_size(index);
            self.fill_split_lane(res + index as usize, vn, bitpos, byte_size, data);
        }
        self.new_varnodes[res + num as usize - 1].flags = TransformVar::SPLIT_TERMINATOR;
        res
    }

    pub fn new_split_lanes(
        &mut self,
        vn: VarnodeId,
        description: &LaneDescription,
        num_lanes: i32,
        start_lane: i32,
        data: &Funcdata,
    ) -> usize {
        let res = self.new_varnodes.len();
        for _ in 0..num_lanes {
            self.new_varnodes.push(TransformVar::default());
        }
        self.piece_map.insert(data.vn(vn).get_create_index(), res);
        let base_bit_pos = description.get_position(start_lane) * 8;
        for index in 0..num_lanes {
            let bitpos = description.get_position(start_lane + index) * 8 - base_bit_pos;
            let byte_size = description.get_size(start_lane + index);
            self.fill_split_lane(res + index as usize, vn, bitpos, byte_size, data);
        }
        self.new_varnodes[res + num_lanes as usize - 1].flags = TransformVar::SPLIT_TERMINATOR;
        res
    }

    fn push_op(
        &mut self,
        op: Option<OpId>,
        opc: OpCode,
        special: u32,
        follow: Option<usize>,
        num_params: i32,
    ) -> usize {
        self.new_ops.push(TransformOp {
            op,
            replacement: None,
            opc,
            special,
            output: None,
            input: vec![None; num_params as usize],
            follow,
        });
        self.new_ops.len() - 1
    }

    pub fn new_op_replace(&mut self, num_params: i32, opc: OpCode, replace: OpId) -> usize {
        self.push_op(Some(replace), opc, TransformOp::OP_REPLACEMENT, None, num_params)
    }

    pub fn new_indirect_replace(&mut self, replace: OpId, data: &Funcdata) -> usize {
        let mut special = TransformOp::OP_REPLACEMENT | TransformOp::OP_INDIRECT;
        let replace_op = data.op(replace);
        if replace_op.is_indirect_creation() {
            if data.vn(replace_op.get_in(0)).is_indirect_zero() {
                special |= TransformOp::INDIRECT_CREATION;
            } else {
                special |= TransformOp::INDIRECT_CREATION_POSSIBLE_OUT;
            }
        }
        self.push_op(Some(replace), OpCode::Indirect, special, None, 1)
    }

    pub fn new_op(&mut self, num_params: i32, opc: OpCode, follow: usize) -> usize {
        let op = self.new_ops[follow].op;
        self.push_op(op, opc, 0, Some(follow), num_params)
    }

    pub fn new_preexisting_op(&mut self, num_params: i32, opc: OpCode, original_op: OpId) -> usize {
        self.push_op(Some(original_op), opc, TransformOp::OP_PREEXISTING, None, num_params)
    }

    pub fn get_preexisting_varnode(&mut self, vn: VarnodeId, data: &Funcdata) -> usize {
        let original = data.vn(vn);
        if original.is_constant() {
            return self.new_constant(original.get_size(), 0, original.get_offset());
        }
        if let Some(&res) = self.piece_map.get(&original.get_create_index()) {
            return res;
        }
        self.new_preexisting_varnode(vn, data)
    }

    pub fn get_piece(&mut self, vn: VarnodeId, bit_size: i32, lsb_offset: i32, data: &Funcdata) -> Result<usize> {
        if let Some(&res) = self.piece_map.get(&data.vn(vn).get_create_index()) {
            let var = &self.new_varnodes[res];
            if var.bit_size != bit_size || var.val != lsb_offset as i64 as u64 {
                return Err(Error::Lowlevel(
                    "Cannot create multiple pieces for one Varnode through getPiece".to_string(),
                ));
            }
            return Ok(res);
        }
        Ok(self.new_piece(vn, bit_size, lsb_offset, data))
    }

    pub fn get_split(&mut self, vn: VarnodeId, description: &LaneDescription, data: &Funcdata) -> usize {
        if let Some(&res) = self.piece_map.get(&data.vn(vn).get_create_index()) {
            return res;
        }
        self.new_split(vn, description, data)
    }

    pub fn get_split_lanes(
        &mut self,
        vn: VarnodeId,
        description: &LaneDescription,
        num_lanes: i32,
        start_lane: i32,
        data: &Funcdata,
    ) -> usize {
        if let Some(&res) = self.piece_map.get(&data.vn(vn).get_create_index()) {
            return res;
        }
        self.new_split_lanes(vn, description, num_lanes, start_lane, data)
    }

    pub fn op_set_input(&mut self, rop: usize, rvn: usize, slot: i32) {
        self.new_ops[rop].input[slot as usize] = Some(rvn);
    }

    pub fn op_set_output(&mut self, rop: usize, rvn: usize) {
        self.new_ops[rop].output = Some(rvn);
        self.new_varnodes[rvn].def = Some(rop);
    }

    pub fn preexisting_guard(slot: i32, rvn: &TransformVar) -> bool {
        if slot == 0 {
            return true;
        }
        if rvn.var_type == TransformVar::PIECE || rvn.var_type == TransformVar::PIECE_TEMP {
            return false;
        }
        true
    }

    pub fn apply(&mut self, data: &mut Funcdata, glb: &mut Architecture) -> Result<()> {
        let mut input_list: Vec<usize> = Vec::new();
        self.create_ops(data, glb)?;
        self.create_varnodes(&mut input_list, data, glb)?;
        self.remove_old(data)?;
        self.transform_input_varnodes(&input_list, data, glb)?;
        self.place_inputs(data, glb)?;
        Ok(())
    }
}

impl Default for TransformManager {
    fn default() -> TransformManager {
        TransformManager::new()
    }
}
