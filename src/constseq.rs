use crate::stdsort::std_sort;
use std::collections::BTreeMap;

use crate::action::{ActionGroupList, Rule, RuleBase};
use crate::address::{Address, calc_mask};
use crate::architecture::Architecture;
use crate::block::BlockId;
use crate::database::EntryId;
use crate::error::Result;
use crate::funcdata::Funcdata;
use crate::op::OpId;
use crate::opcodes::OpCode;
use crate::ruleaction::{types, types_mut, written_def};
use crate::space::{AddrSpace, SpaceRef, SpaceType};
use crate::types::{Datatype, TypeId, TypeMetatype};
use crate::userop::{UserOpManage, UserPcodeOp};
use crate::varnode::VarnodeId;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct WriteNode {
    pub offset: u64,
    pub op: OpId,
    pub slot: i32,
}

impl WriteNode {
    pub fn new(off: u64, op_2: OpId, sl: i32) -> WriteNode {
        WriteNode {
            offset: off,
            op: op_2,
            slot: sl,
        }
    }

    pub fn less_than(&self, node2: &WriteNode, data: &Funcdata) -> bool {
        data.op(self.op).get_seq_num().get_order() < data.op(node2.op).get_seq_num().get_order()
    }
}

fn space_index(space: Option<&SpaceRef>) -> Option<i32> {
    space.map(|spc| spc.get_index())
}

pub struct ArraySequence {
    pub root_op: OpId,
    pub char_type: TypeId,
    pub block: BlockId,
    pub num_elements: i32,
    pub move_ops: Vec<WriteNode>,
    pub byte_array: Vec<u8>,
}

impl ArraySequence {
    pub const MINIMUM_SEQUENCE_LENGTH: i32 = 4;
    pub const MAXIMUM_SEQUENCE_LENGTH: i32 = 0x20000;

    pub fn new(fdata: &Funcdata, ct: TypeId, root: OpId) -> ArraySequence {
        ArraySequence {
            root_op: root,
            char_type: ct,
            block: fdata.op(root).get_parent().expect("op without parent block"),
            num_elements: 0,
            move_ops: Vec::new(),
            byte_array: Vec::new(),
        }
    }

    pub fn interfere_between(start_op: OpId, end_op: OpId, data: &Funcdata) -> bool {
        let mut cur = data.op_next_op(start_op).expect("op sequence ends before the end op");
        while cur != end_op {
            if data.op(cur).get_eval_type() == crate::op::PcodeOp::SPECIAL {
                let opc = data.op(cur).code();
                if opc != OpCode::Indirect
                    && opc != OpCode::Callother
                    && opc != OpCode::Segmentop
                    && opc != OpCode::Cpoolref
                    && opc != OpCode::New
                {
                    return false;
                }
            }
            cur = data.op_next_op(cur).expect("op sequence ends before the end op");
        }
        true
    }

    pub fn check_interference(&mut self, data: &Funcdata) -> bool {
        self.move_ops.sort_by(|first, second| {
            let first_order = data.op(first.op).get_seq_num().get_order();
            let second_order = data.op(second.op).get_seq_num().get_order();
            first_order.cmp(&second_order)
        });
        let Some(pos) = self.move_ops.iter().position(|node| node.op == self.root_op) else {
            return false;
        };
        let mut cur_op = self.move_ops[pos].op;
        let mut starting_pos = pos as i32 - 1;
        while starting_pos >= 0 {
            let prev_op = self.move_ops[starting_pos as usize].op;
            if !ArraySequence::interfere_between(prev_op, cur_op, data) {
                break;
            }
            cur_op = prev_op;
            starting_pos -= 1;
        }
        starting_pos += 1;
        cur_op = self.move_ops[pos].op;
        let mut ending_pos = pos + 1;
        while ending_pos < self.move_ops.len() {
            let next_op = self.move_ops[ending_pos].op;
            if !ArraySequence::interfere_between(cur_op, next_op, data) {
                break;
            }
            cur_op = next_op;
            ending_pos += 1;
        }
        let starting_pos = starting_pos as usize;
        if (ending_pos - starting_pos) < ArraySequence::MINIMUM_SEQUENCE_LENGTH as usize {
            return false;
        }
        if starting_pos > 0 {
            for index in starting_pos..ending_pos {
                self.move_ops[index - starting_pos] = self.move_ops[index].clone();
            }
        }
        self.move_ops.truncate(ending_pos - starting_pos);
        true
    }

    pub fn form_byte_array(
        &mut self,
        sz: i32,
        slot: i32,
        root_off: u64,
        big_endian: bool,
        data: &Funcdata,
        glb: &Architecture,
    ) -> i32 {
        self.byte_array.resize(sz as usize, 0);
        let mut used: Vec<u8> = vec![0; sz as usize];
        let char_type = types(glb).get(self.char_type);
        let el_size = char_type.get_size();
        for node in self.move_ops.iter() {
            let byte_pos = node.offset.wrapping_sub(root_off) as i32;
            if byte_pos < 0 || byte_pos + el_size > sz {
                continue;
            }
            let mut val = data.vn(data.op(node.op).get_in(slot)).get_offset();
            used[byte_pos as usize] = if val == 0 { 2 } else { 1 };
            if big_endian {
                for index in 0..el_size {
                    let shift = ((el_size - 1 - index) * 8) as u32;
                    self.byte_array[(byte_pos + index) as usize] = (val.wrapping_shr(shift) & 0xff) as u8;
                }
            } else {
                for index in 0..el_size {
                    self.byte_array[(byte_pos + index) as usize] = val as u8;
                    val >>= 8;
                }
            }
        }
        let big_el_size = char_type.get_align_size();
        let max_el = used.len() as i32 / big_el_size;
        let mut count = 0;
        while count < max_el {
            let val = used[(count * big_el_size) as usize];
            if val != 1 {
                if val == 2 {
                    count += 1;
                }
                break;
            }
            count += 1;
        }
        if count < ArraySequence::MINIMUM_SEQUENCE_LENGTH {
            return 0;
        }
        if count as usize != self.move_ops.len() {
            let max_off = root_off.wrapping_add((count * big_el_size) as i64 as u64);
            let final_ops: Vec<WriteNode> = self
                .move_ops
                .iter()
                .filter(|node| node.offset < max_off)
                .cloned()
                .collect();
            self.move_ops = final_ops;
        }
        count
    }

    pub fn select_string_copy_function(&mut self, index: &mut i32, glb: &mut Architecture) -> Result<u32> {
        let factory = types_mut(glb);
        let char_size = factory.get_size_of_char();
        if self.char_type == factory.get_type_char(char_size)? {
            *index = self.num_elements;
            return Ok(UserPcodeOp::BUILTIN_STRNCPY);
        }
        let wchar_size = factory.get_size_of_wchar();
        if self.char_type == factory.get_type_char(wchar_size)? {
            *index = self.num_elements;
            return Ok(UserPcodeOp::BUILTIN_WCSNCPY);
        }
        *index = self.num_elements * factory.get(self.char_type).get_align_size();
        Ok(UserPcodeOp::BUILTIN_MEMCPY)
    }

    pub fn is_valid(&self) -> bool {
        self.num_elements != 0
    }
}

pub struct StringSequence {
    pub seq: ArraySequence,
    pub root_addr: Address,
    pub start_addr: Address,
    pub entry: EntryId,
}

impl StringSequence {
    pub fn new(
        fdata: &mut Funcdata,
        ct: TypeId,
        ent: EntryId,
        root: OpId,
        addr: &Address,
        glb: &mut Architecture,
    ) -> StringSequence {
        let mut sequence = StringSequence {
            seq: ArraySequence::new(fdata, ct, root),
            root_addr: addr.clone(),
            start_addr: Address::invalid(),
            entry: ent,
        };
        let database = glb.symboltab.as_deref().expect("symbol table is not initialized");
        let entry = database.entries.get(ent);
        if space_index(entry.get_addr().get_space()) != space_index(addr.get_space()) {
            return sequence;
        }
        let entry_first = entry.get_first();
        let entry_size = entry.get_size();
        let symbol_type = database
            .symbols
            .get(entry.get_symbol())
            .tp
            .expect("symbol without data-type");
        let mut off = sequence.root_addr.get_offset().wrapping_sub(entry_first) as i64;
        if off >= entry_size as i64 {
            return sequence;
        }
        if fdata.vn(fdata.op(sequence.seq.root_op).get_in(0)).get_offset() == 0 {
            return sequence;
        }
        let mut parent_type = Some(symbol_type);
        let mut array_type: Option<TypeId> = None;
        let mut last_off: i64 = 0;
        while let Some(current) = parent_type {
            if current == ct {
                break;
            }
            array_type = Some(current);
            last_off = off;
            if types(glb).get(current).needs_resolution() {
                let mut new_off = off;
                match Datatype::resolve_truncation(current, off, root, -1, &mut new_off, fdata, glb) {
                    Ok(None) | Err(_) => break,
                    Ok(Some(field)) => parent_type = Some(field.tp),
                }
                off = new_off;
            } else {
                let mut new_off = 0;
                parent_type = types(glb).get(current).get_sub_type(off, &mut new_off, glb);
                off = new_off;
            }
        }
        let Some(array_type) = array_type else { return sequence };
        if parent_type != Some(ct) || types(glb).get(array_type).get_metatype() != TypeMetatype::Array {
            return sequence;
        }
        sequence.start_addr = sequence.root_addr.sub(last_off);
        let array_size = types(glb).get(array_type).get_size();
        if !sequence.collect_copy_ops(array_size, fdata, glb) {
            return sequence;
        }
        if !sequence.seq.check_interference(fdata) {
            return sequence;
        }
        let arr_size = array_size
            - sequence
                .root_addr
                .get_offset()
                .wrapping_sub(sequence.start_addr.get_offset()) as i32;
        let root_off = sequence.root_addr.get_offset();
        let big_endian = sequence.root_addr.is_big_endian();
        sequence.seq.num_elements = sequence
            .seq
            .form_byte_array(arr_size, 0, root_off, big_endian, fdata, glb);
        sequence
    }

    pub fn collect_copy_ops(&mut self, size: i32, data: &Funcdata, glb: &Architecture) -> bool {
        let end_addr = self.start_addr.add((size - 1) as i64);
        let align_size = types(glb).get(self.seq.char_type).get_align_size();
        let char_size = types(glb).get(self.seq.char_type).get_size();
        let mut begin_addr = self.start_addr.clone();
        if self.start_addr != self.root_addr {
            begin_addr = self.root_addr.sub(align_size as i64);
        }
        let iter = data.begin_loc_addr(&begin_addr);
        let enditer = data.end_loc_addr(&end_addr, glb);
        let mut diff = self.root_addr.get_offset().wrapping_sub(self.start_addr.get_offset()) as i32;
        for vn in data.vbank.loc_range(&iter, &enditer) {
            let Some(op) = written_def(data, vn) else { continue };
            if data.op(op).code() != OpCode::Copy {
                continue;
            }
            if data.op(op).get_parent() != Some(self.seq.block) {
                continue;
            }
            if !data.vn(data.op(op).get_in(0)).is_constant() {
                continue;
            }
            if data.vn(vn).get_size() != char_size {
                return false;
            }
            let tmp_diff = data.vn(vn).get_offset().wrapping_sub(self.start_addr.get_offset()) as i32;
            if tmp_diff < diff {
                if tmp_diff + align_size == diff {
                    return false;
                }
                continue;
            } else if tmp_diff > diff {
                if tmp_diff - diff < align_size {
                    continue;
                }
                if tmp_diff - diff > align_size {
                    break;
                }
                diff = tmp_diff;
            }
            self.seq.move_ops.push(WriteNode::new(data.vn(vn).get_offset(), op, -1));
        }
        self.seq.move_ops.len() >= ArraySequence::MINIMUM_SEQUENCE_LENGTH as usize
    }

    pub fn build_string_copy(&mut self, data: &mut Funcdata, glb: &mut Architecture) -> Result<Option<OpId>> {
        let insert_point = self.seq.move_ops[0].op;
        let char_size = types(glb).get(self.seq.char_type).get_size();
        let num_bytes = self.seq.move_ops.len() as i32 * char_size;
        let word_size = self
            .root_addr
            .get_space()
            .expect("address without space")
            .get_word_size();
        let factory = types_mut(glb);
        let pointer_size = factory.get_size_of_pointer();
        let char_ptr_type = factory.get_type_pointer(pointer_size, self.seq.char_type, word_size)?;
        let byte_array = self.seq.byte_array.clone();
        let Some(src_ptr) = data.get_internal_string(&byte_array, num_bytes, char_ptr_type, insert_point, glb)? else {
            return Ok(None);
        };
        let mut index = 0;
        let built_in_id = self.seq.select_string_copy_function(&mut index, glb)?;
        UserOpManage::register_builtin(glb, built_in_id)?;
        let addr = data.op(insert_point).get_addr().clone();
        let copy_op = data.new_op(4, &addr);
        data.op_set_opcode(copy_op, OpCode::Callother, glb);
        let idvn = data.new_constant(4, built_in_id as u64, glb);
        data.op_set_input(copy_op, idvn, 0)?;
        let dest_ptr = self.construct_typed_pointer(insert_point, data, glb)?;
        data.op_set_input(copy_op, dest_ptr, 1)?;
        data.op_set_input(copy_op, src_ptr, 2)?;
        let dest_type = data.vn(dest_ptr).get_type();
        if types(glb).get(dest_type).needs_resolution() {
            data.inherit_union_field_ptr(dest_type, copy_op, 1, insert_point, -1, glb);
        }
        let len_vn = data.new_constant(4, index as i64 as u64, glb);
        let len_type = data.op_input_type_local(copy_op, 3, glb);
        data.vn_update_type(len_vn, len_type);
        data.op_set_input(copy_op, len_vn, 3)?;
        data.op_insert_before(copy_op, insert_point);
        Ok(Some(copy_op))
    }

    pub fn remove_forward(
        cur_node: &WriteNode,
        xref: &mut BTreeMap<OpId, usize>,
        points: &mut Vec<Option<WriteNode>>,
        dead_ops: &mut Vec<WriteNode>,
        data: &Funcdata,
    ) {
        let vn = data.op(cur_node.op).get_out().expect("op without output");
        for &op in data.vn(vn).descend() {
            if let Some(&position) = xref.get(&op) {
                let mut off = points[position]
                    .as_ref()
                    .expect("concatenation point already removed")
                    .offset;
                if cur_node.offset < off {
                    off = cur_node.offset;
                }
                points[position] = None;
                dead_ops.push(WriteNode::new(off, op, -1));
            } else {
                let slot = data.op(op).get_slot(vn);
                points.push(Some(WriteNode::new(cur_node.offset, op, slot)));
                if data.op(op).code() == OpCode::Piece {
                    xref.insert(op, points.len() - 1);
                }
            }
        }
    }

    pub fn remove_copy_ops(&mut self, replace_op: OpId, data: &mut Funcdata, glb: &mut Architecture) -> Result<()> {
        let mut concat_set: BTreeMap<OpId, usize> = BTreeMap::new();
        let mut points: Vec<Option<WriteNode>> = Vec::new();
        let mut dead_ops: Vec<WriteNode> = Vec::new();
        for node in self.seq.move_ops.iter() {
            StringSequence::remove_forward(node, &mut concat_set, &mut points, &mut dead_ops, data);
        }
        let mut pos = 0;
        while pos < dead_ops.len() {
            let node = dead_ops[pos].clone();
            StringSequence::remove_forward(&node, &mut concat_set, &mut points, &mut dead_ops, data);
            pos += 1;
        }
        for point in points.iter().flatten() {
            let vn = data.op(point.op).get_in(point.slot);
            let def = data.vn(vn).get_def().expect("removed copy output without defining op");
            if data.op(def).code() != OpCode::Indirect {
                let new_in = data.new_constant(data.vn(vn).get_size(), 0, glb);
                let ind_op = data.new_indirect(replace_op, glb)?;
                data.op_set_input(ind_op, new_in, 0)?;
                data.op_set_output(ind_op, vn, glb)?;
                data.mark_indirect_creation(ind_op, false, glb)?;
                data.op_insert_before(ind_op, replace_op);
            }
        }
        for node in self.seq.move_ops.iter() {
            data.op_destroy(node.op)?;
        }
        for node in dead_ops.iter() {
            data.op_destroy(node.op)?;
        }
        Ok(())
    }

    pub fn construct_typed_pointer(
        &mut self,
        insert_point: OpId,
        data: &mut Funcdata,
        glb: &mut Architecture,
    ) -> Result<VarnodeId> {
        let spc = self.root_addr.get_space().expect("address without space").clone();
        let mut space_ptr = if spc.get_type() == SpaceType::Spacebase {
            data.construct_spacebase_input(&spc, glb)?
        } else {
            data.construct_const_spacebase(&spc, glb)?
        };
        let database = glb.symboltab.as_deref().expect("symbol table is not initialized");
        let entry = database.entries.get(self.entry);
        let entry_first = entry.get_first();
        let mut base_type = database
            .symbols
            .get(entry.get_symbol())
            .tp
            .expect("symbol without data-type");
        let word_size = spc.get_word_size();
        let addr = data.op(insert_point).get_addr().clone();
        let mut ptrsub = data.new_op(2, &addr);
        data.op_set_opcode(ptrsub, OpCode::Ptrsub, glb);
        data.op_set_input(ptrsub, space_ptr, 0)?;
        let mut base_off = AddrSpace::byte_to_address(entry_first, word_size);
        let ptr_size = data.vn(space_ptr).get_size();
        let offvn = data.new_constant(ptr_size, base_off, glb);
        data.op_set_input(ptrsub, offvn, 1)?;
        space_ptr = data.new_unique_out(ptr_size, ptrsub, glb)?;
        data.op_insert_before(ptrsub, insert_point);
        let mut cur_type = types_mut(glb).get_type_pointer_strip_array(ptr_size, base_type, word_size)?;
        data.vn_update_type(space_ptr, cur_type);
        let mut cur_off = self.root_addr.get_offset().wrapping_sub(entry_first) as i64;
        while base_type != self.seq.char_type {
            let mut el_size = -1;
            let factory = types(glb);
            if factory.get(base_type).get_metatype() == TypeMetatype::Array {
                el_size = factory.get(factory.get(base_type).get_base()).get_align_size();
            }
            let mut new_off: i64 = 0;
            if factory.get(base_type).needs_resolution() {
                match Datatype::resolve_truncation(base_type, cur_off, insert_point, -1, &mut new_off, data, glb)? {
                    Some(field) => {
                        base_type = field.tp;
                        cur_off = new_off;
                        continue;
                    }
                    None => break,
                }
            } else {
                match factory.get(base_type).get_sub_type(cur_off, &mut new_off, glb) {
                    Some(sub) => base_type = sub,
                    None => break,
                }
            }
            cur_off -= new_off;
            base_off = AddrSpace::byte_to_address(cur_off as u64, word_size);
            if el_size >= 0 {
                if cur_off == 0 {
                    continue;
                }
                ptrsub = data.new_op(3, &addr);
                data.op_set_opcode(ptrsub, OpCode::Ptradd, glb);
                let num_el = cur_off / el_size as i64;
                let numvn = data.new_constant(4, num_el as u64, glb);
                data.op_set_input(ptrsub, numvn, 1)?;
                let sizevn = data.new_constant(4, el_size as i64 as u64, glb);
                data.op_set_input(ptrsub, sizevn, 2)?;
            } else {
                ptrsub = data.new_op(2, &addr);
                data.op_set_opcode(ptrsub, OpCode::Ptrsub, glb);
                let offvn = data.new_constant(data.vn(space_ptr).get_size(), base_off, glb);
                data.op_set_input(ptrsub, offvn, 1)?;
            }
            data.op_set_input(ptrsub, space_ptr, 0)?;
            if types(glb).get(cur_type).needs_resolution() {
                data.inherit_union_field_ptr(cur_type, ptrsub, 0, insert_point, -1, glb);
            }
            space_ptr = data.new_unique_out(data.vn(space_ptr).get_size(), ptrsub, glb)?;
            data.op_insert_before(ptrsub, insert_point);
            cur_type =
                types_mut(glb).get_type_pointer_strip_array(data.vn(space_ptr).get_size(), base_type, word_size)?;
            data.vn_update_type(space_ptr, cur_type);
            cur_off = new_off;
        }
        if cur_off != 0 {
            let add_op = data.new_op(2, &addr);
            data.op_set_opcode(add_op, OpCode::IntAdd, glb);
            data.op_set_input(add_op, space_ptr, 0)?;
            base_off = AddrSpace::byte_to_address(cur_off as u64, word_size);
            let offvn = data.new_constant(data.vn(space_ptr).get_size(), base_off, glb);
            data.op_set_input(add_op, offvn, 1)?;
            space_ptr = data.new_unique_out(data.vn(space_ptr).get_size(), add_op, glb)?;
            data.op_insert_before(add_op, insert_point);
            cur_type = types_mut(glb).get_type_pointer(data.vn(space_ptr).get_size(), self.seq.char_type, word_size)?;
            data.vn_update_type(space_ptr, cur_type);
        }
        Ok(space_ptr)
    }

    pub fn transform(&mut self, data: &mut Funcdata, glb: &mut Architecture) -> Result<bool> {
        let Some(mem_cpy_op) = self.build_string_copy(data, glb)? else {
            return Ok(false);
        };
        self.remove_copy_ops(mem_cpy_op, data, glb)?;
        Ok(true)
    }

    pub fn is_valid(&self) -> bool {
        self.seq.is_valid()
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct IndirectPair {
    pub in_vn: Option<VarnodeId>,
    pub out_vn: VarnodeId,
}

impl IndirectPair {
    pub fn new(input: VarnodeId, out: VarnodeId) -> IndirectPair {
        IndirectPair {
            in_vn: Some(input),
            out_vn: out,
        }
    }

    pub fn mark_duplicate(&mut self) {
        self.in_vn = None;
    }

    pub fn is_duplicate(&self) -> bool {
        self.in_vn.is_none()
    }

    pub fn compare_output(first: &IndirectPair, second: &IndirectPair, data: &Funcdata) -> bool {
        let vn1 = data.vn(first.out_vn);
        let vn2 = data.vn(second.out_vn);
        let space1 = space_index(vn1.get_space());
        let space2 = space_index(vn2.get_space());
        if space1 != space2 {
            return space1 < space2;
        }
        if vn1.get_offset() != vn2.get_offset() {
            return vn1.get_offset() < vn2.get_offset();
        }
        if vn1.get_size() != vn2.get_size() {
            return vn1.get_size() < vn2.get_size();
        }
        false
    }
}

pub struct HeapSequence {
    pub seq: ArraySequence,
    pub base_pointer: Option<VarnodeId>,
    pub immed_read: Option<OpId>,
    pub base_offset: u64,
    pub store_space: Option<SpaceRef>,
    pub ptr_add_mult: i32,
    pub non_const_adds: Vec<VarnodeId>,
}

impl HeapSequence {
    pub fn new(fdata: &mut Funcdata, ct: TypeId, root: OpId, glb: &mut Architecture) -> HeapSequence {
        let store_space = fdata
            .vn(fdata.op(root).get_in(0))
            .get_space_from_const(&glb.manager)
            .expect("store operand without space");
        let align_size = types(glb).get(ct).get_align_size();
        let ptr_add_mult = AddrSpace::byte_to_address_int(align_size as i64, store_space.get_word_size()) as i32;
        let big_endian = store_space.is_big_endian();
        let mut sequence = HeapSequence {
            seq: ArraySequence::new(fdata, ct, root),
            base_pointer: None,
            immed_read: None,
            base_offset: 0,
            store_space: Some(store_space),
            ptr_add_mult,
            non_const_adds: Vec::new(),
        };
        sequence.find_base_pointer(fdata);
        if !sequence.collect_store_ops(fdata, glb) {
            return sequence;
        }
        if !sequence.seq.check_interference(fdata) {
            return sequence;
        }
        let arr_size = sequence.seq.move_ops.len() as i32 * align_size;
        sequence.seq.num_elements = sequence.seq.form_byte_array(arr_size, 2, 0, big_endian, fdata, glb);
        sequence
    }

    fn base(&self) -> VarnodeId {
        self.base_pointer.expect("base pointer is not computed")
    }

    fn word_size(&self) -> u32 {
        self.store_space
            .as_ref()
            .expect("store space is not defined")
            .get_word_size()
    }

    pub fn find_base_pointer(&mut self, data: &Funcdata) {
        let mut base = data.op(self.seq.root_op).get_in(1);
        let mut immed = self.seq.root_op;
        while let Some(op) = written_def(data, base) {
            let opc = data.op(op).code();
            if opc == OpCode::Ptradd {
                let sz = data.vn(data.op(op).get_in(2)).get_offset() as i64;
                if sz != self.ptr_add_mult as i64 {
                    break;
                }
            } else if opc != OpCode::Copy {
                break;
            }
            base = data.op(op).get_in(0);
            immed = op;
        }
        self.base_pointer = Some(base);
        self.immed_read = Some(immed);
    }

    pub fn find_duplicate_bases(&mut self, duplist: &mut Vec<VarnodeId>, data: &Funcdata) {
        let base = self.base();
        let Some(mut op) = written_def(data, base) else {
            duplist.push(base);
            return;
        };
        let mut opc = data.op(op).code();
        if (opc != OpCode::Ptrsub && opc != OpCode::IntAdd && opc != OpCode::Ptradd)
            || !data.vn(data.op(op).get_in(1)).is_constant()
        {
            duplist.push(base);
            return;
        }
        let mut copy_root;
        let mut offset: Vec<u64> = Vec::new();
        loop {
            let mut off = data.vn(data.op(op).get_in(1)).get_offset();
            if opc == OpCode::Ptradd {
                off = off.wrapping_mul(data.vn(data.op(op).get_in(2)).get_offset());
            }
            offset.push(off);
            copy_root = data.op(op).get_in(0);
            let Some(next) = written_def(data, copy_root) else {
                break;
            };
            op = next;
            opc = data.op(op).code();
            if opc != OpCode::Ptrsub && opc != OpCode::IntAdd && opc != OpCode::Ptradd {
                break;
            }
            if !data.vn(data.op(op).get_in(1)).is_constant() {
                break;
            }
        }
        duplist.push(copy_root);
        for index in (0..offset.len()).rev() {
            let midlist = std::mem::take(duplist);
            for &vn in midlist.iter() {
                for &read_op in data.vn(vn).descend() {
                    let read_code = data.op(read_op).code();
                    if read_code != OpCode::Ptrsub && read_code != OpCode::IntAdd && read_code != OpCode::Ptradd {
                        continue;
                    }
                    if data.op(read_op).get_in(0) != vn || !data.vn(data.op(read_op).get_in(1)).is_constant() {
                        continue;
                    }
                    let mut off = data.vn(data.op(read_op).get_in(1)).get_offset();
                    if read_code == OpCode::Ptradd {
                        off = off.wrapping_mul(data.vn(data.op(read_op).get_in(2)).get_offset());
                    }
                    if off != offset[index] {
                        continue;
                    }
                    duplist.push(data.op(read_op).get_out().expect("op without output"));
                }
            }
        }
    }

    pub fn find_initial_stores(&mut self, stores: &mut Vec<OpId>, data: &Funcdata) {
        let mut ptradds: Vec<VarnodeId> = Vec::new();
        self.find_duplicate_bases(&mut ptradds, data);
        let mut pos = 0;
        while pos < ptradds.len() {
            let vn = ptradds[pos];
            pos += 1;
            for &op in data.vn(vn).descend() {
                let opc = data.op(op).code();
                if opc == OpCode::Ptradd {
                    if data.op(op).get_in(0) != vn {
                        continue;
                    }
                    if data.vn(data.op(op).get_in(2)).get_offset() != self.ptr_add_mult as i64 as u64 {
                        continue;
                    }
                    ptradds.push(data.op(op).get_out().expect("op without output"));
                } else if opc == OpCode::Copy {
                    ptradds.push(data.op(op).get_out().expect("op without output"));
                } else if opc == OpCode::Store
                    && data.op(op).get_parent() == Some(self.seq.block)
                    && op != self.seq.root_op
                {
                    if data.op(op).get_in(1) != vn {
                        continue;
                    }
                    stores.push(op);
                }
            }
        }
    }

    pub fn calc_add_elements(vn: VarnodeId, non_const: &mut Vec<VarnodeId>, max_depth: i32, data: &Funcdata) -> u64 {
        if data.vn(vn).is_constant() {
            return data.vn(vn).get_offset();
        }
        let def = match written_def(data, vn) {
            Some(def) if data.op(def).code() == OpCode::IntAdd && max_depth != 0 => def,
            _ => {
                non_const.push(vn);
                return 0;
            }
        };
        let res = HeapSequence::calc_add_elements(data.op(def).get_in(0), non_const, max_depth - 1, data);
        res.wrapping_add(HeapSequence::calc_add_elements(
            data.op(def).get_in(1),
            non_const,
            max_depth - 1,
            data,
        ))
    }

    pub fn calc_ptradd_offset(&mut self, vn: VarnodeId, non_const: &mut Vec<VarnodeId>, data: &Funcdata) -> u64 {
        let mut res: u64 = 0;
        let mut vn = vn;
        while let Some(op) = written_def(data, vn) {
            let opc = data.op(op).code();
            if opc == OpCode::Ptradd {
                let mult = data.vn(data.op(op).get_in(2)).get_offset();
                if mult != self.ptr_add_mult as i64 as u64 {
                    break;
                }
                let mut off = HeapSequence::calc_add_elements(data.op(op).get_in(1), non_const, 3, data);
                off = off.wrapping_mul(mult);
                res = res.wrapping_add(off);
                vn = data.op(op).get_in(0);
            } else if opc == OpCode::Copy {
                vn = data.op(op).get_in(0);
            } else {
                break;
            }
        }
        AddrSpace::address_to_byte_int(res as i64, self.word_size()) as u64
    }

    pub fn sets_equal(op1: &[VarnodeId], op2: &[VarnodeId]) -> bool {
        if op1.len() != op2.len() {
            return false;
        }
        op1.iter().zip(op2.iter()).all(|(first, second)| first == second)
    }

    pub fn test_value(&mut self, op: OpId, data: &Funcdata, glb: &Architecture) -> bool {
        let vn = data.op(op).get_in(2);
        if !data.vn(vn).is_constant() {
            return false;
        }
        if data.vn(vn).get_size() != types(glb).get(self.seq.char_type).get_size() {
            return false;
        }
        true
    }

    pub fn collect_store_ops(&mut self, data: &Funcdata, glb: &Architecture) -> bool {
        let mut init_stores: Vec<OpId> = Vec::new();
        self.find_initial_stores(&mut init_stores, data);
        if init_stores.len() + 1 < ArraySequence::MINIMUM_SEQUENCE_LENGTH as usize {
            return false;
        }
        let align_size = types(glb).get(self.seq.char_type).get_align_size();
        let max_size = (ArraySequence::MAXIMUM_SEQUENCE_LENGTH * align_size) as i64 as u64;
        let wrap_mask = calc_mask(
            self.store_space
                .as_ref()
                .expect("store space is not defined")
                .get_addr_size() as i32,
        );
        let mut non_const_adds = std::mem::take(&mut self.non_const_adds);
        self.base_offset = self.calc_ptradd_offset(data.op(self.seq.root_op).get_in(1), &mut non_const_adds, data);
        self.non_const_adds = non_const_adds;
        let mut non_const_comp: Vec<VarnodeId> = Vec::new();
        for &op in init_stores.iter() {
            non_const_comp.clear();
            let cur_offset = self.calc_ptradd_offset(data.op(op).get_in(1), &mut non_const_comp, data);
            let diff = cur_offset.wrapping_sub(self.base_offset) & wrap_mask;
            if HeapSequence::sets_equal(&self.non_const_adds, &non_const_comp) {
                if diff >= max_size {
                    return false;
                }
                if !self.test_value(op, data, glb) {
                    return false;
                }
                self.seq.move_ops.push(WriteNode::new(diff, op, -1));
            }
        }
        self.seq.move_ops.push(WriteNode::new(0, self.seq.root_op, -1));
        true
    }

    pub fn build_string_copy(&mut self, data: &mut Funcdata, glb: &mut Architecture) -> Result<Option<OpId>> {
        let insert_point = self.seq.move_ops[0].op;
        let root_ptr = data.op(self.seq.root_op).get_in(1);
        let char_ptr_type = data.vn_get_type_read_facing(root_ptr, self.seq.root_op, glb);
        let char_size = types(glb).get(self.seq.char_type).get_size();
        let align_size = types(glb).get(self.seq.char_type).get_align_size();
        let num_bytes = self.seq.num_elements * char_size;
        let byte_array = self.seq.byte_array.clone();
        let Some(src_ptr) = data.get_internal_string(&byte_array, num_bytes, char_ptr_type, insert_point, glb)? else {
            return Ok(None);
        };
        let base_pointer = self.base();
        let immed_read = self.immed_read.expect("base pointer reader is not computed");
        let base_size = data.vn(base_pointer).get_size();
        let addr = data.op(insert_point).get_addr().clone();
        let mut dest_ptr = base_pointer;
        if self.base_offset != 0 || !self.non_const_adds.is_empty() {
            let mut index_vn: Option<VarnodeId> = None;
            let int_type = types_mut(glb).get_base(base_size, TypeMetatype::Int)?;
            if !self.non_const_adds.is_empty() {
                let mut current = self.non_const_adds[0];
                for position in 1..self.non_const_adds.len() {
                    let add_op = data.new_op(2, &addr);
                    data.op_set_opcode(add_op, OpCode::IntAdd, glb);
                    data.op_set_input(add_op, current, 0)?;
                    data.op_set_input(add_op, self.non_const_adds[position], 1)?;
                    current = data.new_unique_out(data.vn(current).get_size(), add_op, glb)?;
                    data.vn_update_type(current, int_type);
                    data.op_insert_before(add_op, insert_point);
                }
                index_vn = Some(current);
            }
            if self.base_offset != 0 {
                let num_el = self.base_offset / align_size as i64 as u64;
                let cvn = data.new_constant(base_size, num_el, glb);
                data.vn_update_type(cvn, int_type);
                match index_vn {
                    None => index_vn = Some(cvn),
                    Some(current) => {
                        let add_op = data.new_op(2, &addr);
                        data.op_set_opcode(add_op, OpCode::IntAdd, glb);
                        data.op_set_input(add_op, current, 0)?;
                        data.op_set_input(add_op, cvn, 1)?;
                        let sum = data.new_unique_out(data.vn(current).get_size(), add_op, glb)?;
                        data.vn_update_type(sum, int_type);
                        data.op_insert_before(add_op, insert_point);
                        index_vn = Some(sum);
                    }
                }
            }
            let index_vn = index_vn.expect("index varnode is not built");
            let ptr_add = data.new_op(3, &addr);
            data.op_set_opcode(ptr_add, OpCode::Ptradd, glb);
            dest_ptr = data.new_unique_out(base_size, ptr_add, glb)?;
            data.op_set_input(ptr_add, base_pointer, 0)?;
            data.op_set_input(ptr_add, index_vn, 1)?;
            let sizevn = data.new_constant(base_size, align_size as i64 as u64, glb);
            data.op_set_input(ptr_add, sizevn, 2)?;
            data.vn_update_type(dest_ptr, char_ptr_type);
            data.op_insert_before(ptr_add, insert_point);
            let base_type = data.vn(base_pointer).get_type();
            if types(glb).get(base_type).needs_resolution() {
                let slot = data.op(immed_read).get_slot(base_pointer);
                data.inherit_union_field(base_type, ptr_add, 0, immed_read, slot, glb);
            }
        }
        let mut index = 0;
        let built_in_id = self.seq.select_string_copy_function(&mut index, glb)?;
        UserOpManage::register_builtin(glb, built_in_id)?;
        let copy_op = data.new_op(4, &addr);
        data.op_set_opcode(copy_op, OpCode::Callother, glb);
        let idvn = data.new_constant(4, built_in_id as u64, glb);
        data.op_set_input(copy_op, idvn, 0)?;
        data.op_set_input(copy_op, dest_ptr, 1)?;
        data.op_set_input(copy_op, src_ptr, 2)?;
        let len_vn = data.new_constant(4, index as i64 as u64, glb);
        let len_type = data.op_input_type_local(copy_op, 3, glb);
        data.vn_update_type(len_vn, len_type);
        data.op_set_input(copy_op, len_vn, 3)?;
        data.op_insert_before(copy_op, insert_point);
        let dest_type = data.vn(dest_ptr).get_type();
        if types(glb).get(dest_type).needs_resolution() {
            let slot = data.op(immed_read).get_slot(dest_ptr);
            data.inherit_union_field(dest_type, copy_op, 1, immed_read, slot, glb);
        }
        Ok(Some(copy_op))
    }

    pub fn gather_indirect_pairs(
        &mut self,
        indirects: &mut Vec<OpId>,
        pairs: &mut Vec<IndirectPair>,
        data: &mut Funcdata,
    ) {
        for node in self.seq.move_ops.iter() {
            let mut cur = data.op_previous_op(node.op);
            while let Some(op) = cur {
                if data.op(op).code() != OpCode::Indirect {
                    break;
                }
                data.op_mut(op).set_mark();
                indirects.push(op);
                cur = data.op_previous_op(op);
            }
        }
        for &op in indirects.iter() {
            let outvn = data.op(op).get_out().expect("op without output");
            let has_use = data
                .vn(outvn)
                .descend()
                .iter()
                .any(|&use_op| !data.op(use_op).is_mark());
            if has_use {
                let mut invn = data.op(op).get_in(0);
                while let Some(def_op) = written_def(data, invn) {
                    if !data.op(def_op).is_mark() {
                        break;
                    }
                    invn = data.op(def_op).get_in(0);
                }
                pairs.push(IndirectPair::new(invn, outvn));
            }
        }
        for &op in indirects.iter() {
            data.op_mut(op).clear_mark();
        }
    }

    pub fn deduplicate_pairs(&mut self, pairs: &mut [IndirectPair], data: &mut Funcdata) -> Result<bool> {
        if pairs.is_empty() {
            return Ok(true);
        }
        let mut copy: Vec<usize> = (0..pairs.len()).collect();
        std_sort(&mut copy, |&first, &second| {
            IndirectPair::compare_output(&pairs[first], &pairs[second], data)
        });
        let mut head = copy[0];
        let mut dup_count = 0;
        for &current in copy.iter().skip(1) {
            let overlap = data
                .vn(pairs[head].out_vn)
                .characterize_overlap(data.vn(pairs[current].out_vn));
            if overlap == 1 {
                return Ok(false);
            }
            if overlap == 2 {
                if pairs[current].in_vn != pairs[head].in_vn {
                    return Ok(false);
                }
                pairs[current].mark_duplicate();
                dup_count += 1;
            } else {
                head = current;
            }
        }
        if dup_count > 0 {
            head = copy[0];
            for &current in copy.iter().skip(1) {
                if pairs[current].is_duplicate() {
                    data.total_replace(pairs[current].out_vn, pairs[head].out_vn)?;
                } else {
                    head = current;
                }
            }
        }
        Ok(true)
    }

    pub fn remove_store_ops(
        &mut self,
        indirects: &mut [OpId],
        indirect_pairs: &mut [IndirectPair],
        replace_op: OpId,
        data: &mut Funcdata,
        glb: &mut Architecture,
    ) -> Result<()> {
        let mut scratch: Vec<OpId> = Vec::new();
        for pair in indirect_pairs.iter() {
            let def = data
                .vn(pair.out_vn)
                .get_def()
                .expect("indirect output without defining op");
            data.op_unset_output(def)?;
        }
        for node in self.seq.move_ops.iter() {
            data.op_destroy_recursive(node.op, &mut scratch)?;
        }
        for &op in indirects.iter() {
            data.op_destroy(op)?;
        }
        for pair in indirect_pairs.iter() {
            let Some(in_vn) = pair.in_vn else { continue };
            let new_ind = data.new_indirect(replace_op, glb)?;
            data.op_set_output(new_ind, pair.out_vn, glb)?;
            data.op_set_input(new_ind, in_vn, 0)?;
            data.op_insert_before(new_ind, replace_op);
        }
        Ok(())
    }

    pub fn transform(&mut self, data: &mut Funcdata, glb: &mut Architecture) -> Result<bool> {
        let mut indirects: Vec<OpId> = Vec::new();
        let mut indirect_pairs: Vec<IndirectPair> = Vec::new();
        self.gather_indirect_pairs(&mut indirects, &mut indirect_pairs, data);
        if !self.deduplicate_pairs(&mut indirect_pairs, data)? {
            return Ok(false);
        }
        let Some(mem_cpy_op) = self.build_string_copy(data, glb)? else {
            return Ok(false);
        };
        self.remove_store_ops(&mut indirects, &mut indirect_pairs, mem_cpy_op, data, glb)?;
        Ok(true)
    }

    pub fn is_valid(&self) -> bool {
        self.seq.is_valid()
    }
}

pub struct RuleStringCopy {
    pub base: RuleBase,
}

impl RuleStringCopy {
    pub fn new(group: &str) -> RuleStringCopy {
        RuleStringCopy {
            base: RuleBase::new(group, 0, "stringcopy"),
        }
    }
}

impl Rule for RuleStringCopy {
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
        Some(Box::new(RuleStringCopy::new(self.get_group())))
    }

    fn get_op_list(&self, oplist: &mut Vec<OpCode>) {
        oplist.push(OpCode::Copy);
    }

    fn apply_op(&mut self, op: OpId, data: &mut Funcdata, glb: &mut Architecture) -> Result<i32> {
        if !data.vn(data.op(op).get_in(0)).is_constant() {
            return Ok(0);
        }
        let outvn = data.op(op).get_out().expect("op without output");
        let ct = data.vn_get_type_def_facing(outvn, glb);
        let char_type = types(glb).get(ct);
        if !char_type.is_char_print() {
            return Ok(0);
        }
        if char_type.is_opaque_string() {
            return Ok(0);
        }
        if !data.vn(outvn).is_addr_tied() {
            return Ok(0);
        }
        let scope = data.get_scope_local().expect("function without local scope");
        let outaddr = data.vn(outvn).get_addr().clone();
        let opaddr = data.op(op).get_addr().clone();
        let database = glb.symboltab.as_deref().expect("symbol table is not initialized");
        let Some(entry) = database.scope_query_container(scope, &outaddr, data.vn(outvn).get_size(), &opaddr) else {
            return Ok(0);
        };
        let mut sequence = StringSequence::new(data, ct, entry, op, &outaddr, glb);
        if !sequence.is_valid() {
            return Ok(0);
        }
        if !sequence.transform(data, glb)? {
            return Ok(0);
        }
        Ok(1)
    }
}

pub struct RuleStringStore {
    pub base: RuleBase,
}

impl RuleStringStore {
    pub fn new(group: &str) -> RuleStringStore {
        RuleStringStore {
            base: RuleBase::new(group, 0, "stringstore"),
        }
    }
}

impl Rule for RuleStringStore {
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
        Some(Box::new(RuleStringStore::new(self.get_group())))
    }

    fn get_op_list(&self, oplist: &mut Vec<OpCode>) {
        oplist.push(OpCode::Store);
    }

    fn apply_op(&mut self, op: OpId, data: &mut Funcdata, glb: &mut Architecture) -> Result<i32> {
        if !data.vn(data.op(op).get_in(2)).is_constant() {
            return Ok(0);
        }
        let ptrvn = data.op(op).get_in(1);
        let ptr_type = data.vn_get_type_read_facing(ptrvn, op, glb);
        let factory = types(glb);
        if factory.get(ptr_type).get_metatype() != TypeMetatype::Ptr {
            return Ok(0);
        }
        let ct = factory.get(ptr_type).get_ptr_to();
        if !factory.get(ct).is_char_print() {
            return Ok(0);
        }
        if factory.get(ct).is_opaque_string() {
            return Ok(0);
        }
        let mut sequence = HeapSequence::new(data, ct, op, glb);
        if !sequence.is_valid() {
            return Ok(0);
        }
        if !sequence.transform(data, glb)? {
            return Ok(0);
        }
        Ok(1)
    }
}
