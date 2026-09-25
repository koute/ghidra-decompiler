use crate::stdsort::std_sort;
use std::collections::VecDeque;

use crate::action::{ActionGroupList, Rule, RuleBase};
use crate::address::{BitRange, calc_mask, coveringmask, extend_signbit, leastsigbit_set, popcount};
use crate::architecture::Architecture;
use crate::block::BlockId;
use crate::error::Result;
use crate::expression::{BitFieldExpression, InsertExpression, pointer_equality, root_pointer};
use crate::funcdata::Funcdata;
use crate::op::{OpId, PcodeOp};
use crate::opcodes::OpCode;
use crate::types::{BitFieldTriple, Datatype, TypeBitField, TypeFactory, TypeId, TypeMetatype};
use crate::varnode::VarnodeId;

const UINTB_BYTES: i32 = 8;
const UINTB_BITS: i32 = 64;

fn type_factory(glb: &Architecture) -> &TypeFactory {
    glb.types.as_deref().expect("type factory is not initialized")
}

fn type_factory_mut(glb: &mut Architecture) -> &mut TypeFactory {
    glb.types.as_deref_mut().expect("type factory is not initialized")
}

fn bit_field_of<'t>(field: &BitFieldRef, types: &'t TypeFactory) -> &'t TypeBitField {
    types.get(field.parent).get_bit_field(field.index as i32)
}

fn basic_prev(data: &Funcdata, op: OpId) -> Option<OpId> {
    data.op(op).links[PcodeOp::BASIC_LIST].prev
}

fn out_of(data: &Funcdata, op: OpId) -> VarnodeId {
    data.op(op).get_out().expect("p-code op has no output")
}

fn in_offset(data: &Funcdata, op: OpId, slot: i32) -> u64 {
    data.vn(data.op(op).get_in(slot)).get_offset()
}

fn list_merge<T>(first: Vec<T>, second: Vec<T>, less: &mut dyn FnMut(&T, &T) -> bool) -> Vec<T> {
    let mut result = Vec::with_capacity(first.len() + second.len());
    let mut first_iter = first.into_iter().peekable();
    let mut second_iter = second.into_iter().peekable();
    loop {
        let take_second = match (first_iter.peek(), second_iter.peek()) {
            (Some(first_item), Some(second_item)) => less(second_item, first_item),
            _ => break,
        };
        if take_second {
            result.push(second_iter.next().expect("merge list is empty"));
        } else {
            result.push(first_iter.next().expect("merge list is empty"));
        }
    }
    result.extend(first_iter);
    result.extend(second_iter);
    result
}

pub(crate) fn list_sort<T>(items: Vec<T>, less: &mut dyn FnMut(&T, &T) -> bool) -> Vec<T> {
    if items.len() <= 1 {
        return items;
    }
    let mut input: VecDeque<T> = items.into();
    let mut buckets: Vec<Vec<T>> = Vec::new();
    while let Some(item) = input.pop_front() {
        let mut carry = vec![item];
        let mut counter = 0;
        while counter < buckets.len() && !buckets[counter].is_empty() {
            let bucket = std::mem::take(&mut buckets[counter]);
            carry = list_merge(bucket, carry, less);
            counter += 1;
        }
        if counter == buckets.len() {
            buckets.push(carry);
        } else {
            buckets[counter] = carry;
        }
    }
    for counter in 1..buckets.len() {
        let previous = std::mem::take(&mut buckets[counter - 1]);
        let current = std::mem::take(&mut buckets[counter]);
        buckets[counter] = list_merge(current, previous, less);
    }
    buckets.pop().expect("sorted list has no bucket")
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct BitFieldRef {
    pub parent: TypeId,
    pub index: usize,
}

#[derive(Clone, Debug)]
pub struct BitFieldNodeState {
    pub bits_used: BitRange,
    pub bits_field: BitRange,
    pub node: Option<VarnodeId>,
    pub field: Option<BitFieldRef>,
    pub orig_least_sig_bit: i32,
    pub is_sign_extended: bool,
}

impl BitFieldNodeState {
    pub fn new(used: &BitRange, vn: VarnodeId, fld: BitFieldRef, glb: &Architecture) -> BitFieldNodeState {
        let types = type_factory(glb);
        let bitfield = bit_field_of(&fld, types);
        let bits_field = BitRange::from_container(&bitfield.bits, used.byte_offset, used.byte_size);
        let is_sign_extended =
            types.get(bitfield.tp).get_metatype() == TypeMetatype::Int && bits_field.is_most_significant();
        BitFieldNodeState {
            bits_used: *used,
            bits_field,
            node: Some(vn),
            field: Some(fld),
            orig_least_sig_bit: bits_field.least_sig_bit,
            is_sign_extended,
        }
    }

    pub fn new_bits(used: &BitRange, vn: VarnodeId, least_sig: i32, num_bits: i32) -> BitFieldNodeState {
        let bits_field = BitRange::new(
            used.byte_offset,
            used.byte_size,
            least_sig,
            num_bits,
            used.is_big_endian,
        );
        BitFieldNodeState {
            bits_used: *used,
            bits_field,
            node: Some(vn),
            field: None,
            orig_least_sig_bit: bits_field.least_sig_bit,
            is_sign_extended: false,
        }
    }

    pub fn new_copy(copy: &BitFieldNodeState, new_field: &BitRange, vn: VarnodeId, sgn_ext: bool) -> BitFieldNodeState {
        BitFieldNodeState {
            bits_used: copy.bits_used,
            bits_field: *new_field,
            node: Some(vn),
            field: copy.field,
            orig_least_sig_bit: copy.orig_least_sig_bit,
            is_sign_extended: sgn_ext,
        }
    }

    pub fn is_field_aligned(&self) -> bool {
        self.bits_field.least_sig_bit == 0 && self.bits_field.num_bits == self.bits_used.num_bits
    }

    pub fn does_sign_extension_match(&self, glb: &Architecture) -> bool {
        let types = type_factory(glb);
        let field = self.field.as_ref().expect("bitfield node without field");
        let field_type = bit_field_of(field, types).tp;
        self.is_sign_extended == (types.get(field_type).get_metatype() == TypeMetatype::Int)
    }
}

#[derive(Clone, Debug)]
pub struct BitFieldTransform {
    pub parent_struct: Option<TypeId>,
    pub work_list: VecDeque<BitFieldNodeState>,
    pub initial_offset: i32,
    pub container_size: i32,
    pub is_big_endian: bool,
}

impl BitFieldTransform {
    pub fn new(dt: TypeId, off: i32, glb: &Architecture) -> BitFieldTransform {
        let types = type_factory(glb);
        let mut parent_struct = None;
        let mut initial_offset = -1;
        let datatype = types.get(dt);
        if datatype.get_metatype() == TypeMetatype::Struct {
            parent_struct = Some(dt);
            initial_offset = off;
        } else if datatype.get_metatype() == TypeMetatype::PartialStruct {
            let parent = datatype.get_parent();
            if types.get(parent).get_metatype() == TypeMetatype::Struct {
                parent_struct = Some(parent);
                initial_offset = off + datatype.get_offset();
            }
        }
        let is_big_endian = glb
            .manager
            .get_default_data_space()
            .expect("no default data space")
            .is_big_endian();
        BitFieldTransform {
            parent_struct,
            work_list: VecDeque::new(),
            initial_offset,
            container_size: -1,
            is_big_endian,
        }
    }

    pub fn establish_fields(&mut self, vn: VarnodeId, follow_holes: bool, data: &Funcdata, glb: &Architecture) {
        let types = type_factory(glb);
        let vn_size = data.vn(vn).get_size();
        let vn_bit_size = vn_size * 8;
        let bitrange = BitRange::new(self.initial_offset, vn_size, 0, vn_bit_size, self.is_big_endian);
        let mut overlap: Vec<BitFieldTriple> = Vec::new();
        let parent = self.parent_struct.expect("bitfield transform without parent structure");
        Datatype::collect_bit_fields(parent, 0, &mut overlap, self.initial_offset, vn_size, types);
        std_sort(&mut overlap, |first, second| {
            BitFieldTriple::compare(first, second, types)
        });
        let mut pos = 0;
        for triple in overlap.iter() {
            let field_ref = BitFieldRef {
                parent: triple.immed_container,
                index: triple.bitfield,
            };
            let bits = bit_field_of(&field_ref, types).bits;
            let mut field_pos = bitrange.translate_lsb(&bits);
            let mut field_end = field_pos + bits.num_bits;
            if field_pos > vn_bit_size {
                field_pos = vn_bit_size;
            }
            if field_end > vn_bit_size {
                field_end = vn_bit_size;
            }
            if field_pos > pos {
                if follow_holes {
                    self.work_list
                        .push_back(BitFieldNodeState::new_bits(&bitrange, vn, pos, field_pos - pos));
                }
                pos = field_pos;
            }
            let code = bitrange.overlap_test(&bits);
            if code == 0 || code == 3 {
                self.work_list
                    .push_back(BitFieldNodeState::new(&bitrange, vn, field_ref, glb));
            } else if follow_holes {
                self.work_list
                    .push_back(BitFieldNodeState::new_bits(&bitrange, vn, pos, field_end - pos));
            }
            pos = field_end;
        }
        if pos < vn_bit_size && follow_holes {
            self.work_list
                .push_back(BitFieldNodeState::new_bits(&bitrange, vn, pos, vn_bit_size - pos));
        }
    }

    pub fn build_partial_type(&mut self, glb: &mut Architecture) -> Result<TypeId> {
        let parent = self.parent_struct.expect("bitfield transform without parent structure");
        if self.container_size == type_factory(glb).get(parent).get_size() {
            return Ok(parent);
        }
        type_factory_mut(glb).get_type_partial_struct(parent, self.initial_offset, self.container_size)
    }

    pub fn find_overwrite(vn: VarnodeId, bl: BlockId, range: &BitRange, data: &Funcdata) -> bool {
        let mut min_range = *range;
        min_range.minimize_container();
        let addr = data
            .vn(vn)
            .get_addr()
            .add((min_range.byte_offset - range.byte_offset) as i64);
        for &start_op in data.vn(vn).descend() {
            let mut cur_vn = vn;
            let mut op = start_op;
            let mut cur_range = *range;
            loop {
                if data.op(op).get_parent() != Some(bl) {
                    if cur_range.num_bits != 0 {
                        return false;
                    }
                    break;
                }
                let mut follow = true;
                match data.op(op).code() {
                    OpCode::Piece => {
                        if data.op(op).get_in(0) == cur_vn {
                            let sz = data.vn(data.op(op).get_in(1)).get_size();
                            cur_range.extend_bytes(sz);
                            cur_range.shift(sz * 8);
                        } else {
                            cur_range.extend_bytes(data.vn(data.op(op).get_in(0)).get_size());
                        }
                    }
                    OpCode::IntLeft => {
                        let cvn = data.vn(data.op(op).get_in(1));
                        if cvn.is_constant() {
                            cur_range.shift(cvn.get_offset() as i32);
                        } else {
                            return false;
                        }
                    }
                    OpCode::IntRight => {
                        let cvn = data.vn(data.op(op).get_in(1));
                        if cvn.is_constant() {
                            cur_range.shift((cvn.get_offset() as i32).wrapping_neg());
                        } else {
                            return false;
                        }
                    }
                    OpCode::Copy | OpCode::IntOr | OpCode::IntXor | OpCode::IntNegate => {}
                    OpCode::IntAnd => {
                        let cvn = data.vn(data.op(op).get_in(1));
                        if cvn.is_constant() {
                            cur_range.intersect_mask(cvn.get_offset());
                        }
                    }
                    OpCode::Insert => {
                        cur_range.intersect_mask(!InsertExpression::get_range_mask(op, data));
                    }
                    OpCode::Indirect => {
                        let out = data.vn(out_of(data, op));
                        if addr.contained_by(min_range.byte_size, out.get_addr(), out.get_size()) {
                            return cur_range.num_bits == 0;
                        }
                        return false;
                    }
                    _ => {
                        if cur_range.num_bits != 0 {
                            return false;
                        }
                        follow = false;
                    }
                }
                if !follow {
                    break;
                }
                cur_vn = out_of(data, op);
                let cur = data.vn(cur_vn);
                if addr.contained_by(min_range.byte_size, cur.get_addr(), cur.get_size()) && cur_range.num_bits == 0 {
                    return true;
                }
                if cur.has_no_descend() {
                    break;
                }
                match cur.lone_descend() {
                    Some(next_op) => op = next_op,
                    None => break,
                }
            }
        }
        false
    }
}

#[derive(Clone, Debug)]
pub struct InsertRecord {
    pub(crate) vn: Option<VarnodeId>,
    pub(crate) const_val: u64,
    pub(crate) dt: Option<TypeId>,
    pub(crate) pos: i32,
    pub(crate) num_bits: i32,
    pub(crate) shift_amount: i32,
}

impl InsertRecord {
    pub fn new(value_vn: VarnodeId, dt: Option<TypeId>, pos: i32, sz: i32, sa: i32) -> InsertRecord {
        InsertRecord {
            vn: Some(value_vn),
            dt,
            const_val: 0,
            pos,
            num_bits: sz,
            shift_amount: sa,
        }
    }

    pub fn new_constant(val: u64, dt: TypeId, pos: i32, sz: i32) -> InsertRecord {
        InsertRecord {
            vn: None,
            dt: Some(dt),
            const_val: val,
            pos,
            num_bits: sz,
            shift_amount: 0,
        }
    }
}

#[derive(Clone, Debug)]
pub struct BitFieldInsertTransform {
    pub base: BitFieldTransform,
    pub(crate) final_write_op: OpId,
    pub(crate) original_value: Option<VarnodeId>,
    pub(crate) mapped_vn: Option<VarnodeId>,
    pub(crate) insert_list: Vec<InsertRecord>,
}

impl BitFieldInsertTransform {
    pub const ALLOWED_FINAL_WRITES: &'static [OpCode] = &[
        OpCode::Copy,
        OpCode::IntEqual,
        OpCode::IntNotequal,
        OpCode::IntSless,
        OpCode::IntSlessequal,
        OpCode::IntLess,
        OpCode::IntLessequal,
        OpCode::IntZext,
        OpCode::IntSext,
        OpCode::IntAdd,
        OpCode::IntCarry,
        OpCode::IntScarry,
        OpCode::IntXor,
        OpCode::IntAnd,
        OpCode::IntOr,
        OpCode::IntLeft,
        OpCode::IntRight,
        OpCode::IntSright,
        OpCode::IntMult,
        OpCode::BoolNegate,
        OpCode::BoolXor,
        OpCode::BoolAnd,
        OpCode::BoolOr,
        OpCode::FloatEqual,
        OpCode::FloatNotequal,
        OpCode::FloatLess,
        OpCode::FloatLessequal,
        OpCode::FloatNan,
        OpCode::Subpiece,
    ];

    pub fn new(data: &Funcdata, op: OpId, dt: TypeId, off: i32, glb: &Architecture) -> BitFieldInsertTransform {
        let mut transform = BitFieldInsertTransform {
            base: BitFieldTransform::new(dt, off, glb),
            final_write_op: op,
            original_value: None,
            mapped_vn: None,
            insert_list: Vec::new(),
        };
        if transform.base.initial_offset == -1 {
            return transform;
        }
        let outvn;
        match data.op(op).code() {
            OpCode::Store => {
                outvn = data.op(op).get_in(2);
            }
            OpCode::Indirect => {
                let mapped = out_of(data, op);
                transform.mapped_vn = Some(mapped);
                outvn = data.op(op).get_in(0);
                let Some(def_op) = data.vn(outvn).get_def() else {
                    return transform;
                };
                transform.final_write_op = def_op;
                if !data.vn(mapped).is_addr_tied() {
                    return transform;
                }
                if !Self::ALLOWED_FINAL_WRITES.contains(&data.op(def_op).code()) {
                    return transform;
                }
            }
            _ => {
                outvn = out_of(data, op);
                transform.mapped_vn = Some(outvn);
                if !data.vn(outvn).is_addr_tied() {
                    return transform;
                }
            }
        }
        transform.base.container_size = data.vn(outvn).get_size();
        transform.original_value = None;
        transform.base.establish_fields(outvn, true, data, glb);
        transform
    }

    fn verify_load_store_original_value(&self, mask: u64, data: &Funcdata) -> bool {
        let original = self.original_value.expect("missing original value");
        let load_op = data.vn(original).get_def().expect("original value is not written");
        let final_op = self.final_write_op;
        let mut off: u64 = 0;
        let base_ptr = root_pointer(data.op(final_op).get_in(1), &mut off, data);
        let mut cursor = basic_prev(data, final_op);
        while let Some(op) = cursor {
            cursor = basic_prev(data, op);
            if op == load_op {
                return true;
            }
            if data.op(op).is_call() {
                return false;
            }
            if data.op(op).code() != OpCode::Store {
                continue;
            }
            if in_offset(data, op, 0) != in_offset(data, load_op, 0) {
                continue;
            }
            let mut other_off: u64 = 0;
            if base_ptr != root_pointer(data.op(op).get_in(1), &mut other_off, data) {
                return false;
            }
            if other_off != off {
                continue;
            }
            let value_vn = data.op(op).get_in(2);
            let Some(insert_op) = data.vn(value_vn).get_def() else {
                return false;
            };
            if data.op(insert_op).code() != OpCode::Insert {
                return false;
            }
            let insert_mask = InsertExpression::get_range_mask(insert_op, data);
            if (insert_mask & mask) != 0 {
                return false;
            }
        }
        true
    }

    fn verify_mapped_original_value(&self, mask: u64, data: &Funcdata) -> bool {
        let original = self.original_value.expect("missing original value");
        let mut cursor = basic_prev(data, self.final_write_op);
        while let Some(op) = cursor {
            cursor = basic_prev(data, op);
            let out = data.op(op).get_out();
            if out == Some(original) {
                return true;
            }
            let Some(out_vn) = out else {
                continue;
            };
            if data.op(op).is_call() {
                return false;
            }
            if data.vn(out_vn).get_addr() != data.vn(original).get_addr() {
                continue;
            }
            if data.vn(out_vn).get_size() != data.vn(original).get_size() {
                continue;
            }
            let Some(insert_op) = data.vn(out_vn).get_def() else {
                return false;
            };
            if data.op(insert_op).code() != OpCode::Insert {
                return false;
            }
            let insert_mask = InsertExpression::get_range_mask(insert_op, data);
            if (insert_mask & mask) != 0 {
                return false;
            }
        }
        true
    }

    fn construct_original_value_mask(&self, data: &Funcdata) -> u64 {
        let mut mask: u64 = 0;
        for rec in self.insert_list.iter() {
            let mut val: u64 = 0;
            if rec.num_bits < UINTB_BITS {
                val = 1;
                val = val.wrapping_shl(rec.num_bits as u32);
            }
            val = val.wrapping_sub(1);
            val = val.wrapping_shl(rec.pos as u32);
            mask |= val;
        }
        let original = self.original_value.expect("missing original value");
        !mask & calc_mask(data.vn(original).get_size())
    }

    fn verify_original_value_bits(&self, data: &Funcdata) -> bool {
        if self.original_value.is_none() {
            return true;
        }
        let mask = self.construct_original_value_mask(data);
        if mask == 0 {
            return true;
        }
        if data.op(self.final_write_op).code() == OpCode::Store {
            return self.verify_load_store_original_value(mask, data);
        }
        self.verify_mapped_original_value(mask, data)
    }

    fn is_overwritten_partial(&self, state: &BitFieldNodeState, data: &Funcdata) -> bool {
        if state.field.is_some() {
            return false;
        }
        if state.bits_field.byte_size > UINTB_BYTES {
            return false;
        }
        if data.op(self.final_write_op).code() != OpCode::Store {
            let mapped = self.mapped_vn.expect("missing mapped varnode");
            let cur_range = BitRange::new(
                self.base.initial_offset,
                data.vn(mapped).get_size(),
                state.orig_least_sig_bit,
                state.bits_field.num_bits,
                self.base.is_big_endian,
            );
            let parent = data
                .op(self.final_write_op)
                .get_parent()
                .expect("p-code op has no parent block");
            return BitFieldTransform::find_overwrite(mapped, parent, &cur_range, data);
        }
        false
    }

    fn check_pulled_original_value(&mut self, state: &BitFieldNodeState, data: &Funcdata) -> bool {
        let node = state.node.expect("bitfield node without varnode");
        let Some(op) = data.vn(node).get_def() else {
            return false;
        };
        let opc = data.op(op).code();
        if opc != OpCode::Zpull && opc != OpCode::Spull {
            return false;
        }
        let pos = in_offset(data, op, 1) as i32;
        let numbits = in_offset(data, op, 2) as i32;
        if pos != state.bits_field.least_sig_bit {
            return false;
        }
        if numbits != state.bits_field.num_bits {
            return false;
        }
        self.check_original_base(data.op(op).get_in(0), data)
    }

    fn check_original_base(&mut self, vn: VarnodeId, data: &Funcdata) -> bool {
        let final_op = self.final_write_op;
        if data.op(final_op).code() == OpCode::Store {
            let Some(load_op) = data.vn(vn).get_def() else {
                return false;
            };
            if data.op(load_op).code() != OpCode::Load {
                return false;
            }
            if !pointer_equality(data.op(load_op).get_in(1), data.op(final_op).get_in(1), data) {
                return false;
            }
            if data.op(load_op).get_parent() != data.op(final_op).get_parent() {
                return false;
            }
        } else {
            let mapped = self.mapped_vn.expect("missing mapped varnode");
            if mapped == vn {
                return false;
            }
            if data.vn(mapped).get_addr() != data.vn(vn).get_addr()
                || data.vn(mapped).get_size() != data.vn(vn).get_size()
            {
                return false;
            }
            if !data.vn(vn).is_addr_tied() {
                return false;
            }
        }
        self.original_value = Some(vn);
        true
    }

    fn is_original_value(&mut self, state: &BitFieldNodeState, data: &Funcdata) -> bool {
        if state.bits_field.least_sig_bit != state.orig_least_sig_bit {
            return false;
        }
        if state.node == self.original_value {
            return true;
        }
        if self.check_pulled_original_value(state, data) {
            return true;
        }
        self.check_original_base(state.node.expect("bitfield node without varnode"), data)
    }

    fn add_constant_write(&mut self, state: &mut BitFieldNodeState, data: &Funcdata, glb: &Architecture) -> bool {
        let mut value = data.vn(state.node.expect("bitfield node without varnode")).get_offset();
        state.node = None;
        let Some(field) = state.field else {
            return false;
        };
        if state.bits_field.byte_size > UINTB_BYTES {
            return false;
        }
        let types = type_factory(glb);
        let bitfield = bit_field_of(&field, types);
        let mask = state.bits_field.get_mask();
        value &= mask;
        value = value.wrapping_shr(state.bits_field.least_sig_bit as u32);
        if types.get(bitfield.tp).get_metatype() == TypeMetatype::Int {
            value = extend_signbit(value, state.bits_field.num_bits, state.bits_field.byte_size);
        }
        self.insert_list.push(InsertRecord::new_constant(
            value,
            bitfield.tp,
            state.orig_least_sig_bit,
            bitfield.bits.num_bits,
        ));
        true
    }

    fn add_zero_out(&mut self, state: &mut BitFieldNodeState, glb: &Architecture) -> bool {
        state.node = None;
        let Some(field) = state.field else {
            return false;
        };
        let bitfield = bit_field_of(&field, type_factory(glb));
        self.insert_list.push(InsertRecord::new_constant(
            0,
            bitfield.tp,
            state.orig_least_sig_bit,
            bitfield.bits.num_bits,
        ));
        true
    }

    fn add_field_write(&mut self, state: &mut BitFieldNodeState, data: &Funcdata, glb: &Architecture) {
        let types = type_factory(glb);
        let field = state.field.expect("bitfield node without field");
        let bitfield = bit_field_of(&field, types);
        let node = state.node.expect("bitfield node without varnode");
        let mut dt = Some(bitfield.tp);
        if types.get(bitfield.tp).get_size() != data.vn(node).get_size() {
            dt = None;
        }
        self.insert_list.push(InsertRecord::new(
            node,
            dt,
            state.orig_least_sig_bit,
            bitfield.bits.num_bits,
            state.bits_field.least_sig_bit,
        ));
        state.node = None;
    }

    fn handle_and_back(
        &mut self,
        state: &mut BitFieldNodeState,
        op: OpId,
        data: &Funcdata,
        glb: &Architecture,
    ) -> bool {
        let cvn = data.vn(data.op(op).get_in(1));
        if !cvn.is_constant() {
            return false;
        }
        if state.bits_field.byte_size > UINTB_BYTES {
            return false;
        }
        let val = state.bits_field.get_mask();
        let res = val & cvn.get_offset();
        if res == val {
            state.node = Some(data.op(op).get_in(0));
            state.bits_used.intersect_mask(cvn.get_offset());
            return true;
        }
        if res == 0 {
            return self.add_zero_out(state, glb);
        }
        false
    }

    fn handle_or_back(&mut self, state: &mut BitFieldNodeState, op: OpId, data: &Funcdata) -> bool {
        if state.bits_field.byte_size > UINTB_BYTES {
            return false;
        }
        let mask = state.bits_field.get_mask();
        let vn0 = data.op(op).get_in(0);
        let vn1 = data.op(op).get_in(1);
        let is_masked0 = (data.vn(vn0).get_nz_mask() & mask) == 0;
        let is_masked1 = (data.vn(vn1).get_nz_mask() & mask) == 0;
        if is_masked0 == is_masked1 {
            if data.vn(vn1).is_constant() && (data.vn(vn1).get_nz_mask() & mask) == mask {
                state.node = Some(vn1);
                return true;
            }
            return false;
        }
        state.node = Some(if is_masked0 { vn1 } else { vn0 });
        true
    }

    fn handle_add_back(&mut self, state: &mut BitFieldNodeState, op: OpId, data: &Funcdata) -> bool {
        if state.bits_field.byte_size > UINTB_BYTES {
            return false;
        }
        let vn0 = data.op(op).get_in(0);
        let vn1 = data.op(op).get_in(1);
        let mask0 = data.vn(vn0).get_nz_mask();
        let mask1 = data.vn(vn1).get_nz_mask();
        if (mask0 & mask1) != 0 {
            return false;
        }
        let mask = state.bits_field.get_mask();
        let is_masked0 = (mask0 & mask) == 0;
        let is_masked1 = (mask1 & mask) == 0;
        if is_masked0 == is_masked1 {
            return false;
        }
        state.node = Some(if is_masked0 { vn1 } else { vn0 });
        true
    }

    fn handle_left_back(
        &mut self,
        state: &mut BitFieldNodeState,
        op: OpId,
        data: &Funcdata,
        glb: &Architecture,
    ) -> bool {
        let cvn = data.vn(data.op(op).get_in(1));
        if !cvn.is_constant() {
            return false;
        }
        let sa = cvn.get_offset() as i32;
        if !(0..UINTB_BITS).contains(&sa) {
            return false;
        }
        let mut new_range = state.bits_field;
        new_range.shift(-sa);
        if state.bits_field.num_bits == new_range.num_bits {
            state.bits_field = new_range;
            state.bits_used.shift(-sa);
            state.node = Some(data.op(op).get_in(0));
            return true;
        } else if new_range.num_bits == 0 {
            return self.add_zero_out(state, glb);
        }
        false
    }

    fn handle_right_back(&mut self, state: &mut BitFieldNodeState, op: OpId, data: &Funcdata) -> bool {
        let cvn = data.vn(data.op(op).get_in(1));
        if !cvn.is_constant() {
            return false;
        }
        let sa = cvn.get_offset() as i32;
        if !(0..UINTB_BITS).contains(&sa) {
            return false;
        }
        let mut new_range = state.bits_field;
        new_range.shift(sa);
        if state.bits_field.num_bits == new_range.num_bits {
            state.bits_field = new_range;
            state.bits_used.shift(sa);
            state.node = Some(data.op(op).get_in(0));
            return true;
        }
        false
    }

    fn handle_zext_back(
        &mut self,
        state: &mut BitFieldNodeState,
        op: OpId,
        data: &Funcdata,
        glb: &Architecture,
    ) -> bool {
        let vn = data.op(op).get_in(0);
        let trunc_amount = data.vn(out_of(data, op)).get_size() - data.vn(vn).get_size();
        let mut new_range = state.bits_field;
        new_range.truncate_most_sig_bytes(trunc_amount);
        if state.bits_field.num_bits == new_range.num_bits {
            state.bits_field = new_range;
            state.bits_used.truncate_most_sig_bytes(trunc_amount);
            state.node = Some(vn);
        } else if state.bits_field.num_bits == 0 {
            return self.add_zero_out(state, glb);
        } else {
            return false;
        }
        true
    }

    fn handle_mult_back(
        &mut self,
        state: &mut BitFieldNodeState,
        op: OpId,
        data: &Funcdata,
        glb: &Architecture,
    ) -> bool {
        let vn1 = data.vn(data.op(op).get_in(1));
        if !vn1.is_constant() {
            return false;
        }
        let val = vn1.get_offset();
        if popcount(val) != 1 {
            return false;
        }
        let sa = leastsigbit_set(val);
        let mut new_range = state.bits_field;
        new_range.shift(-sa);
        if state.bits_field.num_bits == new_range.num_bits {
            state.bits_field = new_range;
            state.bits_used.shift(-sa);
            state.node = Some(data.op(op).get_in(0));
            return true;
        } else if state.bits_field.num_bits == 0 {
            return self.add_zero_out(state, glb);
        }
        false
    }

    fn handle_subpiece_back(&mut self, state: &mut BitFieldNodeState, op: OpId, data: &Funcdata) -> bool {
        let in_vn = data.op(op).get_in(0);
        let node = state.node.expect("bitfield node without varnode");
        let extend_amount = data.vn(in_vn).get_size() - data.vn(node).get_size();
        let sa = (in_offset(data, op, 1) as i32).wrapping_mul(8);
        let mut new_range = state.bits_field;
        new_range.extend_bytes(extend_amount);
        new_range.shift(-sa);
        if state.bits_field.num_bits == new_range.num_bits {
            state.bits_field = new_range;
            state.bits_used.extend_bytes(extend_amount);
            state.bits_used.shift(-sa);
            state.node = Some(in_vn);
            return true;
        }
        false
    }

    fn test_call_original(&mut self, state: &BitFieldNodeState, op: OpId, data: &Funcdata, glb: &Architecture) -> bool {
        if !data.op(op).is_call() {
            return false;
        }
        if data.op(self.final_write_op).code() == OpCode::Store {
            return false;
        }
        if state.bits_field.least_sig_bit != state.orig_least_sig_bit {
            return false;
        }
        let mapped = self.mapped_vn.expect("missing mapped varnode");
        if data.vn(mapped).is_addr_tied() {
            return false;
        }
        if self.original_value.is_some() {
            return false;
        }
        let out = out_of(data, op);
        let types = type_factory(glb);
        let mut dt = data.vn_get_type_def_facing(out, glb);
        let off;
        let datatype = types.get(dt);
        if datatype.get_metatype() == TypeMetatype::Struct {
            off = 0;
        } else if datatype.get_metatype() == TypeMetatype::PartialStruct {
            off = datatype.get_offset();
            dt = datatype.get_parent();
        } else {
            return false;
        }
        if Some(dt) != self.base.parent_struct {
            return false;
        }
        if off != self.base.initial_offset {
            return false;
        }
        self.original_value = Some(out);
        true
    }

    fn process_backward(&mut self, state: &mut BitFieldNodeState, data: &Funcdata, glb: &Architecture) -> bool {
        while let Some(node) = state.node {
            if data.vn(node).is_constant() {
                return self.add_constant_write(state, data, glb);
            }
            if self.is_original_value(state, data) {
                state.node = None;
                return true;
            }
            if state.field.is_some() && state.is_field_aligned() {
                self.add_field_write(state, data, glb);
                return true;
            }
            let Some(op) = data.vn(node).get_def() else {
                return false;
            };
            let lift_res = match data.op(op).code() {
                OpCode::Copy => {
                    state.node = Some(data.op(op).get_in(0));
                    true
                }
                OpCode::IntAdd => self.handle_add_back(state, op, data),
                OpCode::IntAnd => self.handle_and_back(state, op, data, glb),
                OpCode::IntLeft => self.handle_left_back(state, op, data, glb),
                OpCode::IntZext => self.handle_zext_back(state, op, data, glb),
                OpCode::IntOr => self.handle_or_back(state, op, data),
                OpCode::IntMult => self.handle_mult_back(state, op, data, glb),
                OpCode::Subpiece => self.handle_subpiece_back(state, op, data),
                OpCode::IntSright => self.handle_right_back(state, op, data),
                OpCode::Call | OpCode::Callind | OpCode::Callother => {
                    if self.test_call_original(state, op, data, glb) {
                        state.node = None;
                        return true;
                    }
                    false
                }
                _ => false,
            };
            if !lift_res {
                if state.field.is_none() {
                    return false;
                }
                if state.bits_field.byte_size > UINTB_BYTES {
                    return false;
                }
                let current = state.node.expect("bitfield node without varnode");
                let nz_mask = data.vn(current).get_nz_mask();
                let mut non_zero_bits = state.bits_field;
                non_zero_bits.intersect_mask(nz_mask);
                if non_zero_bits.num_bits == 0 {
                    return self.add_zero_out(state, glb);
                }
                state.bits_used.intersect_mask(nz_mask);
                if non_zero_bits.num_bits == state.bits_used.num_bits {
                    self.add_field_write(state, data, glb);
                    return true;
                }
                return false;
            }
        }
        true
    }

    fn set_insert_inputs(
        &self,
        op: Option<OpId>,
        rec: &InsertRecord,
        data: &mut Funcdata,
        glb: &mut Architecture,
    ) -> Result<OpId> {
        let op = match op {
            None => {
                let addr = data.op(self.final_write_op).get_addr().clone();
                data.new_op(4, &addr)
            }
            Some(existing) => {
                while data.op(existing).num_input() < 4 {
                    let slot = data.op(existing).num_input();
                    data.op_mut(existing).insert_input(slot);
                }
                existing
            }
        };
        data.op_set_opcode(op, OpCode::Insert, glb);
        data.op_set_input(op, self.original_value.expect("missing original value"), 0)?;
        let val_vn = match rec.vn {
            Some(value_vn) => value_vn,
            None => match rec.dt {
                Some(dt) => {
                    let size = type_factory(glb).get(dt).get_size();
                    let constant = data.new_constant(size, rec.const_val, glb);
                    data.vn_update_type(constant, dt);
                    constant
                }
                None => data.new_constant(self.base.container_size, rec.const_val, glb),
            },
        };
        data.op_set_input(op, val_vn, 1)?;
        let pos_vn = data.new_constant(4, rec.pos as i64 as u64, glb);
        data.op_set_input(op, pos_vn, 2)?;
        let num_vn = data.new_constant(4, rec.num_bits as i64 as u64, glb);
        data.op_set_input(op, num_vn, 3)?;
        data.op_mark_special_print(op);
        Ok(op)
    }

    fn add_field_shift(
        &self,
        insert_op: OpId,
        rec: &InsertRecord,
        data: &mut Funcdata,
        glb: &mut Architecture,
    ) -> Result<()> {
        if rec.shift_amount == 0 {
            return Ok(());
        }
        let val_vn = data.op(insert_op).get_in(1);
        let addr = data.op(insert_op).get_addr().clone();
        let shift_op = data.new_op(2, &addr);
        data.op_set_opcode(shift_op, OpCode::IntRight, glb);
        let size = data.vn(val_vn).get_size();
        let new_out = data.new_unique_out(size, shift_op, glb)?;
        data.op_set_input(insert_op, new_out, 1)?;
        data.op_set_input(shift_op, val_vn, 0)?;
        let shift_vn = data.new_constant(4, rec.shift_amount as i64 as u64, glb);
        data.op_set_input(shift_op, shift_vn, 1)?;
        data.op_insert_before(shift_op, insert_op);
        Ok(())
    }

    fn fold_load(&self, load_op: OpId, data: &mut Funcdata) -> bool {
        let outvn = out_of(data, load_op);
        for &op in data.vn(outvn).descend() {
            if op == self.final_write_op {
                continue;
            }
            let opc = data.op(op).code();
            if opc != OpCode::Insert && opc != OpCode::Zpull && opc != OpCode::Spull {
                return false;
            }
        }
        data.op_mark_non_printing(load_op);
        true
    }

    fn fold_ptrsub(&self, load_op: OpId, data: &mut Funcdata) {
        let vn = data.op(load_op).get_in(1);
        let Some(ptrsub) = data.vn(vn).get_def() else {
            return;
        };
        if data.op(ptrsub).code() != OpCode::Ptrsub {
            return;
        }
        for &op in data.vn(vn).descend() {
            let read = data.op(op);
            if read.code() == OpCode::Store && read.does_special_printing() {
                continue;
            }
            if read.code() == OpCode::Load && read.not_printed() {
                continue;
            }
            return;
        }
        data.op_mark_non_printing(ptrsub);
    }

    fn check_redundancy(&self, rec: &InsertRecord, data: &mut Funcdata) -> Result<()> {
        let Some(value_vn) = rec.vn else {
            return Ok(());
        };
        let mut immed_op: Option<OpId> = None;
        let descendants = data.vn(value_vn).descend().to_vec();
        for desc in descendants {
            let mut op = desc;
            if data.op(op).code() != OpCode::Insert {
                if data.op(op).code() != OpCode::IntRight {
                    continue;
                }
                match data.vn(out_of(data, op)).lone_descend() {
                    Some(next_op) if data.op(next_op).code() == OpCode::Insert => op = next_op,
                    _ => continue,
                }
            }
            let Some(immed) = immed_op else {
                immed_op = Some(op);
                continue;
            };
            if in_offset(data, op, 2) != in_offset(data, immed, 2) {
                continue;
            }
            if in_offset(data, op, 3) != in_offset(data, immed, 3) {
                continue;
            }
            if data.op(self.final_write_op).code() == OpCode::Store {
                let Some(store1) = data.vn(out_of(data, op)).lone_descend() else {
                    continue;
                };
                if data.op(store1).code() != OpCode::Store {
                    continue;
                }
                let Some(store2) = data.vn(out_of(data, immed)).lone_descend() else {
                    continue;
                };
                if data.op(store2).code() != OpCode::Store {
                    continue;
                }
                if data.op(store1).get_parent() != data.op(store2).get_parent() {
                    continue;
                }
                if !pointer_equality(data.op(store1).get_in(1), data.op(store2).get_in(1), data) {
                    continue;
                }
                let mut scratch: Vec<OpId> = Vec::new();
                if data.op(store1).get_seq_num().get_order() < data.op(store2).get_seq_num().get_order() {
                    data.op_destroy_recursive(store2, &mut scratch)?;
                } else {
                    data.op_destroy_recursive(store1, &mut scratch)?;
                }
            }
            return Ok(());
        }
        Ok(())
    }

    pub fn do_trace(&mut self, data: &Funcdata, glb: &Architecture) -> bool {
        if self.base.work_list.is_empty() {
            return false;
        }
        while let Some(mut node) = self.base.work_list.pop_front() {
            if !self.process_backward(&mut node, data, glb) && !self.is_overwritten_partial(&node, data) {
                return false;
            }
        }
        if self.insert_list.is_empty() {
            return false;
        }
        self.verify_original_value_bits(data)
    }

    pub fn apply(&mut self, data: &mut Funcdata, glb: &mut Architecture) -> Result<()> {
        let partial_type = self.base.build_partial_type(glb)?;
        let records = self.insert_list.clone();
        let final_op = self.final_write_op;
        let container_size = self.base.container_size;
        if data.op(final_op).code() == OpCode::Store {
            let dead_point = data.op(final_op).get_in(2);
            let mut current_store = Some(final_op);
            let mut load_model: Option<OpId> = None;
            let mut load_type: Option<TypeId> = None;
            match self.original_value {
                None => {
                    self.original_value = Some(data.new_constant(container_size, 0, glb));
                }
                Some(original) => {
                    load_model = data.vn(original).get_def();
                    load_type = Some(data.vn_get_type_def_facing(original, glb));
                }
            }
            for rec in records.iter() {
                if current_store.is_none() {
                    let addr = data.op(final_op).get_addr().clone();
                    let store_op = data.new_op(3, &addr);
                    data.op_set_opcode(store_op, OpCode::Store, glb);
                    let space_vn = data.op(final_op).get_in(0);
                    let ptr_vn = data.op(final_op).get_in(1);
                    data.op_set_input(store_op, space_vn, 0)?;
                    data.op_set_input(store_op, ptr_vn, 1)?;
                    data.op_insert_after(store_op, final_op);
                    if let Some(model) = load_model {
                        let model_addr = data.op(model).get_addr().clone();
                        let load_op = data.new_op(2, &model_addr);
                        data.op_set_opcode(load_op, OpCode::Load, glb);
                        let load_space = data.op(model).get_in(0);
                        let load_ptr = data.op(model).get_in(1);
                        data.op_set_input(load_op, load_space, 0)?;
                        data.op_set_input(load_op, load_ptr, 1)?;
                        let original = data.new_unique_out(container_size, load_op, glb)?;
                        data.vn_update_type(original, load_type.expect("missing load data-type"));
                        self.original_value = Some(original);
                        data.op_insert_before(load_op, store_op);
                        data.op_mark_non_printing(load_op);
                    }
                    current_store = Some(store_op);
                }
                let store_op = current_store.expect("missing store op");
                let insert_op = self.set_insert_inputs(None, rec, data, glb)?;
                let new_out = data.new_unique_out(container_size, insert_op, glb)?;
                data.vn_update_type(new_out, partial_type);
                data.op_set_input(store_op, new_out, 2)?;
                data.op_insert_before(insert_op, store_op);
                data.op_mark_special_print(store_op);
                self.add_field_shift(insert_op, rec, data, glb)?;
                current_store = None;
            }
            data.destroy_varnode_recursive(dead_point)?;
            if let Some(model) = load_model
                && data.op(model).code() == OpCode::Load
                && self.fold_load(model, data)
            {
                self.fold_ptrsub(model, data);
            }
        } else {
            let dead_points: Vec<VarnodeId> = (0..data.op(final_op).num_input())
                .map(|slot| data.op(final_op).get_in(slot))
                .collect();
            if self.original_value.is_none() {
                self.original_value = Some(data.new_constant(container_size, 0, glb));
            }
            let mut record_iter = records.iter();
            let first = record_iter.next().expect("insert list is empty");
            let mut insert_op = self.set_insert_inputs(Some(final_op), first, data, glb)?;
            let first_out = out_of(data, insert_op);
            data.vn_update_type(first_out, partial_type);
            self.add_field_shift(insert_op, first, data, glb)?;
            let mapped_addr = data
                .vn(self.mapped_vn.expect("missing mapped varnode"))
                .get_addr()
                .clone();
            for rec in record_iter {
                let last_op = insert_op;
                data.op_unset_input(last_op, 0);
                insert_op = self.set_insert_inputs(None, rec, data, glb)?;
                let new_out = data.new_varnode_out(container_size, &mapped_addr, insert_op, glb)?;
                data.vn_update_type(new_out, partial_type);
                data.op_set_input(last_op, new_out, 0)?;
                data.op_insert_before(insert_op, last_op);
                self.add_field_shift(insert_op, rec, data, glb)?;
            }
            for dead_point in dead_points {
                data.destroy_varnode_recursive(dead_point)?;
            }
        }
        for rec in records.iter() {
            self.check_redundancy(rec, data)?;
        }
        Ok(())
    }
}

#[derive(Clone, Debug, Default)]
pub struct TransformState {
    pub(crate) dead_scratch: Vec<OpId>,
    pub(crate) partial_type: Option<TypeId>,
    pub(crate) count: i32,
}

#[derive(Clone, Debug)]
pub struct PullRecord {
    pub(crate) read_vn: Option<VarnodeId>,
    pub(crate) read_op: Option<OpId>,
    pub(crate) dt: Option<TypeId>,
    pub(crate) record_type: i32,
    pub(crate) pos: i32,
    pub(crate) num_bits: i32,
    pub(crate) left_shift: i32,
    pub(crate) mask: u64,
}

impl PullRecord {
    pub const NORMAL: i32 = 0;
    pub const EQUAL: i32 = 1;
    pub const ABORTED: i32 = 2;

    pub fn new(state: &BitFieldNodeState, op: Option<OpId>, glb: &Architecture) -> PullRecord {
        let field = state.field.expect("bitfield node without field");
        let bitfield = bit_field_of(&field, type_factory(glb));
        PullRecord {
            read_vn: state.node,
            read_op: op,
            dt: Some(bitfield.tp),
            record_type: PullRecord::NORMAL,
            pos: state.orig_least_sig_bit,
            num_bits: bitfield.bits.num_bits,
            left_shift: state.bits_field.least_sig_bit,
            mask: 0,
        }
    }

    pub fn new_equal(state: &BitFieldNodeState, op: OpId, val: u64, glb: &Architecture) -> PullRecord {
        let field = state.field.expect("bitfield node without field");
        let bitfield = bit_field_of(&field, type_factory(glb));
        PullRecord {
            read_vn: state.node,
            read_op: Some(op),
            dt: Some(bitfield.tp),
            record_type: PullRecord::EQUAL,
            pos: state.orig_least_sig_bit,
            num_bits: bitfield.bits.num_bits,
            left_shift: state.bits_field.least_sig_bit,
            mask: val,
        }
    }

    pub fn new_aborted(op: OpId) -> PullRecord {
        PullRecord {
            read_vn: None,
            read_op: Some(op),
            dt: None,
            record_type: PullRecord::ABORTED,
            pos: 0,
            num_bits: 0,
            left_shift: 0,
            mask: 0,
        }
    }

    pub fn less_than(&self, op2: &PullRecord, data: &Funcdata) -> bool {
        match (self.read_op, op2.read_op) {
            (Some(first), Some(second)) => {
                if first != second {
                    return data.op(first).get_seq_num() < data.op(second).get_seq_num();
                }
                false
            }
            (None, _) => true,
            (_, None) => false,
        }
    }
}

#[derive(Clone, Debug)]
pub struct BitFieldPullTransform {
    pub base: BitFieldTransform,
    pub(crate) root: VarnodeId,
    pub(crate) load_op: Option<OpId>,
    pub(crate) pull_list: Vec<PullRecord>,
}

impl BitFieldPullTransform {
    pub fn new(data: &Funcdata, root: VarnodeId, dt: TypeId, off: i32, glb: &Architecture) -> BitFieldPullTransform {
        let mut transform = BitFieldPullTransform {
            base: BitFieldTransform::new(dt, off, glb),
            root,
            load_op: None,
            pull_list: Vec::new(),
        };
        if transform.base.initial_offset == -1 {
            return transform;
        }
        transform.base.container_size = data.vn(root).get_size();
        if let Some(def_op) = data.vn(root).get_def()
            && data.op(def_op).code() == OpCode::Load
        {
            transform.load_op = Some(def_op);
        }
        transform.base.establish_fields(root, false, data, glb);
        transform
    }

    fn test_consumed(vn: VarnodeId, bit_field: &BitRange, data: &Funcdata) -> bool {
        if bit_field.byte_size > UINTB_BYTES {
            return false;
        }
        let mask = bit_field.get_mask();
        let consume = data.vn(vn).get_consume();
        (mask & consume) == consume
    }

    fn handle_left_forward(&mut self, state: &BitFieldNodeState, op: OpId, data: &Funcdata, glb: &Architecture) {
        if Some(data.op(op).get_in(0)) != state.node {
            return;
        }
        let cvn = data.vn(data.op(op).get_in(1));
        if !cvn.is_constant() {
            return;
        }
        let sa = cvn.get_offset() as i32;
        let mut new_range = state.bits_field;
        new_range.shift(sa);
        if new_range.num_bits == 0 {
            return;
        }
        let out = out_of(data, op);
        if state.bits_field.num_bits == new_range.num_bits {
            let new_sign_ext = state.is_sign_extended || new_range.is_most_significant();
            let mut next = BitFieldNodeState::new_copy(state, &new_range, out, new_sign_ext);
            next.bits_used.shift(sa);
            self.base.work_list.push_back(next);
        } else if Self::test_consumed(out, &new_range, data) {
            self.pull_list.push(PullRecord::new(state, Some(op), glb));
        }
    }

    fn handle_right_forward(&mut self, state: &BitFieldNodeState, op: OpId, data: &Funcdata, glb: &Architecture) {
        if Some(data.op(op).get_in(0)) != state.node {
            return;
        }
        let cvn = data.vn(data.op(op).get_in(1));
        if !cvn.is_constant() {
            return;
        }
        let sa = cvn.get_offset() as i32;
        let mut new_range = state.bits_field;
        new_range.shift(sa.wrapping_neg());
        if new_range.num_bits == 0 {
            return;
        }
        let out = out_of(data, op);
        let is_sright = data.op(op).code() == OpCode::IntSright;
        if state.bits_field.num_bits == new_range.num_bits {
            let new_sign_ext = if is_sright { state.is_sign_extended } else { false };
            let mut next = BitFieldNodeState::new_copy(state, &new_range, out, new_sign_ext);
            next.bits_used.shift(sa.wrapping_neg());
            if is_sright && !state.is_sign_extended {
                next.bits_used.expand_to_most();
            }
            self.base.work_list.push_back(next);
        } else if Self::test_consumed(out, &new_range, data) {
            self.pull_list.push(PullRecord::new(state, Some(op), glb));
        }
    }

    fn handle_and_forward(&mut self, state: &BitFieldNodeState, op: OpId, data: &Funcdata, glb: &Architecture) {
        if Some(data.op(op).get_in(0)) != state.node {
            return;
        }
        if state.bits_field.byte_size > UINTB_BYTES {
            return;
        }
        let cvn = data.vn(data.op(op).get_in(1));
        if !cvn.is_constant() {
            return;
        }
        let and_val = cvn.get_offset();
        let mask = state.bits_field.get_mask();
        let intersect = and_val & mask;
        if intersect == 0 {
            return;
        }
        let out = out_of(data, op);
        if intersect == mask {
            let new_sign_ext = state.bits_field.is_most_significant();
            let mut next = BitFieldNodeState::new_copy(state, &state.bits_field, out, new_sign_ext);
            next.bits_used.intersect_mask(and_val);
            self.base.work_list.push_back(next);
        } else if Self::test_consumed(out, &state.bits_field, data) {
            self.pull_list.push(PullRecord::new(state, Some(op), glb));
        }
    }

    fn handle_ext_forward(&mut self, state: &BitFieldNodeState, op: OpId, data: &Funcdata) {
        let outvn = out_of(data, op);
        let node = state.node.expect("bitfield node without varnode");
        let diff = data.vn(outvn).get_size() - data.vn(node).get_size();
        let is_sext = data.op(op).code() == OpCode::IntSext;
        let new_sign_ext = if is_sext { state.is_sign_extended } else { false };
        let mut next = BitFieldNodeState::new_copy(state, &state.bits_field, outvn, new_sign_ext);
        next.bits_field.extend_bytes(diff);
        next.bits_used.extend_bytes(diff);
        if is_sext && !state.is_sign_extended {
            next.bits_used.expand_to_most();
        }
        self.base.work_list.push_back(next);
    }

    fn handle_mult_forward(&mut self, state: &BitFieldNodeState, op: OpId, data: &Funcdata, glb: &Architecture) {
        if Some(data.op(op).get_in(0)) != state.node {
            return;
        }
        let vn1 = data.vn(data.op(op).get_in(1));
        if !vn1.is_constant() {
            return;
        }
        let val = vn1.get_offset();
        if popcount(val) != 1 {
            self.handle_least_sig_op(state, op, data, glb);
            return;
        }
        let sa = leastsigbit_set(val);
        let mut new_range = state.bits_field;
        new_range.shift(sa);
        if new_range.num_bits == 0 {
            return;
        }
        if state.bits_field.num_bits == new_range.num_bits {
            let new_sign_ext = state.is_sign_extended || new_range.is_most_significant();
            let mut next = BitFieldNodeState::new_copy(state, &new_range, out_of(data, op), new_sign_ext);
            next.bits_used.shift(sa);
            self.base.work_list.push_back(next);
        }
    }

    fn handle_subpiece_forward(&mut self, state: &BitFieldNodeState, op: OpId, data: &Funcdata, glb: &Architecture) {
        if Some(data.op(op).get_in(0)) != state.node {
            return;
        }
        let out = out_of(data, op);
        let least_trunc = in_offset(data, op, 1) as i32;
        let most_trunc = (state.bits_field.byte_size - least_trunc) - data.vn(out).get_size();
        let mut new_range = state.bits_field;
        new_range.truncate_least_sig_bytes(least_trunc);
        new_range.truncate_most_sig_bytes(most_trunc);
        if new_range.num_bits == 0 {
            return;
        }
        if state.bits_field.num_bits == new_range.num_bits {
            let new_sign_ext = state.is_sign_extended;
            let mut next = BitFieldNodeState::new_copy(state, &new_range, out, new_sign_ext);
            next.bits_used.truncate_least_sig_bytes(least_trunc);
            next.bits_used.truncate_most_sig_bytes(most_trunc);
            self.base.work_list.push_back(next);
        } else if Self::test_consumed(out, &new_range, data) {
            self.pull_list.push(PullRecord::new(state, Some(op), glb));
        }
    }

    fn handle_insert_forward(&mut self, state: &BitFieldNodeState, op: OpId, data: &Funcdata, glb: &Architecture) {
        if Some(data.op(op).get_in(1)) != state.node {
            return;
        }
        if state.bits_field.least_sig_bit != 0 {
            return;
        }
        let sz = in_offset(data, op, 3) as i32;
        if sz > state.bits_field.num_bits {
            return;
        }
        self.pull_list.push(PullRecord::new(state, Some(op), glb));
    }

    fn handle_less_forward(&mut self, state: &BitFieldNodeState, op: OpId, data: &Funcdata, glb: &Architecture) {
        if !state.bits_field.is_most_significant() {
            return;
        }
        let node = state.node.expect("bitfield node without varnode");
        let slot = data.op(op).get_slot(node);
        let cvn = data.vn(data.op(op).get_in(1 - slot));
        if !cvn.is_constant() {
            return;
        }
        let val = cvn.get_offset();
        let least_sig_zero_bits = (val & 1) == 0;
        let mut num_extremal_bits = if least_sig_zero_bits {
            leastsigbit_set(val)
        } else {
            leastsigbit_set(!val)
        };
        if num_extremal_bits < 0 {
            num_extremal_bits = UINTB_BITS;
        }
        let mut need_mask_check = false;
        let opc = data.op(op).code();
        if opc == OpCode::IntSless || opc == OpCode::IntLess {
            if least_sig_zero_bits && slot != 0 {
                return;
            }
            if !least_sig_zero_bits && slot == 0 {
                need_mask_check = true;
            }
        } else if opc == OpCode::IntSlessequal || opc == OpCode::IntLessequal {
            if least_sig_zero_bits && slot != 1 {
                return;
            }
            if !least_sig_zero_bits && slot == 1 {
                need_mask_check = true;
            }
        }
        if need_mask_check {
            let mut mask: u64 = if num_extremal_bits >= UINTB_BITS {
                0
            } else {
                1u64 << num_extremal_bits
            };
            mask = mask.wrapping_sub(1);
            if (mask & data.vn(node).get_nz_mask()) == mask {
                return;
            }
        }
        if state.bits_field.least_sig_bit <= num_extremal_bits {
            self.pull_list.push(PullRecord::new(state, Some(op), glb));
        }
    }

    fn handle_least_sig_op(&mut self, state: &BitFieldNodeState, op: OpId, data: &Funcdata, glb: &Architecture) {
        if state.bits_field.least_sig_bit != 0 {
            return;
        }
        if Self::test_consumed(out_of(data, op), &state.bits_field, data) {
            self.pull_list.push(PullRecord::new(state, Some(op), glb));
        }
    }

    fn handle_equal_forward(&mut self, state: &BitFieldNodeState, op: OpId, data: &Funcdata, glb: &Architecture) {
        let cvn = data.vn(data.op(op).get_in(1));
        if state.bits_field.byte_size > UINTB_BYTES {
            return;
        }
        if !cvn.is_constant() {
            return;
        }
        let full_field = match state.field {
            Some(field) => bit_field_of(&field, type_factory(glb)).bits.num_bits == state.bits_field.num_bits,
            None => false,
        };
        if full_field {
            let val = state.bits_field.get_mask();
            self.pull_list.push(PullRecord::new_equal(state, op, val, glb));
        } else {
            self.pull_list.push(PullRecord::new_aborted(op));
        }
    }

    fn process_forward(&mut self, state: &BitFieldNodeState, data: &Funcdata, glb: &Architecture) {
        if state.is_field_aligned() && state.does_sign_extension_match(glb) {
            self.pull_list.push(PullRecord::new(state, None, glb));
            return;
        }
        let node = state.node.expect("bitfield node without varnode");
        for &op in data.vn(node).descend() {
            match data.op(op).code() {
                OpCode::IntLeft => self.handle_left_forward(state, op, data, glb),
                OpCode::IntMult => self.handle_mult_forward(state, op, data, glb),
                OpCode::IntRight | OpCode::IntSright => self.handle_right_forward(state, op, data, glb),
                OpCode::IntAnd => self.handle_and_forward(state, op, data, glb),
                OpCode::IntZext | OpCode::IntSext => self.handle_ext_forward(state, op, data),
                OpCode::IntLess | OpCode::IntLessequal | OpCode::IntSless | OpCode::IntSlessequal => {
                    self.handle_less_forward(state, op, data, glb)
                }
                OpCode::IntEqual | OpCode::IntNotequal => self.handle_equal_forward(state, op, data, glb),
                OpCode::IntAdd | OpCode::IntOr | OpCode::IntXor | OpCode::Int2comp | OpCode::IntNegate => {
                    self.handle_least_sig_op(state, op, data, glb)
                }
                OpCode::Subpiece => self.handle_subpiece_forward(state, op, data, glb),
                OpCode::Insert => self.handle_insert_forward(state, op, data, glb),
                _ => {}
            }
        }
    }

    fn test_compare_group(&mut self, iter: usize, data: &Funcdata) -> usize {
        let mut curiter = iter;
        let mut is_aborted = false;
        let mut collect_mask: u64 = 0;
        let vn = self.pull_list[iter].read_vn;
        let op = self.pull_list[iter].read_op;
        let val = in_offset(data, op.expect("compare pull without op"), 1);
        while curiter < self.pull_list.len() {
            let rec = &self.pull_list[curiter];
            if rec.read_op != op {
                break;
            }
            curiter += 1;
            if rec.record_type == PullRecord::ABORTED {
                is_aborted = true;
            }
            collect_mask |= rec.mask;
        }
        if is_aborted
            || (!collect_mask & val) != 0
            || (!collect_mask & data.vn(vn.expect("compare pull without varnode")).get_nz_mask()) != 0
        {
            self.pull_list.drain(iter..curiter);
            curiter = iter;
        }
        curiter
    }

    fn apply_record(
        &mut self,
        rec: &mut PullRecord,
        state: &mut TransformState,
        data: &mut Funcdata,
        glb: &mut Architecture,
    ) -> Result<()> {
        let mod_op;
        match rec.read_op {
            None => {
                let read_vn = rec.read_vn.expect("pull record without varnode");
                mod_op = data.vn(read_vn).get_def().expect("pulled varnode is not written");
                data.op_unset_output(mod_op)?;
            }
            Some(read_op) => {
                let read_vn = rec.read_vn.expect("pull record without varnode");
                if read_vn != self.root {
                    mod_op = data.vn(read_vn).get_def().expect("pulled varnode is not written");
                } else {
                    mod_op = read_op;
                }
                let slot = data.op(read_op).get_slot(read_vn);
                let size = data.vn(read_vn).get_size();
                let new_vn = data.new_unique(size, None, glb);
                rec.read_vn = Some(new_vn);
                data.op_set_input(read_op, new_vn, slot)?;
            }
        }
        let read_vn = rec.read_vn.expect("pull record without varnode");
        let mut in_vn = self.root;
        if let Some(load_op) = self.load_op
            && state.count > 0
        {
            let addr = data.op(load_op).get_addr().clone();
            let new_load = data.new_op(2, &addr);
            data.op_set_opcode(new_load, OpCode::Load, glb);
            let load_space = data.op(load_op).get_in(0);
            let load_ptr = data.op(load_op).get_in(1);
            data.op_set_input(new_load, load_space, 0)?;
            data.op_set_input(new_load, load_ptr, 1)?;
            in_vn = data.new_unique_out(self.base.container_size, new_load, glb)?;
            data.op_insert_after(new_load, load_op);
            data.op_mark_non_printing(new_load);
        }
        data.vn_update_type(in_vn, state.partial_type.expect("missing partial data-type"));
        let rec_dt = rec.dt.expect("pull record without data-type");
        let mod_addr = data.op(mod_op).get_addr().clone();
        let pull_op = data.new_op(3, &mod_addr);
        let pull_code = if type_factory(glb).get(rec_dt).get_metatype() == TypeMetatype::Int {
            OpCode::Spull
        } else {
            OpCode::Zpull
        };
        data.op_set_opcode(pull_op, pull_code, glb);
        data.op_set_input(pull_op, in_vn, 0)?;
        let pos_vn = data.new_constant(4, rec.pos as i64 as u64, glb);
        data.op_set_input(pull_op, pos_vn, 1)?;
        let num_vn = data.new_constant(4, rec.num_bits as i64 as u64, glb);
        data.op_set_input(pull_op, num_vn, 2)?;
        if Some(mod_op) != rec.read_op {
            data.op_insert_after(pull_op, mod_op);
        } else {
            data.op_insert_before(pull_op, mod_op);
        }
        if rec.left_shift != 0 {
            let shift_vn = data.new_unique_out(self.base.container_size, pull_op, glb)?;
            let shift_op = data.new_op(2, &mod_addr);
            data.op_set_opcode(shift_op, OpCode::IntLeft, glb);
            data.op_set_input(shift_op, shift_vn, 0)?;
            let amount_vn = data.new_constant(4, rec.left_shift as i64 as u64, glb);
            data.op_set_input(shift_op, amount_vn, 1)?;
            data.op_insert_after(shift_op, pull_op);
            data.op_set_output(shift_op, read_vn, glb)?;
        } else {
            data.op_set_output(pull_op, read_vn, glb)?;
        }
        let pull_out = out_of(data, pull_op);
        let pull_out_size = data.vn(pull_out).get_size();
        let pull_out_meta = type_factory(glb).get(data.vn(pull_out).get_type()).get_metatype();
        if pull_out_meta == TypeMetatype::Unknown {
            let dt = type_factory_mut(glb).resize_integer(rec_dt, pull_out_size)?;
            data.vn_update_type(pull_out, dt);
        } else if type_factory(glb).get(rec_dt).get_metatype() == TypeMetatype::Bool
            && pull_out_size == 1
            && rec.num_bits == 1
        {
            data.vn_update_type(pull_out, rec_dt);
        }
        if Some(mod_op) != rec.read_op {
            let destroy = match data.op(mod_op).get_out() {
                None => true,
                Some(outvn) => data.vn(outvn).has_no_descend(),
            };
            if destroy {
                data.op_destroy_recursive(mod_op, &mut state.dead_scratch)?;
            }
        }
        state.count += 1;
        Ok(())
    }

    fn apply_compare_record(&mut self, rec: &PullRecord, data: &mut Funcdata, glb: &mut Architecture) -> Result<()> {
        let read_op = rec.read_op.expect("compare pull without op");
        let orig_val = in_offset(data, read_op, 1);
        let mut num = 0;
        let mut enditer = 0;
        while enditer < self.pull_list.len() {
            if self.pull_list[enditer].read_op != rec.read_op {
                break;
            }
            enditer += 1;
            num += 1;
        }
        if num > 1 {
            let opc = data.op(read_op).code();
            let combine_code = if opc == OpCode::IntEqual {
                OpCode::BoolAnd
            } else {
                OpCode::BoolOr
            };
            let vn = data.op(read_op).get_in(0);
            let mut cur_combine = read_op;
            data.op_set_opcode(cur_combine, combine_code, glb);
            for index in 0..num {
                let addr = data.op(cur_combine).get_addr().clone();
                let op = data.new_op(2, &addr);
                data.op_set_opcode(op, opc, glb);
                let bool_vn = data.new_unique_out(1, op, glb)?;
                data.op_set_input(op, vn, 0)?;
                data.op_insert_before(op, cur_combine);
                if index == 0 {
                    data.op_set_input(cur_combine, bool_vn, 0)?;
                } else if index < num - 1 {
                    let combine_op = data.new_op(2, &addr);
                    data.op_set_opcode(combine_op, combine_code, glb);
                    let bool2_vn = data.new_unique_out(1, combine_op, glb)?;
                    data.op_set_input(cur_combine, bool2_vn, 1)?;
                    data.op_set_input(combine_op, bool_vn, 0)?;
                    data.op_insert_before(combine_op, cur_combine);
                    cur_combine = combine_op;
                } else {
                    data.op_set_input(cur_combine, bool_vn, 1)?;
                }
                self.pull_list[index].read_op = Some(op);
            }
        }
        for index in 0..enditer {
            let subrec = self.pull_list[index].clone();
            let sub_dt = subrec.dt.expect("pull record without data-type");
            let read_size = data.vn(subrec.read_vn.expect("pull record without varnode")).get_size();
            let mut val = orig_val & subrec.mask;
            val = val.wrapping_shr(subrec.left_shift as u32);
            if type_factory(glb).get(sub_dt).get_metatype() == TypeMetatype::Int {
                val = extend_signbit(val, subrec.num_bits, read_size);
            }
            let vn = data.new_constant(read_size, val, glb);
            let dt = type_factory_mut(glb).resize_integer(sub_dt, read_size)?;
            data.vn_update_type(vn, dt);
            data.op_set_input(subrec.read_op.expect("pull record without op"), vn, 1)?;
            let record = &mut self.pull_list[index];
            record.record_type = PullRecord::NORMAL;
            record.left_shift = 0;
        }
        Ok(())
    }

    fn fold_load(&self, load_op: OpId, data: &mut Funcdata) -> bool {
        let outvn = out_of(data, load_op);
        for &op in data.vn(outvn).descend() {
            let opc = data.op(op).code();
            if opc != OpCode::Zpull && opc != OpCode::Spull && opc != OpCode::Insert {
                return false;
            }
        }
        data.op_mark_non_printing(load_op);
        true
    }

    fn fold_ptrsub(&self, load_op: OpId, data: &mut Funcdata) {
        let vn = data.op(load_op).get_in(1);
        let Some(ptrsub) = data.vn(vn).get_def() else {
            return;
        };
        if data.op(ptrsub).code() != OpCode::Ptrsub {
            return;
        }
        for &op in data.vn(vn).descend() {
            if data.op(op).code() != OpCode::Load {
                return;
            }
            if !data.op(op).not_printed() {
                return;
            }
        }
        data.op_mark_non_printing(ptrsub);
    }

    pub fn do_trace(&mut self, data: &Funcdata, glb: &Architecture) -> bool {
        while let Some(state) = self.base.work_list.pop_front() {
            self.process_forward(&state, data, glb);
        }
        if self.pull_list.is_empty() {
            return false;
        }
        let records = std::mem::take(&mut self.pull_list);
        self.pull_list = list_sort(records, &mut |first: &PullRecord, second: &PullRecord| {
            first.less_than(second, data)
        });
        let mut iter = 0;
        while iter < self.pull_list.len() {
            if self.pull_list[iter].record_type != PullRecord::NORMAL {
                iter = self.test_compare_group(iter, data);
            } else {
                iter += 1;
            }
        }
        !self.pull_list.is_empty()
    }

    pub fn apply(&mut self, data: &mut Funcdata, glb: &mut Architecture) -> Result<()> {
        let mut state = TransformState {
            dead_scratch: Vec::new(),
            partial_type: Some(self.base.build_partial_type(glb)?),
            count: 0,
        };
        while !self.pull_list.is_empty() {
            if self.pull_list[0].record_type == PullRecord::EQUAL {
                let rec = self.pull_list[0].clone();
                self.apply_compare_record(&rec, data, glb)?;
            } else {
                let mut rec = self.pull_list.remove(0);
                self.apply_record(&mut rec, &mut state, data, glb)?;
            }
        }
        if let Some(load_op) = self.load_op
            && self.fold_load(load_op, data)
        {
            self.fold_ptrsub(load_op, data);
        }
        Ok(())
    }
}

pub struct RuleBitFieldStore {
    base: RuleBase,
}

impl RuleBitFieldStore {
    pub fn new(group: &str) -> RuleBitFieldStore {
        RuleBitFieldStore {
            base: RuleBase::new(group, 0, "bitfield_store"),
        }
    }
}

impl Rule for RuleBitFieldStore {
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
        Some(Box::new(RuleBitFieldStore::new(self.get_group())))
    }

    fn get_op_list(&self, oplist: &mut Vec<OpCode>) {
        oplist.push(OpCode::Store);
    }

    fn apply_op(&mut self, op: OpId, data: &mut Funcdata, glb: &mut Architecture) -> Result<i32> {
        let ptr = data.vn_get_type_read_facing(data.op(op).get_in(1), op, glb);
        let mut off: i32 = 0;
        let types = type_factory(glb);
        let Some(dt) = types.get(ptr).get_ptr_into(&mut off, types) else {
            return Ok(0);
        };
        if !types.get(dt).has_bitfields() {
            return Ok(0);
        }
        let vn = data.op(op).get_in(2);
        if let Some(def_op) = data.vn(vn).get_def()
            && data.op(def_op).code() == OpCode::Insert
        {
            return Ok(0);
        }
        let mut transform = BitFieldInsertTransform::new(data, op, dt, off, glb);
        if !transform.do_trace(data, glb) {
            return Ok(0);
        }
        transform.apply(data, glb)?;
        Ok(1)
    }
}

pub struct RuleBitFieldOut {
    base: RuleBase,
}

impl RuleBitFieldOut {
    pub fn new(group: &str) -> RuleBitFieldOut {
        RuleBitFieldOut {
            base: RuleBase::new(group, 0, "bitfield_out"),
        }
    }
}

impl Rule for RuleBitFieldOut {
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
        Some(Box::new(RuleBitFieldOut::new(self.get_group())))
    }

    fn get_op_list(&self, oplist: &mut Vec<OpCode>) {
        oplist.extend_from_slice(BitFieldInsertTransform::ALLOWED_FINAL_WRITES);
    }

    fn apply_op(&mut self, op: OpId, data: &mut Funcdata, glb: &mut Architecture) -> Result<i32> {
        let outvn = out_of(data, op);
        let dt = data.vn_get_type_def_facing(outvn, glb);
        if type_factory(glb).get(dt).has_bitfields() {
            let mut transform = BitFieldInsertTransform::new(data, op, dt, 0, glb);
            if transform.do_trace(data, glb) {
                transform.apply(data, glb)?;
                return Ok(1);
            }
        }
        let descendants = data.vn(outvn).descend().to_vec();
        for ind_op in descendants {
            if data.op(ind_op).code() != OpCode::Indirect {
                continue;
            }
            let dt = data.vn_get_type_def_facing(out_of(data, ind_op), glb);
            if type_factory(glb).get(dt).has_bitfields() {
                let mut transform = BitFieldInsertTransform::new(data, ind_op, dt, 0, glb);
                if transform.do_trace(data, glb) {
                    transform.apply(data, glb)?;
                    return Ok(1);
                }
            }
        }
        Ok(0)
    }
}

pub struct RuleBitFieldLoad {
    base: RuleBase,
}

impl RuleBitFieldLoad {
    pub fn new(group: &str) -> RuleBitFieldLoad {
        RuleBitFieldLoad {
            base: RuleBase::new(group, 0, "bitfield_load"),
        }
    }
}

impl Rule for RuleBitFieldLoad {
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
        Some(Box::new(RuleBitFieldLoad::new(self.get_group())))
    }

    fn get_op_list(&self, oplist: &mut Vec<OpCode>) {
        oplist.push(OpCode::Load);
    }

    fn apply_op(&mut self, op: OpId, data: &mut Funcdata, glb: &mut Architecture) -> Result<i32> {
        let ptr = data.vn_get_type_read_facing(data.op(op).get_in(1), op, glb);
        let mut off: i32 = 0;
        let types = type_factory(glb);
        let Some(dt) = types.get(ptr).get_ptr_into(&mut off, types) else {
            return Ok(0);
        };
        if !types.get(dt).has_bitfields() {
            return Ok(0);
        }
        if data.op(op).not_printed() {
            return Ok(0);
        }
        let mut transform = BitFieldPullTransform::new(data, out_of(data, op), dt, off, glb);
        if !transform.do_trace(data, glb) {
            return Ok(0);
        }
        transform.apply(data, glb)?;
        Ok(1)
    }
}

pub struct RuleBitFieldIn {
    base: RuleBase,
}

impl RuleBitFieldIn {
    pub fn new(group: &str) -> RuleBitFieldIn {
        RuleBitFieldIn {
            base: RuleBase::new(group, 0, "bitfield_in"),
        }
    }
}

impl Rule for RuleBitFieldIn {
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
        Some(Box::new(RuleBitFieldIn::new(self.get_group())))
    }

    fn get_op_list(&self, oplist: &mut Vec<OpCode>) {
        oplist.extend_from_slice(&[
            OpCode::Copy,
            OpCode::IntEqual,
            OpCode::IntNotequal,
            OpCode::IntSless,
            OpCode::IntSlessequal,
            OpCode::IntLess,
            OpCode::IntLessequal,
            OpCode::IntZext,
            OpCode::IntSext,
            OpCode::IntAdd,
            OpCode::IntNegate,
            OpCode::IntAnd,
            OpCode::IntLeft,
            OpCode::IntRight,
            OpCode::IntSright,
            OpCode::IntMult,
            OpCode::Subpiece,
        ]);
    }

    fn apply_op(&mut self, op: OpId, data: &mut Funcdata, glb: &mut Architecture) -> Result<i32> {
        let invn = data.op(op).get_in(0);
        let dt = data.vn_get_type_read_facing(invn, op, glb);
        if !type_factory(glb).get(dt).has_bitfields() {
            return Ok(0);
        }
        let mut transform = BitFieldPullTransform::new(data, invn, dt, 0, glb);
        if !transform.do_trace(data, glb) {
            return Ok(0);
        }
        transform.apply(data, glb)?;
        Ok(1)
    }
}

pub struct RulePullAbsorb {
    base: RuleBase,
}

impl RulePullAbsorb {
    pub fn new(group: &str) -> RulePullAbsorb {
        RulePullAbsorb {
            base: RuleBase::new(group, 0, "pull_absorb"),
        }
    }

    fn absorb_right(
        &mut self,
        data: &mut Funcdata,
        glb: &mut Architecture,
        right_op: OpId,
        pull_op: OpId,
    ) -> Result<i32> {
        let outvn = out_of(data, right_op);
        let descendants = data.vn(outvn).descend().to_vec();
        for read_op in descendants {
            if data.op(read_op).code() == OpCode::IntAnd {
                let res = self.absorb_right_and_comp_zero(data, glb, right_op, read_op, pull_op)?;
                if res != 0 {
                    return Ok(res);
                }
            }
        }
        Ok(0)
    }

    fn absorb_right_and_comp_zero(
        &mut self,
        data: &mut Funcdata,
        glb: &mut Architecture,
        right_op: OpId,
        and_op: OpId,
        pull_op: OpId,
    ) -> Result<i32> {
        if data.op(pull_op).code() != OpCode::Spull {
            return Ok(0);
        }
        let cvn = data.vn(data.op(right_op).get_in(1));
        if !cvn.is_constant() {
            return Ok(0);
        }
        let sa = cvn.get_offset() as i32;
        let numbits = in_offset(data, pull_op, 2) as i32;
        if numbits.wrapping_sub(1) != sa {
            return Ok(0);
        }
        if !data.vn(data.op(and_op).get_in(1)).constant_match(1) {
            return Ok(0);
        }
        let outvn = out_of(data, and_op);
        let descendants = data.vn(outvn).descend().to_vec();
        for read_op in descendants {
            let opc = data.op(read_op).code();
            if opc != OpCode::IntEqual && opc != OpCode::IntNotequal {
                continue;
            }
            if !data.vn(data.op(read_op).get_in(1)).constant_match(0) {
                continue;
            }
            let vn = out_of(data, pull_op);
            if opc == OpCode::IntEqual {
                data.op_set_opcode(read_op, OpCode::IntLessequal, glb);
                let zvn = data.op(read_op).get_in(1);
                data.op_set_input(read_op, vn, 1)?;
                data.op_set_input(read_op, zvn, 0)?;
            } else {
                data.op_set_opcode(read_op, OpCode::IntSless, glb);
                data.op_set_input(read_op, vn, 0)?;
            }
            data.destroy_varnode_recursive(outvn)?;
            return Ok(1);
        }
        Ok(0)
    }

    fn absorb_left(
        &mut self,
        data: &mut Funcdata,
        glb: &mut Architecture,
        left_op: OpId,
        pull_op: OpId,
    ) -> Result<i32> {
        let outvn = out_of(data, left_op);
        let descendants = data.vn(outvn).descend().to_vec();
        for read_op in descendants {
            let opc = data.op(read_op).code();
            let res = if opc == OpCode::IntSless {
                self.absorb_compare(data, glb, read_op, Some(left_op), pull_op)?
            } else if opc == OpCode::IntRight {
                self.absorb_left_right(data, glb, read_op, left_op, pull_op)?
            } else if opc == OpCode::IntAnd {
                self.absorb_left_and(data, glb, read_op, left_op, pull_op)?
            } else {
                0
            };
            if res != 0 {
                return Ok(res);
            }
        }
        Ok(0)
    }

    fn absorb_left_right(
        &mut self,
        data: &mut Funcdata,
        glb: &mut Architecture,
        right_op: OpId,
        left_op: OpId,
        pull_op: OpId,
    ) -> Result<i32> {
        let leftcvn = data.op(left_op).get_in(1);
        if !data.vn(leftcvn).is_constant() {
            return Ok(0);
        }
        let rightcvn = data.op(right_op).get_in(1);
        if !data.vn(rightcvn).is_constant() {
            return Ok(0);
        }
        let bitsize = in_offset(data, pull_op, 2) as i32;
        let invn = data.op(pull_op).get_in(0);
        let container_size = data.vn(invn).get_size() * 8;
        let leftshift = data.vn(leftcvn).get_offset() as i32;
        let rightshift = data.vn(rightcvn).get_offset() as i32;
        if leftshift.wrapping_add(bitsize) > container_size {
            return Ok(0);
        }
        let sa = rightshift.wrapping_sub(leftshift);
        let pull_out = out_of(data, pull_op);
        let right_size = data.vn(rightcvn).get_size();
        if sa == 0 {
            let right_out = out_of(data, right_op);
            data.total_replace(right_out, pull_out)?;
            data.destroy_varnode_recursive(right_out)?;
        } else if sa > 0 {
            let amount = data.new_constant(right_size, sa as i64 as u64, glb);
            data.op_set_input(right_op, amount, 1)?;
            data.op_set_input(right_op, pull_out, 0)?;
            data.destroy_varnode_recursive(out_of(data, left_op))?;
        } else {
            data.op_set_opcode(right_op, OpCode::IntLeft, glb);
            let amount = data.new_constant(right_size, sa.wrapping_neg() as i64 as u64, glb);
            data.op_set_input(right_op, amount, 1)?;
            data.op_set_input(right_op, pull_out, 0)?;
            data.destroy_varnode_recursive(out_of(data, left_op))?;
        }
        Ok(1)
    }

    fn absorb_left_and(
        &mut self,
        data: &mut Funcdata,
        glb: &mut Architecture,
        and_op: OpId,
        left_op: OpId,
        _pull_op: OpId,
    ) -> Result<i32> {
        let shift_amount = data.vn(data.op(left_op).get_in(1));
        if !shift_amount.is_constant() {
            return Ok(0);
        }
        let sa = shift_amount.get_offset() as i32;
        if !(0..UINTB_BITS).contains(&sa) {
            return Ok(0);
        }
        let mask_vn = data.op(and_op).get_in(1);
        if !data.vn(mask_vn).is_constant() {
            return Ok(0);
        }
        let mut mask = data.vn(mask_vn).get_offset();
        let outvn = out_of(data, and_op);
        let descendants = data.vn(outvn).descend().to_vec();
        for read_op in descendants {
            let opc = data.op(read_op).code();
            if opc == OpCode::IntEqual || opc == OpCode::IntNotequal {
                let comp_val = data.op(read_op).get_in(1);
                if !data.vn(comp_val).is_constant() {
                    continue;
                }
                let comp_offset = data.vn(comp_val).get_offset();
                let val = comp_offset >> sa;
                if val << sa != comp_offset {
                    continue;
                }
                mask >>= sa;
                let mask_size = data.vn(mask_vn).get_size();
                let mask_type = data.vn(mask_vn).get_type();
                let new_and = data.new_constant(mask_size, mask, glb);
                data.vn_update_type(new_and, mask_type);
                data.op_set_input(and_op, new_and, 1)?;
                if val != comp_offset {
                    let comp_size = data.vn(comp_val).get_size();
                    let comp_type = data.vn(comp_val).get_type();
                    let new_val = data.new_constant(comp_size, val, glb);
                    data.vn_update_type(new_val, comp_type);
                    data.op_set_input(read_op, new_val, 1)?;
                }
                let left_in = data.op(left_op).get_in(0);
                data.op_set_input(and_op, left_in, 0)?;
                data.destroy_varnode_recursive(out_of(data, left_op))?;
                return Ok(1);
            }
        }
        Ok(0)
    }

    fn absorb_and(&mut self, data: &mut Funcdata, glb: &mut Architecture, and_op: OpId, pull_op: OpId) -> Result<i32> {
        let mask_vn = data.op(and_op).get_in(1);
        if !data.vn(mask_vn).is_constant() {
            return Ok(0);
        }
        let vn = out_of(data, pull_op);
        if data.op(pull_op).code() != OpCode::Spull {
            return Ok(0);
        }
        let bitsize = in_offset(data, pull_op, 2) as i32;
        let match_val = 1u64.wrapping_shl(bitsize.wrapping_sub(1) as u32);
        if match_val != data.vn(mask_vn).get_offset() {
            return Ok(0);
        }
        let outvn = out_of(data, and_op);
        let descendants = data.vn(outvn).descend().to_vec();
        for read_op in descendants {
            let opc = data.op(read_op).code();
            if opc == OpCode::IntEqual || opc == OpCode::IntNotequal {
                if !data.vn(data.op(read_op).get_in(1)).constant_match(0) {
                    continue;
                }
                let vn_size = data.vn(vn).get_size();
                let new_zero = data.new_constant(vn_size, 0, glb);
                let vn_type = data.vn(vn).get_type();
                let dt = type_factory_mut(glb).resize_integer(vn_type, vn_size)?;
                data.vn_update_type(new_zero, dt);
                if opc == OpCode::IntEqual {
                    data.op_set_opcode(read_op, OpCode::IntSlessequal, glb);
                    data.op_set_input(read_op, new_zero, 0)?;
                    data.op_set_input(read_op, vn, 1)?;
                } else {
                    data.op_set_opcode(read_op, OpCode::IntSless, glb);
                    data.op_set_input(read_op, vn, 0)?;
                    data.op_set_input(read_op, new_zero, 1)?;
                }
                data.destroy_varnode_recursive(outvn)?;
                return Ok(1);
            }
        }
        Ok(0)
    }

    fn absorb_compare(
        &mut self,
        data: &mut Funcdata,
        glb: &mut Architecture,
        comp_op: OpId,
        left_op: Option<OpId>,
        pull_op: OpId,
    ) -> Result<i32> {
        let mut sa: i32 = 0;
        if let Some(left) = left_op {
            let cvn = data.vn(data.op(left).get_in(1));
            if !cvn.is_constant() {
                return Ok(0);
            }
            sa = cvn.get_offset() as i32;
        }
        let numbits = in_offset(data, pull_op, 2) as i32;
        let invn = data.op(pull_op).get_in(0);
        let sz = data.vn(invn).get_size() * 8;
        if numbits.wrapping_add(sa) != sz {
            return Ok(0);
        }
        let pull_out = out_of(data, pull_op);
        let in_vn = match left_op {
            None => pull_out,
            Some(left) => out_of(data, left),
        };
        let less_vn0 = data.op(comp_op).get_in(0);
        let less_vn1 = data.op(comp_op).get_in(1);
        let in_size = data.vn(in_vn).get_size();
        if data.op(comp_op).code() == OpCode::IntSless {
            if numbits == 1
                && less_vn0 == in_vn
                && data.vn(less_vn1).is_constant()
                && data.vn(less_vn1).get_offset() == 0
            {
                let old_vn = out_of(data, comp_op);
                data.total_replace(old_vn, pull_out)?;
                data.destroy_varnode_recursive(old_vn)?;
                return Ok(1);
            }
            if numbits == 1
                && less_vn1 == in_vn
                && data.vn(less_vn0).is_constant()
                && data.vn(less_vn0).get_offset() == calc_mask(in_size)
            {
                data.op_remove_input(comp_op, 0);
                data.op_set_opcode(comp_op, OpCode::BoolNegate, glb);
                data.op_set_input(comp_op, pull_out, 0)?;
                data.destroy_varnode_recursive(in_vn)?;
                return Ok(1);
            }
        }
        let mask = 1u64.wrapping_shl(sa as u32).wrapping_sub(1);
        if sa > 0 && sa < UINTB_BITS && in_vn == less_vn0 && data.vn(less_vn1).is_constant() {
            let orig_val = data.vn(less_vn1).get_offset();
            let low_bits = mask & orig_val;
            if low_bits == 0 || low_bits == 1 {
                let new_val = if low_bits == 1 {
                    let shifted = orig_val.wrapping_sub(1) >> sa;
                    shifted.wrapping_add(1) & calc_mask(in_size)
                } else {
                    orig_val >> sa
                };
                data.op_set_input(comp_op, pull_out, 0)?;
                let constant = data.new_constant(in_size, new_val, glb);
                data.op_set_input(comp_op, constant, 1)?;
                data.destroy_varnode_recursive(in_vn)?;
                return Ok(1);
            }
        }
        if sa > 0 && sa < UINTB_BITS && in_vn == less_vn1 && data.vn(less_vn0).is_constant() {
            let orig_val = data.vn(less_vn0).get_offset();
            let low_bits = mask & orig_val;
            if low_bits == 0 || low_bits == mask {
                let new_val = if low_bits == mask {
                    let shifted = orig_val.wrapping_add(1) >> sa;
                    shifted.wrapping_sub(1) & calc_mask(in_size)
                } else {
                    orig_val >> sa
                };
                data.op_set_input(comp_op, pull_out, 1)?;
                let constant = data.new_constant(in_size, new_val, glb);
                data.op_set_input(comp_op, constant, 0)?;
                data.destroy_varnode_recursive(in_vn)?;
                return Ok(1);
            }
        }
        Ok(0)
    }

    fn absorb_ext(&mut self, data: &mut Funcdata, glb: &mut Architecture, ext_op: OpId, pull_op: OpId) -> Result<i32> {
        let pull_code = data.op(pull_op).code();
        let pull_signed = pull_code == OpCode::Spull;
        let ext_signed = data.op(ext_op).code() == OpCode::IntSext;
        if ext_signed != pull_signed {
            return Ok(0);
        }
        let vn = data.op(ext_op).get_in(0);
        if data.vn(vn).lone_descend() != Some(ext_op) {
            return Ok(0);
        }
        data.op_set_opcode(ext_op, pull_code, glb);
        let pull_in = data.op(pull_op).get_in(0);
        data.op_set_input(ext_op, pull_in, 0)?;
        let pos_vn = data.op(pull_op).get_in(1);
        let num_vn = data.op(pull_op).get_in(2);
        data.op_insert_input(ext_op, pos_vn, 1)?;
        data.op_insert_input(ext_op, num_vn, 2)?;
        data.destroy_varnode_recursive(vn)?;
        Ok(1)
    }

    fn absorb_subpiece(
        &mut self,
        data: &mut Funcdata,
        glb: &mut Architecture,
        sub_op: OpId,
        pull_op: OpId,
    ) -> Result<i32> {
        if in_offset(data, sub_op, 1) != 0 {
            return Ok(0);
        }
        let bitsize = in_offset(data, pull_op, 2) as i32;
        let outvn = out_of(data, sub_op);
        if bitsize > 8 * data.vn(outvn).get_size() {
            return Ok(0);
        }
        let vn = data.op(sub_op).get_in(0);
        if data.vn(vn).lone_descend() != Some(sub_op) {
            return Ok(0);
        }
        let pull_code = data.op(pull_op).code();
        data.op_set_opcode(sub_op, pull_code, glb);
        let pull_in = data.op(pull_op).get_in(0);
        data.op_set_input(sub_op, pull_in, 0)?;
        let pos_vn = data.op(pull_op).get_in(1);
        let num_vn = data.op(pull_op).get_in(2);
        data.op_set_input(sub_op, pos_vn, 1)?;
        data.op_insert_input(sub_op, num_vn, 2)?;
        data.destroy_varnode_recursive(vn)?;
        Ok(1)
    }

    fn absorb_comp_zero(
        &mut self,
        data: &mut Funcdata,
        glb: &mut Architecture,
        comp_op: OpId,
        pull_op: OpId,
    ) -> Result<i32> {
        let zvn = data.op(comp_op).get_in(1);
        if !data.vn(zvn).constant_match(0) {
            return Ok(0);
        }
        let bitsize = in_offset(data, pull_op, 2) as i32;
        if bitsize != 1 {
            return Ok(0);
        }
        let vn = data.op(comp_op).get_in(0);
        if data.vn(vn).lone_descend() != Some(comp_op) {
            return Ok(0);
        }
        if data.vn(vn).is_addr_tied() {
            return Ok(0);
        }
        let pull_code = data.op(pull_op).code();
        if pull_code == OpCode::Spull {
            return Ok(0);
        }
        let Some((parent, index)) = BitFieldExpression::get_pull_field(pull_op, data, glb) else {
            return Ok(0);
        };
        let field_ref = BitFieldRef { parent, index };
        {
            let types = type_factory(glb);
            if types.get(bit_field_of(&field_ref, types).tp).get_metatype() != TypeMetatype::Bool {
                return Ok(0);
            }
        }
        if data.op(comp_op).code() == OpCode::IntEqual {
            let vn_size = data.vn(vn).get_size();
            if vn_size > 1 {
                let mut smalladdr = data.vn(vn).get_addr().clone();
                let big_endian = data
                    .vn(vn)
                    .get_space()
                    .expect("varnode has no address space")
                    .is_big_endian();
                if big_endian {
                    smalladdr = smalladdr.add((vn_size - 1) as i64);
                }
                data.op_unset_output(pull_op)?;
                let new_vn = data.new_varnode_out(1, &smalladdr, pull_op, glb)?;
                let dt = type_factory_mut(glb).get_base(1, TypeMetatype::Bool)?;
                data.vn_update_type(new_vn, dt);
                data.op_set_input(comp_op, new_vn, 0)?;
                data.delete_varnode(vn)?;
            }
            data.op_set_opcode(comp_op, OpCode::BoolNegate, glb);
            data.op_remove_input(comp_op, 1);
        } else {
            data.op_set_opcode(comp_op, pull_code, glb);
            let pull_in = data.op(pull_op).get_in(0);
            data.op_set_input(comp_op, pull_in, 0)?;
            let pos_vn = data.op(pull_op).get_in(1);
            let num_vn = data.op(pull_op).get_in(2);
            data.op_set_input(comp_op, pos_vn, 1)?;
            data.op_insert_input(comp_op, num_vn, 2)?;
            data.destroy_varnode_recursive(vn)?;
        }
        Ok(1)
    }
}

impl Rule for RulePullAbsorb {
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
        Some(Box::new(RulePullAbsorb::new(self.get_group())))
    }

    fn get_op_list(&self, oplist: &mut Vec<OpCode>) {
        oplist.push(OpCode::Zpull);
        oplist.push(OpCode::Spull);
    }

    fn apply_op(&mut self, op: OpId, data: &mut Funcdata, glb: &mut Architecture) -> Result<i32> {
        let outvn = out_of(data, op);
        let descendants = data.vn(outvn).descend().to_vec();
        for read_op in descendants {
            let res = match data.op(read_op).code() {
                OpCode::IntRight | OpCode::IntSright => self.absorb_right(data, glb, read_op, op)?,
                OpCode::IntLeft => self.absorb_left(data, glb, read_op, op)?,
                OpCode::IntAnd => self.absorb_and(data, glb, read_op, op)?,
                OpCode::IntSless | OpCode::IntLess => self.absorb_compare(data, glb, read_op, None, op)?,
                OpCode::IntZext | OpCode::IntSext => self.absorb_ext(data, glb, read_op, op)?,
                OpCode::Subpiece => self.absorb_subpiece(data, glb, read_op, op)?,
                OpCode::IntEqual | OpCode::IntNotequal => self.absorb_comp_zero(data, glb, read_op, op)?,
                _ => 0,
            };
            if res != 0 {
                return Ok(res);
            }
        }
        Ok(0)
    }
}

pub struct RuleInsertAbsorb {
    base: RuleBase,
}

impl RuleInsertAbsorb {
    pub fn new(group: &str) -> RuleInsertAbsorb {
        RuleInsertAbsorb {
            base: RuleBase::new(group, 0, "insert_absorb"),
        }
    }

    fn left_shift_varnode(vn: VarnodeId, sa: i32, data: &Funcdata) -> Option<VarnodeId> {
        let mult_op = data.vn(vn).get_def()?;
        let mult_val = data.vn(data.op(mult_op).get_in(1));
        if !mult_val.is_constant() {
            return None;
        }
        let match_val: u64 = match data.op(mult_op).code() {
            OpCode::IntMult => 1u64.wrapping_shl(sa as u32),
            OpCode::IntLeft => sa as i64 as u64,
            _ => return None,
        };
        if mult_val.get_offset() != match_val {
            return None;
        }
        Some(data.op(mult_op).get_in(0))
    }

    fn absorb_and(&mut self, data: &mut Funcdata, and_op: OpId, insert_op: OpId) -> Result<i32> {
        let cvn = data.vn(data.op(and_op).get_in(1));
        if !cvn.is_constant() {
            return Ok(0);
        }
        let val = cvn.get_offset();
        let mask = InsertExpression::get_lsb_mask(insert_op, data);
        if (mask & val) != mask {
            return Ok(0);
        }
        let and_in = data.op(and_op).get_in(0);
        data.op_set_input(insert_op, and_in, 1)?;
        data.destroy_varnode_recursive(out_of(data, and_op))?;
        Ok(1)
    }

    fn absorb_right_left(
        &mut self,
        data: &mut Funcdata,
        next_op: OpId,
        right_op: OpId,
        insert_op: OpId,
    ) -> Result<i32> {
        let left_op;
        match data.op(next_op).code() {
            OpCode::IntLeft => left_op = next_op,
            OpCode::Subpiece => {
                if in_offset(data, next_op, 1) != 0 {
                    return Ok(0);
                }
                let subin = data.op(next_op).get_in(0);
                let Some(def_op) = data.vn(subin).get_def() else {
                    return Ok(0);
                };
                left_op = def_op;
                if data.op(left_op).code() != OpCode::IntLeft {
                    return Ok(0);
                }
            }
            _ => return Ok(0),
        }
        let lvn = data.vn(data.op(left_op).get_in(1));
        if !lvn.is_constant() {
            return Ok(0);
        }
        let rvn = data.vn(data.op(right_op).get_in(1));
        if !rvn.is_constant() {
            return Ok(0);
        }
        let lsa = lvn.get_offset() as i32;
        let rsa = rvn.get_offset() as i32;
        if lsa != rsa {
            return Ok(0);
        }
        let bitsize = in_offset(data, insert_op, 3) as i32;
        if bitsize > (data.vn(data.op(insert_op).get_in(1)).get_size() * 8).wrapping_sub(lsa) {
            return Ok(0);
        }
        let left_in = data.op(left_op).get_in(0);
        data.op_set_input(insert_op, left_in, 1)?;
        data.destroy_varnode_recursive(out_of(data, right_op))?;
        Ok(1)
    }

    fn absorb_shift_add(
        &mut self,
        data: &mut Funcdata,
        glb: &mut Architecture,
        right_op: OpId,
        add_op: OpId,
        insert_op: OpId,
    ) -> Result<i32> {
        let sa = in_offset(data, right_op, 1) as i32;
        if sa <= 0 || sa >= UINTB_BITS {
            return Ok(0);
        }
        let Some(vn0) = Self::left_shift_varnode(data.op(add_op).get_in(0), sa, data) else {
            return Ok(0);
        };
        let add_vn1 = data.op(add_op).get_in(1);
        let vn1;
        if data.vn(add_vn1).is_constant() {
            let add_offset = data.vn(add_vn1).get_offset();
            let add_val = add_offset >> sa;
            if (add_val << sa) != add_offset {
                return Ok(0);
            }
            let vn0_size = data.vn(vn0).get_size();
            let add_type = data.vn(add_vn1).get_type();
            vn1 = data.new_constant(vn0_size, add_val, glb);
            data.vn_update_type(vn1, add_type);
        } else {
            let Some(shifted) = Self::left_shift_varnode(add_vn1, sa, data) else {
                return Ok(0);
            };
            vn1 = shifted;
        }
        let bitsize = in_offset(data, insert_op, 3) as i32;
        if bitsize > data.vn(vn0).get_size() * 8 - sa {
            return Ok(0);
        }
        data.op_set_opcode(right_op, OpCode::IntAdd, glb);
        data.op_set_input(right_op, vn0, 0)?;
        data.op_set_input(right_op, vn1, 1)?;
        data.destroy_varnode_recursive(out_of(data, add_op))?;
        Ok(1)
    }

    fn absorb_nested_and(&mut self, data: &mut Funcdata, base_op: OpId, insert_op: OpId) -> Result<i32> {
        if data.vn(out_of(data, base_op)).lone_descend() != Some(insert_op) {
            return Ok(0);
        }
        for slot in 0..2 {
            let vn = data.op(base_op).get_in(slot);
            let Some(and_op) = data.vn(vn).get_def() else {
                continue;
            };
            if data.op(and_op).code() != OpCode::IntAnd {
                continue;
            }
            let cvn = data.vn(data.op(and_op).get_in(1));
            if !cvn.is_constant() {
                continue;
            }
            let mask = coveringmask(cvn.get_offset());
            if mask != cvn.get_offset() {
                continue;
            }
            if (mask & 1) == 0 {
                continue;
            }
            let count = popcount(mask);
            let bitsize = in_offset(data, insert_op, 3) as i32;
            if count < bitsize {
                continue;
            }
            let and_in = data.op(and_op).get_in(0);
            data.op_set_input(base_op, and_in, slot)?;
            data.destroy_varnode_recursive(out_of(data, and_op))?;
            return Ok(1);
        }
        Ok(0)
    }
}

impl Rule for RuleInsertAbsorb {
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
        Some(Box::new(RuleInsertAbsorb::new(self.get_group())))
    }

    fn get_op_list(&self, oplist: &mut Vec<OpCode>) {
        oplist.push(OpCode::Insert);
    }

    fn apply_op(&mut self, op: OpId, data: &mut Funcdata, glb: &mut Architecture) -> Result<i32> {
        let in_vn = data.op(op).get_in(1);
        let Some(in_op) = data.vn(in_vn).get_def() else {
            return Ok(0);
        };
        match data.op(in_op).code() {
            OpCode::Subpiece => {
                if in_offset(data, in_op, 1) != 0 {
                    return Ok(0);
                }
                let sub_in = data.op(in_op).get_in(0);
                data.op_set_input(op, sub_in, 1)?;
                data.destroy_varnode_recursive(in_vn)?;
                Ok(1)
            }
            OpCode::IntRight | OpCode::IntSright => {
                if !data.vn(data.op(in_op).get_in(1)).is_constant() {
                    return Ok(0);
                }
                let vn = data.op(in_op).get_in(0);
                let Some(next_op) = data.vn(vn).get_def() else {
                    return Ok(0);
                };
                let opc = data.op(next_op).code();
                if opc == OpCode::IntAdd {
                    return self.absorb_shift_add(data, glb, in_op, next_op, op);
                } else if opc == OpCode::IntLeft || opc == OpCode::Subpiece {
                    return self.absorb_right_left(data, next_op, in_op, op);
                }
                Ok(0)
            }
            OpCode::IntAnd => self.absorb_and(data, in_op, op),
            OpCode::IntAdd | OpCode::IntOr | OpCode::IntXor | OpCode::IntMult => {
                self.absorb_nested_and(data, in_op, op)
            }
            _ => Ok(0),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::list_sort;

    fn record_less(first: &(i32, usize), second: &(i32, usize)) -> bool {
        if first.0 >= 0 && second.0 >= 0 {
            if first.0 != second.0 {
                return first.0 < second.0;
            }
        } else if first.0 < 0 {
            return true;
        } else if second.0 < 0 {
            return false;
        }
        false
    }

    #[test]
    fn list_sort_matches_libstdcxx() {
        let expected = include_str!("../tests/data/bitfield/listsort_expected.txt");
        let mut lines = expected.lines();
        let mut cases = 0;
        while let Some(case_line) = lines.next() {
            let sorted_line = lines.next().expect("missing sorted line");
            let keys: Vec<i32> = case_line
                .split_whitespace()
                .skip(1)
                .map(|word| word.parse().expect("invalid key"))
                .collect();
            let ids: Vec<usize> = sorted_line
                .split_whitespace()
                .skip(1)
                .map(|word| word.parse().expect("invalid id"))
                .collect();
            let records: Vec<(i32, usize)> = keys.iter().enumerate().map(|(index, &key)| (key, index)).collect();
            let result = list_sort(records, &mut record_less);
            let result_ids: Vec<usize> = result.iter().map(|record| record.1).collect();
            assert_eq!(result_ids, ids, "case {}", cases);
            cases += 1;
        }
        assert_eq!(cases, 200);
    }
}
