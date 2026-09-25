mod arith;
mod division;
mod late;
mod pointer;
mod shiftcompare;
mod simplify;

pub use arith::*;
pub use division::*;
pub use late::*;
pub use pointer::*;
pub use shiftcompare::*;
pub use simplify::*;

use crate::address::{calc_mask, sign_extend, uintb_negate};
use crate::architecture::Architecture;
use crate::error::Result;
use crate::funcdata::Funcdata;
use crate::op::OpId;
use crate::opcodes::OpCode;
use crate::space::AddrSpace;
use crate::typeop::with_type_op;
use crate::types::{TypeFactory, TypeId, TypeMetatype};
use crate::varnode::VarnodeId;

pub(crate) fn types(glb: &Architecture) -> &TypeFactory {
    glb.types.as_deref().expect("type factory is not initialized")
}

pub(crate) fn types_mut(glb: &mut Architecture) -> &mut TypeFactory {
    glb.types.as_deref_mut().expect("type factory is not initialized")
}

pub(crate) fn written_def(data: &Funcdata, vn: VarnodeId) -> Option<OpId> {
    let varnode = data.vn(vn);
    if varnode.is_written() { varnode.get_def() } else { None }
}

pub struct AddTreeState {
    pub base_op: OpId,
    pub ptr: VarnodeId,
    pub ct: TypeId,
    pub base_type: TypeId,
    pub p_rel_type: Option<TypeId>,
    pub ptrsize: i32,
    pub size: i32,
    pub base_slot: i32,
    pub biggest_non_mult_coeff: u32,
    pub ptrmask: u64,
    pub offset: u64,
    pub correct: u64,
    pub multiple: Vec<VarnodeId>,
    pub coeff: Vec<i64>,
    pub nonmult: Vec<VarnodeId>,
    pub distribute_op: Option<OpId>,
    pub multsum: u64,
    pub nonmultsum: u64,
    pub prevent_distribution: bool,
    pub is_distribute_used: bool,
    pub is_subtype: bool,
    pub valid: bool,
    pub is_degenerate: bool,
}

impl AddTreeState {
    pub fn new(data: &mut Funcdata, op: OpId, slot: i32, glb: &mut Architecture) -> AddTreeState {
        let ptr = data.op(op).get_in(slot);
        let ct = data.vn_get_type_read_facing(ptr, op, glb);
        let ptrsize = data.vn(ptr).get_size();
        let ptrmask = calc_mask(ptrsize);
        let factory = types(glb);
        let ct_type = factory.get(ct);
        let mut base_type = ct_type.get_ptr_to();
        let mut nonmultsum: u64 = 0;
        let mut p_rel_type = None;
        if ct_type.is_formal_pointer_rel() {
            p_rel_type = Some(ct);
            base_type = ct_type.get_parent();
            nonmultsum = ct_type.get_address_offset() as i64 as u64;
            nonmultsum &= ptrmask;
        }
        let base = factory.get(base_type);
        let size = if base.is_variable_length() {
            0
        } else {
            AddrSpace::byte_to_address_int(base.get_align_size() as i64, ct_type.get_word_size()) as i32
        };
        let unitsize = AddrSpace::address_to_byte_int(1, ct_type.get_word_size()) as i32;
        let is_degenerate = base.get_align_size() <= unitsize && base.get_align_size() > 0;
        AddTreeState {
            base_op: op,
            ptr,
            ct,
            base_type,
            p_rel_type,
            ptrsize,
            size,
            base_slot: slot,
            biggest_non_mult_coeff: 0,
            ptrmask,
            offset: 0,
            correct: 0,
            multiple: Vec::new(),
            coeff: Vec::new(),
            nonmult: Vec::new(),
            distribute_op: None,
            multsum: 0,
            nonmultsum,
            prevent_distribution: false,
            is_distribute_used: false,
            is_subtype: false,
            valid: true,
            is_degenerate,
        }
    }

    pub fn check_mult_term(
        &mut self,
        vn: VarnodeId,
        op: OpId,
        tree_coeff: u64,
        data: &mut Funcdata,
        glb: &mut Architecture,
    ) -> bool {
        let vnconst = data.op(op).get_in(1);
        let vnterm = data.op(op).get_in(0);
        if data.vn(vnterm).is_free() {
            self.valid = false;
            return false;
        }
        if data.vn(vnconst).is_constant() {
            let val = data.vn(vnconst).get_offset().wrapping_mul(tree_coeff) & self.ptrmask;
            let sval = sign_extend(val as i64, data.vn(vn).get_size() * 8 - 1);
            let rem = if self.size == 0 {
                sval
            } else {
                sval.wrapping_rem(self.size as i64)
            };
            if rem != 0 {
                if val >= self.size as u64 && self.size != 0 {
                    self.valid = false;
                    return false;
                }
                if !self.prevent_distribution
                    && let Some(def) = data.vn(vnterm).get_def()
                    && data.op(def).code() == OpCode::IntAdd
                {
                    if self.distribute_op.is_none() {
                        self.distribute_op = Some(op);
                    }
                    return self.span_add_tree(def, val, data, glb);
                }
                let vncoeff = if sval < 0 {
                    sval.wrapping_neg() as u32
                } else {
                    sval as u32
                };
                if vncoeff > self.biggest_non_mult_coeff {
                    self.biggest_non_mult_coeff = vncoeff;
                }
                return true;
            } else {
                if tree_coeff != 1 {
                    self.is_distribute_used = true;
                }
                self.multiple.push(vnterm);
                self.coeff.push(sval);
                return false;
            }
        }
        if tree_coeff > self.biggest_non_mult_coeff as u64 {
            self.biggest_non_mult_coeff = tree_coeff as u32;
        }
        true
    }

    pub fn check_term(&mut self, vn: VarnodeId, tree_coeff: u64, data: &mut Funcdata, glb: &mut Architecture) -> bool {
        if vn == self.ptr {
            return false;
        }
        if data.vn(vn).is_constant() {
            let val = data.vn(vn).get_offset().wrapping_mul(tree_coeff);
            let sval = sign_extend(val as i64, data.vn(vn).get_size() * 8 - 1);
            let rem = if self.size == 0 {
                sval
            } else {
                sval.wrapping_rem(self.size as i64)
            };
            if rem != 0 {
                if tree_coeff != 1 {
                    let meta = types(glb).get(self.base_type).get_metatype();
                    if meta == TypeMetatype::Array || meta == TypeMetatype::Struct {
                        self.is_distribute_used = true;
                    }
                }
                self.nonmultsum = self.nonmultsum.wrapping_add(val);
                self.nonmultsum &= self.ptrmask;
                return true;
            }
            if tree_coeff != 1 {
                self.is_distribute_used = true;
            }
            self.multsum = self.multsum.wrapping_add(val);
            self.multsum &= self.ptrmask;
            return false;
        }
        if data.vn(vn).is_written() {
            let def = data.vn(vn).get_def().expect("written varnode without defining op");
            match data.op(def).code() {
                OpCode::IntAdd => return self.span_add_tree(def, tree_coeff, data, glb),
                OpCode::Copy => {
                    self.valid = false;
                    return false;
                }
                OpCode::IntMult => return self.check_mult_term(vn, def, tree_coeff, data, glb),
                _ => {}
            }
        } else if data.vn(vn).is_free() {
            self.valid = false;
            return false;
        }
        if tree_coeff > self.biggest_non_mult_coeff as u64 {
            self.biggest_non_mult_coeff = tree_coeff as u32;
        }
        true
    }

    pub fn span_add_tree(&mut self, op: OpId, tree_coeff: u64, data: &mut Funcdata, glb: &mut Architecture) -> bool {
        let one_is_non = self.check_term(data.op(op).get_in(0), tree_coeff, data, glb);
        if !self.valid {
            return false;
        }
        let two_is_non = self.check_term(data.op(op).get_in(1), tree_coeff, data, glb);
        if !self.valid {
            return false;
        }
        if self.p_rel_type.is_some()
            && (self.multsum != 0 || self.nonmultsum >= self.size as u64 || !self.multiple.is_empty())
        {
            self.valid = false;
            return false;
        }
        if one_is_non && two_is_non {
            return true;
        }
        if one_is_non {
            self.nonmult.push(data.op(op).get_in(0));
        }
        if two_is_non {
            self.nonmult.push(data.op(op).get_in(1));
        }
        false
    }

    pub fn calc_subtype(&mut self, glb: &Architecture) {
        let tmpoff = self.multsum.wrapping_add(self.nonmultsum) & self.ptrmask;
        let base_meta = types(glb).get(self.base_type).get_metatype();
        if self.size == 0 || tmpoff < self.size as u64 {
            self.offset = tmpoff;
        } else {
            let mut stmpoff = sign_extend(tmpoff as i64, self.ptrsize * 8 - 1);
            stmpoff = stmpoff.wrapping_rem(self.size as i64);
            if stmpoff >= 0 {
                self.offset = stmpoff as u64;
            } else if base_meta == TypeMetatype::Struct && self.biggest_non_mult_coeff != 0 && self.multsum == 0 {
                self.offset = tmpoff;
            } else {
                self.offset = stmpoff.wrapping_add(self.size as i64) as u64;
            }
        }
        self.correct = self.nonmultsum;
        self.multsum = tmpoff.wrapping_sub(self.offset) & self.ptrmask;
        let wordsize = types(glb).get(self.ct).get_word_size();
        if self.nonmult.is_empty() {
            if self.multsum == 0 && self.multiple.is_empty() {
                self.valid = false;
                return;
            }
            self.is_subtype = false;
        } else if base_meta == TypeMetatype::Spacebase {
            let offsetbytes = AddrSpace::address_to_byte_int(self.offset as i64, wordsize);
            let mut extra: i64 = 0;
            let base = types(glb).get(self.base_type);
            let mut found_symbol = false;
            if self.biggest_non_mult_coeff != 0 {
                found_symbol =
                    base.nearest_arrayed_component(offsetbytes, self.biggest_non_mult_coeff, &mut extra, glb);
            }
            if !found_symbol {
                found_symbol = base.get_sub_type(offsetbytes, &mut extra, glb).is_some();
            }
            if !found_symbol && self.biggest_non_mult_coeff == 0 {
                found_symbol = base.nearest_arrayed_component(offsetbytes, 1, &mut extra, glb);
            }
            if !found_symbol {
                self.valid = false;
                return;
            }
            extra = AddrSpace::byte_to_address(extra as u64, wordsize) as i64;
            self.offset = self.offset.wrapping_sub(extra as u64) & self.ptrmask;
            self.correct = self.correct.wrapping_sub(extra as u64) & self.ptrmask;
            self.is_subtype = true;
        } else if base_meta == TypeMetatype::Struct {
            let soffset = sign_extend(self.offset as i64, self.ptrsize * 8 - 1);
            let offsetbytes = AddrSpace::address_to_byte_int(soffset, wordsize);
            let mut extra: i64 = 0;
            let base = types(glb).get(self.base_type);
            let mut found_field = false;
            if self.biggest_non_mult_coeff != 0 {
                found_field = base.nearest_arrayed_component(offsetbytes, self.biggest_non_mult_coeff, &mut extra, glb);
            }
            if !found_field {
                found_field = base.get_sub_type(offsetbytes, &mut extra, glb).is_some();
            }
            if !found_field {
                if offsetbytes < 0 || offsetbytes >= base.get_size() as i64 {
                    self.valid = false;
                    return;
                }
                extra = 0;
            }
            extra = AddrSpace::byte_to_address_int(extra, wordsize);
            self.offset = self.offset.wrapping_sub(extra as u64) & self.ptrmask;
            self.correct = self.correct.wrapping_sub(extra as u64) & self.ptrmask;
            if let Some(rel) = self.p_rel_type {
                let factory = types(glb);
                let rel_type = factory.get(rel);
                if self.offset == rel_type.get_address_offset() as i64 as u64
                    && !rel_type.evaluate_thru_parent(0, factory)
                {
                    self.valid = false;
                    return;
                }
            }
            self.is_subtype = true;
        } else if base_meta == TypeMetatype::Array {
            self.is_subtype = true;
            self.correct = self.correct.wrapping_sub(self.offset) & self.ptrmask;
            self.offset = 0;
        } else {
            self.valid = false;
        }
        if self.p_rel_type.is_some() {
            let ptr_off = types(glb).get(self.ct).get_address_offset();
            self.offset = self.offset.wrapping_sub(ptr_off as i64 as u64) & self.ptrmask;
            self.correct = self.correct.wrapping_sub(ptr_off as i64 as u64) & self.ptrmask;
        }
    }

    pub fn assign_propagated_type(&mut self, op: OpId, data: &mut Funcdata, glb: &mut Architecture) -> Result<()> {
        let vn = data.op(op).get_in(0);
        let in_type = data.vn_get_type_read_facing(vn, op, glb);
        let outvn = data.op(op).get_out().expect("op without output");
        let opc = data.op(op).code();
        let new_type = with_type_op(glb, opc, |top, glb| {
            top.propagate_type(in_type, op, vn, outvn, 0, -1, data, glb)
        })?;
        if let Some(new_type) = new_type {
            data.vn_update_type(outvn, new_type);
        }
        Ok(())
    }

    pub fn build_multiples(&mut self, data: &mut Funcdata, glb: &mut Architecture) -> Result<Option<VarnodeId>> {
        let smultsum = sign_extend(self.multsum as i64, self.ptrsize * 8 - 1);
        let const_coeff = if self.size == 0 {
            0
        } else {
            (smultsum.wrapping_div(self.size as i64) as u64) & self.ptrmask
        };
        let mut res_node = if const_coeff == 0 {
            None
        } else {
            Some(data.new_constant(self.ptrsize, const_coeff, glb))
        };
        for index in 0..self.multiple.len() {
            let final_coeff = if self.size == 0 {
                0
            } else {
                (self.coeff[index].wrapping_div(self.size as i64) as u64) & self.ptrmask
            };
            let mut vn = self.multiple[index];
            if final_coeff != 1 {
                let constvn = data.new_constant(self.ptrsize, final_coeff, glb);
                let op = data.new_op_before(self.base_op, OpCode::IntMult, vn, constvn, None, glb)?;
                vn = data.op(op).get_out().expect("op without output");
            }
            res_node = match res_node {
                None => Some(vn),
                Some(prev) => {
                    let op = data.new_op_before(self.base_op, OpCode::IntAdd, vn, prev, None, glb)?;
                    data.op(op).get_out()
                }
            };
        }
        Ok(res_node)
    }

    pub fn build_extra(&mut self, data: &mut Funcdata, glb: &mut Architecture) -> Result<Option<VarnodeId>> {
        let mut res_node: Option<VarnodeId> = None;
        for index in 0..self.nonmult.len() {
            let vn = self.nonmult[index];
            if data.vn(vn).is_constant() {
                self.correct = self.correct.wrapping_sub(data.vn(vn).get_offset());
                continue;
            }
            res_node = match res_node {
                None => Some(vn),
                Some(prev) => {
                    let op = data.new_op_before(self.base_op, OpCode::IntAdd, vn, prev, None, glb)?;
                    data.op(op).get_out()
                }
            };
        }
        self.correct &= self.ptrmask;
        if self.correct != 0 {
            let vn = data.new_constant(
                self.ptrsize,
                uintb_negate(self.correct.wrapping_sub(1), self.ptrsize),
                glb,
            );
            res_node = match res_node {
                None => Some(vn),
                Some(prev) => {
                    let op = data.new_op_before(self.base_op, OpCode::IntAdd, vn, prev, None, glb)?;
                    data.op(op).get_out()
                }
            };
        }
        Ok(res_node)
    }

    pub fn build_degenerate(&mut self, data: &mut Funcdata, glb: &mut Architecture) -> Result<bool> {
        let factory = types(glb);
        let ct_type = factory.get(self.ct);
        if (factory.get(self.base_type).get_align_size() as i64) < ct_type.get_word_size() as i64 {
            return Ok(false);
        }
        let ct_size = ct_type.get_size();
        let outvn = data.op(self.base_op).get_out().expect("op without output");
        let out_type = data.vn_get_type_def_facing(outvn, glb);
        if types(glb).get(out_type).get_metatype() != TypeMetatype::Ptr {
            return Ok(false);
        }
        let slot = data.op(self.base_op).get_slot(self.ptr);
        let other = data.op(self.base_op).get_in(1 - slot);
        let constvn = data.new_constant(ct_size, 1, glb);
        let newparams = vec![self.ptr, other, constvn];
        data.op_set_all_input(self.base_op, &newparams)?;
        data.op_set_opcode(self.base_op, OpCode::Ptradd, glb);
        Ok(true)
    }

    pub fn build_tree(&mut self, data: &mut Funcdata, glb: &mut Architecture) -> Result<()> {
        let mult_result = self.build_multiples(data, glb)?;
        let extra_node = self.build_extra(data, glb)?;
        let mut newop: Option<OpId> = None;
        let mut mult_node = match mult_result {
            Some(mult_result) => {
                let sizevn = data.new_constant(self.ptrsize, self.size as i64 as u64, glb);
                let created =
                    data.new_op_before(self.base_op, OpCode::Ptradd, self.ptr, mult_result, Some(sizevn), glb)?;
                newop = Some(created);
                let ptr_type = data.vn(self.ptr).get_type();
                if types(glb).get(ptr_type).needs_resolution() {
                    let factory = types(glb);
                    let pointed = factory.get(ptr_type).get_ptr_to();
                    if factory.get(pointed).get_size() == factory.get(self.base_type).get_size() {
                        data.force_facing_type(ptr_type, -1, created, 0, glb);
                    } else {
                        data.inherit_union_field(ptr_type, created, 0, self.base_op, self.base_slot, glb);
                    }
                }
                if data.is_type_recovery_exceeded() {
                    self.assign_propagated_type(created, data, glb)?;
                }
                data.op(created).get_out().expect("op without output")
            }
            None => self.ptr,
        };
        if self.is_subtype {
            let offvn = data.new_constant(self.ptrsize, self.offset, glb);
            let created = data.new_op_before(self.base_op, OpCode::Ptrsub, mult_node, offvn, None, glb)?;
            newop = Some(created);
            let mult_type = data.vn(mult_node).get_type();
            if types(glb).get(mult_type).needs_resolution() {
                data.inherit_union_field(mult_type, created, 0, self.base_op, self.base_slot, glb);
            }
            if data.is_type_recovery_exceeded() {
                self.assign_propagated_type(created, data, glb)?;
            }
            if self.size != 0 {
                data.op_mut(created).set_stop_type_propagation();
            }
            mult_node = data.op(created).get_out().expect("op without output");
        }
        if let Some(extra_node) = extra_node {
            newop = Some(data.new_op_before(self.base_op, OpCode::IntAdd, mult_node, extra_node, None, glb)?);
        }
        let newop = match newop {
            Some(newop) => newop,
            None => {
                let addr = data.op(self.base_op).get_addr().clone();
                data.warning("ptrarith problems", &addr, glb);
                return Ok(());
            }
        };
        let outvn = data.op(self.base_op).get_out().expect("op without output");
        data.op_set_output(newop, outvn, glb)?;
        data.op_destroy(self.base_op)?;
        Ok(())
    }

    pub fn clear(&mut self, glb: &Architecture) {
        self.multsum = 0;
        self.nonmultsum = 0;
        self.biggest_non_mult_coeff = 0;
        if self.p_rel_type.is_some() {
            self.nonmultsum = types(glb).get(self.ct).get_address_offset() as i64 as u64;
            self.nonmultsum &= self.ptrmask;
        }
        self.multiple.clear();
        self.coeff.clear();
        self.nonmult.clear();
        self.correct = 0;
        self.offset = 0;
        self.valid = true;
        self.is_distribute_used = false;
        self.is_subtype = false;
        self.distribute_op = None;
    }

    pub fn apply(&mut self, data: &mut Funcdata, glb: &mut Architecture) -> Result<bool> {
        if self.is_degenerate {
            return self.build_degenerate(data, glb);
        }
        self.span_add_tree(self.base_op, 1, data, glb);
        if !self.valid {
            return Ok(false);
        }
        if self.distribute_op.is_some() && !self.is_distribute_used {
            self.clear(glb);
            self.prevent_distribution = true;
            self.span_add_tree(self.base_op, 1, data, glb);
        }
        self.calc_subtype(glb);
        if !self.valid {
            return Ok(false);
        }
        while self.valid {
            let distribute_op = match self.distribute_op {
                Some(distribute_op) => distribute_op,
                None => break,
            };
            if !data.distribute_int_mult_add(distribute_op, glb)? {
                self.valid = false;
                break;
            }
            let first = data.op(distribute_op).get_in(0);
            data.collapse_int_mult_mult(first, glb)?;
            let second = data.op(distribute_op).get_in(1);
            data.collapse_int_mult_mult(second, glb)?;
            self.clear(glb);
            self.span_add_tree(self.base_op, 1, data, glb);
            if self.distribute_op.is_some() && !self.is_distribute_used {
                self.clear(glb);
                self.prevent_distribution = true;
                self.span_add_tree(self.base_op, 1, data, glb);
            }
            self.calc_subtype(glb);
        }
        if !self.valid {
            let mut message = String::from("Problems distributing in pointer arithmetic at ");
            data.op(self.base_op).get_addr().print_raw(&mut message);
            data.warning_header(&message, glb);
            return Ok(true);
        }
        self.build_tree(data, glb)?;
        Ok(true)
    }

    pub fn init_alternate_form(&mut self, glb: &Architecture) -> bool {
        if self.p_rel_type.is_none() {
            return false;
        }
        self.p_rel_type = None;
        let factory = types(glb);
        let ct_type = factory.get(self.ct);
        self.base_type = ct_type.get_ptr_to();
        let base = factory.get(self.base_type);
        self.size = if base.is_variable_length() {
            0
        } else {
            AddrSpace::byte_to_address_int(base.get_align_size() as i64, ct_type.get_word_size()) as i32
        };
        let unitsize = AddrSpace::address_to_byte_int(1, ct_type.get_word_size()) as i32;
        self.is_degenerate = base.get_align_size() <= unitsize && base.get_align_size() > 0;
        self.prevent_distribution = false;
        self.clear(glb);
        true
    }
}
