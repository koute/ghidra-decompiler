use crate::address::{mostsigbit_set, signbit_negative, uintb_negate};
use crate::architecture::Architecture;
use crate::error::Result;
use crate::funcdata::Funcdata;
use crate::op::OpId;
use crate::opcodes::OpCode;
use crate::types::{TypeFactory, TypeId, TypeMetatype, types_of, types_of_mut};
use crate::varnode::VarnodeId;

pub const NO_PROMOTION: i32 = -1;
pub const UNKNOWN_PROMOTION: i32 = 0;
pub const UNSIGNED_EXTENSION: i32 = 1;
pub const SIGNED_EXTENSION: i32 = 2;
pub const EITHER_EXTENSION: i32 = 3;

#[derive(Clone, Debug, Default)]
pub struct CastStrategyBase {
    pub promote_size: i32,
}

pub trait CastStrategy: Send {
    fn base(&self) -> &CastStrategyBase;

    fn base_mut(&mut self) -> &mut CastStrategyBase;

    fn set_type_factory(&mut self, types: &TypeFactory) {
        self.base_mut().promote_size = types.get_size_of_int();
    }

    fn local_extension_type(&self, vn: VarnodeId, op: OpId, data: &mut Funcdata, glb: &Architecture) -> Result<i32>;

    fn int_promotion_type(&self, vn: VarnodeId, data: &mut Funcdata, glb: &Architecture) -> Result<i32>;

    fn check_int_promotion_for_compare(
        &self,
        op: OpId,
        slot: i32,
        data: &mut Funcdata,
        glb: &Architecture,
    ) -> Result<bool>;

    fn check_int_promotion_for_extension(&self, op: OpId, data: &mut Funcdata, glb: &Architecture) -> Result<bool>;

    fn is_extension_cast_implied(
        &self,
        op: OpId,
        read_op: Option<OpId>,
        data: &mut Funcdata,
        glb: &Architecture,
    ) -> Result<bool>;

    fn cast_standard(
        &self,
        reqtype: TypeId,
        curtype: TypeId,
        care_uint_int: bool,
        care_ptr_uint: bool,
        types: &TypeFactory,
    ) -> Option<TypeId>;

    fn arithmetic_output_standard(&mut self, op: OpId, data: &mut Funcdata, glb: &mut Architecture) -> Result<TypeId>;

    fn is_subpiece_cast(&self, outtype: TypeId, intype: TypeId, offset: u32, types: &TypeFactory) -> bool;

    fn is_subpiece_cast_endian(
        &self,
        outtype: TypeId,
        intype: TypeId,
        offset: u32,
        isbigend: bool,
        types: &TypeFactory,
    ) -> bool;

    fn is_sext_cast(&self, outtype: TypeId, intype: TypeId, types: &TypeFactory) -> bool;

    fn is_zext_cast(&self, outtype: TypeId, intype: TypeId, types: &TypeFactory) -> bool;

    fn mark_explicit_unsigned(&self, op: OpId, slot: i32, data: &mut Funcdata, glb: &Architecture) -> Result<bool> {
        let opcode = data.op(op).get_opcode(glb);
        if !opcode.inherits_sign() {
            return Ok(false);
        }
        let inherits_first_param_only = opcode.inherits_sign_first_param_only();
        if slot == 1 && inherits_first_param_only {
            return Ok(false);
        }
        let vn = data.op(op).get_in(slot);
        if !data.vn(vn).is_constant() {
            return Ok(false);
        }
        let dt = data.vn_get_high_type_read_facing(vn, op, glb)?;
        let types = types_of(glb);
        let dt_data = types.get(dt);
        let meta = dt_data.get_metatype();
        if meta != TypeMetatype::Uint
            && meta != TypeMetatype::Unknown
            && meta != TypeMetatype::PartialStruct
            && meta != TypeMetatype::PartialUnion
        {
            return Ok(false);
        }
        if dt_data.is_char_print() {
            return Ok(false);
        }
        if dt_data.is_enum_type() {
            return Ok(false);
        }
        if data.op(op).num_input() == 2 && !inherits_first_param_only {
            let firstvn = data.op(op).get_in(1 - slot);
            let first_type = data.vn_get_high_type_read_facing(firstvn, op, glb)?;
            let meta = types.get(first_type).get_metatype();
            if meta == TypeMetatype::Uint
                || meta == TypeMetatype::Unknown
                || meta == TypeMetatype::PartialStruct
                || meta == TypeMetatype::PartialUnion
            {
                return Ok(false);
            }
        }
        if let Some(outvn) = data.op(op).get_out() {
            let out_data = data.vn(outvn);
            if out_data.is_explicit() {
                return Ok(false);
            }
            if let Some(lone) = out_data.lone_descend()
                && !data.op(lone).get_opcode(glb).inherits_sign()
            {
                return Ok(false);
            }
        }
        data.vn_mut(vn).set_unsigned_print();
        Ok(true)
    }

    fn mark_explicit_long_size(&self, op: OpId, slot: i32, data: &mut Funcdata, glb: &Architecture) -> Result<bool> {
        if !data.op(op).get_opcode(glb).is_shift_op() {
            return Ok(false);
        }
        if slot != 0 {
            return Ok(false);
        }
        let vn = data.op(op).get_in(slot);
        if !data.vn(vn).is_constant() {
            return Ok(false);
        }
        let promote_size = self.base().promote_size;
        if data.vn(vn).get_size() <= promote_size {
            return Ok(false);
        }
        let high = data.vn(vn).get_high()?;
        let dt = data.high_get_type(high, glb);
        let meta = types_of(glb).get(dt).get_metatype();
        if meta != TypeMetatype::Uint
            && meta != TypeMetatype::Int
            && meta != TypeMetatype::Unknown
            && meta != TypeMetatype::PartialStruct
            && meta != TypeMetatype::PartialUnion
        {
            return Ok(false);
        }
        let mut off = data.vn(vn).get_offset();
        let size = data.vn(vn).get_size();
        if meta == TypeMetatype::Int && signbit_negative(off, size) {
            off = uintb_negate(off, size);
            let bit = mostsigbit_set(off);
            if bit >= promote_size * 8 - 1 {
                return Ok(false);
            }
        } else {
            let bit = mostsigbit_set(off);
            if bit >= promote_size * 8 {
                return Ok(false);
            }
        }
        data.vn_mut(vn).set_long_print();
        Ok(true)
    }

    fn cares_about_char_representation(&self, _vn: VarnodeId, _op: Option<OpId>) -> bool {
        false
    }
}

fn integer_like(meta: TypeMetatype) -> bool {
    meta == TypeMetatype::Unknown
        || meta == TypeMetatype::Int
        || meta == TypeMetatype::Uint
        || meta == TypeMetatype::Bool
        || meta == TypeMetatype::PartialStruct
        || meta == TypeMetatype::PartialUnion
}

fn unknown_like(meta: TypeMetatype) -> bool {
    meta == TypeMetatype::Unknown || meta == TypeMetatype::PartialStruct || meta == TypeMetatype::PartialUnion
}

fn code_without_prototype(reqbase: TypeId, curbase: TypeId, types: &TypeFactory) -> bool {
    if types.get(curbase).get_metatype() == TypeMetatype::Code {
        if types.get(reqbase).get_prototype().is_none() {
            return true;
        }
        if types.get(curbase).get_prototype().is_none() {
            return true;
        }
    }
    false
}

#[derive(Clone, Debug, Default)]
pub struct CastStrategyC {
    pub base: CastStrategyBase,
}

impl CastStrategyC {
    pub fn new() -> CastStrategyC {
        CastStrategyC::default()
    }
}

impl CastStrategyC {
    fn high_type_read_facing_option(
        vn: VarnodeId,
        op: Option<OpId>,
        data: &mut Funcdata,
        glb: &Architecture,
    ) -> Result<TypeId> {
        match op {
            Some(op) => data.vn_get_high_type_read_facing(vn, op, glb),
            None => {
                let high = data.vn(vn).get_high()?;
                Ok(data.high_get_type(high, glb))
            }
        }
    }

    fn local_extension_type_option(
        &self,
        vn: VarnodeId,
        op: Option<OpId>,
        data: &mut Funcdata,
        glb: &Architecture,
    ) -> Result<i32> {
        let high_type = CastStrategyC::high_type_read_facing_option(vn, op, data, glb)?;
        let meta = types_of(glb).get(high_type).get_metatype();
        let natural;
        if meta == TypeMetatype::Uint
            || meta == TypeMetatype::Bool
            || meta == TypeMetatype::Unknown
            || meta == TypeMetatype::PartialStruct
            || meta == TypeMetatype::PartialUnion
        {
            natural = UNSIGNED_EXTENSION;
        } else if meta == TypeMetatype::Int {
            natural = SIGNED_EXTENSION;
        } else {
            return Ok(UNKNOWN_PROMOTION);
        }
        let vn_data = data.vn(vn);
        if vn_data.is_constant() {
            if !signbit_negative(vn_data.get_offset(), vn_data.get_size()) {
                return Ok(EITHER_EXTENSION);
            }
            return Ok(natural);
        }
        if vn_data.is_explicit() {
            return Ok(natural);
        }
        if !vn_data.is_written() {
            return Ok(UNKNOWN_PROMOTION);
        }
        let def_op = data.op(vn_data.get_def().expect("written varnode without definition"));
        if def_op.is_bool_output() {
            return Ok(EITHER_EXTENSION);
        }
        let opc = def_op.code();
        if opc == OpCode::Cast || opc == OpCode::Load || def_op.is_call() {
            return Ok(natural);
        }
        if opc == OpCode::IntAnd {
            let tmpvn = data.vn(def_op.get_in(1));
            if tmpvn.is_constant() {
                if !signbit_negative(tmpvn.get_offset(), tmpvn.get_size()) {
                    return Ok(EITHER_EXTENSION);
                }
                return Ok(natural);
            }
        }
        Ok(UNKNOWN_PROMOTION)
    }

    fn int_promotion_type_impl(&self, vn: VarnodeId, data: &mut Funcdata, glb: &Architecture) -> Result<i32> {
        let vn_data = data.vn(vn);
        if vn_data.get_size() >= self.base.promote_size {
            return Ok(NO_PROMOTION);
        }
        if vn_data.is_constant() {
            let lone = vn_data.lone_descend();
            return self.local_extension_type_option(vn, lone, data, glb);
        }
        if vn_data.is_explicit() {
            return Ok(NO_PROMOTION);
        }
        if !vn_data.is_written() {
            return Ok(UNKNOWN_PROMOTION);
        }
        let op = vn_data.get_def().expect("written varnode without definition");
        let op_data = data.op(op);
        let in0 = op_data.get_in_option(0);
        let in1 = op_data.get_in_option(1);
        match op_data.code() {
            OpCode::IntAnd => {
                let othervn = in1.expect("missing p-code op input");
                if (self.local_extension_type(othervn, op, data, glb)? & UNSIGNED_EXTENSION) != 0 {
                    return Ok(UNSIGNED_EXTENSION);
                }
                let othervn = in0.expect("missing p-code op input");
                if (self.local_extension_type(othervn, op, data, glb)? & UNSIGNED_EXTENSION) != 0 {
                    return Ok(UNSIGNED_EXTENSION);
                }
            }
            OpCode::IntRight => {
                let othervn = in0.expect("missing p-code op input");
                let val = self.local_extension_type(othervn, op, data, glb)?;
                if (val & UNSIGNED_EXTENSION) != 0 {
                    return Ok(val);
                }
            }
            OpCode::IntSright => {
                let othervn = in0.expect("missing p-code op input");
                let val = self.local_extension_type(othervn, op, data, glb)?;
                if (val & SIGNED_EXTENSION) != 0 {
                    return Ok(val);
                }
            }
            OpCode::IntXor | OpCode::IntOr | OpCode::IntDiv | OpCode::IntRem => {
                let othervn = in0.expect("missing p-code op input");
                if (self.local_extension_type(othervn, op, data, glb)? & UNSIGNED_EXTENSION) == 0 {
                    return Ok(UNKNOWN_PROMOTION);
                }
                let othervn = in1.expect("missing p-code op input");
                if (self.local_extension_type(othervn, op, data, glb)? & UNSIGNED_EXTENSION) == 0 {
                    return Ok(UNKNOWN_PROMOTION);
                }
                return Ok(UNSIGNED_EXTENSION);
            }
            OpCode::IntSdiv | OpCode::IntSrem => {
                let othervn = in0.expect("missing p-code op input");
                if (self.local_extension_type(othervn, op, data, glb)? & SIGNED_EXTENSION) == 0 {
                    return Ok(UNKNOWN_PROMOTION);
                }
                let othervn = in1.expect("missing p-code op input");
                if (self.local_extension_type(othervn, op, data, glb)? & SIGNED_EXTENSION) == 0 {
                    return Ok(UNKNOWN_PROMOTION);
                }
                return Ok(SIGNED_EXTENSION);
            }
            OpCode::IntNegate | OpCode::Int2comp => {
                let othervn = in0.expect("missing p-code op input");
                if (self.local_extension_type(othervn, op, data, glb)? & SIGNED_EXTENSION) != 0 {
                    return Ok(SIGNED_EXTENSION);
                }
            }
            OpCode::IntAdd | OpCode::IntSub | OpCode::IntLeft | OpCode::IntMult => {}
            _ => return Ok(NO_PROMOTION),
        }
        Ok(UNKNOWN_PROMOTION)
    }
}

impl CastStrategy for CastStrategyC {
    fn base(&self) -> &CastStrategyBase {
        &self.base
    }

    fn base_mut(&mut self) -> &mut CastStrategyBase {
        &mut self.base
    }

    fn local_extension_type(&self, vn: VarnodeId, op: OpId, data: &mut Funcdata, glb: &Architecture) -> Result<i32> {
        self.local_extension_type_option(vn, Some(op), data, glb)
    }

    fn int_promotion_type(&self, vn: VarnodeId, data: &mut Funcdata, glb: &Architecture) -> Result<i32> {
        self.int_promotion_type_impl(vn, data, glb)
    }

    fn check_int_promotion_for_compare(
        &self,
        op: OpId,
        slot: i32,
        data: &mut Funcdata,
        glb: &Architecture,
    ) -> Result<bool> {
        let vn = data.op(op).get_in(slot);
        let exttype1 = self.int_promotion_type(vn, data, glb)?;
        if exttype1 == NO_PROMOTION {
            return Ok(false);
        }
        if exttype1 == UNKNOWN_PROMOTION {
            return Ok(true);
        }
        let othervn = data.op(op).get_in(1 - slot);
        let exttype2 = self.int_promotion_type(othervn, data, glb)?;
        if (exttype1 & exttype2) != 0 {
            return Ok(false);
        }
        if exttype2 == NO_PROMOTION {
            return Ok(false);
        }
        Ok(true)
    }

    fn check_int_promotion_for_extension(&self, op: OpId, data: &mut Funcdata, glb: &Architecture) -> Result<bool> {
        let vn = data.op(op).get_in(0);
        let exttype = self.int_promotion_type(vn, data, glb)?;
        if exttype == NO_PROMOTION {
            return Ok(false);
        }
        if exttype == UNKNOWN_PROMOTION {
            return Ok(true);
        }
        let opc = data.op(op).code();
        if (exttype & UNSIGNED_EXTENSION) != 0 && opc == OpCode::IntZext {
            return Ok(false);
        }
        if (exttype & SIGNED_EXTENSION) != 0 && opc == OpCode::IntSext {
            return Ok(false);
        }
        Ok(true)
    }

    fn is_extension_cast_implied(
        &self,
        op: OpId,
        read_op: Option<OpId>,
        data: &mut Funcdata,
        glb: &Architecture,
    ) -> Result<bool> {
        let out_vn = data.op(op).get_out().expect("extension without output");
        if data.vn(out_vn).is_explicit() {
            return Ok(false);
        }
        let Some(read_op) = read_op else {
            return Ok(false);
        };
        let out_type = data.vn_get_high_type_read_facing(out_vn, read_op, glb)?;
        let metatype = types_of(glb).get(out_type).get_metatype();
        match data.op(read_op).code() {
            OpCode::Ptradd => {}
            OpCode::IntAdd
            | OpCode::IntSub
            | OpCode::IntMult
            | OpCode::IntDiv
            | OpCode::IntAnd
            | OpCode::IntOr
            | OpCode::IntXor
            | OpCode::IntEqual
            | OpCode::IntNotequal
            | OpCode::IntLess
            | OpCode::IntLessequal
            | OpCode::IntSless
            | OpCode::IntSlessequal => {
                let slot = data.op(read_op).get_slot(out_vn);
                let other_vn = data.op(read_op).get_in(1 - slot);
                let other_data = data.vn(other_vn);
                if other_data.is_constant() {
                    if other_data.get_size() > self.base.promote_size {
                        return Ok(false);
                    }
                } else if !other_data.is_explicit() {
                    return Ok(false);
                }
                let other_type = data.vn_get_high_type_read_facing(other_vn, read_op, glb)?;
                if types_of(glb).get(other_type).get_metatype() != metatype {
                    return Ok(false);
                }
            }
            _ => return Ok(false),
        }
        Ok(true)
    }

    fn cast_standard(
        &self,
        reqtype: TypeId,
        curtype: TypeId,
        care_uint_int: bool,
        care_ptr_uint: bool,
        types: &TypeFactory,
    ) -> Option<TypeId> {
        if curtype == reqtype {
            return None;
        }
        if types.get(curtype).get_metatype() == TypeMetatype::Void {
            return Some(reqtype);
        }
        let mut care_uint_int = care_uint_int;
        let mut reqbase = reqtype;
        let mut curbase = curtype;
        let mut isptr = false;
        while types.get(reqbase).get_metatype() == TypeMetatype::Ptr
            && types.get(curbase).get_metatype() == TypeMetatype::Ptr
        {
            let reqptr = types.get(reqbase);
            let curptr = types.get(curbase);
            if reqptr.get_word_size() != curptr.get_word_size() {
                return Some(reqtype);
            }
            let reqspace = reqptr.get_space().map(|spc| spc.get_index());
            let curspace = curptr.get_space().map(|spc| spc.get_index());
            if reqspace != curspace && reqspace.is_some() && curspace.is_some() {
                return Some(reqtype);
            }
            reqbase = reqptr.get_ptr_to();
            curbase = curptr.get_ptr_to();
            care_uint_int = true;
            isptr = true;
        }
        while let Some(typedef_imm) = types.get(reqbase).get_typedef() {
            reqbase = typedef_imm;
        }
        while let Some(typedef_imm) = types.get(curbase).get_typedef() {
            curbase = typedef_imm;
        }
        if curbase == reqbase {
            return None;
        }
        let req_dt = types.get(reqbase);
        let cur_dt = types.get(curbase);
        if req_dt.get_metatype() == TypeMetatype::Void || cur_dt.get_metatype() == TypeMetatype::Void {
            return None;
        }
        if req_dt.get_size() != cur_dt.get_size() {
            if req_dt.is_variable_length() && isptr && req_dt.has_same_variable_base(cur_dt) {
                return None;
            }
            return Some(reqtype);
        }
        match req_dt.get_metatype() {
            TypeMetatype::Unknown | TypeMetatype::PartialStruct | TypeMetatype::PartialUnion => return None,
            TypeMetatype::Uint => {
                let meta = cur_dt.get_metatype();
                if !care_uint_int {
                    if integer_like(meta) {
                        return None;
                    }
                } else {
                    if meta == TypeMetatype::Uint || meta == TypeMetatype::Bool {
                        return None;
                    }
                    if isptr && unknown_like(meta) {
                        return None;
                    }
                }
                if !care_ptr_uint && meta == TypeMetatype::Ptr {
                    return None;
                }
            }
            TypeMetatype::Int => {
                let meta = cur_dt.get_metatype();
                if !care_uint_int {
                    if integer_like(meta) {
                        return None;
                    }
                } else {
                    if meta == TypeMetatype::Int || meta == TypeMetatype::Bool {
                        return None;
                    }
                    if isptr && unknown_like(meta) {
                        return None;
                    }
                }
            }
            TypeMetatype::Code if code_without_prototype(reqbase, curbase, types) => {
                return None;
            }
            _ => {}
        }
        Some(reqtype)
    }

    fn arithmetic_output_standard(&mut self, op: OpId, data: &mut Funcdata, glb: &mut Architecture) -> Result<TypeId> {
        let in0 = data.op(op).get_in(0);
        let mut res1 = data.vn_get_high_type_read_facing(in0, op, glb)?;
        if types_of(glb).get(res1).get_metatype() == TypeMetatype::Bool {
            let size = types_of(glb).get(res1).get_size();
            res1 = types_of_mut(glb).get_base(size, TypeMetatype::Int)?;
        }
        let num_input = data.op(op).num_input();
        for index in 1..num_input {
            let input = data.op(op).get_in(index);
            let res2 = data.vn_get_high_type_read_facing(input, op, glb)?;
            let types = types_of(glb);
            if types.get(res2).get_metatype() == TypeMetatype::Bool {
                continue;
            }
            if 0 > types.get(res2).type_order(types.get(res1), types) {
                res1 = res2;
            }
        }
        Ok(res1)
    }

    fn is_subpiece_cast(&self, outtype: TypeId, intype: TypeId, offset: u32, types: &TypeFactory) -> bool {
        if offset != 0 {
            return false;
        }
        let inmeta = types.get(intype).get_metatype();
        if inmeta != TypeMetatype::Int
            && inmeta != TypeMetatype::Uint
            && inmeta != TypeMetatype::Unknown
            && inmeta != TypeMetatype::Ptr
            && inmeta != TypeMetatype::PartialStruct
            && inmeta != TypeMetatype::PartialUnion
        {
            return false;
        }
        let outmeta = types.get(outtype).get_metatype();
        if outmeta != TypeMetatype::Int
            && outmeta != TypeMetatype::Uint
            && outmeta != TypeMetatype::Unknown
            && outmeta != TypeMetatype::Ptr
            && outmeta != TypeMetatype::Float
        {
            return false;
        }
        if inmeta == TypeMetatype::Ptr {
            if outmeta == TypeMetatype::Ptr && types.get(outtype).get_size() < types.get(intype).get_size() {
                return true;
            }
            if outmeta != TypeMetatype::Int && outmeta != TypeMetatype::Uint {
                return false;
            }
        }
        true
    }

    fn is_subpiece_cast_endian(
        &self,
        outtype: TypeId,
        intype: TypeId,
        offset: u32,
        isbigend: bool,
        types: &TypeFactory,
    ) -> bool {
        let mut tmpoff = offset;
        if isbigend {
            tmpoff = (types.get(intype).get_size() as u32)
                .wrapping_sub(1)
                .wrapping_sub(offset);
        }
        self.is_subpiece_cast(outtype, intype, tmpoff, types)
    }

    fn is_sext_cast(&self, outtype: TypeId, intype: TypeId, types: &TypeFactory) -> bool {
        let metaout = types.get(outtype).get_metatype();
        if metaout != TypeMetatype::Uint && metaout != TypeMetatype::Int {
            return false;
        }
        let metain = types.get(intype).get_metatype();
        if metain != TypeMetatype::Int && metain != TypeMetatype::Bool {
            return false;
        }
        true
    }

    fn is_zext_cast(&self, outtype: TypeId, intype: TypeId, types: &TypeFactory) -> bool {
        let metaout = types.get(outtype).get_metatype();
        if metaout != TypeMetatype::Uint && metaout != TypeMetatype::Int {
            return false;
        }
        let metain = types.get(intype).get_metatype();
        if metain != TypeMetatype::Uint && metain != TypeMetatype::Bool {
            return false;
        }
        true
    }
}

#[derive(Clone, Debug, Default)]
pub struct CastStrategyJava {
    pub parent: CastStrategyC,
}

impl CastStrategyJava {
    pub fn new() -> CastStrategyJava {
        CastStrategyJava::default()
    }
}

impl CastStrategy for CastStrategyJava {
    fn base(&self) -> &CastStrategyBase {
        &self.parent.base
    }

    fn base_mut(&mut self) -> &mut CastStrategyBase {
        &mut self.parent.base
    }

    fn local_extension_type(&self, vn: VarnodeId, op: OpId, data: &mut Funcdata, glb: &Architecture) -> Result<i32> {
        self.parent.local_extension_type(vn, op, data, glb)
    }

    fn int_promotion_type(&self, vn: VarnodeId, data: &mut Funcdata, glb: &Architecture) -> Result<i32> {
        self.parent.int_promotion_type(vn, data, glb)
    }

    fn check_int_promotion_for_compare(
        &self,
        op: OpId,
        slot: i32,
        data: &mut Funcdata,
        glb: &Architecture,
    ) -> Result<bool> {
        self.parent.check_int_promotion_for_compare(op, slot, data, glb)
    }

    fn check_int_promotion_for_extension(&self, op: OpId, data: &mut Funcdata, glb: &Architecture) -> Result<bool> {
        self.parent.check_int_promotion_for_extension(op, data, glb)
    }

    fn is_extension_cast_implied(
        &self,
        op: OpId,
        read_op: Option<OpId>,
        data: &mut Funcdata,
        glb: &Architecture,
    ) -> Result<bool> {
        self.parent.is_extension_cast_implied(op, read_op, data, glb)
    }

    fn cast_standard(
        &self,
        reqtype: TypeId,
        curtype: TypeId,
        care_uint_int: bool,
        _care_ptr_uint: bool,
        types: &TypeFactory,
    ) -> Option<TypeId> {
        if curtype == reqtype {
            return None;
        }
        let reqbase = reqtype;
        let curbase = curtype;
        let req_dt = types.get(reqbase);
        let cur_dt = types.get(curbase);
        if req_dt.get_metatype() == TypeMetatype::Ptr || cur_dt.get_metatype() == TypeMetatype::Ptr {
            return None;
        }
        if req_dt.get_metatype() == TypeMetatype::Void || types.get(curtype).get_metatype() == TypeMetatype::Void {
            return None;
        }
        if req_dt.get_size() != cur_dt.get_size() {
            return Some(reqtype);
        }
        match req_dt.get_metatype() {
            TypeMetatype::Unknown | TypeMetatype::PartialStruct | TypeMetatype::PartialUnion => return None,
            TypeMetatype::Uint => {
                let meta = cur_dt.get_metatype();
                if !care_uint_int {
                    if integer_like(meta) {
                        return None;
                    }
                } else if meta == TypeMetatype::Uint || meta == TypeMetatype::Bool {
                    return None;
                }
            }
            TypeMetatype::Int => {
                let meta = cur_dt.get_metatype();
                if !care_uint_int {
                    if integer_like(meta) {
                        return None;
                    }
                } else if meta == TypeMetatype::Int || meta == TypeMetatype::Bool {
                    return None;
                }
            }
            TypeMetatype::Code if code_without_prototype(reqbase, curbase, types) => {
                return None;
            }
            _ => {}
        }
        Some(reqtype)
    }

    fn arithmetic_output_standard(&mut self, op: OpId, data: &mut Funcdata, glb: &mut Architecture) -> Result<TypeId> {
        self.parent.arithmetic_output_standard(op, data, glb)
    }

    fn is_subpiece_cast(&self, outtype: TypeId, intype: TypeId, offset: u32, types: &TypeFactory) -> bool {
        self.parent.is_subpiece_cast(outtype, intype, offset, types)
    }

    fn is_subpiece_cast_endian(
        &self,
        outtype: TypeId,
        intype: TypeId,
        offset: u32,
        isbigend: bool,
        types: &TypeFactory,
    ) -> bool {
        self.parent
            .is_subpiece_cast_endian(outtype, intype, offset, isbigend, types)
    }

    fn is_sext_cast(&self, outtype: TypeId, intype: TypeId, types: &TypeFactory) -> bool {
        self.parent.is_sext_cast(outtype, intype, types)
    }

    fn is_zext_cast(&self, outtype: TypeId, intype: TypeId, types: &TypeFactory) -> bool {
        let outmeta = types.get(outtype).get_metatype();
        if outmeta != TypeMetatype::Int && outmeta != TypeMetatype::Uint && outmeta != TypeMetatype::Bool {
            return false;
        }
        let in_dt = types.get(intype);
        let inmeta = in_dt.get_metatype();
        if inmeta != TypeMetatype::Int && inmeta != TypeMetatype::Uint && inmeta != TypeMetatype::Bool {
            return false;
        }
        if in_dt.get_size() == 2 && !in_dt.is_char_print() {
            return false;
        }
        if in_dt.get_size() == 1 && inmeta == TypeMetatype::Int {
            return false;
        }
        if in_dt.get_size() >= 4 {
            return false;
        }
        true
    }
}
