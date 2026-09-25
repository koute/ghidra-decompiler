#![allow(unused_variables)]

use std::sync::Arc;

use crate::address::calc_mask;
use crate::architecture::Architecture;
use crate::block::BlockId;
use crate::cast::{CastStrategy, NO_PROMOTION, SIGNED_EXTENSION, UNSIGNED_EXTENSION};
use crate::cpool::CPoolRecord;
use crate::error::{Error, Result};
use crate::fspec::{CallSpecId, FuncCallSpecs};
use crate::funcdata::Funcdata;
use crate::op::{OpId, PcodeOp};
use crate::opbehavior::*;
use crate::opcodes::OpCode;
use crate::printlanguage::{PrintContext, PrintLanguage};
use crate::space::{AddrSpace, SpaceRef, SpaceType};
use crate::translate::Translate;
use crate::types::{Datatype, TypeFactory, TypeId, TypeMetatype};
use crate::userop::UserPcodeOp;
use crate::varnode::VarnodeId;

pub const INHERITS_SIGN: u32 = 1;
pub const INHERITS_SIGN_ZERO: u32 = 2;
pub const SHIFT_OP: u32 = 4;
pub const ARITHMETIC_OP: u32 = 8;
pub const LOGICAL_OP: u32 = 0x10;
pub const FLOATINGPOINT_OP: u32 = 0x20;

pub struct TypeOpBase {
    pub opcode: OpCode,
    pub opflags: u32,
    pub addlflags: u32,
    pub name: String,
    pub behave: Option<OpBehaviorRef>,
}

impl TypeOpBase {
    pub fn new(opc: OpCode, name: &str) -> TypeOpBase {
        TypeOpBase {
            opcode: opc,
            opflags: 0,
            addlflags: 0,
            name: name.to_string(),
            behave: None,
        }
    }
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct TypeOpMeta {
    pub metaout: TypeMetatype,
    pub metain: TypeMetatype,
}

impl TypeOpMeta {
    pub fn new(mout: TypeMetatype, min: TypeMetatype) -> TypeOpMeta {
        TypeOpMeta {
            metaout: mout,
            metain: min,
        }
    }
}

pub trait TypeOp: Send {
    fn base(&self) -> &TypeOpBase;

    fn base_mut(&mut self) -> &mut TypeOpBase;

    fn set_metatype_in(&mut self, val: TypeMetatype) {}

    fn set_metatype_out(&mut self, val: TypeMetatype) {}

    fn set_symbol(&mut self, nm: &str) {
        self.base_mut().name = nm.to_string();
    }

    fn get_name(&self) -> &str {
        &self.base().name
    }

    fn get_opcode(&self) -> OpCode {
        self.base().opcode
    }

    fn get_flags(&self) -> u32 {
        self.base().opflags
    }

    fn get_behavior(&self) -> Option<&dyn OpBehavior> {
        self.base().behave.as_deref()
    }

    fn evaluate_unary(&self, sizeout: i32, sizein: i32, in1: u64) -> Result<u64> {
        self.base()
            .behave
            .as_ref()
            .expect("TypeOp has no OpBehavior")
            .evaluate_unary(sizeout, sizein, in1)
    }

    fn evaluate_binary(&self, sizeout: i32, sizein: i32, in1: u64, in2: u64) -> Result<u64> {
        self.base()
            .behave
            .as_ref()
            .expect("TypeOp has no OpBehavior")
            .evaluate_binary(sizeout, sizein, in1, in2)
    }

    fn evaluate_ternary(&self, sizeout: i32, sizein: i32, in1: u64, in2: u64, in3: u64) -> Result<u64> {
        self.base()
            .behave
            .as_ref()
            .expect("TypeOp has no OpBehavior")
            .evaluate_ternary(sizeout, sizein, in1, in2, in3)
    }

    fn recover_input_binary(&self, slot: i32, sizeout: i32, out: u64, sizein: i32, input: u64) -> Result<u64> {
        self.base()
            .behave
            .as_ref()
            .expect("TypeOp has no OpBehavior")
            .recover_input_binary(slot, sizeout, out, sizein, input)
    }

    fn recover_input_unary(&self, sizeout: i32, out: u64, sizein: i32) -> Result<u64> {
        self.base()
            .behave
            .as_ref()
            .expect("TypeOp has no OpBehavior")
            .recover_input_unary(sizeout, out, sizein)
    }

    fn is_commutative(&self) -> bool {
        (self.base().opflags & PcodeOp::COMMUTATIVE) != 0
    }

    fn inherits_sign(&self) -> bool {
        (self.base().addlflags & INHERITS_SIGN) != 0
    }

    fn inherits_sign_first_param_only(&self) -> bool {
        (self.base().addlflags & INHERITS_SIGN_ZERO) != 0
    }

    fn is_shift_op(&self) -> bool {
        (self.base().addlflags & SHIFT_OP) != 0
    }

    fn is_arithmetic_op(&self) -> bool {
        (self.base().addlflags & ARITHMETIC_OP) != 0
    }

    fn is_logical_op(&self) -> bool {
        (self.base().addlflags & LOGICAL_OP) != 0
    }

    fn is_floating_point_op(&self) -> bool {
        (self.base().addlflags & FLOATINGPOINT_OP) != 0
    }

    fn get_output_local(&self, op: OpId, data: &mut Funcdata, glb: &mut Architecture) -> Result<TypeId> {
        default_output_local(op, data, glb)
    }

    fn get_input_local(&self, op: OpId, slot: i32, data: &mut Funcdata, glb: &mut Architecture) -> Result<TypeId> {
        default_input_local(op, slot, data, glb)
    }

    fn get_output_token(
        &self,
        op: OpId,
        cast_strategy: &mut dyn CastStrategy,
        data: &mut Funcdata,
        glb: &mut Architecture,
    ) -> Result<TypeId> {
        self.get_output_local(op, data, glb)
    }

    fn get_input_cast(
        &self,
        op: OpId,
        slot: i32,
        cast_strategy: &dyn CastStrategy,
        data: &mut Funcdata,
        glb: &mut Architecture,
    ) -> Result<Option<TypeId>> {
        base_input_cast(self, op, slot, cast_strategy, data, glb)
    }

    fn propagate_type(
        &self,
        alttype: TypeId,
        op: OpId,
        invn: VarnodeId,
        outvn: VarnodeId,
        inslot: i32,
        outslot: i32,
        data: &mut Funcdata,
        glb: &mut Architecture,
    ) -> Result<Option<TypeId>> {
        Ok(None)
    }

    fn push(
        &self,
        lng: &mut dyn PrintLanguage,
        ctx: &mut PrintContext<'_>,
        op: OpId,
        read_op: Option<OpId>,
    ) -> Result<()>;

    fn print_raw(&mut self, out: &mut String, op: OpId, data: &Funcdata, glb: &Architecture);

    fn get_operator_name(&self, op: OpId, data: &Funcdata, glb: &Architecture) -> String {
        self.base().name.clone()
    }
}

pub fn with_type_op<R>(
    glb: &mut Architecture,
    opc: OpCode,
    run: impl FnOnce(&mut dyn TypeOp, &mut Architecture) -> R,
) -> R {
    let mut top = glb.inst[opc.index()].take().expect("no TypeOp registered for opcode");
    let result = run(top.as_mut(), glb);
    glb.inst[opc.index()] = Some(top);
    result
}

pub fn register_instructions(inst: &mut Vec<Option<Box<dyn TypeOp>>>, tlst: &TypeFactory, trans: &dyn Translate) {
    fn boxed<T: TypeOp + 'static>(top: T) -> Option<Box<dyn TypeOp>> {
        Some(Box::new(top))
    }
    inst.extend((0..OpCode::Max.index()).map(|_slot| None));

    inst[OpCode::Copy.index()] = boxed(TypeOpCopy::new());
    inst[OpCode::Load.index()] = boxed(TypeOpLoad::new());
    inst[OpCode::Store.index()] = boxed(TypeOpStore::new());
    inst[OpCode::Branch.index()] = boxed(TypeOpBranch::new());
    inst[OpCode::Cbranch.index()] = boxed(TypeOpCbranch::new());
    inst[OpCode::Branchind.index()] = boxed(TypeOpBranchind::new());
    inst[OpCode::Call.index()] = boxed(TypeOpCall::new());
    inst[OpCode::Callind.index()] = boxed(TypeOpCallind::new());
    inst[OpCode::Callother.index()] = boxed(TypeOpCallother::new());
    inst[OpCode::Return.index()] = boxed(TypeOpReturn::new());

    inst[OpCode::Multiequal.index()] = boxed(TypeOpMulti::new());
    inst[OpCode::Indirect.index()] = boxed(TypeOpIndirect::new());

    inst[OpCode::Piece.index()] = boxed(TypeOpPiece::new(tlst));
    inst[OpCode::Subpiece.index()] = boxed(TypeOpSubpiece::new(tlst));
    inst[OpCode::IntEqual.index()] = boxed(TypeOpEqual::new());
    inst[OpCode::IntNotequal.index()] = boxed(TypeOpNotEqual::new());
    inst[OpCode::IntSless.index()] = boxed(TypeOpIntSless::new());
    inst[OpCode::IntSlessequal.index()] = boxed(TypeOpIntSlessEqual::new());
    inst[OpCode::IntLess.index()] = boxed(TypeOpIntLess::new());
    inst[OpCode::IntLessequal.index()] = boxed(TypeOpIntLessEqual::new());
    inst[OpCode::IntZext.index()] = boxed(TypeOpIntZext::new());
    inst[OpCode::IntSext.index()] = boxed(TypeOpIntSext::new());
    inst[OpCode::IntAdd.index()] = boxed(TypeOpIntAdd::new());
    inst[OpCode::IntSub.index()] = boxed(TypeOpIntSub::new());
    inst[OpCode::IntCarry.index()] = boxed(TypeOpIntCarry::new());
    inst[OpCode::IntScarry.index()] = boxed(TypeOpIntScarry::new());
    inst[OpCode::IntSborrow.index()] = boxed(TypeOpIntSborrow::new());
    inst[OpCode::Int2comp.index()] = boxed(TypeOpInt2Comp::new());
    inst[OpCode::IntNegate.index()] = boxed(TypeOpIntNegate::new());
    inst[OpCode::IntXor.index()] = boxed(TypeOpIntXor::new());
    inst[OpCode::IntAnd.index()] = boxed(TypeOpIntAnd::new());
    inst[OpCode::IntOr.index()] = boxed(TypeOpIntOr::new());
    inst[OpCode::IntLeft.index()] = boxed(TypeOpIntLeft::new());
    inst[OpCode::IntRight.index()] = boxed(TypeOpIntRight::new());
    inst[OpCode::IntSright.index()] = boxed(TypeOpIntSright::new());
    inst[OpCode::IntMult.index()] = boxed(TypeOpIntMult::new());
    inst[OpCode::IntDiv.index()] = boxed(TypeOpIntDiv::new());
    inst[OpCode::IntSdiv.index()] = boxed(TypeOpIntSdiv::new());
    inst[OpCode::IntRem.index()] = boxed(TypeOpIntRem::new());
    inst[OpCode::IntSrem.index()] = boxed(TypeOpIntSrem::new());

    inst[OpCode::BoolNegate.index()] = boxed(TypeOpBoolNegate::new());
    inst[OpCode::BoolXor.index()] = boxed(TypeOpBoolXor::new());
    inst[OpCode::BoolAnd.index()] = boxed(TypeOpBoolAnd::new());
    inst[OpCode::BoolOr.index()] = boxed(TypeOpBoolOr::new());

    inst[OpCode::Cast.index()] = boxed(TypeOpCast::new());
    inst[OpCode::Ptradd.index()] = boxed(TypeOpPtradd::new());
    inst[OpCode::Ptrsub.index()] = boxed(TypeOpPtrsub::new());

    inst[OpCode::FloatEqual.index()] = boxed(TypeOpFloatEqual::new(trans));
    inst[OpCode::FloatNotequal.index()] = boxed(TypeOpFloatNotEqual::new(trans));
    inst[OpCode::FloatLess.index()] = boxed(TypeOpFloatLess::new(trans));
    inst[OpCode::FloatLessequal.index()] = boxed(TypeOpFloatLessEqual::new(trans));
    inst[OpCode::FloatNan.index()] = boxed(TypeOpFloatNan::new(trans));

    inst[OpCode::FloatAdd.index()] = boxed(TypeOpFloatAdd::new(trans));
    inst[OpCode::FloatDiv.index()] = boxed(TypeOpFloatDiv::new(trans));
    inst[OpCode::FloatMult.index()] = boxed(TypeOpFloatMult::new(trans));
    inst[OpCode::FloatSub.index()] = boxed(TypeOpFloatSub::new(trans));
    inst[OpCode::FloatNeg.index()] = boxed(TypeOpFloatNeg::new(trans));
    inst[OpCode::FloatAbs.index()] = boxed(TypeOpFloatAbs::new(trans));
    inst[OpCode::FloatSqrt.index()] = boxed(TypeOpFloatSqrt::new(trans));

    inst[OpCode::FloatInt2float.index()] = boxed(TypeOpFloatInt2Float::new(trans));
    inst[OpCode::FloatFloat2float.index()] = boxed(TypeOpFloatFloat2Float::new(trans));
    inst[OpCode::FloatTrunc.index()] = boxed(TypeOpFloatTrunc::new(trans));
    inst[OpCode::FloatCeil.index()] = boxed(TypeOpFloatCeil::new(trans));
    inst[OpCode::FloatFloor.index()] = boxed(TypeOpFloatFloor::new(trans));
    inst[OpCode::FloatRound.index()] = boxed(TypeOpFloatRound::new(trans));
    inst[OpCode::Segmentop.index()] = boxed(TypeOpSegment::new());
    inst[OpCode::Cpoolref.index()] = boxed(TypeOpCpoolref::new());
    inst[OpCode::New.index()] = boxed(TypeOpNew::new());
    inst[OpCode::Insert.index()] = boxed(TypeOpInsert::new());
    inst[OpCode::Zpull.index()] = boxed(TypeOpZpull::new());
    inst[OpCode::Popcount.index()] = boxed(TypeOpPopcount::new());
    inst[OpCode::Lzcount.index()] = boxed(TypeOpLzcount::new());
    inst[OpCode::Spull.index()] = boxed(TypeOpSpull::new());
}

pub fn select_java_operators(inst: &mut [Option<Box<dyn TypeOp>>], val: bool) {
    let mut configure = |opc: OpCode, metain: TypeMetatype, metaout: TypeMetatype| {
        let top = inst[opc.index()].as_mut().expect("no TypeOp registered for opcode");
        top.set_metatype_in(metain);
        top.set_metatype_out(metaout);
    };
    if val {
        configure(OpCode::IntZext, TypeMetatype::Unknown, TypeMetatype::Int);
        configure(OpCode::IntNegate, TypeMetatype::Int, TypeMetatype::Int);
        configure(OpCode::IntXor, TypeMetatype::Int, TypeMetatype::Int);
        configure(OpCode::IntOr, TypeMetatype::Int, TypeMetatype::Int);
        configure(OpCode::IntAnd, TypeMetatype::Int, TypeMetatype::Int);
        configure(OpCode::IntRight, TypeMetatype::Int, TypeMetatype::Int);
        inst[OpCode::IntRight.index()]
            .as_mut()
            .expect("no TypeOp registered for opcode")
            .set_symbol(">>>");
    } else {
        configure(OpCode::IntZext, TypeMetatype::Uint, TypeMetatype::Uint);
        configure(OpCode::IntNegate, TypeMetatype::Uint, TypeMetatype::Uint);
        configure(OpCode::IntXor, TypeMetatype::Uint, TypeMetatype::Uint);
        configure(OpCode::IntOr, TypeMetatype::Uint, TypeMetatype::Uint);
        configure(OpCode::IntAnd, TypeMetatype::Uint, TypeMetatype::Uint);
        configure(OpCode::IntRight, TypeMetatype::Uint, TypeMetatype::Uint);
        inst[OpCode::IntRight.index()]
            .as_mut()
            .expect("no TypeOp registered for opcode")
            .set_symbol(">>");
    }
}

pub fn float_sign_manipulation(op: OpId, data: &Funcdata) -> OpCode {
    let pcode = data.op(op);
    let opc = pcode.code();
    if opc == OpCode::IntAnd {
        let cvn = data.vn(pcode.get_in(1));
        if cvn.is_constant() {
            let mut val = calc_mask(cvn.get_size());
            val >>= 1;
            if val == cvn.get_offset() {
                return OpCode::FloatAbs;
            }
        }
    } else if opc == OpCode::IntXor {
        let cvn = data.vn(pcode.get_in(1));
        if cvn.is_constant() {
            let mut val = calc_mask(cvn.get_size());
            val ^= val >> 1;
            if val == cvn.get_offset() {
                return OpCode::FloatNeg;
            }
        }
    }
    OpCode::Max
}

pub fn propagate_to_pointer(types: &mut TypeFactory, dt: TypeId, sz: i32, wordsz: u32) -> Result<TypeId> {
    let mut dt = dt;
    let meta = types.get(dt).get_metatype();
    if meta == TypeMetatype::Ptr {
        dt = types.get_base(types.get(dt).get_size(), TypeMetatype::Unknown)?;
    } else if meta == TypeMetatype::PartialStruct {
        dt = types.get(dt).get_component_for_ptr(types);
    }
    types.get_type_pointer(sz, dt, wordsz)
}

pub fn propagate_from_pointer(types: &mut TypeFactory, dt: TypeId, sz: i32) -> Result<Option<TypeId>> {
    if types.get(dt).get_metatype() != TypeMetatype::Ptr {
        return Ok(None);
    }
    let ptrto = types.get(dt).get_ptr_to();
    if types.get(ptrto).is_variable_length() {
        return Ok(None);
    }
    if types.get(ptrto).get_size() == sz {
        return Ok(Some(ptrto));
    }
    if types.get(dt).is_pointer_rel() {
        let parent = types.get(dt).get_parent();
        let byte_offset = types.get(dt).get_byte_offset();
        if let Some(res) = types.get_exact_piece(parent, byte_offset, sz)?
            && types.get(res).is_enum_type()
        {
            return Ok(Some(res));
        }
    } else if types.get(ptrto).is_enum_type() && !types.get(ptrto).has_stripped() {
        return types.get_type_partial_enum(ptrto, 0, sz).map(Some);
    }
    Ok(None)
}

pub struct TypeOpCopy {
    pub base: TypeOpBase,
}

impl Default for TypeOpCopy {
    fn default() -> Self {
        Self::new()
    }
}

impl TypeOpCopy {
    pub fn new() -> TypeOpCopy {
        TypeOpCopy {
            base: new_base(
                OpCode::Copy,
                "copy",
                PcodeOp::UNARY | PcodeOp::NOCOLLAPSE,
                0,
                Arc::new(OpBehaviorCopy::new()),
            ),
        }
    }
}

impl TypeOp for TypeOpCopy {
    fn base(&self) -> &TypeOpBase {
        &self.base
    }

    fn base_mut(&mut self) -> &mut TypeOpBase {
        &mut self.base
    }

    fn get_input_cast(
        &self,
        op: OpId,
        slot: i32,
        cast_strategy: &dyn CastStrategy,
        data: &mut Funcdata,
        glb: &mut Architecture,
    ) -> Result<Option<TypeId>> {
        let outvn = out_vn(data, op);
        let reqtype = data.vn_get_high_type_def_facing(outvn, glb)?;
        let invn = data.op(op).get_in(0);
        let curtype = data.vn_get_high_type_read_facing(invn, op, glb)?;
        Ok(cast_strategy.cast_standard(reqtype, curtype, false, true, types_mut(glb)))
    }

    fn get_output_token(
        &self,
        op: OpId,
        cast_strategy: &mut dyn CastStrategy,
        data: &mut Funcdata,
        glb: &mut Architecture,
    ) -> Result<TypeId> {
        let invn = data.op(op).get_in(0);
        data.vn_get_high_type_read_facing(invn, op, glb)
    }

    fn propagate_type(
        &self,
        alttype: TypeId,
        op: OpId,
        invn: VarnodeId,
        outvn: VarnodeId,
        inslot: i32,
        outslot: i32,
        data: &mut Funcdata,
        glb: &mut Architecture,
    ) -> Result<Option<TypeId>> {
        if inslot != -1 && outslot != -1 {
            return Ok(None);
        }
        pass_through_type(alttype, invn, data, glb).map(Some)
    }

    fn print_raw(&mut self, out: &mut String, op: OpId, data: &Funcdata, glb: &Architecture) {
        let pcode = data.op(op);
        data.vn_print_raw_option(pcode.get_out(), out, glb);
        out.push_str(" = ");
        data.vn_print_raw_option(pcode.get_in_option(0), out, glb);
    }

    fn push(
        &self,
        lng: &mut dyn PrintLanguage,
        ctx: &mut PrintContext<'_>,
        op: OpId,
        read_op: Option<OpId>,
    ) -> Result<()> {
        lng.op_copy(ctx, op)
    }
}

pub struct TypeOpLoad {
    pub base: TypeOpBase,
}

impl Default for TypeOpLoad {
    fn default() -> Self {
        Self::new()
    }
}

impl TypeOpLoad {
    pub fn new() -> TypeOpLoad {
        TypeOpLoad {
            base: new_base(
                OpCode::Load,
                "load",
                PcodeOp::SPECIAL | PcodeOp::NOCOLLAPSE,
                0,
                Arc::new(OpBehaviorGeneric::new_special(OpCode::Load, false, true)),
            ),
        }
    }
}

impl TypeOp for TypeOpLoad {
    fn base(&self) -> &TypeOpBase {
        &self.base
    }

    fn base_mut(&mut self) -> &mut TypeOpBase {
        &mut self.base
    }

    fn get_input_cast(
        &self,
        op: OpId,
        slot: i32,
        cast_strategy: &dyn CastStrategy,
        data: &mut Funcdata,
        glb: &mut Architecture,
    ) -> Result<Option<TypeId>> {
        if slot != 1 {
            return Ok(None);
        }
        let outvn = out_vn(data, op);
        let reqtype = data.vn_get_high_type_def_facing(outvn, glb)?;
        let invn = data.op(op).get_in(1);
        let mut curtype = data.vn_get_high_type_read_facing(invn, op, glb)?;
        let wordsize = const_space(data, data.op(op).get_in(0), glb).get_word_size();
        let insize = data.vn(invn).get_size();
        if types(glb).get(curtype).get_metatype() == TypeMetatype::Ptr {
            curtype = types(glb).get(curtype).get_ptr_to();
        } else {
            return types_mut(glb).get_type_pointer(insize, reqtype, wordsize).map(Some);
        }
        if curtype != reqtype && types(glb).get(curtype).get_size() == types(glb).get(reqtype).get_size() {
            let curmeta = types(glb).get(curtype).get_metatype();
            if curmeta != TypeMetatype::Struct
                && curmeta != TypeMetatype::Array
                && curmeta != TypeMetatype::Spacebase
                && curmeta != TypeMetatype::Union
            {
                let inrec = data.vn(invn);
                if !inrec.is_implied() || !inrec.is_written() || def_code(data, invn) != Some(OpCode::Cast) {
                    return Ok(None);
                }
            }
        }
        let Some(reqtype) = cast_strategy.cast_standard(reqtype, curtype, false, true, types_mut(glb)) else {
            return Ok(None);
        };
        types_mut(glb).get_type_pointer(insize, reqtype, wordsize).map(Some)
    }

    fn get_output_token(
        &self,
        op: OpId,
        cast_strategy: &mut dyn CastStrategy,
        data: &mut Funcdata,
        glb: &mut Architecture,
    ) -> Result<TypeId> {
        let invn = data.op(op).get_in(1);
        let ct = data.vn_get_high_type_read_facing(invn, op, glb)?;
        let outvn = out_vn(data, op);
        let factory = types(glb);
        if factory.get(ct).get_metatype() == TypeMetatype::Ptr {
            let ptrto = factory.get(ct).get_ptr_to();
            if factory.get(ptrto).get_size() == data.vn(outvn).get_size() {
                return Ok(ptrto);
            }
        }
        data.vn_get_high_type_def_facing(outvn, glb)
    }

    fn propagate_type(
        &self,
        alttype: TypeId,
        op: OpId,
        invn: VarnodeId,
        outvn: VarnodeId,
        inslot: i32,
        outslot: i32,
        data: &mut Funcdata,
        glb: &mut Architecture,
    ) -> Result<Option<TypeId>> {
        if inslot == 0 || outslot == 0 {
            return Ok(None);
        }
        if data.vn(invn).is_spacebase() {
            return Ok(None);
        }
        let outsize = data.vn(outvn).get_size();
        if inslot == -1 {
            let wordsize = const_space(data, data.op(op).get_in(0), glb).get_word_size();
            propagate_to_pointer(types_mut(glb), alttype, outsize, wordsize).map(Some)
        } else {
            propagate_from_pointer(types_mut(glb), alttype, outsize)
        }
    }

    fn print_raw(&mut self, out: &mut String, op: OpId, data: &Funcdata, glb: &Architecture) {
        let pcode = data.op(op);
        data.vn_print_raw_option(pcode.get_out(), out, glb);
        out.push_str(" = *(");
        let spc = const_space(data, pcode.get_in(0), glb);
        out.push_str(spc.get_name());
        out.push(',');
        data.vn_print_raw_option(pcode.get_in_option(1), out, glb);
        out.push(')');
    }

    fn push(
        &self,
        lng: &mut dyn PrintLanguage,
        ctx: &mut PrintContext<'_>,
        op: OpId,
        read_op: Option<OpId>,
    ) -> Result<()> {
        lng.op_load(ctx, op)
    }
}

pub struct TypeOpStore {
    pub base: TypeOpBase,
}

impl Default for TypeOpStore {
    fn default() -> Self {
        Self::new()
    }
}

impl TypeOpStore {
    pub fn new() -> TypeOpStore {
        TypeOpStore {
            base: new_base(
                OpCode::Store,
                "store",
                PcodeOp::SPECIAL | PcodeOp::NOCOLLAPSE,
                0,
                Arc::new(OpBehaviorGeneric::new_special(OpCode::Store, false, true)),
            ),
        }
    }
}

impl TypeOp for TypeOpStore {
    fn base(&self) -> &TypeOpBase {
        &self.base
    }

    fn base_mut(&mut self) -> &mut TypeOpBase {
        &mut self.base
    }

    fn get_input_cast(
        &self,
        op: OpId,
        slot: i32,
        cast_strategy: &dyn CastStrategy,
        data: &mut Funcdata,
        glb: &mut Architecture,
    ) -> Result<Option<TypeId>> {
        if slot == 0 {
            return Ok(None);
        }
        if data.op(op).does_special_printing() {
            return Ok(None);
        }
        let pointer_vn = data.op(op).get_in(1);
        let pointer_type = data.vn_get_high_type_read_facing(pointer_vn, op, glb)?;
        let mut pointed_to_type = pointer_type;
        let value_vn = data.op(op).get_in(2);
        let value_type = data.vn_get_high_type_read_facing(value_vn, op, glb)?;
        let wordsize = const_space(data, data.op(op).get_in(0), glb).get_word_size();
        let dest_size;
        if types(glb).get(pointer_type).get_metatype() == TypeMetatype::Ptr {
            pointed_to_type = types(glb).get(pointer_type).get_ptr_to();
            dest_size = types(glb).get(pointed_to_type).get_size();
        } else {
            dest_size = -1;
        }
        let pointer_size = data.vn(pointer_vn).get_size();
        if dest_size != types(glb).get(value_type).get_size() {
            if slot == 1 {
                return types_mut(glb)
                    .get_type_pointer(pointer_size, value_type, wordsize)
                    .map(Some);
            } else {
                return Ok(None);
            }
        }
        if slot == 1 {
            let pointer_rec = data.vn(pointer_vn);
            if pointer_rec.is_written()
                && def_code(data, pointer_vn) == Some(OpCode::Cast)
                && pointer_rec.is_implied()
                && pointer_rec.lone_descend() == Some(op)
            {
                let new_type = types_mut(glb).get_type_pointer(pointer_size, value_type, wordsize)?;
                if pointer_type != new_type {
                    return Ok(Some(new_type));
                }
            }
            return Ok(None);
        }
        Ok(cast_strategy.cast_standard(pointed_to_type, value_type, false, true, types_mut(glb)))
    }

    fn propagate_type(
        &self,
        alttype: TypeId,
        op: OpId,
        invn: VarnodeId,
        outvn: VarnodeId,
        inslot: i32,
        outslot: i32,
        data: &mut Funcdata,
        glb: &mut Architecture,
    ) -> Result<Option<TypeId>> {
        if inslot == 0 || outslot == 0 {
            return Ok(None);
        }
        if data.vn(invn).is_spacebase() {
            return Ok(None);
        }
        let outsize = data.vn(outvn).get_size();
        if inslot == 2 {
            let wordsize = const_space(data, data.op(op).get_in(0), glb).get_word_size();
            propagate_to_pointer(types_mut(glb), alttype, outsize, wordsize).map(Some)
        } else {
            propagate_from_pointer(types_mut(glb), alttype, outsize)
        }
    }

    fn print_raw(&mut self, out: &mut String, op: OpId, data: &Funcdata, glb: &Architecture) {
        let pcode = data.op(op);
        out.push_str("*(");
        let spc = const_space(data, pcode.get_in(0), glb);
        out.push_str(spc.get_name());
        out.push(',');
        data.vn_print_raw_option(pcode.get_in_option(1), out, glb);
        out.push_str(") = ");
        data.vn_print_raw_option(pcode.get_in_option(2), out, glb);
    }

    fn push(
        &self,
        lng: &mut dyn PrintLanguage,
        ctx: &mut PrintContext<'_>,
        op: OpId,
        read_op: Option<OpId>,
    ) -> Result<()> {
        lng.op_store(ctx, op)
    }
}

pub struct TypeOpBranch {
    pub base: TypeOpBase,
}

impl Default for TypeOpBranch {
    fn default() -> Self {
        Self::new()
    }
}

impl TypeOpBranch {
    pub fn new() -> TypeOpBranch {
        TypeOpBranch {
            base: new_base(
                OpCode::Branch,
                "goto",
                PcodeOp::SPECIAL | PcodeOp::BRANCH | PcodeOp::CODEREF | PcodeOp::NOCOLLAPSE,
                0,
                Arc::new(OpBehaviorGeneric::new_special(OpCode::Branch, false, true)),
            ),
        }
    }
}

impl TypeOp for TypeOpBranch {
    fn base(&self) -> &TypeOpBase {
        &self.base
    }

    fn base_mut(&mut self) -> &mut TypeOpBase {
        &mut self.base
    }

    fn print_raw(&mut self, out: &mut String, op: OpId, data: &Funcdata, glb: &Architecture) {
        out.push_str(&self.base.name);
        out.push(' ');
        let pcode = data.op(op);
        match pcode.get_parent() {
            Some(parent) if data.block(parent).size_out() == 1 => {
                let target = data.block(parent).get_out(0);
                data.block(target).print_short_header(out);
            }
            _ => data.vn_print_raw_option(pcode.get_in_option(0), out, glb),
        }
    }

    fn push(
        &self,
        lng: &mut dyn PrintLanguage,
        ctx: &mut PrintContext<'_>,
        op: OpId,
        read_op: Option<OpId>,
    ) -> Result<()> {
        lng.op_branch(ctx, op)
    }
}

pub struct TypeOpCbranch {
    pub base: TypeOpBase,
}

impl Default for TypeOpCbranch {
    fn default() -> Self {
        Self::new()
    }
}

impl TypeOpCbranch {
    pub fn new() -> TypeOpCbranch {
        TypeOpCbranch {
            base: new_base(
                OpCode::Cbranch,
                "goto",
                PcodeOp::SPECIAL | PcodeOp::BRANCH | PcodeOp::CODEREF | PcodeOp::NOCOLLAPSE,
                0,
                Arc::new(OpBehaviorGeneric::new_special(OpCode::Cbranch, false, true)),
            ),
        }
    }
}

impl TypeOp for TypeOpCbranch {
    fn base(&self) -> &TypeOpBase {
        &self.base
    }

    fn base_mut(&mut self) -> &mut TypeOpBase {
        &mut self.base
    }

    fn get_input_local(&self, op: OpId, slot: i32, data: &mut Funcdata, glb: &mut Architecture) -> Result<TypeId> {
        let pcode = data.op(op);
        if slot == 1 {
            let size = data.vn(pcode.get_in(1)).get_size();
            return types_mut(glb).get_base(size, TypeMetatype::Bool);
        }
        let invn = data.vn(pcode.get_in(0));
        let size = invn.get_size();
        let wordsize = invn.get_space().expect("varnode has no address space").get_word_size();
        let td = types_mut(glb).get_type_code()?;
        types_mut(glb).get_type_pointer(size, td, wordsize)
    }

    fn print_raw(&mut self, out: &mut String, op: OpId, data: &Funcdata, glb: &Architecture) {
        out.push_str(&self.base.name);
        out.push(' ');
        let pcode = data.op(op);
        let mut false_out: Option<BlockId> = None;
        match pcode.get_parent() {
            Some(parent) if data.block(parent).size_out() == 2 => {
                let true_out = data.block(parent).get_true_out();
                false_out = Some(data.block(parent).get_false_out());
                data.block(true_out).print_short_header(out);
            }
            _ => data.vn_print_raw_option(pcode.get_in_option(0), out, glb),
        }
        out.push_str(" if (");
        data.vn_print_raw_option(pcode.get_in_option(1), out, glb);
        if pcode.is_boolean_flip() {
            out.push_str(" == 0)");
        } else {
            out.push_str(" != 0)");
        }
        if let Some(false_out) = false_out {
            out.push_str(" else ");
            data.block(false_out).print_short_header(out);
        }
    }

    fn push(
        &self,
        lng: &mut dyn PrintLanguage,
        ctx: &mut PrintContext<'_>,
        op: OpId,
        read_op: Option<OpId>,
    ) -> Result<()> {
        lng.op_cbranch(ctx, op)
    }
}

pub struct TypeOpBranchind {
    pub base: TypeOpBase,
}

impl Default for TypeOpBranchind {
    fn default() -> Self {
        Self::new()
    }
}

impl TypeOpBranchind {
    pub fn new() -> TypeOpBranchind {
        TypeOpBranchind {
            base: new_base(
                OpCode::Branchind,
                "switch",
                PcodeOp::SPECIAL | PcodeOp::BRANCH | PcodeOp::NOCOLLAPSE,
                0,
                Arc::new(OpBehaviorGeneric::new_special(OpCode::Branchind, false, true)),
            ),
        }
    }
}

impl TypeOp for TypeOpBranchind {
    fn base(&self) -> &TypeOpBase {
        &self.base
    }

    fn base_mut(&mut self) -> &mut TypeOpBase {
        &mut self.base
    }

    fn print_raw(&mut self, out: &mut String, op: OpId, data: &Funcdata, glb: &Architecture) {
        out.push_str(&self.base.name);
        out.push(' ');
        data.vn_print_raw_option(data.op(op).get_in_option(0), out, glb);
    }

    fn push(
        &self,
        lng: &mut dyn PrintLanguage,
        ctx: &mut PrintContext<'_>,
        op: OpId,
        read_op: Option<OpId>,
    ) -> Result<()> {
        lng.op_branchind(ctx, op)
    }
}

pub struct TypeOpCall {
    pub base: TypeOpBase,
}

impl Default for TypeOpCall {
    fn default() -> Self {
        Self::new()
    }
}

impl TypeOpCall {
    pub fn new() -> TypeOpCall {
        TypeOpCall {
            base: new_base(
                OpCode::Call,
                "call",
                PcodeOp::SPECIAL | PcodeOp::CALL | PcodeOp::HAS_CALLSPEC | PcodeOp::CODEREF | PcodeOp::NOCOLLAPSE,
                0,
                Arc::new(OpBehaviorGeneric::new_special(OpCode::Call, false, true)),
            ),
        }
    }
}

impl TypeOp for TypeOpCall {
    fn base(&self) -> &TypeOpBase {
        &self.base
    }

    fn base_mut(&mut self) -> &mut TypeOpBase {
        &mut self.base
    }

    fn print_raw(&mut self, out: &mut String, op: OpId, data: &Funcdata, glb: &Architecture) {
        let pcode = data.op(op);
        if pcode.get_out().is_some() {
            data.vn_print_raw_option(pcode.get_out(), out, glb);
            out.push_str(" = ");
        }
        out.push_str(&self.base.name);
        out.push(' ');
        data.vn_print_raw_option(pcode.get_in_option(0), out, glb);
        if pcode.num_input() > 1 {
            print_input_list(data, op, 1, out, glb);
        }
    }

    fn get_input_local(&self, op: OpId, slot: i32, data: &mut Funcdata, glb: &mut Architecture) -> Result<TypeId> {
        let vn = data.op(op).get_in(0);
        if slot == 0 || !is_fspec_varnode(data, vn) {
            return default_input_local(op, slot, data, glb);
        }
        let fc = FuncCallSpecs::get_fspec_from_const(data.vn(vn).get_addr());
        let insize = data.vn(data.op(op).get_in(slot)).get_size();
        if let Some(ct) = locked_param_type(data, fc, slot, Some(insize), glb) {
            return Ok(ct);
        }
        default_input_local(op, slot, data, glb)
    }

    fn get_output_local(&self, op: OpId, data: &mut Funcdata, glb: &mut Architecture) -> Result<TypeId> {
        let vn = data.op(op).get_in(0);
        if !is_fspec_varnode(data, vn) {
            return default_output_local(op, data, glb);
        }
        let fc = FuncCallSpecs::get_fspec_from_const(data.vn(vn).get_addr());
        locked_output_type(op, fc, data, glb)
    }

    fn push(
        &self,
        lng: &mut dyn PrintLanguage,
        ctx: &mut PrintContext<'_>,
        op: OpId,
        read_op: Option<OpId>,
    ) -> Result<()> {
        lng.op_call(ctx, op)
    }
}

pub struct TypeOpCallind {
    pub base: TypeOpBase,
}

impl Default for TypeOpCallind {
    fn default() -> Self {
        Self::new()
    }
}

impl TypeOpCallind {
    pub fn new() -> TypeOpCallind {
        TypeOpCallind {
            base: new_base(
                OpCode::Callind,
                "callind",
                PcodeOp::SPECIAL | PcodeOp::CALL | PcodeOp::HAS_CALLSPEC | PcodeOp::NOCOLLAPSE,
                0,
                Arc::new(OpBehaviorGeneric::new_special(OpCode::Callind, false, true)),
            ),
        }
    }
}

impl TypeOp for TypeOpCallind {
    fn base(&self) -> &TypeOpBase {
        &self.base
    }

    fn base_mut(&mut self) -> &mut TypeOpBase {
        &mut self.base
    }

    fn print_raw(&mut self, out: &mut String, op: OpId, data: &Funcdata, glb: &Architecture) {
        let pcode = data.op(op);
        if pcode.get_out().is_some() {
            data.vn_print_raw_option(pcode.get_out(), out, glb);
            out.push_str(" = ");
        }
        out.push_str(&self.base.name);
        data.vn_print_raw_option(pcode.get_in_option(0), out, glb);
        if pcode.num_input() > 1 {
            print_input_list(data, op, 1, out, glb);
        }
    }

    fn get_input_local(&self, op: OpId, slot: i32, data: &mut Funcdata, glb: &mut Architecture) -> Result<TypeId> {
        if slot == 0 {
            let wordsize = data
                .op(op)
                .get_addr()
                .get_space()
                .expect("p-code op address has no space")
                .get_word_size();
            let size = data.vn(data.op(op).get_in(0)).get_size();
            let td = types_mut(glb).get_type_code()?;
            return types_mut(glb).get_type_pointer(size, td, wordsize);
        }
        let Some(fc) = data.get_call_specs_op(op) else {
            return default_input_local(op, slot, data, glb);
        };
        if let Some(ct) = locked_param_type(data, fc, slot, None, glb) {
            return Ok(ct);
        }
        default_input_local(op, slot, data, glb)
    }

    fn get_output_local(&self, op: OpId, data: &mut Funcdata, glb: &mut Architecture) -> Result<TypeId> {
        let Some(fc) = data.get_call_specs_op(op) else {
            return default_output_local(op, data, glb);
        };
        locked_output_type(op, fc, data, glb)
    }

    fn push(
        &self,
        lng: &mut dyn PrintLanguage,
        ctx: &mut PrintContext<'_>,
        op: OpId,
        read_op: Option<OpId>,
    ) -> Result<()> {
        lng.op_callind(ctx, op)
    }
}

pub struct TypeOpCallother {
    pub base: TypeOpBase,
}

impl Default for TypeOpCallother {
    fn default() -> Self {
        Self::new()
    }
}

impl TypeOpCallother {
    pub fn new() -> TypeOpCallother {
        TypeOpCallother {
            base: new_base(
                OpCode::Callother,
                "syscall",
                PcodeOp::SPECIAL | PcodeOp::CALL | PcodeOp::NOCOLLAPSE,
                0,
                Arc::new(OpBehaviorGeneric::new_special(OpCode::Callother, false, true)),
            ),
        }
    }
}

impl TypeOp for TypeOpCallother {
    fn base(&self) -> &TypeOpBase {
        &self.base
    }

    fn base_mut(&mut self) -> &mut TypeOpBase {
        &mut self.base
    }

    fn print_raw(&mut self, out: &mut String, op: OpId, data: &Funcdata, glb: &Architecture) {
        let pcode = data.op(op);
        if pcode.get_out().is_some() {
            data.vn_print_raw_option(pcode.get_out(), out, glb);
            out.push_str(" = ");
        }
        out.push_str(&self.get_operator_name(op, data, glb));
        if pcode.num_input() > 1 {
            print_input_list(data, op, 1, out, glb);
        }
    }

    fn get_operator_name(&self, op: OpId, data: &Funcdata, glb: &Architecture) -> String {
        let pcode = data.op(op);
        if pcode.get_parent().is_some() {
            let index = data.vn(pcode.get_in(0)).get_offset() as i32;
            if let Some(userop) = glb.userops.get_op(index as u32) {
                return userop.get_operator_name(op, data);
            }
        }
        let mut res = String::new();
        res.push_str(&self.base.name);
        res.push('[');
        data.vn_print_raw(pcode.get_in(0), &mut res, glb);
        res.push(']');
        res
    }

    fn get_input_local(&self, op: OpId, slot: i32, data: &mut Funcdata, glb: &mut Architecture) -> Result<TypeId> {
        let userop = callother_userop(op, data, glb)?;
        if let Some(res) = userop.get_input_local(op, slot, data, glb)? {
            return Ok(res);
        }
        default_input_local(op, slot, data, glb)
    }

    fn get_output_local(&self, op: OpId, data: &mut Funcdata, glb: &mut Architecture) -> Result<TypeId> {
        let userop = callother_userop(op, data, glb)?;
        if let Some(res) = userop.get_output_local(op, data, glb)? {
            return Ok(res);
        }
        default_output_local(op, data, glb)
    }

    fn push(
        &self,
        lng: &mut dyn PrintLanguage,
        ctx: &mut PrintContext<'_>,
        op: OpId,
        read_op: Option<OpId>,
    ) -> Result<()> {
        lng.op_callother(ctx, op)
    }
}

pub struct TypeOpReturn {
    pub base: TypeOpBase,
}

impl Default for TypeOpReturn {
    fn default() -> Self {
        Self::new()
    }
}

impl TypeOpReturn {
    pub fn new() -> TypeOpReturn {
        TypeOpReturn {
            base: new_base(
                OpCode::Return,
                "return",
                PcodeOp::SPECIAL | PcodeOp::RETURNS | PcodeOp::NOCOLLAPSE | PcodeOp::RETURN_COPY,
                0,
                Arc::new(OpBehaviorGeneric::new_special(OpCode::Return, false, true)),
            ),
        }
    }
}

impl TypeOp for TypeOpReturn {
    fn base(&self) -> &TypeOpBase {
        &self.base
    }

    fn base_mut(&mut self) -> &mut TypeOpBase {
        &mut self.base
    }

    fn print_raw(&mut self, out: &mut String, op: OpId, data: &Funcdata, glb: &Architecture) {
        let pcode = data.op(op);
        out.push_str(&self.base.name);
        if pcode.num_input() >= 1 {
            out.push('(');
            data.vn_print_raw_option(pcode.get_in_option(0), out, glb);
            out.push(')');
        }
        if pcode.num_input() > 1 {
            out.push(' ');
            data.vn_print_raw_option(pcode.get_in_option(1), out, glb);
            for index in 2..pcode.num_input() {
                out.push(',');
                data.vn_print_raw_option(pcode.get_in_option(index), out, glb);
            }
        }
    }

    fn get_input_local(&self, op: OpId, slot: i32, data: &mut Funcdata, glb: &mut Architecture) -> Result<TypeId> {
        if slot == 0 {
            return default_input_local(op, slot, data, glb);
        }
        if data.op(op).get_parent().is_none() {
            return default_input_local(op, slot, data, glb);
        }
        let ct = data.get_func_proto().get_output_type(glb);
        let insize = data.vn(data.op(op).get_in(slot)).get_size();
        let factory = types(glb);
        if factory.get(ct).get_metatype() == TypeMetatype::Void || factory.get(ct).get_size() != insize {
            return default_input_local(op, slot, data, glb);
        }
        Ok(ct)
    }

    fn push(
        &self,
        lng: &mut dyn PrintLanguage,
        ctx: &mut PrintContext<'_>,
        op: OpId,
        read_op: Option<OpId>,
    ) -> Result<()> {
        lng.op_return(ctx, op)
    }
}

pub struct TypeOpEqual {
    pub base: TypeOpBase,
    pub meta: TypeOpMeta,
}

impl Default for TypeOpEqual {
    fn default() -> Self {
        Self::new()
    }
}

impl TypeOpEqual {
    pub fn new() -> TypeOpEqual {
        TypeOpEqual {
            base: new_base(
                OpCode::IntEqual,
                "==",
                PcodeOp::BINARY | PcodeOp::BOOLOUTPUT | PcodeOp::COMMUTATIVE,
                INHERITS_SIGN,
                Arc::new(OpBehaviorEqual::new()),
            ),
            meta: TypeOpMeta::new(TypeMetatype::Bool, TypeMetatype::Int),
        }
    }

    pub fn propagate_across_compare(
        alttype: TypeId,
        invn: VarnodeId,
        outvn: VarnodeId,
        inslot: i32,
        outslot: i32,
        data: &mut Funcdata,
        glb: &mut Architecture,
    ) -> Result<Option<TypeId>> {
        if inslot == -1 || outslot == -1 {
            return Ok(None);
        }
        let newtype;
        if data.vn(invn).is_spacebase() {
            newtype = spacebase_pointer(alttype, glb)?;
        } else if types(glb).get(alttype).is_pointer_rel() && !data.vn(outvn).is_constant() {
            let rel_ptr = types(glb).get(alttype);
            let parent = rel_ptr.get_parent();
            if types(glb).get(parent).get_metatype() == TypeMetatype::Struct && rel_ptr.get_byte_offset() >= 0 {
                let size = rel_ptr.get_size();
                let wordsize = rel_ptr.get_word_size();
                let unknown = types_mut(glb).get_base(1, TypeMetatype::Unknown)?;
                newtype = types_mut(glb).get_type_pointer(size, unknown, wordsize)?;
            } else {
                newtype = alttype;
            }
        } else {
            newtype = alttype;
        }
        Ok(Some(newtype))
    }
}

impl TypeOp for TypeOpEqual {
    fn base(&self) -> &TypeOpBase {
        &self.base
    }

    fn base_mut(&mut self) -> &mut TypeOpBase {
        &mut self.base
    }

    fn set_metatype_in(&mut self, val: TypeMetatype) {
        self.meta.metain = val;
    }

    fn set_metatype_out(&mut self, val: TypeMetatype) {
        self.meta.metaout = val;
    }

    fn get_input_cast(
        &self,
        op: OpId,
        slot: i32,
        cast_strategy: &dyn CastStrategy,
        data: &mut Funcdata,
        glb: &mut Architecture,
    ) -> Result<Option<TypeId>> {
        equality_input_cast(op, slot, cast_strategy, data, glb)
    }

    fn propagate_type(
        &self,
        alttype: TypeId,
        op: OpId,
        invn: VarnodeId,
        outvn: VarnodeId,
        inslot: i32,
        outslot: i32,
        data: &mut Funcdata,
        glb: &mut Architecture,
    ) -> Result<Option<TypeId>> {
        TypeOpEqual::propagate_across_compare(alttype, invn, outvn, inslot, outslot, data, glb)
    }

    fn get_output_local(&self, op: OpId, data: &mut Funcdata, glb: &mut Architecture) -> Result<TypeId> {
        binary_get_output_local(&self.meta, op, data, glb)
    }

    fn get_input_local(&self, op: OpId, slot: i32, data: &mut Funcdata, glb: &mut Architecture) -> Result<TypeId> {
        binary_get_input_local(&self.meta, op, slot, data, glb)
    }

    fn print_raw(&mut self, out: &mut String, op: OpId, data: &Funcdata, glb: &Architecture) {
        binary_print_raw(&self.get_operator_name(op, data, glb), out, op, data, glb)
    }

    fn push(
        &self,
        lng: &mut dyn PrintLanguage,
        ctx: &mut PrintContext<'_>,
        op: OpId,
        read_op: Option<OpId>,
    ) -> Result<()> {
        lng.op_int_equal(ctx, op)
    }
}

pub struct TypeOpNotEqual {
    pub base: TypeOpBase,
    pub meta: TypeOpMeta,
}

impl Default for TypeOpNotEqual {
    fn default() -> Self {
        Self::new()
    }
}

impl TypeOpNotEqual {
    pub fn new() -> TypeOpNotEqual {
        TypeOpNotEqual {
            base: new_base(
                OpCode::IntNotequal,
                "!=",
                PcodeOp::BINARY | PcodeOp::BOOLOUTPUT | PcodeOp::COMMUTATIVE,
                INHERITS_SIGN,
                Arc::new(OpBehaviorNotEqual::new()),
            ),
            meta: TypeOpMeta::new(TypeMetatype::Bool, TypeMetatype::Int),
        }
    }
}

impl TypeOp for TypeOpNotEqual {
    fn base(&self) -> &TypeOpBase {
        &self.base
    }

    fn base_mut(&mut self) -> &mut TypeOpBase {
        &mut self.base
    }

    fn set_metatype_in(&mut self, val: TypeMetatype) {
        self.meta.metain = val;
    }

    fn set_metatype_out(&mut self, val: TypeMetatype) {
        self.meta.metaout = val;
    }

    fn get_input_cast(
        &self,
        op: OpId,
        slot: i32,
        cast_strategy: &dyn CastStrategy,
        data: &mut Funcdata,
        glb: &mut Architecture,
    ) -> Result<Option<TypeId>> {
        equality_input_cast(op, slot, cast_strategy, data, glb)
    }

    fn propagate_type(
        &self,
        alttype: TypeId,
        op: OpId,
        invn: VarnodeId,
        outvn: VarnodeId,
        inslot: i32,
        outslot: i32,
        data: &mut Funcdata,
        glb: &mut Architecture,
    ) -> Result<Option<TypeId>> {
        TypeOpEqual::propagate_across_compare(alttype, invn, outvn, inslot, outslot, data, glb)
    }

    fn get_output_local(&self, op: OpId, data: &mut Funcdata, glb: &mut Architecture) -> Result<TypeId> {
        binary_get_output_local(&self.meta, op, data, glb)
    }

    fn get_input_local(&self, op: OpId, slot: i32, data: &mut Funcdata, glb: &mut Architecture) -> Result<TypeId> {
        binary_get_input_local(&self.meta, op, slot, data, glb)
    }

    fn print_raw(&mut self, out: &mut String, op: OpId, data: &Funcdata, glb: &Architecture) {
        binary_print_raw(&self.get_operator_name(op, data, glb), out, op, data, glb)
    }

    fn push(
        &self,
        lng: &mut dyn PrintLanguage,
        ctx: &mut PrintContext<'_>,
        op: OpId,
        read_op: Option<OpId>,
    ) -> Result<()> {
        lng.op_int_not_equal(ctx, op)
    }
}

pub struct TypeOpIntSless {
    pub base: TypeOpBase,
    pub meta: TypeOpMeta,
}

impl Default for TypeOpIntSless {
    fn default() -> Self {
        Self::new()
    }
}

impl TypeOpIntSless {
    pub fn new() -> TypeOpIntSless {
        TypeOpIntSless {
            base: new_base(
                OpCode::IntSless,
                "<",
                PcodeOp::BINARY | PcodeOp::BOOLOUTPUT,
                INHERITS_SIGN,
                Arc::new(OpBehaviorIntSless::new()),
            ),
            meta: TypeOpMeta::new(TypeMetatype::Bool, TypeMetatype::Int),
        }
    }
}

impl TypeOp for TypeOpIntSless {
    fn base(&self) -> &TypeOpBase {
        &self.base
    }

    fn base_mut(&mut self) -> &mut TypeOpBase {
        &mut self.base
    }

    fn set_metatype_in(&mut self, val: TypeMetatype) {
        self.meta.metain = val;
    }

    fn set_metatype_out(&mut self, val: TypeMetatype) {
        self.meta.metaout = val;
    }

    fn print_raw(&mut self, out: &mut String, op: OpId, data: &Funcdata, glb: &Architecture) {
        binary_print_raw("s<", out, op, data, glb)
    }

    fn get_input_cast(
        &self,
        op: OpId,
        slot: i32,
        cast_strategy: &dyn CastStrategy,
        data: &mut Funcdata,
        glb: &mut Architecture,
    ) -> Result<Option<TypeId>> {
        compare_input_cast(self, op, slot, cast_strategy, true, data, glb)
    }

    fn propagate_type(
        &self,
        alttype: TypeId,
        op: OpId,
        invn: VarnodeId,
        outvn: VarnodeId,
        inslot: i32,
        outslot: i32,
        data: &mut Funcdata,
        glb: &mut Architecture,
    ) -> Result<Option<TypeId>> {
        if inslot == -1 || outslot == -1 {
            return Ok(None);
        }
        if types(glb).get(alttype).get_metatype() != TypeMetatype::Int {
            return Ok(None);
        }
        Ok(Some(alttype))
    }

    fn get_output_local(&self, op: OpId, data: &mut Funcdata, glb: &mut Architecture) -> Result<TypeId> {
        binary_get_output_local(&self.meta, op, data, glb)
    }

    fn get_input_local(&self, op: OpId, slot: i32, data: &mut Funcdata, glb: &mut Architecture) -> Result<TypeId> {
        binary_get_input_local(&self.meta, op, slot, data, glb)
    }

    fn push(
        &self,
        lng: &mut dyn PrintLanguage,
        ctx: &mut PrintContext<'_>,
        op: OpId,
        read_op: Option<OpId>,
    ) -> Result<()> {
        lng.op_int_sless(ctx, op)
    }
}

pub struct TypeOpIntSlessEqual {
    pub base: TypeOpBase,
    pub meta: TypeOpMeta,
}

impl Default for TypeOpIntSlessEqual {
    fn default() -> Self {
        Self::new()
    }
}

impl TypeOpIntSlessEqual {
    pub fn new() -> TypeOpIntSlessEqual {
        TypeOpIntSlessEqual {
            base: new_base(
                OpCode::IntSlessequal,
                "<=",
                PcodeOp::BINARY | PcodeOp::BOOLOUTPUT,
                INHERITS_SIGN,
                Arc::new(OpBehaviorIntSlessEqual::new()),
            ),
            meta: TypeOpMeta::new(TypeMetatype::Bool, TypeMetatype::Int),
        }
    }
}

impl TypeOp for TypeOpIntSlessEqual {
    fn base(&self) -> &TypeOpBase {
        &self.base
    }

    fn base_mut(&mut self) -> &mut TypeOpBase {
        &mut self.base
    }

    fn set_metatype_in(&mut self, val: TypeMetatype) {
        self.meta.metain = val;
    }

    fn set_metatype_out(&mut self, val: TypeMetatype) {
        self.meta.metaout = val;
    }

    fn print_raw(&mut self, out: &mut String, op: OpId, data: &Funcdata, glb: &Architecture) {
        binary_print_raw("s<=", out, op, data, glb)
    }

    fn get_input_cast(
        &self,
        op: OpId,
        slot: i32,
        cast_strategy: &dyn CastStrategy,
        data: &mut Funcdata,
        glb: &mut Architecture,
    ) -> Result<Option<TypeId>> {
        compare_input_cast(self, op, slot, cast_strategy, true, data, glb)
    }

    fn propagate_type(
        &self,
        alttype: TypeId,
        op: OpId,
        invn: VarnodeId,
        outvn: VarnodeId,
        inslot: i32,
        outslot: i32,
        data: &mut Funcdata,
        glb: &mut Architecture,
    ) -> Result<Option<TypeId>> {
        if inslot == -1 || outslot == -1 {
            return Ok(None);
        }
        if types(glb).get(alttype).get_metatype() != TypeMetatype::Int {
            return Ok(None);
        }
        Ok(Some(alttype))
    }

    fn get_output_local(&self, op: OpId, data: &mut Funcdata, glb: &mut Architecture) -> Result<TypeId> {
        binary_get_output_local(&self.meta, op, data, glb)
    }

    fn get_input_local(&self, op: OpId, slot: i32, data: &mut Funcdata, glb: &mut Architecture) -> Result<TypeId> {
        binary_get_input_local(&self.meta, op, slot, data, glb)
    }

    fn push(
        &self,
        lng: &mut dyn PrintLanguage,
        ctx: &mut PrintContext<'_>,
        op: OpId,
        read_op: Option<OpId>,
    ) -> Result<()> {
        lng.op_int_sless_equal(ctx, op)
    }
}

pub struct TypeOpIntLess {
    pub base: TypeOpBase,
    pub meta: TypeOpMeta,
}

impl Default for TypeOpIntLess {
    fn default() -> Self {
        Self::new()
    }
}

impl TypeOpIntLess {
    pub fn new() -> TypeOpIntLess {
        TypeOpIntLess {
            base: new_base(
                OpCode::IntLess,
                "<",
                PcodeOp::BINARY | PcodeOp::BOOLOUTPUT,
                INHERITS_SIGN,
                Arc::new(OpBehaviorIntLess::new()),
            ),
            meta: TypeOpMeta::new(TypeMetatype::Bool, TypeMetatype::Uint),
        }
    }
}

impl TypeOp for TypeOpIntLess {
    fn base(&self) -> &TypeOpBase {
        &self.base
    }

    fn base_mut(&mut self) -> &mut TypeOpBase {
        &mut self.base
    }

    fn set_metatype_in(&mut self, val: TypeMetatype) {
        self.meta.metain = val;
    }

    fn set_metatype_out(&mut self, val: TypeMetatype) {
        self.meta.metaout = val;
    }

    fn get_input_cast(
        &self,
        op: OpId,
        slot: i32,
        cast_strategy: &dyn CastStrategy,
        data: &mut Funcdata,
        glb: &mut Architecture,
    ) -> Result<Option<TypeId>> {
        compare_input_cast(self, op, slot, cast_strategy, false, data, glb)
    }

    fn propagate_type(
        &self,
        alttype: TypeId,
        op: OpId,
        invn: VarnodeId,
        outvn: VarnodeId,
        inslot: i32,
        outslot: i32,
        data: &mut Funcdata,
        glb: &mut Architecture,
    ) -> Result<Option<TypeId>> {
        TypeOpEqual::propagate_across_compare(alttype, invn, outvn, inslot, outslot, data, glb)
    }

    fn get_output_local(&self, op: OpId, data: &mut Funcdata, glb: &mut Architecture) -> Result<TypeId> {
        binary_get_output_local(&self.meta, op, data, glb)
    }

    fn get_input_local(&self, op: OpId, slot: i32, data: &mut Funcdata, glb: &mut Architecture) -> Result<TypeId> {
        binary_get_input_local(&self.meta, op, slot, data, glb)
    }

    fn print_raw(&mut self, out: &mut String, op: OpId, data: &Funcdata, glb: &Architecture) {
        binary_print_raw(&self.get_operator_name(op, data, glb), out, op, data, glb)
    }

    fn push(
        &self,
        lng: &mut dyn PrintLanguage,
        ctx: &mut PrintContext<'_>,
        op: OpId,
        read_op: Option<OpId>,
    ) -> Result<()> {
        lng.op_int_less(ctx, op)
    }
}

pub struct TypeOpIntLessEqual {
    pub base: TypeOpBase,
    pub meta: TypeOpMeta,
}

impl Default for TypeOpIntLessEqual {
    fn default() -> Self {
        Self::new()
    }
}

impl TypeOpIntLessEqual {
    pub fn new() -> TypeOpIntLessEqual {
        TypeOpIntLessEqual {
            base: new_base(
                OpCode::IntLessequal,
                "<=",
                PcodeOp::BINARY | PcodeOp::BOOLOUTPUT,
                INHERITS_SIGN,
                Arc::new(OpBehaviorIntLessEqual::new()),
            ),
            meta: TypeOpMeta::new(TypeMetatype::Bool, TypeMetatype::Uint),
        }
    }
}

impl TypeOp for TypeOpIntLessEqual {
    fn base(&self) -> &TypeOpBase {
        &self.base
    }

    fn base_mut(&mut self) -> &mut TypeOpBase {
        &mut self.base
    }

    fn set_metatype_in(&mut self, val: TypeMetatype) {
        self.meta.metain = val;
    }

    fn set_metatype_out(&mut self, val: TypeMetatype) {
        self.meta.metaout = val;
    }

    fn get_input_cast(
        &self,
        op: OpId,
        slot: i32,
        cast_strategy: &dyn CastStrategy,
        data: &mut Funcdata,
        glb: &mut Architecture,
    ) -> Result<Option<TypeId>> {
        compare_input_cast(self, op, slot, cast_strategy, false, data, glb)
    }

    fn propagate_type(
        &self,
        alttype: TypeId,
        op: OpId,
        invn: VarnodeId,
        outvn: VarnodeId,
        inslot: i32,
        outslot: i32,
        data: &mut Funcdata,
        glb: &mut Architecture,
    ) -> Result<Option<TypeId>> {
        TypeOpEqual::propagate_across_compare(alttype, invn, outvn, inslot, outslot, data, glb)
    }

    fn get_output_local(&self, op: OpId, data: &mut Funcdata, glb: &mut Architecture) -> Result<TypeId> {
        binary_get_output_local(&self.meta, op, data, glb)
    }

    fn get_input_local(&self, op: OpId, slot: i32, data: &mut Funcdata, glb: &mut Architecture) -> Result<TypeId> {
        binary_get_input_local(&self.meta, op, slot, data, glb)
    }

    fn print_raw(&mut self, out: &mut String, op: OpId, data: &Funcdata, glb: &Architecture) {
        binary_print_raw(&self.get_operator_name(op, data, glb), out, op, data, glb)
    }

    fn push(
        &self,
        lng: &mut dyn PrintLanguage,
        ctx: &mut PrintContext<'_>,
        op: OpId,
        read_op: Option<OpId>,
    ) -> Result<()> {
        lng.op_int_less_equal(ctx, op)
    }
}

pub struct TypeOpIntZext {
    pub base: TypeOpBase,
    pub meta: TypeOpMeta,
}

impl Default for TypeOpIntZext {
    fn default() -> Self {
        Self::new()
    }
}

impl TypeOpIntZext {
    pub fn new() -> TypeOpIntZext {
        TypeOpIntZext {
            base: new_base(
                OpCode::IntZext,
                "ZEXT",
                PcodeOp::UNARY,
                0,
                Arc::new(OpBehaviorIntZext::new()),
            ),
            meta: TypeOpMeta::new(TypeMetatype::Uint, TypeMetatype::Uint),
        }
    }
}

impl TypeOp for TypeOpIntZext {
    fn base(&self) -> &TypeOpBase {
        &self.base
    }

    fn base_mut(&mut self) -> &mut TypeOpBase {
        &mut self.base
    }

    fn set_metatype_in(&mut self, val: TypeMetatype) {
        self.meta.metain = val;
    }

    fn set_metatype_out(&mut self, val: TypeMetatype) {
        self.meta.metaout = val;
    }

    fn get_operator_name(&self, op: OpId, data: &Funcdata, glb: &Architecture) -> String {
        let pcode = data.op(op);
        format!(
            "{}{}{}",
            self.base.name,
            data.vn(pcode.get_in(0)).get_size(),
            data.vn(out_vn(data, op)).get_size()
        )
    }

    fn get_input_cast(
        &self,
        op: OpId,
        slot: i32,
        cast_strategy: &dyn CastStrategy,
        data: &mut Funcdata,
        glb: &mut Architecture,
    ) -> Result<Option<TypeId>> {
        let reqtype = self.get_input_local(op, slot, data, glb)?;
        if cast_strategy.check_int_promotion_for_extension(op, data, glb)? {
            return Ok(Some(reqtype));
        }
        let invn = data.op(op).get_in(slot);
        let curtype = data.vn_get_high_type_read_facing(invn, op, glb)?;
        Ok(cast_strategy.cast_standard(reqtype, curtype, true, false, types_mut(glb)))
    }

    fn get_output_local(&self, op: OpId, data: &mut Funcdata, glb: &mut Architecture) -> Result<TypeId> {
        func_get_output_local(&self.meta, op, data, glb)
    }

    fn get_input_local(&self, op: OpId, slot: i32, data: &mut Funcdata, glb: &mut Architecture) -> Result<TypeId> {
        func_get_input_local(&self.meta, op, slot, data, glb)
    }

    fn print_raw(&mut self, out: &mut String, op: OpId, data: &Funcdata, glb: &Architecture) {
        func_print_raw(&self.get_operator_name(op, data, glb), out, op, data, glb)
    }

    fn push(
        &self,
        lng: &mut dyn PrintLanguage,
        ctx: &mut PrintContext<'_>,
        op: OpId,
        read_op: Option<OpId>,
    ) -> Result<()> {
        lng.op_int_zext(ctx, op, read_op)
    }
}

pub struct TypeOpIntSext {
    pub base: TypeOpBase,
    pub meta: TypeOpMeta,
}

impl Default for TypeOpIntSext {
    fn default() -> Self {
        Self::new()
    }
}

impl TypeOpIntSext {
    pub fn new() -> TypeOpIntSext {
        TypeOpIntSext {
            base: new_base(
                OpCode::IntSext,
                "SEXT",
                PcodeOp::UNARY,
                0,
                Arc::new(OpBehaviorIntSext::new()),
            ),
            meta: TypeOpMeta::new(TypeMetatype::Int, TypeMetatype::Int),
        }
    }
}

impl TypeOp for TypeOpIntSext {
    fn base(&self) -> &TypeOpBase {
        &self.base
    }

    fn base_mut(&mut self) -> &mut TypeOpBase {
        &mut self.base
    }

    fn set_metatype_in(&mut self, val: TypeMetatype) {
        self.meta.metain = val;
    }

    fn set_metatype_out(&mut self, val: TypeMetatype) {
        self.meta.metaout = val;
    }

    fn get_operator_name(&self, op: OpId, data: &Funcdata, glb: &Architecture) -> String {
        let pcode = data.op(op);
        format!(
            "{}{}{}",
            self.base.name,
            data.vn(pcode.get_in(0)).get_size(),
            data.vn(out_vn(data, op)).get_size()
        )
    }

    fn get_input_cast(
        &self,
        op: OpId,
        slot: i32,
        cast_strategy: &dyn CastStrategy,
        data: &mut Funcdata,
        glb: &mut Architecture,
    ) -> Result<Option<TypeId>> {
        let reqtype = self.get_input_local(op, slot, data, glb)?;
        if cast_strategy.check_int_promotion_for_extension(op, data, glb)? {
            return Ok(Some(reqtype));
        }
        let invn = data.op(op).get_in(slot);
        let curtype = data.vn_get_high_type_read_facing(invn, op, glb)?;
        Ok(cast_strategy.cast_standard(reqtype, curtype, true, false, types_mut(glb)))
    }

    fn get_output_local(&self, op: OpId, data: &mut Funcdata, glb: &mut Architecture) -> Result<TypeId> {
        func_get_output_local(&self.meta, op, data, glb)
    }

    fn get_input_local(&self, op: OpId, slot: i32, data: &mut Funcdata, glb: &mut Architecture) -> Result<TypeId> {
        func_get_input_local(&self.meta, op, slot, data, glb)
    }

    fn print_raw(&mut self, out: &mut String, op: OpId, data: &Funcdata, glb: &Architecture) {
        func_print_raw(&self.get_operator_name(op, data, glb), out, op, data, glb)
    }

    fn push(
        &self,
        lng: &mut dyn PrintLanguage,
        ctx: &mut PrintContext<'_>,
        op: OpId,
        read_op: Option<OpId>,
    ) -> Result<()> {
        lng.op_int_sext(ctx, op, read_op)
    }
}

pub struct TypeOpIntAdd {
    pub base: TypeOpBase,
    pub meta: TypeOpMeta,
}

impl Default for TypeOpIntAdd {
    fn default() -> Self {
        Self::new()
    }
}

impl TypeOpIntAdd {
    pub fn new() -> TypeOpIntAdd {
        TypeOpIntAdd {
            base: new_base(
                OpCode::IntAdd,
                "+",
                PcodeOp::BINARY | PcodeOp::COMMUTATIVE,
                ARITHMETIC_OP | INHERITS_SIGN,
                Arc::new(OpBehaviorIntAdd::new()),
            ),
            meta: TypeOpMeta::new(TypeMetatype::Int, TypeMetatype::Int),
        }
    }

    pub fn propagate_add_in2_out(
        alttype: TypeId,
        op: OpId,
        inslot: i32,
        data: &mut Funcdata,
        glb: &mut Architecture,
    ) -> Result<Option<TypeId>> {
        let mut pointer = Some(alttype);
        let mut offset: u64 = 0;
        let factory = types(glb);
        let align_size = factory.get(factory.get(alttype).get_ptr_to()).get_align_size();
        let command = TypeOpIntAdd::propagate_add_pointer(&mut offset, op, inslot, align_size, data, factory);
        if command == 2 {
            return Ok(None);
        }
        let mut parent: Option<TypeId> = None;
        let mut parent_off: i64 = 0;
        if command != 3 {
            let mut type_offset =
                AddrSpace::address_to_byte_int(offset as i64, types(glb).get(alttype).get_word_size());
            let allow_wrap = data.op(op).code() != OpCode::Ptrsub;
            while let Some(current) = pointer {
                pointer =
                    Datatype::down_chain(current, &mut type_offset, &mut parent, &mut parent_off, allow_wrap, glb)?;
                if pointer.is_none() || type_offset == 0 {
                    break;
                }
            }
        }
        if let Some(parent) = parent {
            let pt = match pointer {
                None => types_mut(glb).get_base(1, TypeMetatype::Unknown)?,
                Some(current) => types(glb).get(current).get_ptr_to(),
            };
            pointer = Some(types_mut(glb).get_type_pointer_rel(parent, pt, parent_off as i32)?);
        }
        let Some(mut result) = pointer else {
            if command == 0 {
                return Ok(Some(alttype));
            }
            return Ok(None);
        };
        if data.vn(data.op(op).get_in(inslot)).is_spacebase() {
            let factory = types(glb);
            if factory.get(factory.get(result).get_ptr_to()).get_metatype() == TypeMetatype::Spacebase {
                let size = factory.get(result).get_size();
                let wordsize = factory.get(result).get_word_size();
                let unknown = types_mut(glb).get_base(1, TypeMetatype::Unknown)?;
                result = types_mut(glb).get_type_pointer(size, unknown, wordsize)?;
            }
        }
        Ok(Some(result))
    }

    pub fn propagate_add_pointer(
        off: &mut u64,
        op: OpId,
        slot: i32,
        sz: i32,
        data: &Funcdata,
        types: &TypeFactory,
    ) -> i32 {
        let pcode = data.op(op);
        let divisor = sz as i64 as u64;
        match pcode.code() {
            OpCode::Ptradd => {
                if slot != 0 {
                    return 2;
                }
                let constvn = data.vn(pcode.get_in(1));
                let mult = data.vn(pcode.get_in(2)).get_offset();
                if constvn.is_constant() {
                    *off = constvn.get_offset().wrapping_mul(mult) & calc_mask(constvn.get_size());
                    return if *off == 0 { 0 } else { 1 };
                }
                if sz != 0 && !mult.is_multiple_of(divisor) {
                    return 2;
                }
                3
            }
            OpCode::Ptrsub => {
                if slot != 0 {
                    return 2;
                }
                *off = data.vn(pcode.get_in(1)).get_offset();
                if *off == 0 { 0 } else { 1 }
            }
            OpCode::IntAdd => {
                let othervn = data.vn(pcode.get_in(1 - slot));
                if !othervn.is_constant() {
                    if othervn.is_written() {
                        let multop = data.op(othervn.get_def().expect("written varnode has no defining op"));
                        if multop.code() == OpCode::IntMult {
                            let constvn = data.vn(multop.get_in(1));
                            if constvn.is_constant() {
                                let mult = constvn.get_offset();
                                if mult == calc_mask(constvn.get_size()) {
                                    return 2;
                                }
                                if sz != 0 && !mult.is_multiple_of(divisor) {
                                    return 2;
                                }
                            }
                            return 3;
                        }
                    }
                    if sz == 1 {
                        return 3;
                    }
                    return 2;
                }
                let temp_is_pointer = othervn
                    .get_temp_type()
                    .is_some_and(|tp| types.get(tp).get_metatype() == TypeMetatype::Ptr);
                if temp_is_pointer {
                    return 2;
                }
                *off = othervn.get_offset();
                if *off == 0 { 0 } else { 1 }
            }
            _ => 2,
        }
    }
}

impl TypeOp for TypeOpIntAdd {
    fn base(&self) -> &TypeOpBase {
        &self.base
    }

    fn base_mut(&mut self) -> &mut TypeOpBase {
        &mut self.base
    }

    fn set_metatype_in(&mut self, val: TypeMetatype) {
        self.meta.metain = val;
    }

    fn set_metatype_out(&mut self, val: TypeMetatype) {
        self.meta.metaout = val;
    }

    fn get_output_token(
        &self,
        op: OpId,
        cast_strategy: &mut dyn CastStrategy,
        data: &mut Funcdata,
        glb: &mut Architecture,
    ) -> Result<TypeId> {
        cast_strategy.arithmetic_output_standard(op, data, glb)
    }

    fn propagate_type(
        &self,
        alttype: TypeId,
        op: OpId,
        invn: VarnodeId,
        outvn: VarnodeId,
        inslot: i32,
        outslot: i32,
        data: &mut Funcdata,
        glb: &mut Architecture,
    ) -> Result<Option<TypeId>> {
        let invn_meta = types(glb).get(alttype).get_metatype();
        if invn_meta != TypeMetatype::Ptr {
            if invn_meta != TypeMetatype::Int && invn_meta != TypeMetatype::Uint {
                return Ok(None);
            }
            if outslot != 1 || !data.vn(data.op(op).get_in(1)).is_constant() {
                return Ok(None);
            }
        } else if inslot != -1 && outslot != -1 {
            return Ok(None);
        }
        if data.vn(outvn).is_constant() && types(glb).get(alttype).get_metatype() != TypeMetatype::Ptr {
            Ok(Some(alttype))
        } else if inslot == -1 {
            Ok(None)
        } else {
            TypeOpIntAdd::propagate_add_in2_out(alttype, op, inslot, data, glb)
        }
    }

    fn get_output_local(&self, op: OpId, data: &mut Funcdata, glb: &mut Architecture) -> Result<TypeId> {
        binary_get_output_local(&self.meta, op, data, glb)
    }

    fn get_input_local(&self, op: OpId, slot: i32, data: &mut Funcdata, glb: &mut Architecture) -> Result<TypeId> {
        binary_get_input_local(&self.meta, op, slot, data, glb)
    }

    fn print_raw(&mut self, out: &mut String, op: OpId, data: &Funcdata, glb: &Architecture) {
        binary_print_raw(&self.get_operator_name(op, data, glb), out, op, data, glb)
    }

    fn push(
        &self,
        lng: &mut dyn PrintLanguage,
        ctx: &mut PrintContext<'_>,
        op: OpId,
        read_op: Option<OpId>,
    ) -> Result<()> {
        lng.op_int_add(ctx, op)
    }
}

pub struct TypeOpIntSub {
    pub base: TypeOpBase,
    pub meta: TypeOpMeta,
}

impl Default for TypeOpIntSub {
    fn default() -> Self {
        Self::new()
    }
}

impl TypeOpIntSub {
    pub fn new() -> TypeOpIntSub {
        TypeOpIntSub {
            base: new_base(
                OpCode::IntSub,
                "-",
                PcodeOp::BINARY,
                ARITHMETIC_OP | INHERITS_SIGN,
                Arc::new(OpBehaviorIntSub::new()),
            ),
            meta: TypeOpMeta::new(TypeMetatype::Int, TypeMetatype::Int),
        }
    }
}

impl TypeOp for TypeOpIntSub {
    fn base(&self) -> &TypeOpBase {
        &self.base
    }

    fn base_mut(&mut self) -> &mut TypeOpBase {
        &mut self.base
    }

    fn set_metatype_in(&mut self, val: TypeMetatype) {
        self.meta.metain = val;
    }

    fn set_metatype_out(&mut self, val: TypeMetatype) {
        self.meta.metaout = val;
    }

    fn get_output_token(
        &self,
        op: OpId,
        cast_strategy: &mut dyn CastStrategy,
        data: &mut Funcdata,
        glb: &mut Architecture,
    ) -> Result<TypeId> {
        cast_strategy.arithmetic_output_standard(op, data, glb)
    }

    fn get_output_local(&self, op: OpId, data: &mut Funcdata, glb: &mut Architecture) -> Result<TypeId> {
        binary_get_output_local(&self.meta, op, data, glb)
    }

    fn get_input_local(&self, op: OpId, slot: i32, data: &mut Funcdata, glb: &mut Architecture) -> Result<TypeId> {
        binary_get_input_local(&self.meta, op, slot, data, glb)
    }

    fn print_raw(&mut self, out: &mut String, op: OpId, data: &Funcdata, glb: &Architecture) {
        binary_print_raw(&self.get_operator_name(op, data, glb), out, op, data, glb)
    }

    fn push(
        &self,
        lng: &mut dyn PrintLanguage,
        ctx: &mut PrintContext<'_>,
        op: OpId,
        read_op: Option<OpId>,
    ) -> Result<()> {
        lng.op_int_sub(ctx, op)
    }
}

pub struct TypeOpIntCarry {
    pub base: TypeOpBase,
    pub meta: TypeOpMeta,
}

impl Default for TypeOpIntCarry {
    fn default() -> Self {
        Self::new()
    }
}

impl TypeOpIntCarry {
    pub fn new() -> TypeOpIntCarry {
        TypeOpIntCarry {
            base: new_base(
                OpCode::IntCarry,
                "CARRY",
                PcodeOp::BINARY | PcodeOp::COMMUTATIVE | PcodeOp::BOOLOUTPUT,
                ARITHMETIC_OP,
                Arc::new(OpBehaviorIntCarry::new()),
            ),
            meta: TypeOpMeta::new(TypeMetatype::Bool, TypeMetatype::Uint),
        }
    }
}

impl TypeOp for TypeOpIntCarry {
    fn base(&self) -> &TypeOpBase {
        &self.base
    }

    fn base_mut(&mut self) -> &mut TypeOpBase {
        &mut self.base
    }

    fn set_metatype_in(&mut self, val: TypeMetatype) {
        self.meta.metain = val;
    }

    fn set_metatype_out(&mut self, val: TypeMetatype) {
        self.meta.metaout = val;
    }

    fn get_operator_name(&self, op: OpId, data: &Funcdata, glb: &Architecture) -> String {
        format!("{}{}", self.base.name, data.vn(data.op(op).get_in(0)).get_size())
    }

    fn get_output_local(&self, op: OpId, data: &mut Funcdata, glb: &mut Architecture) -> Result<TypeId> {
        func_get_output_local(&self.meta, op, data, glb)
    }

    fn get_input_local(&self, op: OpId, slot: i32, data: &mut Funcdata, glb: &mut Architecture) -> Result<TypeId> {
        func_get_input_local(&self.meta, op, slot, data, glb)
    }

    fn print_raw(&mut self, out: &mut String, op: OpId, data: &Funcdata, glb: &Architecture) {
        func_print_raw(&self.get_operator_name(op, data, glb), out, op, data, glb)
    }

    fn push(
        &self,
        lng: &mut dyn PrintLanguage,
        ctx: &mut PrintContext<'_>,
        op: OpId,
        read_op: Option<OpId>,
    ) -> Result<()> {
        lng.op_int_carry(ctx, op)
    }
}

pub struct TypeOpIntScarry {
    pub base: TypeOpBase,
    pub meta: TypeOpMeta,
}

impl Default for TypeOpIntScarry {
    fn default() -> Self {
        Self::new()
    }
}

impl TypeOpIntScarry {
    pub fn new() -> TypeOpIntScarry {
        TypeOpIntScarry {
            base: new_base(
                OpCode::IntScarry,
                "SCARRY",
                PcodeOp::BINARY | PcodeOp::COMMUTATIVE | PcodeOp::BOOLOUTPUT,
                ARITHMETIC_OP,
                Arc::new(OpBehaviorIntScarry::new()),
            ),
            meta: TypeOpMeta::new(TypeMetatype::Bool, TypeMetatype::Int),
        }
    }
}

impl TypeOp for TypeOpIntScarry {
    fn base(&self) -> &TypeOpBase {
        &self.base
    }

    fn base_mut(&mut self) -> &mut TypeOpBase {
        &mut self.base
    }

    fn set_metatype_in(&mut self, val: TypeMetatype) {
        self.meta.metain = val;
    }

    fn set_metatype_out(&mut self, val: TypeMetatype) {
        self.meta.metaout = val;
    }

    fn get_operator_name(&self, op: OpId, data: &Funcdata, glb: &Architecture) -> String {
        format!("{}{}", self.base.name, data.vn(data.op(op).get_in(0)).get_size())
    }

    fn get_output_local(&self, op: OpId, data: &mut Funcdata, glb: &mut Architecture) -> Result<TypeId> {
        func_get_output_local(&self.meta, op, data, glb)
    }

    fn get_input_local(&self, op: OpId, slot: i32, data: &mut Funcdata, glb: &mut Architecture) -> Result<TypeId> {
        func_get_input_local(&self.meta, op, slot, data, glb)
    }

    fn print_raw(&mut self, out: &mut String, op: OpId, data: &Funcdata, glb: &Architecture) {
        func_print_raw(&self.get_operator_name(op, data, glb), out, op, data, glb)
    }

    fn push(
        &self,
        lng: &mut dyn PrintLanguage,
        ctx: &mut PrintContext<'_>,
        op: OpId,
        read_op: Option<OpId>,
    ) -> Result<()> {
        lng.op_int_scarry(ctx, op)
    }
}

pub struct TypeOpIntSborrow {
    pub base: TypeOpBase,
    pub meta: TypeOpMeta,
}

impl Default for TypeOpIntSborrow {
    fn default() -> Self {
        Self::new()
    }
}

impl TypeOpIntSborrow {
    pub fn new() -> TypeOpIntSborrow {
        TypeOpIntSborrow {
            base: new_base(
                OpCode::IntSborrow,
                "SBORROW",
                PcodeOp::BINARY | PcodeOp::BOOLOUTPUT,
                ARITHMETIC_OP,
                Arc::new(OpBehaviorIntSborrow::new()),
            ),
            meta: TypeOpMeta::new(TypeMetatype::Bool, TypeMetatype::Int),
        }
    }
}

impl TypeOp for TypeOpIntSborrow {
    fn base(&self) -> &TypeOpBase {
        &self.base
    }

    fn base_mut(&mut self) -> &mut TypeOpBase {
        &mut self.base
    }

    fn set_metatype_in(&mut self, val: TypeMetatype) {
        self.meta.metain = val;
    }

    fn set_metatype_out(&mut self, val: TypeMetatype) {
        self.meta.metaout = val;
    }

    fn get_operator_name(&self, op: OpId, data: &Funcdata, glb: &Architecture) -> String {
        format!("{}{}", self.base.name, data.vn(data.op(op).get_in(0)).get_size())
    }

    fn get_output_local(&self, op: OpId, data: &mut Funcdata, glb: &mut Architecture) -> Result<TypeId> {
        func_get_output_local(&self.meta, op, data, glb)
    }

    fn get_input_local(&self, op: OpId, slot: i32, data: &mut Funcdata, glb: &mut Architecture) -> Result<TypeId> {
        func_get_input_local(&self.meta, op, slot, data, glb)
    }

    fn print_raw(&mut self, out: &mut String, op: OpId, data: &Funcdata, glb: &Architecture) {
        func_print_raw(&self.get_operator_name(op, data, glb), out, op, data, glb)
    }

    fn push(
        &self,
        lng: &mut dyn PrintLanguage,
        ctx: &mut PrintContext<'_>,
        op: OpId,
        read_op: Option<OpId>,
    ) -> Result<()> {
        lng.op_int_sborrow(ctx, op)
    }
}

pub struct TypeOpInt2Comp {
    pub base: TypeOpBase,
    pub meta: TypeOpMeta,
}

impl Default for TypeOpInt2Comp {
    fn default() -> Self {
        Self::new()
    }
}

impl TypeOpInt2Comp {
    pub fn new() -> TypeOpInt2Comp {
        TypeOpInt2Comp {
            base: new_base(
                OpCode::Int2comp,
                "-",
                PcodeOp::UNARY,
                ARITHMETIC_OP | INHERITS_SIGN,
                Arc::new(OpBehaviorInt2Comp::new()),
            ),
            meta: TypeOpMeta::new(TypeMetatype::Int, TypeMetatype::Int),
        }
    }
}

impl TypeOp for TypeOpInt2Comp {
    fn base(&self) -> &TypeOpBase {
        &self.base
    }

    fn base_mut(&mut self) -> &mut TypeOpBase {
        &mut self.base
    }

    fn set_metatype_in(&mut self, val: TypeMetatype) {
        self.meta.metain = val;
    }

    fn set_metatype_out(&mut self, val: TypeMetatype) {
        self.meta.metaout = val;
    }

    fn get_output_token(
        &self,
        op: OpId,
        cast_strategy: &mut dyn CastStrategy,
        data: &mut Funcdata,
        glb: &mut Architecture,
    ) -> Result<TypeId> {
        cast_strategy.arithmetic_output_standard(op, data, glb)
    }

    fn get_output_local(&self, op: OpId, data: &mut Funcdata, glb: &mut Architecture) -> Result<TypeId> {
        unary_get_output_local(&self.meta, op, data, glb)
    }

    fn get_input_local(&self, op: OpId, slot: i32, data: &mut Funcdata, glb: &mut Architecture) -> Result<TypeId> {
        unary_get_input_local(&self.meta, op, slot, data, glb)
    }

    fn print_raw(&mut self, out: &mut String, op: OpId, data: &Funcdata, glb: &Architecture) {
        unary_print_raw(&self.get_operator_name(op, data, glb), out, op, data, glb)
    }

    fn push(
        &self,
        lng: &mut dyn PrintLanguage,
        ctx: &mut PrintContext<'_>,
        op: OpId,
        read_op: Option<OpId>,
    ) -> Result<()> {
        lng.op_int_2comp(ctx, op)
    }
}

pub struct TypeOpIntNegate {
    pub base: TypeOpBase,
    pub meta: TypeOpMeta,
}

impl Default for TypeOpIntNegate {
    fn default() -> Self {
        Self::new()
    }
}

impl TypeOpIntNegate {
    pub fn new() -> TypeOpIntNegate {
        TypeOpIntNegate {
            base: new_base(
                OpCode::IntNegate,
                "~",
                PcodeOp::UNARY,
                LOGICAL_OP | INHERITS_SIGN,
                Arc::new(OpBehaviorIntNegate::new()),
            ),
            meta: TypeOpMeta::new(TypeMetatype::Uint, TypeMetatype::Uint),
        }
    }
}

impl TypeOp for TypeOpIntNegate {
    fn base(&self) -> &TypeOpBase {
        &self.base
    }

    fn base_mut(&mut self) -> &mut TypeOpBase {
        &mut self.base
    }

    fn set_metatype_in(&mut self, val: TypeMetatype) {
        self.meta.metain = val;
    }

    fn set_metatype_out(&mut self, val: TypeMetatype) {
        self.meta.metaout = val;
    }

    fn get_output_token(
        &self,
        op: OpId,
        cast_strategy: &mut dyn CastStrategy,
        data: &mut Funcdata,
        glb: &mut Architecture,
    ) -> Result<TypeId> {
        cast_strategy.arithmetic_output_standard(op, data, glb)
    }

    fn get_output_local(&self, op: OpId, data: &mut Funcdata, glb: &mut Architecture) -> Result<TypeId> {
        unary_get_output_local(&self.meta, op, data, glb)
    }

    fn get_input_local(&self, op: OpId, slot: i32, data: &mut Funcdata, glb: &mut Architecture) -> Result<TypeId> {
        unary_get_input_local(&self.meta, op, slot, data, glb)
    }

    fn print_raw(&mut self, out: &mut String, op: OpId, data: &Funcdata, glb: &Architecture) {
        unary_print_raw(&self.get_operator_name(op, data, glb), out, op, data, glb)
    }

    fn push(
        &self,
        lng: &mut dyn PrintLanguage,
        ctx: &mut PrintContext<'_>,
        op: OpId,
        read_op: Option<OpId>,
    ) -> Result<()> {
        lng.op_int_negate(ctx, op)
    }
}

pub struct TypeOpIntXor {
    pub base: TypeOpBase,
    pub meta: TypeOpMeta,
}

impl Default for TypeOpIntXor {
    fn default() -> Self {
        Self::new()
    }
}

impl TypeOpIntXor {
    pub fn new() -> TypeOpIntXor {
        TypeOpIntXor {
            base: new_base(
                OpCode::IntXor,
                "^",
                PcodeOp::BINARY | PcodeOp::COMMUTATIVE,
                LOGICAL_OP | INHERITS_SIGN,
                Arc::new(OpBehaviorIntXor::new()),
            ),
            meta: TypeOpMeta::new(TypeMetatype::Uint, TypeMetatype::Uint),
        }
    }
}

impl TypeOp for TypeOpIntXor {
    fn base(&self) -> &TypeOpBase {
        &self.base
    }

    fn base_mut(&mut self) -> &mut TypeOpBase {
        &mut self.base
    }

    fn set_metatype_in(&mut self, val: TypeMetatype) {
        self.meta.metain = val;
    }

    fn set_metatype_out(&mut self, val: TypeMetatype) {
        self.meta.metaout = val;
    }

    fn get_output_token(
        &self,
        op: OpId,
        cast_strategy: &mut dyn CastStrategy,
        data: &mut Funcdata,
        glb: &mut Architecture,
    ) -> Result<TypeId> {
        cast_strategy.arithmetic_output_standard(op, data, glb)
    }

    fn propagate_type(
        &self,
        alttype: TypeId,
        op: OpId,
        invn: VarnodeId,
        outvn: VarnodeId,
        inslot: i32,
        outslot: i32,
        data: &mut Funcdata,
        glb: &mut Architecture,
    ) -> Result<Option<TypeId>> {
        let factory = types(glb);
        if !factory.get(alttype).is_enum_type() {
            if factory.get(alttype).get_metatype() != TypeMetatype::Float {
                return Ok(None);
            }
            if float_sign_manipulation(op, data) == OpCode::Max {
                return Ok(None);
            }
        }
        pass_through_type(alttype, invn, data, glb).map(Some)
    }

    fn get_output_local(&self, op: OpId, data: &mut Funcdata, glb: &mut Architecture) -> Result<TypeId> {
        binary_get_output_local(&self.meta, op, data, glb)
    }

    fn get_input_local(&self, op: OpId, slot: i32, data: &mut Funcdata, glb: &mut Architecture) -> Result<TypeId> {
        binary_get_input_local(&self.meta, op, slot, data, glb)
    }

    fn print_raw(&mut self, out: &mut String, op: OpId, data: &Funcdata, glb: &Architecture) {
        binary_print_raw(&self.get_operator_name(op, data, glb), out, op, data, glb)
    }

    fn push(
        &self,
        lng: &mut dyn PrintLanguage,
        ctx: &mut PrintContext<'_>,
        op: OpId,
        read_op: Option<OpId>,
    ) -> Result<()> {
        lng.op_int_xor(ctx, op)
    }
}

pub struct TypeOpIntAnd {
    pub base: TypeOpBase,
    pub meta: TypeOpMeta,
}

impl Default for TypeOpIntAnd {
    fn default() -> Self {
        Self::new()
    }
}

impl TypeOpIntAnd {
    pub fn new() -> TypeOpIntAnd {
        TypeOpIntAnd {
            base: new_base(
                OpCode::IntAnd,
                "&",
                PcodeOp::BINARY | PcodeOp::COMMUTATIVE,
                LOGICAL_OP | INHERITS_SIGN,
                Arc::new(OpBehaviorIntAnd::new()),
            ),
            meta: TypeOpMeta::new(TypeMetatype::Uint, TypeMetatype::Uint),
        }
    }
}

impl TypeOp for TypeOpIntAnd {
    fn base(&self) -> &TypeOpBase {
        &self.base
    }

    fn base_mut(&mut self) -> &mut TypeOpBase {
        &mut self.base
    }

    fn set_metatype_in(&mut self, val: TypeMetatype) {
        self.meta.metain = val;
    }

    fn set_metatype_out(&mut self, val: TypeMetatype) {
        self.meta.metaout = val;
    }

    fn get_output_token(
        &self,
        op: OpId,
        cast_strategy: &mut dyn CastStrategy,
        data: &mut Funcdata,
        glb: &mut Architecture,
    ) -> Result<TypeId> {
        cast_strategy.arithmetic_output_standard(op, data, glb)
    }

    fn propagate_type(
        &self,
        alttype: TypeId,
        op: OpId,
        invn: VarnodeId,
        outvn: VarnodeId,
        inslot: i32,
        outslot: i32,
        data: &mut Funcdata,
        glb: &mut Architecture,
    ) -> Result<Option<TypeId>> {
        let factory = types(glb);
        if !factory.get(alttype).is_enum_type() {
            if factory.get(alttype).get_metatype() != TypeMetatype::Float {
                return Ok(None);
            }
            if float_sign_manipulation(op, data) == OpCode::Max {
                return Ok(None);
            }
        }
        pass_through_type(alttype, invn, data, glb).map(Some)
    }

    fn get_output_local(&self, op: OpId, data: &mut Funcdata, glb: &mut Architecture) -> Result<TypeId> {
        binary_get_output_local(&self.meta, op, data, glb)
    }

    fn get_input_local(&self, op: OpId, slot: i32, data: &mut Funcdata, glb: &mut Architecture) -> Result<TypeId> {
        binary_get_input_local(&self.meta, op, slot, data, glb)
    }

    fn print_raw(&mut self, out: &mut String, op: OpId, data: &Funcdata, glb: &Architecture) {
        binary_print_raw(&self.get_operator_name(op, data, glb), out, op, data, glb)
    }

    fn push(
        &self,
        lng: &mut dyn PrintLanguage,
        ctx: &mut PrintContext<'_>,
        op: OpId,
        read_op: Option<OpId>,
    ) -> Result<()> {
        lng.op_int_and(ctx, op)
    }
}

pub struct TypeOpIntOr {
    pub base: TypeOpBase,
    pub meta: TypeOpMeta,
}

impl Default for TypeOpIntOr {
    fn default() -> Self {
        Self::new()
    }
}

impl TypeOpIntOr {
    pub fn new() -> TypeOpIntOr {
        TypeOpIntOr {
            base: new_base(
                OpCode::IntOr,
                "|",
                PcodeOp::BINARY | PcodeOp::COMMUTATIVE,
                LOGICAL_OP | INHERITS_SIGN,
                Arc::new(OpBehaviorIntOr::new()),
            ),
            meta: TypeOpMeta::new(TypeMetatype::Uint, TypeMetatype::Uint),
        }
    }
}

impl TypeOp for TypeOpIntOr {
    fn base(&self) -> &TypeOpBase {
        &self.base
    }

    fn base_mut(&mut self) -> &mut TypeOpBase {
        &mut self.base
    }

    fn set_metatype_in(&mut self, val: TypeMetatype) {
        self.meta.metain = val;
    }

    fn set_metatype_out(&mut self, val: TypeMetatype) {
        self.meta.metaout = val;
    }

    fn get_output_token(
        &self,
        op: OpId,
        cast_strategy: &mut dyn CastStrategy,
        data: &mut Funcdata,
        glb: &mut Architecture,
    ) -> Result<TypeId> {
        cast_strategy.arithmetic_output_standard(op, data, glb)
    }

    fn propagate_type(
        &self,
        alttype: TypeId,
        op: OpId,
        invn: VarnodeId,
        outvn: VarnodeId,
        inslot: i32,
        outslot: i32,
        data: &mut Funcdata,
        glb: &mut Architecture,
    ) -> Result<Option<TypeId>> {
        if !types(glb).get(alttype).is_enum_type() {
            return Ok(None);
        }
        pass_through_type(alttype, invn, data, glb).map(Some)
    }

    fn get_output_local(&self, op: OpId, data: &mut Funcdata, glb: &mut Architecture) -> Result<TypeId> {
        binary_get_output_local(&self.meta, op, data, glb)
    }

    fn get_input_local(&self, op: OpId, slot: i32, data: &mut Funcdata, glb: &mut Architecture) -> Result<TypeId> {
        binary_get_input_local(&self.meta, op, slot, data, glb)
    }

    fn print_raw(&mut self, out: &mut String, op: OpId, data: &Funcdata, glb: &Architecture) {
        binary_print_raw(&self.get_operator_name(op, data, glb), out, op, data, glb)
    }

    fn push(
        &self,
        lng: &mut dyn PrintLanguage,
        ctx: &mut PrintContext<'_>,
        op: OpId,
        read_op: Option<OpId>,
    ) -> Result<()> {
        lng.op_int_or(ctx, op)
    }
}

pub struct TypeOpIntLeft {
    pub base: TypeOpBase,
    pub meta: TypeOpMeta,
}

impl Default for TypeOpIntLeft {
    fn default() -> Self {
        Self::new()
    }
}

impl TypeOpIntLeft {
    pub fn new() -> TypeOpIntLeft {
        TypeOpIntLeft {
            base: new_base(
                OpCode::IntLeft,
                "<<",
                PcodeOp::BINARY,
                INHERITS_SIGN | INHERITS_SIGN_ZERO | SHIFT_OP,
                Arc::new(OpBehaviorIntLeft::new()),
            ),
            meta: TypeOpMeta::new(TypeMetatype::Int, TypeMetatype::Int),
        }
    }
}

impl TypeOp for TypeOpIntLeft {
    fn base(&self) -> &TypeOpBase {
        &self.base
    }

    fn base_mut(&mut self) -> &mut TypeOpBase {
        &mut self.base
    }

    fn set_metatype_in(&mut self, val: TypeMetatype) {
        self.meta.metain = val;
    }

    fn set_metatype_out(&mut self, val: TypeMetatype) {
        self.meta.metaout = val;
    }

    fn get_input_local(&self, op: OpId, slot: i32, data: &mut Funcdata, glb: &mut Architecture) -> Result<TypeId> {
        if slot == 1 {
            let size = data.vn(data.op(op).get_in(1)).get_size();
            return types_mut(glb).get_base_no_char(size, TypeMetatype::Int);
        }
        binary_get_input_local(&self.meta, op, slot, data, glb)
    }

    fn get_output_token(
        &self,
        op: OpId,
        cast_strategy: &mut dyn CastStrategy,
        data: &mut Funcdata,
        glb: &mut Architecture,
    ) -> Result<TypeId> {
        let invn = data.op(op).get_in(0);
        let res1 = data.vn_get_high_type_read_facing(invn, op, glb)?;
        if types(glb).get(res1).get_metatype() == TypeMetatype::Bool {
            let size = types(glb).get(res1).get_size();
            return types_mut(glb).get_base(size, TypeMetatype::Int);
        }
        Ok(res1)
    }

    fn get_output_local(&self, op: OpId, data: &mut Funcdata, glb: &mut Architecture) -> Result<TypeId> {
        binary_get_output_local(&self.meta, op, data, glb)
    }

    fn print_raw(&mut self, out: &mut String, op: OpId, data: &Funcdata, glb: &Architecture) {
        binary_print_raw(&self.get_operator_name(op, data, glb), out, op, data, glb)
    }

    fn push(
        &self,
        lng: &mut dyn PrintLanguage,
        ctx: &mut PrintContext<'_>,
        op: OpId,
        read_op: Option<OpId>,
    ) -> Result<()> {
        lng.op_int_left(ctx, op)
    }
}

pub struct TypeOpIntRight {
    pub base: TypeOpBase,
    pub meta: TypeOpMeta,
}

impl Default for TypeOpIntRight {
    fn default() -> Self {
        Self::new()
    }
}

impl TypeOpIntRight {
    pub fn new() -> TypeOpIntRight {
        TypeOpIntRight {
            base: new_base(
                OpCode::IntRight,
                ">>",
                PcodeOp::BINARY,
                INHERITS_SIGN | INHERITS_SIGN_ZERO | SHIFT_OP,
                Arc::new(OpBehaviorIntRight::new()),
            ),
            meta: TypeOpMeta::new(TypeMetatype::Uint, TypeMetatype::Uint),
        }
    }
}

impl TypeOp for TypeOpIntRight {
    fn base(&self) -> &TypeOpBase {
        &self.base
    }

    fn base_mut(&mut self) -> &mut TypeOpBase {
        &mut self.base
    }

    fn set_metatype_in(&mut self, val: TypeMetatype) {
        self.meta.metain = val;
    }

    fn set_metatype_out(&mut self, val: TypeMetatype) {
        self.meta.metaout = val;
    }

    fn get_input_cast(
        &self,
        op: OpId,
        slot: i32,
        cast_strategy: &dyn CastStrategy,
        data: &mut Funcdata,
        glb: &mut Architecture,
    ) -> Result<Option<TypeId>> {
        if slot == 0 {
            return extension_input_cast(self, op, slot, cast_strategy, UNSIGNED_EXTENSION, data, glb);
        }
        base_input_cast(self, op, slot, cast_strategy, data, glb)
    }

    fn get_input_local(&self, op: OpId, slot: i32, data: &mut Funcdata, glb: &mut Architecture) -> Result<TypeId> {
        if slot == 1 {
            let size = data.vn(data.op(op).get_in(1)).get_size();
            return types_mut(glb).get_base_no_char(size, TypeMetatype::Int);
        }
        binary_get_input_local(&self.meta, op, slot, data, glb)
    }

    fn get_output_token(
        &self,
        op: OpId,
        cast_strategy: &mut dyn CastStrategy,
        data: &mut Funcdata,
        glb: &mut Architecture,
    ) -> Result<TypeId> {
        let invn = data.op(op).get_in(0);
        let res1 = data.vn_get_high_type_read_facing(invn, op, glb)?;
        if types(glb).get(res1).get_metatype() == TypeMetatype::Bool {
            let size = types(glb).get(res1).get_size();
            return types_mut(glb).get_base(size, TypeMetatype::Int);
        }
        Ok(res1)
    }

    fn get_output_local(&self, op: OpId, data: &mut Funcdata, glb: &mut Architecture) -> Result<TypeId> {
        binary_get_output_local(&self.meta, op, data, glb)
    }

    fn print_raw(&mut self, out: &mut String, op: OpId, data: &Funcdata, glb: &Architecture) {
        binary_print_raw(&self.get_operator_name(op, data, glb), out, op, data, glb)
    }

    fn push(
        &self,
        lng: &mut dyn PrintLanguage,
        ctx: &mut PrintContext<'_>,
        op: OpId,
        read_op: Option<OpId>,
    ) -> Result<()> {
        lng.op_int_right(ctx, op)
    }
}

pub struct TypeOpIntSright {
    pub base: TypeOpBase,
    pub meta: TypeOpMeta,
}

impl Default for TypeOpIntSright {
    fn default() -> Self {
        Self::new()
    }
}

impl TypeOpIntSright {
    pub fn new() -> TypeOpIntSright {
        TypeOpIntSright {
            base: new_base(
                OpCode::IntSright,
                ">>",
                PcodeOp::BINARY,
                INHERITS_SIGN | INHERITS_SIGN_ZERO | SHIFT_OP,
                Arc::new(OpBehaviorIntSright::new()),
            ),
            meta: TypeOpMeta::new(TypeMetatype::Int, TypeMetatype::Int),
        }
    }
}

impl TypeOp for TypeOpIntSright {
    fn base(&self) -> &TypeOpBase {
        &self.base
    }

    fn base_mut(&mut self) -> &mut TypeOpBase {
        &mut self.base
    }

    fn set_metatype_in(&mut self, val: TypeMetatype) {
        self.meta.metain = val;
    }

    fn set_metatype_out(&mut self, val: TypeMetatype) {
        self.meta.metaout = val;
    }

    fn print_raw(&mut self, out: &mut String, op: OpId, data: &Funcdata, glb: &Architecture) {
        binary_print_raw("s>>", out, op, data, glb)
    }

    fn get_input_cast(
        &self,
        op: OpId,
        slot: i32,
        cast_strategy: &dyn CastStrategy,
        data: &mut Funcdata,
        glb: &mut Architecture,
    ) -> Result<Option<TypeId>> {
        if slot == 0 {
            return extension_input_cast(self, op, slot, cast_strategy, SIGNED_EXTENSION, data, glb);
        }
        base_input_cast(self, op, slot, cast_strategy, data, glb)
    }

    fn get_input_local(&self, op: OpId, slot: i32, data: &mut Funcdata, glb: &mut Architecture) -> Result<TypeId> {
        if slot == 1 {
            let size = data.vn(data.op(op).get_in(1)).get_size();
            return types_mut(glb).get_base_no_char(size, TypeMetatype::Int);
        }
        binary_get_input_local(&self.meta, op, slot, data, glb)
    }

    fn get_output_token(
        &self,
        op: OpId,
        cast_strategy: &mut dyn CastStrategy,
        data: &mut Funcdata,
        glb: &mut Architecture,
    ) -> Result<TypeId> {
        let invn = data.op(op).get_in(0);
        let res1 = data.vn_get_high_type_read_facing(invn, op, glb)?;
        if types(glb).get(res1).get_metatype() == TypeMetatype::Bool {
            let size = types(glb).get(res1).get_size();
            return types_mut(glb).get_base(size, TypeMetatype::Int);
        }
        Ok(res1)
    }

    fn get_output_local(&self, op: OpId, data: &mut Funcdata, glb: &mut Architecture) -> Result<TypeId> {
        binary_get_output_local(&self.meta, op, data, glb)
    }

    fn push(
        &self,
        lng: &mut dyn PrintLanguage,
        ctx: &mut PrintContext<'_>,
        op: OpId,
        read_op: Option<OpId>,
    ) -> Result<()> {
        lng.op_int_sright(ctx, op)
    }
}

pub struct TypeOpIntMult {
    pub base: TypeOpBase,
    pub meta: TypeOpMeta,
}

impl Default for TypeOpIntMult {
    fn default() -> Self {
        Self::new()
    }
}

impl TypeOpIntMult {
    pub fn new() -> TypeOpIntMult {
        TypeOpIntMult {
            base: new_base(
                OpCode::IntMult,
                "*",
                PcodeOp::BINARY | PcodeOp::COMMUTATIVE,
                ARITHMETIC_OP | INHERITS_SIGN,
                Arc::new(OpBehaviorIntMult::new()),
            ),
            meta: TypeOpMeta::new(TypeMetatype::Int, TypeMetatype::Int),
        }
    }
}

impl TypeOp for TypeOpIntMult {
    fn base(&self) -> &TypeOpBase {
        &self.base
    }

    fn base_mut(&mut self) -> &mut TypeOpBase {
        &mut self.base
    }

    fn set_metatype_in(&mut self, val: TypeMetatype) {
        self.meta.metain = val;
    }

    fn set_metatype_out(&mut self, val: TypeMetatype) {
        self.meta.metaout = val;
    }

    fn get_output_token(
        &self,
        op: OpId,
        cast_strategy: &mut dyn CastStrategy,
        data: &mut Funcdata,
        glb: &mut Architecture,
    ) -> Result<TypeId> {
        cast_strategy.arithmetic_output_standard(op, data, glb)
    }

    fn get_output_local(&self, op: OpId, data: &mut Funcdata, glb: &mut Architecture) -> Result<TypeId> {
        binary_get_output_local(&self.meta, op, data, glb)
    }

    fn get_input_local(&self, op: OpId, slot: i32, data: &mut Funcdata, glb: &mut Architecture) -> Result<TypeId> {
        binary_get_input_local(&self.meta, op, slot, data, glb)
    }

    fn print_raw(&mut self, out: &mut String, op: OpId, data: &Funcdata, glb: &Architecture) {
        binary_print_raw(&self.get_operator_name(op, data, glb), out, op, data, glb)
    }

    fn push(
        &self,
        lng: &mut dyn PrintLanguage,
        ctx: &mut PrintContext<'_>,
        op: OpId,
        read_op: Option<OpId>,
    ) -> Result<()> {
        lng.op_int_mult(ctx, op)
    }
}

pub struct TypeOpIntDiv {
    pub base: TypeOpBase,
    pub meta: TypeOpMeta,
}

impl Default for TypeOpIntDiv {
    fn default() -> Self {
        Self::new()
    }
}

impl TypeOpIntDiv {
    pub fn new() -> TypeOpIntDiv {
        TypeOpIntDiv {
            base: new_base(
                OpCode::IntDiv,
                "/",
                PcodeOp::BINARY,
                ARITHMETIC_OP | INHERITS_SIGN,
                Arc::new(OpBehaviorIntDiv::new()),
            ),
            meta: TypeOpMeta::new(TypeMetatype::Uint, TypeMetatype::Uint),
        }
    }
}

impl TypeOp for TypeOpIntDiv {
    fn base(&self) -> &TypeOpBase {
        &self.base
    }

    fn base_mut(&mut self) -> &mut TypeOpBase {
        &mut self.base
    }

    fn set_metatype_in(&mut self, val: TypeMetatype) {
        self.meta.metain = val;
    }

    fn set_metatype_out(&mut self, val: TypeMetatype) {
        self.meta.metaout = val;
    }

    fn get_input_cast(
        &self,
        op: OpId,
        slot: i32,
        cast_strategy: &dyn CastStrategy,
        data: &mut Funcdata,
        glb: &mut Architecture,
    ) -> Result<Option<TypeId>> {
        extension_input_cast(self, op, slot, cast_strategy, UNSIGNED_EXTENSION, data, glb)
    }

    fn get_output_local(&self, op: OpId, data: &mut Funcdata, glb: &mut Architecture) -> Result<TypeId> {
        binary_get_output_local(&self.meta, op, data, glb)
    }

    fn get_input_local(&self, op: OpId, slot: i32, data: &mut Funcdata, glb: &mut Architecture) -> Result<TypeId> {
        binary_get_input_local(&self.meta, op, slot, data, glb)
    }

    fn print_raw(&mut self, out: &mut String, op: OpId, data: &Funcdata, glb: &Architecture) {
        binary_print_raw(&self.get_operator_name(op, data, glb), out, op, data, glb)
    }

    fn push(
        &self,
        lng: &mut dyn PrintLanguage,
        ctx: &mut PrintContext<'_>,
        op: OpId,
        read_op: Option<OpId>,
    ) -> Result<()> {
        lng.op_int_div(ctx, op)
    }
}

pub struct TypeOpIntSdiv {
    pub base: TypeOpBase,
    pub meta: TypeOpMeta,
}

impl Default for TypeOpIntSdiv {
    fn default() -> Self {
        Self::new()
    }
}

impl TypeOpIntSdiv {
    pub fn new() -> TypeOpIntSdiv {
        TypeOpIntSdiv {
            base: new_base(
                OpCode::IntSdiv,
                "/",
                PcodeOp::BINARY,
                ARITHMETIC_OP | INHERITS_SIGN,
                Arc::new(OpBehaviorIntSdiv::new()),
            ),
            meta: TypeOpMeta::new(TypeMetatype::Int, TypeMetatype::Int),
        }
    }
}

impl TypeOp for TypeOpIntSdiv {
    fn base(&self) -> &TypeOpBase {
        &self.base
    }

    fn base_mut(&mut self) -> &mut TypeOpBase {
        &mut self.base
    }

    fn set_metatype_in(&mut self, val: TypeMetatype) {
        self.meta.metain = val;
    }

    fn set_metatype_out(&mut self, val: TypeMetatype) {
        self.meta.metaout = val;
    }

    fn print_raw(&mut self, out: &mut String, op: OpId, data: &Funcdata, glb: &Architecture) {
        binary_print_raw("s/", out, op, data, glb)
    }

    fn get_input_cast(
        &self,
        op: OpId,
        slot: i32,
        cast_strategy: &dyn CastStrategy,
        data: &mut Funcdata,
        glb: &mut Architecture,
    ) -> Result<Option<TypeId>> {
        extension_input_cast(self, op, slot, cast_strategy, SIGNED_EXTENSION, data, glb)
    }

    fn get_output_local(&self, op: OpId, data: &mut Funcdata, glb: &mut Architecture) -> Result<TypeId> {
        binary_get_output_local(&self.meta, op, data, glb)
    }

    fn get_input_local(&self, op: OpId, slot: i32, data: &mut Funcdata, glb: &mut Architecture) -> Result<TypeId> {
        binary_get_input_local(&self.meta, op, slot, data, glb)
    }

    fn push(
        &self,
        lng: &mut dyn PrintLanguage,
        ctx: &mut PrintContext<'_>,
        op: OpId,
        read_op: Option<OpId>,
    ) -> Result<()> {
        lng.op_int_sdiv(ctx, op)
    }
}

pub struct TypeOpIntRem {
    pub base: TypeOpBase,
    pub meta: TypeOpMeta,
}

impl Default for TypeOpIntRem {
    fn default() -> Self {
        Self::new()
    }
}

impl TypeOpIntRem {
    pub fn new() -> TypeOpIntRem {
        TypeOpIntRem {
            base: new_base(
                OpCode::IntRem,
                "%",
                PcodeOp::BINARY,
                ARITHMETIC_OP | INHERITS_SIGN | INHERITS_SIGN_ZERO,
                Arc::new(OpBehaviorIntRem::new()),
            ),
            meta: TypeOpMeta::new(TypeMetatype::Uint, TypeMetatype::Uint),
        }
    }
}

impl TypeOp for TypeOpIntRem {
    fn base(&self) -> &TypeOpBase {
        &self.base
    }

    fn base_mut(&mut self) -> &mut TypeOpBase {
        &mut self.base
    }

    fn set_metatype_in(&mut self, val: TypeMetatype) {
        self.meta.metain = val;
    }

    fn set_metatype_out(&mut self, val: TypeMetatype) {
        self.meta.metaout = val;
    }

    fn get_input_cast(
        &self,
        op: OpId,
        slot: i32,
        cast_strategy: &dyn CastStrategy,
        data: &mut Funcdata,
        glb: &mut Architecture,
    ) -> Result<Option<TypeId>> {
        extension_input_cast(self, op, slot, cast_strategy, UNSIGNED_EXTENSION, data, glb)
    }

    fn get_output_local(&self, op: OpId, data: &mut Funcdata, glb: &mut Architecture) -> Result<TypeId> {
        binary_get_output_local(&self.meta, op, data, glb)
    }

    fn get_input_local(&self, op: OpId, slot: i32, data: &mut Funcdata, glb: &mut Architecture) -> Result<TypeId> {
        binary_get_input_local(&self.meta, op, slot, data, glb)
    }

    fn print_raw(&mut self, out: &mut String, op: OpId, data: &Funcdata, glb: &Architecture) {
        binary_print_raw(&self.get_operator_name(op, data, glb), out, op, data, glb)
    }

    fn push(
        &self,
        lng: &mut dyn PrintLanguage,
        ctx: &mut PrintContext<'_>,
        op: OpId,
        read_op: Option<OpId>,
    ) -> Result<()> {
        lng.op_int_rem(ctx, op)
    }
}

pub struct TypeOpIntSrem {
    pub base: TypeOpBase,
    pub meta: TypeOpMeta,
}

impl Default for TypeOpIntSrem {
    fn default() -> Self {
        Self::new()
    }
}

impl TypeOpIntSrem {
    pub fn new() -> TypeOpIntSrem {
        TypeOpIntSrem {
            base: new_base(
                OpCode::IntSrem,
                "%",
                PcodeOp::BINARY,
                ARITHMETIC_OP | INHERITS_SIGN | INHERITS_SIGN_ZERO,
                Arc::new(OpBehaviorIntSrem::new()),
            ),
            meta: TypeOpMeta::new(TypeMetatype::Int, TypeMetatype::Int),
        }
    }
}

impl TypeOp for TypeOpIntSrem {
    fn base(&self) -> &TypeOpBase {
        &self.base
    }

    fn base_mut(&mut self) -> &mut TypeOpBase {
        &mut self.base
    }

    fn set_metatype_in(&mut self, val: TypeMetatype) {
        self.meta.metain = val;
    }

    fn set_metatype_out(&mut self, val: TypeMetatype) {
        self.meta.metaout = val;
    }

    fn print_raw(&mut self, out: &mut String, op: OpId, data: &Funcdata, glb: &Architecture) {
        binary_print_raw("s%", out, op, data, glb)
    }

    fn get_input_cast(
        &self,
        op: OpId,
        slot: i32,
        cast_strategy: &dyn CastStrategy,
        data: &mut Funcdata,
        glb: &mut Architecture,
    ) -> Result<Option<TypeId>> {
        extension_input_cast(self, op, slot, cast_strategy, SIGNED_EXTENSION, data, glb)
    }

    fn get_output_local(&self, op: OpId, data: &mut Funcdata, glb: &mut Architecture) -> Result<TypeId> {
        binary_get_output_local(&self.meta, op, data, glb)
    }

    fn get_input_local(&self, op: OpId, slot: i32, data: &mut Funcdata, glb: &mut Architecture) -> Result<TypeId> {
        binary_get_input_local(&self.meta, op, slot, data, glb)
    }

    fn push(
        &self,
        lng: &mut dyn PrintLanguage,
        ctx: &mut PrintContext<'_>,
        op: OpId,
        read_op: Option<OpId>,
    ) -> Result<()> {
        lng.op_int_srem(ctx, op)
    }
}

pub struct TypeOpBoolNegate {
    pub base: TypeOpBase,
    pub meta: TypeOpMeta,
}

impl Default for TypeOpBoolNegate {
    fn default() -> Self {
        Self::new()
    }
}

impl TypeOpBoolNegate {
    pub fn new() -> TypeOpBoolNegate {
        TypeOpBoolNegate {
            base: new_base(
                OpCode::BoolNegate,
                "!",
                PcodeOp::UNARY | PcodeOp::BOOLOUTPUT,
                LOGICAL_OP,
                Arc::new(OpBehaviorBoolNegate::new()),
            ),
            meta: TypeOpMeta::new(TypeMetatype::Bool, TypeMetatype::Bool),
        }
    }
}

impl TypeOp for TypeOpBoolNegate {
    fn base(&self) -> &TypeOpBase {
        &self.base
    }

    fn base_mut(&mut self) -> &mut TypeOpBase {
        &mut self.base
    }

    fn set_metatype_in(&mut self, val: TypeMetatype) {
        self.meta.metain = val;
    }

    fn set_metatype_out(&mut self, val: TypeMetatype) {
        self.meta.metaout = val;
    }

    fn get_output_local(&self, op: OpId, data: &mut Funcdata, glb: &mut Architecture) -> Result<TypeId> {
        unary_get_output_local(&self.meta, op, data, glb)
    }

    fn get_input_local(&self, op: OpId, slot: i32, data: &mut Funcdata, glb: &mut Architecture) -> Result<TypeId> {
        unary_get_input_local(&self.meta, op, slot, data, glb)
    }

    fn print_raw(&mut self, out: &mut String, op: OpId, data: &Funcdata, glb: &Architecture) {
        unary_print_raw(&self.get_operator_name(op, data, glb), out, op, data, glb)
    }

    fn push(
        &self,
        lng: &mut dyn PrintLanguage,
        ctx: &mut PrintContext<'_>,
        op: OpId,
        read_op: Option<OpId>,
    ) -> Result<()> {
        lng.op_bool_negate(ctx, op)
    }
}

pub struct TypeOpBoolXor {
    pub base: TypeOpBase,
    pub meta: TypeOpMeta,
}

impl Default for TypeOpBoolXor {
    fn default() -> Self {
        Self::new()
    }
}

impl TypeOpBoolXor {
    pub fn new() -> TypeOpBoolXor {
        TypeOpBoolXor {
            base: new_base(
                OpCode::BoolXor,
                "^^",
                PcodeOp::BINARY | PcodeOp::COMMUTATIVE | PcodeOp::BOOLOUTPUT,
                LOGICAL_OP,
                Arc::new(OpBehaviorBoolXor::new()),
            ),
            meta: TypeOpMeta::new(TypeMetatype::Bool, TypeMetatype::Bool),
        }
    }
}

impl TypeOp for TypeOpBoolXor {
    fn base(&self) -> &TypeOpBase {
        &self.base
    }

    fn base_mut(&mut self) -> &mut TypeOpBase {
        &mut self.base
    }

    fn set_metatype_in(&mut self, val: TypeMetatype) {
        self.meta.metain = val;
    }

    fn set_metatype_out(&mut self, val: TypeMetatype) {
        self.meta.metaout = val;
    }

    fn get_output_local(&self, op: OpId, data: &mut Funcdata, glb: &mut Architecture) -> Result<TypeId> {
        binary_get_output_local(&self.meta, op, data, glb)
    }

    fn get_input_local(&self, op: OpId, slot: i32, data: &mut Funcdata, glb: &mut Architecture) -> Result<TypeId> {
        binary_get_input_local(&self.meta, op, slot, data, glb)
    }

    fn print_raw(&mut self, out: &mut String, op: OpId, data: &Funcdata, glb: &Architecture) {
        binary_print_raw(&self.get_operator_name(op, data, glb), out, op, data, glb)
    }

    fn push(
        &self,
        lng: &mut dyn PrintLanguage,
        ctx: &mut PrintContext<'_>,
        op: OpId,
        read_op: Option<OpId>,
    ) -> Result<()> {
        lng.op_bool_xor(ctx, op)
    }
}

pub struct TypeOpBoolAnd {
    pub base: TypeOpBase,
    pub meta: TypeOpMeta,
}

impl Default for TypeOpBoolAnd {
    fn default() -> Self {
        Self::new()
    }
}

impl TypeOpBoolAnd {
    pub fn new() -> TypeOpBoolAnd {
        TypeOpBoolAnd {
            base: new_base(
                OpCode::BoolAnd,
                "&&",
                PcodeOp::BINARY | PcodeOp::COMMUTATIVE | PcodeOp::BOOLOUTPUT,
                LOGICAL_OP,
                Arc::new(OpBehaviorBoolAnd::new()),
            ),
            meta: TypeOpMeta::new(TypeMetatype::Bool, TypeMetatype::Bool),
        }
    }
}

impl TypeOp for TypeOpBoolAnd {
    fn base(&self) -> &TypeOpBase {
        &self.base
    }

    fn base_mut(&mut self) -> &mut TypeOpBase {
        &mut self.base
    }

    fn set_metatype_in(&mut self, val: TypeMetatype) {
        self.meta.metain = val;
    }

    fn set_metatype_out(&mut self, val: TypeMetatype) {
        self.meta.metaout = val;
    }

    fn get_output_local(&self, op: OpId, data: &mut Funcdata, glb: &mut Architecture) -> Result<TypeId> {
        binary_get_output_local(&self.meta, op, data, glb)
    }

    fn get_input_local(&self, op: OpId, slot: i32, data: &mut Funcdata, glb: &mut Architecture) -> Result<TypeId> {
        binary_get_input_local(&self.meta, op, slot, data, glb)
    }

    fn print_raw(&mut self, out: &mut String, op: OpId, data: &Funcdata, glb: &Architecture) {
        binary_print_raw(&self.get_operator_name(op, data, glb), out, op, data, glb)
    }

    fn push(
        &self,
        lng: &mut dyn PrintLanguage,
        ctx: &mut PrintContext<'_>,
        op: OpId,
        read_op: Option<OpId>,
    ) -> Result<()> {
        lng.op_bool_and(ctx, op)
    }
}

pub struct TypeOpBoolOr {
    pub base: TypeOpBase,
    pub meta: TypeOpMeta,
}

impl Default for TypeOpBoolOr {
    fn default() -> Self {
        Self::new()
    }
}

impl TypeOpBoolOr {
    pub fn new() -> TypeOpBoolOr {
        TypeOpBoolOr {
            base: new_base(
                OpCode::BoolOr,
                "||",
                PcodeOp::BINARY | PcodeOp::COMMUTATIVE | PcodeOp::BOOLOUTPUT,
                LOGICAL_OP,
                Arc::new(OpBehaviorBoolOr::new()),
            ),
            meta: TypeOpMeta::new(TypeMetatype::Bool, TypeMetatype::Bool),
        }
    }
}

impl TypeOp for TypeOpBoolOr {
    fn base(&self) -> &TypeOpBase {
        &self.base
    }

    fn base_mut(&mut self) -> &mut TypeOpBase {
        &mut self.base
    }

    fn set_metatype_in(&mut self, val: TypeMetatype) {
        self.meta.metain = val;
    }

    fn set_metatype_out(&mut self, val: TypeMetatype) {
        self.meta.metaout = val;
    }

    fn get_output_local(&self, op: OpId, data: &mut Funcdata, glb: &mut Architecture) -> Result<TypeId> {
        binary_get_output_local(&self.meta, op, data, glb)
    }

    fn get_input_local(&self, op: OpId, slot: i32, data: &mut Funcdata, glb: &mut Architecture) -> Result<TypeId> {
        binary_get_input_local(&self.meta, op, slot, data, glb)
    }

    fn print_raw(&mut self, out: &mut String, op: OpId, data: &Funcdata, glb: &Architecture) {
        binary_print_raw(&self.get_operator_name(op, data, glb), out, op, data, glb)
    }

    fn push(
        &self,
        lng: &mut dyn PrintLanguage,
        ctx: &mut PrintContext<'_>,
        op: OpId,
        read_op: Option<OpId>,
    ) -> Result<()> {
        lng.op_bool_or(ctx, op)
    }
}

pub struct TypeOpFloatEqual {
    pub base: TypeOpBase,
    pub meta: TypeOpMeta,
}

impl TypeOpFloatEqual {
    pub fn new(trans: &dyn Translate) -> TypeOpFloatEqual {
        TypeOpFloatEqual {
            base: new_base(
                OpCode::FloatEqual,
                "==",
                PcodeOp::BINARY | PcodeOp::BOOLOUTPUT | PcodeOp::COMMUTATIVE,
                FLOATINGPOINT_OP,
                Arc::new(OpBehaviorFloatEqual::new(float_format_table(trans))),
            ),
            meta: TypeOpMeta::new(TypeMetatype::Bool, TypeMetatype::Float),
        }
    }
}

impl TypeOp for TypeOpFloatEqual {
    fn base(&self) -> &TypeOpBase {
        &self.base
    }

    fn base_mut(&mut self) -> &mut TypeOpBase {
        &mut self.base
    }

    fn set_metatype_in(&mut self, val: TypeMetatype) {
        self.meta.metain = val;
    }

    fn set_metatype_out(&mut self, val: TypeMetatype) {
        self.meta.metaout = val;
    }

    fn print_raw(&mut self, out: &mut String, op: OpId, data: &Funcdata, glb: &Architecture) {
        binary_print_raw("f==", out, op, data, glb)
    }

    fn get_output_local(&self, op: OpId, data: &mut Funcdata, glb: &mut Architecture) -> Result<TypeId> {
        binary_get_output_local(&self.meta, op, data, glb)
    }

    fn get_input_local(&self, op: OpId, slot: i32, data: &mut Funcdata, glb: &mut Architecture) -> Result<TypeId> {
        binary_get_input_local(&self.meta, op, slot, data, glb)
    }

    fn push(
        &self,
        lng: &mut dyn PrintLanguage,
        ctx: &mut PrintContext<'_>,
        op: OpId,
        read_op: Option<OpId>,
    ) -> Result<()> {
        lng.op_float_equal(ctx, op)
    }
}

pub struct TypeOpFloatNotEqual {
    pub base: TypeOpBase,
    pub meta: TypeOpMeta,
}

impl TypeOpFloatNotEqual {
    pub fn new(trans: &dyn Translate) -> TypeOpFloatNotEqual {
        TypeOpFloatNotEqual {
            base: new_base(
                OpCode::FloatNotequal,
                "!=",
                PcodeOp::BINARY | PcodeOp::BOOLOUTPUT | PcodeOp::COMMUTATIVE,
                FLOATINGPOINT_OP,
                Arc::new(OpBehaviorFloatNotEqual::new(float_format_table(trans))),
            ),
            meta: TypeOpMeta::new(TypeMetatype::Bool, TypeMetatype::Float),
        }
    }
}

impl TypeOp for TypeOpFloatNotEqual {
    fn base(&self) -> &TypeOpBase {
        &self.base
    }

    fn base_mut(&mut self) -> &mut TypeOpBase {
        &mut self.base
    }

    fn set_metatype_in(&mut self, val: TypeMetatype) {
        self.meta.metain = val;
    }

    fn set_metatype_out(&mut self, val: TypeMetatype) {
        self.meta.metaout = val;
    }

    fn print_raw(&mut self, out: &mut String, op: OpId, data: &Funcdata, glb: &Architecture) {
        binary_print_raw("f!=", out, op, data, glb)
    }

    fn get_output_local(&self, op: OpId, data: &mut Funcdata, glb: &mut Architecture) -> Result<TypeId> {
        binary_get_output_local(&self.meta, op, data, glb)
    }

    fn get_input_local(&self, op: OpId, slot: i32, data: &mut Funcdata, glb: &mut Architecture) -> Result<TypeId> {
        binary_get_input_local(&self.meta, op, slot, data, glb)
    }

    fn push(
        &self,
        lng: &mut dyn PrintLanguage,
        ctx: &mut PrintContext<'_>,
        op: OpId,
        read_op: Option<OpId>,
    ) -> Result<()> {
        lng.op_float_not_equal(ctx, op)
    }
}

pub struct TypeOpFloatLess {
    pub base: TypeOpBase,
    pub meta: TypeOpMeta,
}

impl TypeOpFloatLess {
    pub fn new(trans: &dyn Translate) -> TypeOpFloatLess {
        TypeOpFloatLess {
            base: new_base(
                OpCode::FloatLess,
                "<",
                PcodeOp::BINARY | PcodeOp::BOOLOUTPUT,
                FLOATINGPOINT_OP,
                Arc::new(OpBehaviorFloatLess::new(float_format_table(trans))),
            ),
            meta: TypeOpMeta::new(TypeMetatype::Bool, TypeMetatype::Float),
        }
    }
}

impl TypeOp for TypeOpFloatLess {
    fn base(&self) -> &TypeOpBase {
        &self.base
    }

    fn base_mut(&mut self) -> &mut TypeOpBase {
        &mut self.base
    }

    fn set_metatype_in(&mut self, val: TypeMetatype) {
        self.meta.metain = val;
    }

    fn set_metatype_out(&mut self, val: TypeMetatype) {
        self.meta.metaout = val;
    }

    fn print_raw(&mut self, out: &mut String, op: OpId, data: &Funcdata, glb: &Architecture) {
        binary_print_raw("f<", out, op, data, glb)
    }

    fn get_output_local(&self, op: OpId, data: &mut Funcdata, glb: &mut Architecture) -> Result<TypeId> {
        binary_get_output_local(&self.meta, op, data, glb)
    }

    fn get_input_local(&self, op: OpId, slot: i32, data: &mut Funcdata, glb: &mut Architecture) -> Result<TypeId> {
        binary_get_input_local(&self.meta, op, slot, data, glb)
    }

    fn push(
        &self,
        lng: &mut dyn PrintLanguage,
        ctx: &mut PrintContext<'_>,
        op: OpId,
        read_op: Option<OpId>,
    ) -> Result<()> {
        lng.op_float_less(ctx, op)
    }
}

pub struct TypeOpFloatLessEqual {
    pub base: TypeOpBase,
    pub meta: TypeOpMeta,
}

impl TypeOpFloatLessEqual {
    pub fn new(trans: &dyn Translate) -> TypeOpFloatLessEqual {
        TypeOpFloatLessEqual {
            base: new_base(
                OpCode::FloatLessequal,
                "<=",
                PcodeOp::BINARY | PcodeOp::BOOLOUTPUT,
                FLOATINGPOINT_OP,
                Arc::new(OpBehaviorFloatLessEqual::new(float_format_table(trans))),
            ),
            meta: TypeOpMeta::new(TypeMetatype::Bool, TypeMetatype::Float),
        }
    }
}

impl TypeOp for TypeOpFloatLessEqual {
    fn base(&self) -> &TypeOpBase {
        &self.base
    }

    fn base_mut(&mut self) -> &mut TypeOpBase {
        &mut self.base
    }

    fn set_metatype_in(&mut self, val: TypeMetatype) {
        self.meta.metain = val;
    }

    fn set_metatype_out(&mut self, val: TypeMetatype) {
        self.meta.metaout = val;
    }

    fn print_raw(&mut self, out: &mut String, op: OpId, data: &Funcdata, glb: &Architecture) {
        binary_print_raw("f<=", out, op, data, glb)
    }

    fn get_output_local(&self, op: OpId, data: &mut Funcdata, glb: &mut Architecture) -> Result<TypeId> {
        binary_get_output_local(&self.meta, op, data, glb)
    }

    fn get_input_local(&self, op: OpId, slot: i32, data: &mut Funcdata, glb: &mut Architecture) -> Result<TypeId> {
        binary_get_input_local(&self.meta, op, slot, data, glb)
    }

    fn push(
        &self,
        lng: &mut dyn PrintLanguage,
        ctx: &mut PrintContext<'_>,
        op: OpId,
        read_op: Option<OpId>,
    ) -> Result<()> {
        lng.op_float_less_equal(ctx, op)
    }
}

pub struct TypeOpFloatNan {
    pub base: TypeOpBase,
    pub meta: TypeOpMeta,
}

impl TypeOpFloatNan {
    pub fn new(trans: &dyn Translate) -> TypeOpFloatNan {
        TypeOpFloatNan {
            base: new_base(
                OpCode::FloatNan,
                "NAN",
                PcodeOp::UNARY | PcodeOp::BOOLOUTPUT,
                FLOATINGPOINT_OP,
                Arc::new(OpBehaviorFloatNan::new(float_format_table(trans))),
            ),
            meta: TypeOpMeta::new(TypeMetatype::Bool, TypeMetatype::Float),
        }
    }
}

impl TypeOp for TypeOpFloatNan {
    fn base(&self) -> &TypeOpBase {
        &self.base
    }

    fn base_mut(&mut self) -> &mut TypeOpBase {
        &mut self.base
    }

    fn set_metatype_in(&mut self, val: TypeMetatype) {
        self.meta.metain = val;
    }

    fn set_metatype_out(&mut self, val: TypeMetatype) {
        self.meta.metaout = val;
    }

    fn get_output_local(&self, op: OpId, data: &mut Funcdata, glb: &mut Architecture) -> Result<TypeId> {
        func_get_output_local(&self.meta, op, data, glb)
    }

    fn get_input_local(&self, op: OpId, slot: i32, data: &mut Funcdata, glb: &mut Architecture) -> Result<TypeId> {
        func_get_input_local(&self.meta, op, slot, data, glb)
    }

    fn print_raw(&mut self, out: &mut String, op: OpId, data: &Funcdata, glb: &Architecture) {
        func_print_raw(&self.get_operator_name(op, data, glb), out, op, data, glb)
    }

    fn push(
        &self,
        lng: &mut dyn PrintLanguage,
        ctx: &mut PrintContext<'_>,
        op: OpId,
        read_op: Option<OpId>,
    ) -> Result<()> {
        lng.op_float_nan(ctx, op)
    }
}

pub struct TypeOpFloatAdd {
    pub base: TypeOpBase,
    pub meta: TypeOpMeta,
}

impl TypeOpFloatAdd {
    pub fn new(trans: &dyn Translate) -> TypeOpFloatAdd {
        TypeOpFloatAdd {
            base: new_base(
                OpCode::FloatAdd,
                "+",
                PcodeOp::BINARY | PcodeOp::COMMUTATIVE,
                FLOATINGPOINT_OP,
                Arc::new(OpBehaviorFloatAdd::new(float_format_table(trans))),
            ),
            meta: TypeOpMeta::new(TypeMetatype::Float, TypeMetatype::Float),
        }
    }
}

impl TypeOp for TypeOpFloatAdd {
    fn base(&self) -> &TypeOpBase {
        &self.base
    }

    fn base_mut(&mut self) -> &mut TypeOpBase {
        &mut self.base
    }

    fn set_metatype_in(&mut self, val: TypeMetatype) {
        self.meta.metain = val;
    }

    fn set_metatype_out(&mut self, val: TypeMetatype) {
        self.meta.metaout = val;
    }

    fn print_raw(&mut self, out: &mut String, op: OpId, data: &Funcdata, glb: &Architecture) {
        binary_print_raw("f+", out, op, data, glb)
    }

    fn get_output_local(&self, op: OpId, data: &mut Funcdata, glb: &mut Architecture) -> Result<TypeId> {
        binary_get_output_local(&self.meta, op, data, glb)
    }

    fn get_input_local(&self, op: OpId, slot: i32, data: &mut Funcdata, glb: &mut Architecture) -> Result<TypeId> {
        binary_get_input_local(&self.meta, op, slot, data, glb)
    }

    fn push(
        &self,
        lng: &mut dyn PrintLanguage,
        ctx: &mut PrintContext<'_>,
        op: OpId,
        read_op: Option<OpId>,
    ) -> Result<()> {
        lng.op_float_add(ctx, op)
    }
}

pub struct TypeOpFloatDiv {
    pub base: TypeOpBase,
    pub meta: TypeOpMeta,
}

impl TypeOpFloatDiv {
    pub fn new(trans: &dyn Translate) -> TypeOpFloatDiv {
        TypeOpFloatDiv {
            base: new_base(
                OpCode::FloatDiv,
                "/",
                PcodeOp::BINARY,
                FLOATINGPOINT_OP,
                Arc::new(OpBehaviorFloatDiv::new(float_format_table(trans))),
            ),
            meta: TypeOpMeta::new(TypeMetatype::Float, TypeMetatype::Float),
        }
    }
}

impl TypeOp for TypeOpFloatDiv {
    fn base(&self) -> &TypeOpBase {
        &self.base
    }

    fn base_mut(&mut self) -> &mut TypeOpBase {
        &mut self.base
    }

    fn set_metatype_in(&mut self, val: TypeMetatype) {
        self.meta.metain = val;
    }

    fn set_metatype_out(&mut self, val: TypeMetatype) {
        self.meta.metaout = val;
    }

    fn print_raw(&mut self, out: &mut String, op: OpId, data: &Funcdata, glb: &Architecture) {
        binary_print_raw("f/", out, op, data, glb)
    }

    fn get_output_local(&self, op: OpId, data: &mut Funcdata, glb: &mut Architecture) -> Result<TypeId> {
        binary_get_output_local(&self.meta, op, data, glb)
    }

    fn get_input_local(&self, op: OpId, slot: i32, data: &mut Funcdata, glb: &mut Architecture) -> Result<TypeId> {
        binary_get_input_local(&self.meta, op, slot, data, glb)
    }

    fn push(
        &self,
        lng: &mut dyn PrintLanguage,
        ctx: &mut PrintContext<'_>,
        op: OpId,
        read_op: Option<OpId>,
    ) -> Result<()> {
        lng.op_float_div(ctx, op)
    }
}

pub struct TypeOpFloatMult {
    pub base: TypeOpBase,
    pub meta: TypeOpMeta,
}

impl TypeOpFloatMult {
    pub fn new(trans: &dyn Translate) -> TypeOpFloatMult {
        TypeOpFloatMult {
            base: new_base(
                OpCode::FloatMult,
                "*",
                PcodeOp::BINARY | PcodeOp::COMMUTATIVE,
                FLOATINGPOINT_OP,
                Arc::new(OpBehaviorFloatMult::new(float_format_table(trans))),
            ),
            meta: TypeOpMeta::new(TypeMetatype::Float, TypeMetatype::Float),
        }
    }
}

impl TypeOp for TypeOpFloatMult {
    fn base(&self) -> &TypeOpBase {
        &self.base
    }

    fn base_mut(&mut self) -> &mut TypeOpBase {
        &mut self.base
    }

    fn set_metatype_in(&mut self, val: TypeMetatype) {
        self.meta.metain = val;
    }

    fn set_metatype_out(&mut self, val: TypeMetatype) {
        self.meta.metaout = val;
    }

    fn print_raw(&mut self, out: &mut String, op: OpId, data: &Funcdata, glb: &Architecture) {
        binary_print_raw("f*", out, op, data, glb)
    }

    fn get_output_local(&self, op: OpId, data: &mut Funcdata, glb: &mut Architecture) -> Result<TypeId> {
        binary_get_output_local(&self.meta, op, data, glb)
    }

    fn get_input_local(&self, op: OpId, slot: i32, data: &mut Funcdata, glb: &mut Architecture) -> Result<TypeId> {
        binary_get_input_local(&self.meta, op, slot, data, glb)
    }

    fn push(
        &self,
        lng: &mut dyn PrintLanguage,
        ctx: &mut PrintContext<'_>,
        op: OpId,
        read_op: Option<OpId>,
    ) -> Result<()> {
        lng.op_float_mult(ctx, op)
    }
}

pub struct TypeOpFloatSub {
    pub base: TypeOpBase,
    pub meta: TypeOpMeta,
}

impl TypeOpFloatSub {
    pub fn new(trans: &dyn Translate) -> TypeOpFloatSub {
        TypeOpFloatSub {
            base: new_base(
                OpCode::FloatSub,
                "-",
                PcodeOp::BINARY,
                FLOATINGPOINT_OP,
                Arc::new(OpBehaviorFloatSub::new(float_format_table(trans))),
            ),
            meta: TypeOpMeta::new(TypeMetatype::Float, TypeMetatype::Float),
        }
    }
}

impl TypeOp for TypeOpFloatSub {
    fn base(&self) -> &TypeOpBase {
        &self.base
    }

    fn base_mut(&mut self) -> &mut TypeOpBase {
        &mut self.base
    }

    fn set_metatype_in(&mut self, val: TypeMetatype) {
        self.meta.metain = val;
    }

    fn set_metatype_out(&mut self, val: TypeMetatype) {
        self.meta.metaout = val;
    }

    fn print_raw(&mut self, out: &mut String, op: OpId, data: &Funcdata, glb: &Architecture) {
        binary_print_raw("f-", out, op, data, glb)
    }

    fn get_output_local(&self, op: OpId, data: &mut Funcdata, glb: &mut Architecture) -> Result<TypeId> {
        binary_get_output_local(&self.meta, op, data, glb)
    }

    fn get_input_local(&self, op: OpId, slot: i32, data: &mut Funcdata, glb: &mut Architecture) -> Result<TypeId> {
        binary_get_input_local(&self.meta, op, slot, data, glb)
    }

    fn push(
        &self,
        lng: &mut dyn PrintLanguage,
        ctx: &mut PrintContext<'_>,
        op: OpId,
        read_op: Option<OpId>,
    ) -> Result<()> {
        lng.op_float_sub(ctx, op)
    }
}

pub struct TypeOpFloatNeg {
    pub base: TypeOpBase,
    pub meta: TypeOpMeta,
}

impl TypeOpFloatNeg {
    pub fn new(trans: &dyn Translate) -> TypeOpFloatNeg {
        TypeOpFloatNeg {
            base: new_base(
                OpCode::FloatNeg,
                "-",
                PcodeOp::UNARY,
                FLOATINGPOINT_OP,
                Arc::new(OpBehaviorFloatNeg::new(float_format_table(trans))),
            ),
            meta: TypeOpMeta::new(TypeMetatype::Float, TypeMetatype::Float),
        }
    }
}

impl TypeOp for TypeOpFloatNeg {
    fn base(&self) -> &TypeOpBase {
        &self.base
    }

    fn base_mut(&mut self) -> &mut TypeOpBase {
        &mut self.base
    }

    fn set_metatype_in(&mut self, val: TypeMetatype) {
        self.meta.metain = val;
    }

    fn set_metatype_out(&mut self, val: TypeMetatype) {
        self.meta.metaout = val;
    }

    fn print_raw(&mut self, out: &mut String, op: OpId, data: &Funcdata, glb: &Architecture) {
        unary_print_raw("f-", out, op, data, glb)
    }

    fn get_output_local(&self, op: OpId, data: &mut Funcdata, glb: &mut Architecture) -> Result<TypeId> {
        unary_get_output_local(&self.meta, op, data, glb)
    }

    fn get_input_local(&self, op: OpId, slot: i32, data: &mut Funcdata, glb: &mut Architecture) -> Result<TypeId> {
        unary_get_input_local(&self.meta, op, slot, data, glb)
    }

    fn push(
        &self,
        lng: &mut dyn PrintLanguage,
        ctx: &mut PrintContext<'_>,
        op: OpId,
        read_op: Option<OpId>,
    ) -> Result<()> {
        lng.op_float_neg(ctx, op)
    }
}

pub struct TypeOpFloatAbs {
    pub base: TypeOpBase,
    pub meta: TypeOpMeta,
}

impl TypeOpFloatAbs {
    pub fn new(trans: &dyn Translate) -> TypeOpFloatAbs {
        TypeOpFloatAbs {
            base: new_base(
                OpCode::FloatAbs,
                "ABS",
                PcodeOp::UNARY,
                FLOATINGPOINT_OP,
                Arc::new(OpBehaviorFloatAbs::new(float_format_table(trans))),
            ),
            meta: TypeOpMeta::new(TypeMetatype::Float, TypeMetatype::Float),
        }
    }
}

impl TypeOp for TypeOpFloatAbs {
    fn base(&self) -> &TypeOpBase {
        &self.base
    }

    fn base_mut(&mut self) -> &mut TypeOpBase {
        &mut self.base
    }

    fn set_metatype_in(&mut self, val: TypeMetatype) {
        self.meta.metain = val;
    }

    fn set_metatype_out(&mut self, val: TypeMetatype) {
        self.meta.metaout = val;
    }

    fn get_output_local(&self, op: OpId, data: &mut Funcdata, glb: &mut Architecture) -> Result<TypeId> {
        func_get_output_local(&self.meta, op, data, glb)
    }

    fn get_input_local(&self, op: OpId, slot: i32, data: &mut Funcdata, glb: &mut Architecture) -> Result<TypeId> {
        func_get_input_local(&self.meta, op, slot, data, glb)
    }

    fn print_raw(&mut self, out: &mut String, op: OpId, data: &Funcdata, glb: &Architecture) {
        func_print_raw(&self.get_operator_name(op, data, glb), out, op, data, glb)
    }

    fn push(
        &self,
        lng: &mut dyn PrintLanguage,
        ctx: &mut PrintContext<'_>,
        op: OpId,
        read_op: Option<OpId>,
    ) -> Result<()> {
        lng.op_float_abs(ctx, op)
    }
}

pub struct TypeOpFloatSqrt {
    pub base: TypeOpBase,
    pub meta: TypeOpMeta,
}

impl TypeOpFloatSqrt {
    pub fn new(trans: &dyn Translate) -> TypeOpFloatSqrt {
        TypeOpFloatSqrt {
            base: new_base(
                OpCode::FloatSqrt,
                "SQRT",
                PcodeOp::UNARY,
                FLOATINGPOINT_OP,
                Arc::new(OpBehaviorFloatSqrt::new(float_format_table(trans))),
            ),
            meta: TypeOpMeta::new(TypeMetatype::Float, TypeMetatype::Float),
        }
    }
}

impl TypeOp for TypeOpFloatSqrt {
    fn base(&self) -> &TypeOpBase {
        &self.base
    }

    fn base_mut(&mut self) -> &mut TypeOpBase {
        &mut self.base
    }

    fn set_metatype_in(&mut self, val: TypeMetatype) {
        self.meta.metain = val;
    }

    fn set_metatype_out(&mut self, val: TypeMetatype) {
        self.meta.metaout = val;
    }

    fn get_output_local(&self, op: OpId, data: &mut Funcdata, glb: &mut Architecture) -> Result<TypeId> {
        func_get_output_local(&self.meta, op, data, glb)
    }

    fn get_input_local(&self, op: OpId, slot: i32, data: &mut Funcdata, glb: &mut Architecture) -> Result<TypeId> {
        func_get_input_local(&self.meta, op, slot, data, glb)
    }

    fn print_raw(&mut self, out: &mut String, op: OpId, data: &Funcdata, glb: &Architecture) {
        func_print_raw(&self.get_operator_name(op, data, glb), out, op, data, glb)
    }

    fn push(
        &self,
        lng: &mut dyn PrintLanguage,
        ctx: &mut PrintContext<'_>,
        op: OpId,
        read_op: Option<OpId>,
    ) -> Result<()> {
        lng.op_float_sqrt(ctx, op)
    }
}

pub struct TypeOpFloatInt2Float {
    pub base: TypeOpBase,
    pub meta: TypeOpMeta,
}

impl TypeOpFloatInt2Float {
    pub fn new(trans: &dyn Translate) -> TypeOpFloatInt2Float {
        TypeOpFloatInt2Float {
            base: new_base(
                OpCode::FloatInt2float,
                "INT2FLOAT",
                PcodeOp::UNARY,
                FLOATINGPOINT_OP,
                Arc::new(OpBehaviorFloatInt2Float::new(float_format_table(trans))),
            ),
            meta: TypeOpMeta::new(TypeMetatype::Float, TypeMetatype::Int),
        }
    }

    pub fn absorb_zext(op: OpId, data: &Funcdata) -> Option<OpId> {
        let vn0 = data.vn(data.op(op).get_in(0));
        if vn0.is_written() && vn0.is_implied() {
            let zext_op = vn0.get_def().expect("written varnode has no defining op");
            if data.op(zext_op).code() == OpCode::IntZext {
                return Some(zext_op);
            }
        }
        None
    }

    pub fn preferred_zext_size(in_size: i32) -> i32 {
        if in_size < 4 {
            4
        } else if in_size < 8 {
            8
        } else {
            in_size + 1
        }
    }
}

impl TypeOp for TypeOpFloatInt2Float {
    fn base(&self) -> &TypeOpBase {
        &self.base
    }

    fn base_mut(&mut self) -> &mut TypeOpBase {
        &mut self.base
    }

    fn set_metatype_in(&mut self, val: TypeMetatype) {
        self.meta.metain = val;
    }

    fn set_metatype_out(&mut self, val: TypeMetatype) {
        self.meta.metaout = val;
    }

    fn get_input_cast(
        &self,
        op: OpId,
        slot: i32,
        cast_strategy: &dyn CastStrategy,
        data: &mut Funcdata,
        glb: &mut Architecture,
    ) -> Result<Option<TypeId>> {
        if TypeOpFloatInt2Float::absorb_zext(op, data).is_some() {
            return Ok(None);
        }
        let vn = data.op(op).get_in(slot);
        let reqtype = self.get_input_local(op, slot, data, glb)?;
        let curtype = data.vn_get_high_type_read_facing(vn, op, glb)?;
        let mut care_uint_int = true;
        let vnrec = data.vn(vn);
        if vnrec.get_size() <= 8 {
            let mut val = vnrec.get_nz_mask();
            val = val.wrapping_shr((8 * vnrec.get_size() - 1) as u32);
            care_uint_int = (val & 1) != 0;
        }
        Ok(cast_strategy.cast_standard(reqtype, curtype, care_uint_int, true, types_mut(glb)))
    }

    fn get_output_local(&self, op: OpId, data: &mut Funcdata, glb: &mut Architecture) -> Result<TypeId> {
        func_get_output_local(&self.meta, op, data, glb)
    }

    fn get_input_local(&self, op: OpId, slot: i32, data: &mut Funcdata, glb: &mut Architecture) -> Result<TypeId> {
        func_get_input_local(&self.meta, op, slot, data, glb)
    }

    fn print_raw(&mut self, out: &mut String, op: OpId, data: &Funcdata, glb: &Architecture) {
        func_print_raw(&self.get_operator_name(op, data, glb), out, op, data, glb)
    }

    fn push(
        &self,
        lng: &mut dyn PrintLanguage,
        ctx: &mut PrintContext<'_>,
        op: OpId,
        read_op: Option<OpId>,
    ) -> Result<()> {
        lng.op_float_int2float(ctx, op)
    }
}

pub struct TypeOpFloatFloat2Float {
    pub base: TypeOpBase,
    pub meta: TypeOpMeta,
}

impl TypeOpFloatFloat2Float {
    pub fn new(trans: &dyn Translate) -> TypeOpFloatFloat2Float {
        TypeOpFloatFloat2Float {
            base: new_base(
                OpCode::FloatFloat2float,
                "FLOAT2FLOAT",
                PcodeOp::UNARY,
                FLOATINGPOINT_OP,
                Arc::new(OpBehaviorFloatFloat2Float::new(float_format_table(trans))),
            ),
            meta: TypeOpMeta::new(TypeMetatype::Float, TypeMetatype::Float),
        }
    }
}

impl TypeOp for TypeOpFloatFloat2Float {
    fn base(&self) -> &TypeOpBase {
        &self.base
    }

    fn base_mut(&mut self) -> &mut TypeOpBase {
        &mut self.base
    }

    fn set_metatype_in(&mut self, val: TypeMetatype) {
        self.meta.metain = val;
    }

    fn set_metatype_out(&mut self, val: TypeMetatype) {
        self.meta.metaout = val;
    }

    fn get_output_local(&self, op: OpId, data: &mut Funcdata, glb: &mut Architecture) -> Result<TypeId> {
        func_get_output_local(&self.meta, op, data, glb)
    }

    fn get_input_local(&self, op: OpId, slot: i32, data: &mut Funcdata, glb: &mut Architecture) -> Result<TypeId> {
        func_get_input_local(&self.meta, op, slot, data, glb)
    }

    fn print_raw(&mut self, out: &mut String, op: OpId, data: &Funcdata, glb: &Architecture) {
        func_print_raw(&self.get_operator_name(op, data, glb), out, op, data, glb)
    }

    fn push(
        &self,
        lng: &mut dyn PrintLanguage,
        ctx: &mut PrintContext<'_>,
        op: OpId,
        read_op: Option<OpId>,
    ) -> Result<()> {
        lng.op_float_float2float(ctx, op)
    }
}

pub struct TypeOpFloatTrunc {
    pub base: TypeOpBase,
    pub meta: TypeOpMeta,
}

impl TypeOpFloatTrunc {
    pub fn new(trans: &dyn Translate) -> TypeOpFloatTrunc {
        TypeOpFloatTrunc {
            base: new_base(
                OpCode::FloatTrunc,
                "TRUNC",
                PcodeOp::UNARY,
                FLOATINGPOINT_OP,
                Arc::new(OpBehaviorFloatTrunc::new(float_format_table(trans))),
            ),
            meta: TypeOpMeta::new(TypeMetatype::Int, TypeMetatype::Float),
        }
    }
}

impl TypeOp for TypeOpFloatTrunc {
    fn base(&self) -> &TypeOpBase {
        &self.base
    }

    fn base_mut(&mut self) -> &mut TypeOpBase {
        &mut self.base
    }

    fn set_metatype_in(&mut self, val: TypeMetatype) {
        self.meta.metain = val;
    }

    fn set_metatype_out(&mut self, val: TypeMetatype) {
        self.meta.metaout = val;
    }

    fn get_output_local(&self, op: OpId, data: &mut Funcdata, glb: &mut Architecture) -> Result<TypeId> {
        func_get_output_local(&self.meta, op, data, glb)
    }

    fn get_input_local(&self, op: OpId, slot: i32, data: &mut Funcdata, glb: &mut Architecture) -> Result<TypeId> {
        func_get_input_local(&self.meta, op, slot, data, glb)
    }

    fn print_raw(&mut self, out: &mut String, op: OpId, data: &Funcdata, glb: &Architecture) {
        func_print_raw(&self.get_operator_name(op, data, glb), out, op, data, glb)
    }

    fn push(
        &self,
        lng: &mut dyn PrintLanguage,
        ctx: &mut PrintContext<'_>,
        op: OpId,
        read_op: Option<OpId>,
    ) -> Result<()> {
        lng.op_float_trunc(ctx, op)
    }
}

pub struct TypeOpFloatCeil {
    pub base: TypeOpBase,
    pub meta: TypeOpMeta,
}

impl TypeOpFloatCeil {
    pub fn new(trans: &dyn Translate) -> TypeOpFloatCeil {
        TypeOpFloatCeil {
            base: new_base(
                OpCode::FloatCeil,
                "CEIL",
                PcodeOp::UNARY,
                FLOATINGPOINT_OP,
                Arc::new(OpBehaviorFloatCeil::new(float_format_table(trans))),
            ),
            meta: TypeOpMeta::new(TypeMetatype::Float, TypeMetatype::Float),
        }
    }
}

impl TypeOp for TypeOpFloatCeil {
    fn base(&self) -> &TypeOpBase {
        &self.base
    }

    fn base_mut(&mut self) -> &mut TypeOpBase {
        &mut self.base
    }

    fn set_metatype_in(&mut self, val: TypeMetatype) {
        self.meta.metain = val;
    }

    fn set_metatype_out(&mut self, val: TypeMetatype) {
        self.meta.metaout = val;
    }

    fn get_output_local(&self, op: OpId, data: &mut Funcdata, glb: &mut Architecture) -> Result<TypeId> {
        func_get_output_local(&self.meta, op, data, glb)
    }

    fn get_input_local(&self, op: OpId, slot: i32, data: &mut Funcdata, glb: &mut Architecture) -> Result<TypeId> {
        func_get_input_local(&self.meta, op, slot, data, glb)
    }

    fn print_raw(&mut self, out: &mut String, op: OpId, data: &Funcdata, glb: &Architecture) {
        func_print_raw(&self.get_operator_name(op, data, glb), out, op, data, glb)
    }

    fn push(
        &self,
        lng: &mut dyn PrintLanguage,
        ctx: &mut PrintContext<'_>,
        op: OpId,
        read_op: Option<OpId>,
    ) -> Result<()> {
        lng.op_float_ceil(ctx, op)
    }
}

pub struct TypeOpFloatFloor {
    pub base: TypeOpBase,
    pub meta: TypeOpMeta,
}

impl TypeOpFloatFloor {
    pub fn new(trans: &dyn Translate) -> TypeOpFloatFloor {
        TypeOpFloatFloor {
            base: new_base(
                OpCode::FloatFloor,
                "FLOOR",
                PcodeOp::UNARY,
                FLOATINGPOINT_OP,
                Arc::new(OpBehaviorFloatFloor::new(float_format_table(trans))),
            ),
            meta: TypeOpMeta::new(TypeMetatype::Float, TypeMetatype::Float),
        }
    }
}

impl TypeOp for TypeOpFloatFloor {
    fn base(&self) -> &TypeOpBase {
        &self.base
    }

    fn base_mut(&mut self) -> &mut TypeOpBase {
        &mut self.base
    }

    fn set_metatype_in(&mut self, val: TypeMetatype) {
        self.meta.metain = val;
    }

    fn set_metatype_out(&mut self, val: TypeMetatype) {
        self.meta.metaout = val;
    }

    fn get_output_local(&self, op: OpId, data: &mut Funcdata, glb: &mut Architecture) -> Result<TypeId> {
        func_get_output_local(&self.meta, op, data, glb)
    }

    fn get_input_local(&self, op: OpId, slot: i32, data: &mut Funcdata, glb: &mut Architecture) -> Result<TypeId> {
        func_get_input_local(&self.meta, op, slot, data, glb)
    }

    fn print_raw(&mut self, out: &mut String, op: OpId, data: &Funcdata, glb: &Architecture) {
        func_print_raw(&self.get_operator_name(op, data, glb), out, op, data, glb)
    }

    fn push(
        &self,
        lng: &mut dyn PrintLanguage,
        ctx: &mut PrintContext<'_>,
        op: OpId,
        read_op: Option<OpId>,
    ) -> Result<()> {
        lng.op_float_floor(ctx, op)
    }
}

pub struct TypeOpFloatRound {
    pub base: TypeOpBase,
    pub meta: TypeOpMeta,
}

impl TypeOpFloatRound {
    pub fn new(trans: &dyn Translate) -> TypeOpFloatRound {
        TypeOpFloatRound {
            base: new_base(
                OpCode::FloatRound,
                "ROUND",
                PcodeOp::UNARY,
                FLOATINGPOINT_OP,
                Arc::new(OpBehaviorFloatRound::new(float_format_table(trans))),
            ),
            meta: TypeOpMeta::new(TypeMetatype::Float, TypeMetatype::Float),
        }
    }
}

impl TypeOp for TypeOpFloatRound {
    fn base(&self) -> &TypeOpBase {
        &self.base
    }

    fn base_mut(&mut self) -> &mut TypeOpBase {
        &mut self.base
    }

    fn set_metatype_in(&mut self, val: TypeMetatype) {
        self.meta.metain = val;
    }

    fn set_metatype_out(&mut self, val: TypeMetatype) {
        self.meta.metaout = val;
    }

    fn get_output_local(&self, op: OpId, data: &mut Funcdata, glb: &mut Architecture) -> Result<TypeId> {
        func_get_output_local(&self.meta, op, data, glb)
    }

    fn get_input_local(&self, op: OpId, slot: i32, data: &mut Funcdata, glb: &mut Architecture) -> Result<TypeId> {
        func_get_input_local(&self.meta, op, slot, data, glb)
    }

    fn print_raw(&mut self, out: &mut String, op: OpId, data: &Funcdata, glb: &Architecture) {
        func_print_raw(&self.get_operator_name(op, data, glb), out, op, data, glb)
    }

    fn push(
        &self,
        lng: &mut dyn PrintLanguage,
        ctx: &mut PrintContext<'_>,
        op: OpId,
        read_op: Option<OpId>,
    ) -> Result<()> {
        lng.op_float_round(ctx, op)
    }
}

pub struct TypeOpMulti {
    pub base: TypeOpBase,
}

impl Default for TypeOpMulti {
    fn default() -> Self {
        Self::new()
    }
}

impl TypeOpMulti {
    pub fn new() -> TypeOpMulti {
        TypeOpMulti {
            base: new_base(
                OpCode::Multiequal,
                "?",
                PcodeOp::SPECIAL | PcodeOp::MARKER | PcodeOp::NOCOLLAPSE,
                0,
                Arc::new(OpBehaviorGeneric::new_special(OpCode::Multiequal, false, true)),
            ),
        }
    }
}

impl TypeOp for TypeOpMulti {
    fn base(&self) -> &TypeOpBase {
        &self.base
    }

    fn base_mut(&mut self) -> &mut TypeOpBase {
        &mut self.base
    }

    fn propagate_type(
        &self,
        alttype: TypeId,
        op: OpId,
        invn: VarnodeId,
        outvn: VarnodeId,
        inslot: i32,
        outslot: i32,
        data: &mut Funcdata,
        glb: &mut Architecture,
    ) -> Result<Option<TypeId>> {
        if inslot != -1 && outslot != -1 {
            return Ok(None);
        }
        pass_through_type(alttype, invn, data, glb).map(Some)
    }

    fn print_raw(&mut self, out: &mut String, op: OpId, data: &Funcdata, glb: &Architecture) {
        let pcode = data.op(op);
        data.vn_print_raw_option(pcode.get_out(), out, glb);
        out.push_str(" = ");
        data.vn_print_raw_option(pcode.get_in_option(0), out, glb);
        let name = self.get_operator_name(op, data, glb);
        if pcode.num_input() == 1 {
            out.push(' ');
            out.push_str(&name);
        }
        for index in 1..pcode.num_input() {
            out.push(' ');
            out.push_str(&name);
            out.push(' ');
            data.vn_print_raw_option(pcode.get_in_option(index), out, glb);
        }
    }

    fn push(
        &self,
        lng: &mut dyn PrintLanguage,
        ctx: &mut PrintContext<'_>,
        op: OpId,
        read_op: Option<OpId>,
    ) -> Result<()> {
        lng.op_multiequal(ctx, op)
    }
}

pub struct TypeOpIndirect {
    pub base: TypeOpBase,
}

impl Default for TypeOpIndirect {
    fn default() -> Self {
        Self::new()
    }
}

impl TypeOpIndirect {
    pub fn new() -> TypeOpIndirect {
        TypeOpIndirect {
            base: new_base(
                OpCode::Indirect,
                "[]",
                PcodeOp::SPECIAL | PcodeOp::MARKER | PcodeOp::NOCOLLAPSE,
                0,
                Arc::new(OpBehaviorGeneric::new_special(OpCode::Indirect, false, true)),
            ),
        }
    }
}

impl TypeOp for TypeOpIndirect {
    fn base(&self) -> &TypeOpBase {
        &self.base
    }

    fn base_mut(&mut self) -> &mut TypeOpBase {
        &mut self.base
    }

    fn get_input_local(&self, op: OpId, slot: i32, data: &mut Funcdata, glb: &mut Architecture) -> Result<TypeId> {
        if slot == 0 {
            return default_input_local(op, slot, data, glb);
        }
        let pcode = data.op(op);
        let iop = PcodeOp::get_op_from_const(data.vn(pcode.get_in(1)).get_addr());
        let wordsize = data
            .op(iop)
            .get_addr()
            .get_space()
            .expect("p-code op address has no space")
            .get_word_size();
        let size = data.vn(pcode.get_in(0)).get_size();
        let ct = types_mut(glb).get_type_code()?;
        types_mut(glb).get_type_pointer(size, ct, wordsize)
    }

    fn propagate_type(
        &self,
        alttype: TypeId,
        op: OpId,
        invn: VarnodeId,
        outvn: VarnodeId,
        inslot: i32,
        outslot: i32,
        data: &mut Funcdata,
        glb: &mut Architecture,
    ) -> Result<Option<TypeId>> {
        if data.op(op).is_indirect_creation() {
            return Ok(None);
        }
        if inslot == 1 || outslot == 1 {
            return Ok(None);
        }
        if inslot != -1 && outslot != -1 {
            return Ok(None);
        }
        pass_through_type(alttype, invn, data, glb).map(Some)
    }

    fn print_raw(&mut self, out: &mut String, op: OpId, data: &Funcdata, glb: &Architecture) {
        let pcode = data.op(op);
        data.vn_print_raw_option(pcode.get_out(), out, glb);
        out.push_str(" = ");
        if pcode.is_indirect_creation() {
            out.push_str("[create] ");
        } else {
            data.vn_print_raw_option(pcode.get_in_option(0), out, glb);
            out.push(' ');
            out.push_str(&self.get_operator_name(op, data, glb));
            out.push(' ');
        }
        data.vn_print_raw_option(pcode.get_in_option(1), out, glb);
    }

    fn push(
        &self,
        lng: &mut dyn PrintLanguage,
        ctx: &mut PrintContext<'_>,
        op: OpId,
        read_op: Option<OpId>,
    ) -> Result<()> {
        lng.op_indirect(ctx, op)
    }
}

pub struct TypeOpPiece {
    pub base: TypeOpBase,
    pub meta: TypeOpMeta,
    pub near_pointer_size: i32,
    pub far_pointer_size: i32,
}

impl TypeOpPiece {
    pub fn new(tlst: &TypeFactory) -> TypeOpPiece {
        let far_pointer_size = tlst.get_size_of_alt_pointer();
        let near_pointer_size = if far_pointer_size != 0 {
            tlst.get_size_of_pointer()
        } else {
            0
        };
        TypeOpPiece {
            base: new_base(
                OpCode::Piece,
                "CONCAT",
                PcodeOp::BINARY,
                0,
                Arc::new(OpBehaviorPiece::new()),
            ),
            meta: TypeOpMeta::new(TypeMetatype::Unknown, TypeMetatype::Unknown),
            near_pointer_size,
            far_pointer_size,
        }
    }

    pub fn compute_byte_offset_for_composite(op: OpId, slot: i32, data: &Funcdata) -> i32 {
        let pcode = data.op(op);
        let in_vn0 = data.vn(pcode.get_in(0));
        if in_vn0
            .get_space()
            .expect("varnode has no address space")
            .is_big_endian()
        {
            if slot == 0 { 0 } else { in_vn0.get_size() }
        } else if slot == 0 {
            data.vn(pcode.get_in(1)).get_size()
        } else {
            0
        }
    }
}

impl TypeOp for TypeOpPiece {
    fn base(&self) -> &TypeOpBase {
        &self.base
    }

    fn base_mut(&mut self) -> &mut TypeOpBase {
        &mut self.base
    }

    fn set_metatype_in(&mut self, val: TypeMetatype) {
        self.meta.metain = val;
    }

    fn set_metatype_out(&mut self, val: TypeMetatype) {
        self.meta.metaout = val;
    }

    fn get_input_cast(
        &self,
        op: OpId,
        slot: i32,
        cast_strategy: &dyn CastStrategy,
        data: &mut Funcdata,
        glb: &mut Architecture,
    ) -> Result<Option<TypeId>> {
        Ok(None)
    }

    fn get_output_token(
        &self,
        op: OpId,
        cast_strategy: &mut dyn CastStrategy,
        data: &mut Funcdata,
        glb: &mut Architecture,
    ) -> Result<TypeId> {
        let vn = out_vn(data, op);
        let dt = data.vn_get_high_type_def_facing(vn, glb)?;
        let meta = types(glb).get(dt).get_metatype();
        if meta == TypeMetatype::Int || meta == TypeMetatype::Uint {
            return Ok(dt);
        }
        let size = data.vn(vn).get_size();
        types_mut(glb).get_base(size, TypeMetatype::Uint)
    }

    fn propagate_type(
        &self,
        alttype: TypeId,
        op: OpId,
        invn: VarnodeId,
        outvn: VarnodeId,
        inslot: i32,
        outslot: i32,
        data: &mut Funcdata,
        glb: &mut Architecture,
    ) -> Result<Option<TypeId>> {
        if self.near_pointer_size != 0 && types(glb).get(alttype).get_metatype() == TypeMetatype::Ptr {
            let insize = data.vn(invn).get_size();
            let outsize = data.vn(outvn).get_size();
            if inslot == 1 && outslot == -1 {
                if insize == self.near_pointer_size && outsize == self.far_pointer_size {
                    return types_mut(glb).resize_pointer(alttype, self.far_pointer_size).map(Some);
                }
            } else if inslot == -1
                && outslot == 1
                && insize == self.far_pointer_size
                && outsize == self.near_pointer_size
            {
                return types_mut(glb).resize_pointer(alttype, self.near_pointer_size).map(Some);
            }
            return Ok(None);
        }
        if inslot != -1 {
            return Ok(None);
        }
        let byte_off = TypeOpPiece::compute_byte_offset_for_composite(op, outslot, data) as i64;
        Ok(descend_to_size(Some(alttype), byte_off, data.vn(outvn).get_size(), glb))
    }

    fn get_operator_name(&self, op: OpId, data: &Funcdata, glb: &Architecture) -> String {
        let pcode = data.op(op);
        format!(
            "{}{}{}",
            self.base.name,
            data.vn(pcode.get_in(0)).get_size(),
            data.vn(pcode.get_in(1)).get_size()
        )
    }

    fn get_output_local(&self, op: OpId, data: &mut Funcdata, glb: &mut Architecture) -> Result<TypeId> {
        func_get_output_local(&self.meta, op, data, glb)
    }

    fn get_input_local(&self, op: OpId, slot: i32, data: &mut Funcdata, glb: &mut Architecture) -> Result<TypeId> {
        func_get_input_local(&self.meta, op, slot, data, glb)
    }

    fn print_raw(&mut self, out: &mut String, op: OpId, data: &Funcdata, glb: &Architecture) {
        func_print_raw(&self.get_operator_name(op, data, glb), out, op, data, glb)
    }

    fn push(
        &self,
        lng: &mut dyn PrintLanguage,
        ctx: &mut PrintContext<'_>,
        op: OpId,
        read_op: Option<OpId>,
    ) -> Result<()> {
        lng.op_piece(ctx, op)
    }
}

pub struct TypeOpSubpiece {
    pub base: TypeOpBase,
    pub meta: TypeOpMeta,
    pub near_pointer_size: i32,
    pub far_pointer_size: i32,
}

impl TypeOpSubpiece {
    pub fn new(tlst: &TypeFactory) -> TypeOpSubpiece {
        let far_pointer_size = tlst.get_size_of_alt_pointer();
        let near_pointer_size = if far_pointer_size != 0 {
            tlst.get_size_of_pointer()
        } else {
            0
        };
        TypeOpSubpiece {
            base: new_base(
                OpCode::Subpiece,
                "SUB",
                PcodeOp::BINARY,
                0,
                Arc::new(OpBehaviorSubpiece::new()),
            ),
            meta: TypeOpMeta::new(TypeMetatype::Unknown, TypeMetatype::Unknown),
            near_pointer_size,
            far_pointer_size,
        }
    }

    pub fn compute_byte_offset_for_composite(op: OpId, data: &Funcdata) -> i32 {
        let pcode = data.op(op);
        let out_size = data.vn(out_vn(data, op)).get_size();
        let lsb = data.vn(pcode.get_in(1)).get_offset() as i32;
        let vn = data.vn(pcode.get_in(0));
        if vn.get_space().expect("varnode has no address space").is_big_endian() {
            vn.get_size() - out_size - lsb
        } else {
            lsb
        }
    }
}

impl TypeOp for TypeOpSubpiece {
    fn base(&self) -> &TypeOpBase {
        &self.base
    }

    fn base_mut(&mut self) -> &mut TypeOpBase {
        &mut self.base
    }

    fn set_metatype_in(&mut self, val: TypeMetatype) {
        self.meta.metain = val;
    }

    fn set_metatype_out(&mut self, val: TypeMetatype) {
        self.meta.metaout = val;
    }

    fn get_input_cast(
        &self,
        op: OpId,
        slot: i32,
        cast_strategy: &dyn CastStrategy,
        data: &mut Funcdata,
        glb: &mut Architecture,
    ) -> Result<Option<TypeId>> {
        Ok(None)
    }

    fn get_output_token(
        &self,
        op: OpId,
        cast_strategy: &mut dyn CastStrategy,
        data: &mut Funcdata,
        glb: &mut Architecture,
    ) -> Result<TypeId> {
        let outvn = out_vn(data, op);
        let invn = data.op(op).get_in(0);
        let ct = data.vn_get_high_type_read_facing(invn, op, glb)?;
        let mut offset: i64 = 0;
        let byte_off = TypeOpSubpiece::compute_byte_offset_for_composite(op, data) as i64;
        let outsize = data.vn(outvn).get_size();
        let factory = types(glb);
        let field = Datatype::find_truncation(ct, byte_off, outsize, op, 1, &mut offset, data, glb);
        if let Some(field) = field
            && outsize == factory.get(field.tp).get_size()
        {
            return Ok(field.tp);
        }
        let dt = data.vn_get_high_type_def_facing(outvn, glb)?;
        if types(glb).get(dt).get_metatype() != TypeMetatype::Unknown {
            return Ok(dt);
        }
        types_mut(glb).get_base(outsize, TypeMetatype::Int)
    }

    fn propagate_type(
        &self,
        alttype: TypeId,
        op: OpId,
        invn: VarnodeId,
        outvn: VarnodeId,
        inslot: i32,
        outslot: i32,
        data: &mut Funcdata,
        glb: &mut Architecture,
    ) -> Result<Option<TypeId>> {
        if self.near_pointer_size != 0
            && types(glb).get(alttype).get_metatype() == TypeMetatype::Ptr
            && inslot == -1
            && outslot == 0
        {
            if data.vn(data.op(op).get_in(1)).get_offset() != 0 {
                return Ok(None);
            }
            if data.vn(invn).get_size() == self.near_pointer_size && data.vn(outvn).get_size() == self.far_pointer_size
            {
                return types_mut(glb).resize_pointer(alttype, self.far_pointer_size).map(Some);
            }
            return Ok(None);
        }
        if inslot != 0 || outslot != -1 {
            return Ok(None);
        }
        let mut byte_off = TypeOpSubpiece::compute_byte_offset_for_composite(op, data) as i64;
        let meta = types(glb).get(alttype).get_metatype();
        let mut current = Some(alttype);
        if meta == TypeMetatype::Union || meta == TypeMetatype::PartialUnion {
            let mut newoff = byte_off;
            let field = Datatype::resolve_truncation(alttype, byte_off, op, 1, &mut newoff, data, glb)?;
            byte_off = newoff;
            current = field.map(|field| field.tp);
        }
        Ok(descend_to_size(current, byte_off, data.vn(outvn).get_size(), glb))
    }

    fn get_operator_name(&self, op: OpId, data: &Funcdata, glb: &Architecture) -> String {
        let pcode = data.op(op);
        format!(
            "{}{}{}",
            self.base.name,
            data.vn(pcode.get_in(0)).get_size(),
            data.vn(out_vn(data, op)).get_size()
        )
    }

    fn get_output_local(&self, op: OpId, data: &mut Funcdata, glb: &mut Architecture) -> Result<TypeId> {
        func_get_output_local(&self.meta, op, data, glb)
    }

    fn get_input_local(&self, op: OpId, slot: i32, data: &mut Funcdata, glb: &mut Architecture) -> Result<TypeId> {
        func_get_input_local(&self.meta, op, slot, data, glb)
    }

    fn print_raw(&mut self, out: &mut String, op: OpId, data: &Funcdata, glb: &Architecture) {
        func_print_raw(&self.get_operator_name(op, data, glb), out, op, data, glb)
    }

    fn push(
        &self,
        lng: &mut dyn PrintLanguage,
        ctx: &mut PrintContext<'_>,
        op: OpId,
        read_op: Option<OpId>,
    ) -> Result<()> {
        lng.op_subpiece(ctx, op)
    }
}

pub struct TypeOpCast {
    pub base: TypeOpBase,
}

impl Default for TypeOpCast {
    fn default() -> Self {
        Self::new()
    }
}

impl TypeOpCast {
    pub fn new() -> TypeOpCast {
        TypeOpCast {
            base: new_base(
                OpCode::Cast,
                "(cast)",
                PcodeOp::UNARY | PcodeOp::SPECIAL | PcodeOp::NOCOLLAPSE,
                0,
                Arc::new(OpBehaviorGeneric::new_special(OpCode::Cast, false, true)),
            ),
        }
    }
}

impl TypeOp for TypeOpCast {
    fn base(&self) -> &TypeOpBase {
        &self.base
    }

    fn base_mut(&mut self) -> &mut TypeOpBase {
        &mut self.base
    }

    fn print_raw(&mut self, out: &mut String, op: OpId, data: &Funcdata, glb: &Architecture) {
        unary_print_raw(&self.base.name, out, op, data, glb)
    }

    fn push(
        &self,
        lng: &mut dyn PrintLanguage,
        ctx: &mut PrintContext<'_>,
        op: OpId,
        read_op: Option<OpId>,
    ) -> Result<()> {
        lng.op_cast(ctx, op)
    }
}

pub struct TypeOpPtradd {
    pub base: TypeOpBase,
}

impl Default for TypeOpPtradd {
    fn default() -> Self {
        Self::new()
    }
}

impl TypeOpPtradd {
    pub fn new() -> TypeOpPtradd {
        TypeOpPtradd {
            base: new_base(
                OpCode::Ptradd,
                "+",
                PcodeOp::TERNARY | PcodeOp::NOCOLLAPSE,
                ARITHMETIC_OP,
                Arc::new(OpBehaviorPtradd::new()),
            ),
        }
    }
}

impl TypeOp for TypeOpPtradd {
    fn base(&self) -> &TypeOpBase {
        &self.base
    }

    fn base_mut(&mut self) -> &mut TypeOpBase {
        &mut self.base
    }

    fn get_input_local(&self, op: OpId, slot: i32, data: &mut Funcdata, glb: &mut Architecture) -> Result<TypeId> {
        let size = data.vn(data.op(op).get_in(slot)).get_size();
        types_mut(glb).get_base(size, TypeMetatype::Int)
    }

    fn get_output_local(&self, op: OpId, data: &mut Funcdata, glb: &mut Architecture) -> Result<TypeId> {
        let size = data.vn(out_vn(data, op)).get_size();
        types_mut(glb).get_base(size, TypeMetatype::Int)
    }

    fn get_output_token(
        &self,
        op: OpId,
        cast_strategy: &mut dyn CastStrategy,
        data: &mut Funcdata,
        glb: &mut Architecture,
    ) -> Result<TypeId> {
        let invn = data.op(op).get_in(0);
        data.vn_get_high_type_read_facing(invn, op, glb)
    }

    fn get_input_cast(
        &self,
        op: OpId,
        slot: i32,
        cast_strategy: &dyn CastStrategy,
        data: &mut Funcdata,
        glb: &mut Architecture,
    ) -> Result<Option<TypeId>> {
        if slot == 0 {
            let invn = data.op(op).get_in(0);
            let reqtype = data.vn_get_type_read_facing(invn, op, glb);
            let curtype = data.vn_get_high_type_read_facing(invn, op, glb)?;
            let factory = types(glb);
            if factory.get(reqtype).get_metatype() != TypeMetatype::Ptr {
                return Ok(Some(reqtype));
            }
            if factory.get(curtype).get_metatype() != TypeMetatype::Ptr {
                return Ok(Some(reqtype));
            }
            let reqbase = factory.get(reqtype).get_ptr_to();
            let curbase = factory.get(curtype).get_ptr_to();
            if factory.get(reqbase).get_align_size() == factory.get(curbase).get_align_size() {
                return Ok(None);
            }
            return Ok(Some(reqtype));
        }
        base_input_cast(self, op, slot, cast_strategy, data, glb)
    }

    fn propagate_type(
        &self,
        alttype: TypeId,
        op: OpId,
        invn: VarnodeId,
        outvn: VarnodeId,
        inslot: i32,
        outslot: i32,
        data: &mut Funcdata,
        glb: &mut Architecture,
    ) -> Result<Option<TypeId>> {
        if inslot == 2 || outslot == 2 {
            return Ok(None);
        }
        if inslot != -1 && outslot != -1 {
            return Ok(None);
        }
        if types(glb).get(alttype).get_metatype() != TypeMetatype::Ptr {
            return Ok(None);
        }
        if inslot == -1 {
            Ok(None)
        } else {
            TypeOpIntAdd::propagate_add_in2_out(alttype, op, inslot, data, glb)
        }
    }

    fn print_raw(&mut self, out: &mut String, op: OpId, data: &Funcdata, glb: &Architecture) {
        let pcode = data.op(op);
        data.vn_print_raw_option(pcode.get_out(), out, glb);
        out.push_str(" = ");
        data.vn_print_raw_option(pcode.get_in_option(0), out, glb);
        out.push(' ');
        out.push_str(&self.base.name);
        out.push(' ');
        data.vn_print_raw_option(pcode.get_in_option(1), out, glb);
        out.push_str("(*");
        data.vn_print_raw_option(pcode.get_in_option(2), out, glb);
        out.push(')');
    }

    fn push(
        &self,
        lng: &mut dyn PrintLanguage,
        ctx: &mut PrintContext<'_>,
        op: OpId,
        read_op: Option<OpId>,
    ) -> Result<()> {
        lng.op_ptradd(ctx, op)
    }
}

pub struct TypeOpPtrsub {
    pub base: TypeOpBase,
}

impl Default for TypeOpPtrsub {
    fn default() -> Self {
        Self::new()
    }
}

impl TypeOpPtrsub {
    pub fn new() -> TypeOpPtrsub {
        TypeOpPtrsub {
            base: new_base(
                OpCode::Ptrsub,
                "->",
                PcodeOp::BINARY | PcodeOp::NOCOLLAPSE,
                ARITHMETIC_OP,
                Arc::new(OpBehaviorPtrsub::new()),
            ),
        }
    }
}

impl TypeOp for TypeOpPtrsub {
    fn base(&self) -> &TypeOpBase {
        &self.base
    }

    fn base_mut(&mut self) -> &mut TypeOpBase {
        &mut self.base
    }

    fn get_output_local(&self, op: OpId, data: &mut Funcdata, glb: &mut Architecture) -> Result<TypeId> {
        let size = data.vn(out_vn(data, op)).get_size();
        types_mut(glb).get_base(size, TypeMetatype::Int)
    }

    fn get_input_local(&self, op: OpId, slot: i32, data: &mut Funcdata, glb: &mut Architecture) -> Result<TypeId> {
        let size = data.vn(data.op(op).get_in(slot)).get_size();
        types_mut(glb).get_base(size, TypeMetatype::Int)
    }

    fn get_input_cast(
        &self,
        op: OpId,
        slot: i32,
        cast_strategy: &dyn CastStrategy,
        data: &mut Funcdata,
        glb: &mut Architecture,
    ) -> Result<Option<TypeId>> {
        if slot == 0 {
            let invn = data.op(op).get_in(0);
            let reqtype = data.vn_get_type_read_facing(invn, op, glb);
            let curtype = data.vn_get_high_type_read_facing(invn, op, glb)?;
            if curtype == reqtype {
                return Ok(None);
            }
            let factory = types(glb);
            if factory.get(reqtype).get_metatype() != TypeMetatype::Ptr {
                return Ok(Some(reqtype));
            }
            if factory.get(curtype).get_metatype() != TypeMetatype::Ptr {
                return Ok(Some(reqtype));
            }
            let mut reqbase = factory.get(reqtype).get_ptr_to();
            let mut curbase = factory.get(curtype).get_ptr_to();
            if factory.get(curbase).get_metatype() == TypeMetatype::Array
                && factory.get(reqbase).get_metatype() == TypeMetatype::Array
            {
                curbase = factory.get(curbase).get_base();
                reqbase = factory.get(reqbase).get_base();
            }
            while let Some(typedef) = factory.get(reqbase).get_typedef() {
                reqbase = typedef;
            }
            while let Some(typedef) = factory.get(curbase).get_typedef() {
                curbase = typedef;
            }
            if curbase == reqbase {
                return Ok(None);
            }
            return Ok(Some(reqtype));
        }
        base_input_cast(self, op, slot, cast_strategy, data, glb)
    }

    fn get_output_token(
        &self,
        op: OpId,
        cast_strategy: &mut dyn CastStrategy,
        data: &mut Funcdata,
        glb: &mut Architecture,
    ) -> Result<TypeId> {
        let invn = data.op(op).get_in(0);
        let ptype = data.vn_get_high_type_read_facing(invn, op, glb)?;
        if types(glb).get(ptype).get_metatype() == TypeMetatype::Ptr {
            let wordsize = types(glb).get(ptype).get_word_size();
            let raw_offset = data.vn(data.op(op).get_in(1)).get_offset();
            let mut offset = AddrSpace::address_to_byte(raw_offset, wordsize) as i64;
            let mut unused_offset: i64 = 0;
            let mut unused_parent: Option<TypeId> = None;
            let rettype = Datatype::down_chain(ptype, &mut offset, &mut unused_parent, &mut unused_offset, false, glb)?;
            if offset == 0
                && let Some(rettype) = rettype
            {
                return Ok(rettype);
            }
            let unknown = types_mut(glb).get_base(1, TypeMetatype::Unknown)?;
            let size = data.vn(out_vn(data, op)).get_size();
            return types_mut(glb).get_type_pointer(size, unknown, wordsize);
        }
        self.get_output_local(op, data, glb)
    }

    fn propagate_type(
        &self,
        alttype: TypeId,
        op: OpId,
        invn: VarnodeId,
        outvn: VarnodeId,
        inslot: i32,
        outslot: i32,
        data: &mut Funcdata,
        glb: &mut Architecture,
    ) -> Result<Option<TypeId>> {
        if inslot != -1 && outslot != -1 {
            return Ok(None);
        }
        if types(glb).get(alttype).get_metatype() != TypeMetatype::Ptr {
            return Ok(None);
        }
        if inslot == -1 {
            Ok(None)
        } else {
            TypeOpIntAdd::propagate_add_in2_out(alttype, op, inslot, data, glb)
        }
    }

    fn print_raw(&mut self, out: &mut String, op: OpId, data: &Funcdata, glb: &Architecture) {
        let pcode = data.op(op);
        data.vn_print_raw_option(pcode.get_out(), out, glb);
        out.push_str(" = ");
        data.vn_print_raw_option(pcode.get_in_option(0), out, glb);
        out.push(' ');
        out.push_str(&self.base.name);
        out.push(' ');
        data.vn_print_raw_option(pcode.get_in_option(1), out, glb);
    }

    fn push(
        &self,
        lng: &mut dyn PrintLanguage,
        ctx: &mut PrintContext<'_>,
        op: OpId,
        read_op: Option<OpId>,
    ) -> Result<()> {
        lng.op_ptrsub(ctx, op)
    }
}

pub struct TypeOpSegment {
    pub base: TypeOpBase,
}

impl Default for TypeOpSegment {
    fn default() -> Self {
        Self::new()
    }
}

impl TypeOpSegment {
    pub fn new() -> TypeOpSegment {
        TypeOpSegment {
            base: new_base(
                OpCode::Segmentop,
                "segmentop",
                PcodeOp::SPECIAL | PcodeOp::NOCOLLAPSE,
                0,
                Arc::new(OpBehaviorGeneric::new_special(OpCode::Segmentop, false, true)),
            ),
        }
    }
}

impl TypeOp for TypeOpSegment {
    fn base(&self) -> &TypeOpBase {
        &self.base
    }

    fn base_mut(&mut self) -> &mut TypeOpBase {
        &mut self.base
    }

    fn get_input_cast(
        &self,
        op: OpId,
        slot: i32,
        cast_strategy: &dyn CastStrategy,
        data: &mut Funcdata,
        glb: &mut Architecture,
    ) -> Result<Option<TypeId>> {
        Ok(None)
    }

    fn get_output_token(
        &self,
        op: OpId,
        cast_strategy: &mut dyn CastStrategy,
        data: &mut Funcdata,
        glb: &mut Architecture,
    ) -> Result<TypeId> {
        let invn = data.op(op).get_in(2);
        data.vn_get_high_type_read_facing(invn, op, glb)
    }

    fn propagate_type(
        &self,
        alttype: TypeId,
        op: OpId,
        invn: VarnodeId,
        outvn: VarnodeId,
        inslot: i32,
        outslot: i32,
        data: &mut Funcdata,
        glb: &mut Architecture,
    ) -> Result<Option<TypeId>> {
        if inslot == 0 || inslot == 1 {
            return Ok(None);
        }
        if outslot == 0 || outslot == 1 {
            return Ok(None);
        }
        if data.vn(invn).is_spacebase() {
            return Ok(None);
        }
        if types(glb).get(alttype).get_metatype() != TypeMetatype::Ptr {
            return Ok(None);
        }
        let size = data.vn(outvn).get_size();
        types_mut(glb).resize_pointer(alttype, size).map(Some)
    }

    fn print_raw(&mut self, out: &mut String, op: OpId, data: &Funcdata, glb: &Architecture) {
        let pcode = data.op(op);
        if pcode.get_out().is_some() {
            data.vn_print_raw_option(pcode.get_out(), out, glb);
            out.push_str(" = ");
        }
        out.push_str(&self.get_operator_name(op, data, glb));
        out.push('(');
        let spc = const_space(data, pcode.get_in(0), glb);
        out.push_str(spc.get_name());
        out.push(',');
        data.vn_print_raw_option(pcode.get_in_option(1), out, glb);
        out.push(',');
        data.vn_print_raw_option(pcode.get_in_option(2), out, glb);
        out.push(')');
    }

    fn push(
        &self,
        lng: &mut dyn PrintLanguage,
        ctx: &mut PrintContext<'_>,
        op: OpId,
        read_op: Option<OpId>,
    ) -> Result<()> {
        lng.op_segment_op(ctx, op)
    }
}

pub struct TypeOpCpoolref {
    pub base: TypeOpBase,
}

impl Default for TypeOpCpoolref {
    fn default() -> Self {
        Self::new()
    }
}

impl TypeOpCpoolref {
    pub fn new() -> TypeOpCpoolref {
        TypeOpCpoolref {
            base: new_base(
                OpCode::Cpoolref,
                "cpoolref",
                PcodeOp::SPECIAL | PcodeOp::NOCOLLAPSE,
                0,
                Arc::new(OpBehaviorGeneric::new_special(OpCode::Cpoolref, false, true)),
            ),
        }
    }
}

impl TypeOp for TypeOpCpoolref {
    fn base(&self) -> &TypeOpBase {
        &self.base
    }

    fn base_mut(&mut self) -> &mut TypeOpBase {
        &mut self.base
    }

    fn get_input_cast(
        &self,
        op: OpId,
        slot: i32,
        cast_strategy: &dyn CastStrategy,
        data: &mut Funcdata,
        glb: &mut Architecture,
    ) -> Result<Option<TypeId>> {
        Ok(None)
    }

    fn get_output_local(&self, op: OpId, data: &mut Funcdata, glb: &mut Architecture) -> Result<TypeId> {
        let refs = cpool_refs(op, data);
        let found = glb
            .cpool
            .as_deref()
            .expect("missing constant pool")
            .get_record(&refs)
            .map(|rec| (rec.get_tag(), rec.get_type()));
        match found {
            None => default_output_local(op, data, glb),
            Some((tag, _)) if tag == CPoolRecord::INSTANCE_OF => types_mut(glb).get_base(1, TypeMetatype::Bool),
            Some((_, Some(tp))) => Ok(tp),
            Some((_, None)) => default_output_local(op, data, glb),
        }
    }

    fn get_input_local(&self, op: OpId, slot: i32, data: &mut Funcdata, glb: &mut Architecture) -> Result<TypeId> {
        let size = data.vn(data.op(op).get_in(slot)).get_size();
        types_mut(glb).get_base(size, TypeMetatype::Int)
    }

    fn print_raw(&mut self, out: &mut String, op: OpId, data: &Funcdata, glb: &Architecture) {
        let pcode = data.op(op);
        if pcode.get_out().is_some() {
            data.vn_print_raw_option(pcode.get_out(), out, glb);
            out.push_str(" = ");
        }
        out.push_str(&self.get_operator_name(op, data, glb));
        let refs = cpool_refs(op, data);
        if let Some(rec) = glb.cpool.as_deref().expect("missing constant pool").get_record(&refs) {
            out.push('_');
            out.push_str(rec.get_token());
        }
        out.push('(');
        data.vn_print_raw_option(pcode.get_in_option(0), out, glb);
        for index in 2..pcode.num_input() {
            out.push(',');
            data.vn_print_raw_option(pcode.get_in_option(index), out, glb);
        }
        out.push(')');
    }

    fn push(
        &self,
        lng: &mut dyn PrintLanguage,
        ctx: &mut PrintContext<'_>,
        op: OpId,
        read_op: Option<OpId>,
    ) -> Result<()> {
        lng.op_cpool_ref_op(ctx, op)
    }
}

pub struct TypeOpNew {
    pub base: TypeOpBase,
}

impl Default for TypeOpNew {
    fn default() -> Self {
        Self::new()
    }
}

impl TypeOpNew {
    pub fn new() -> TypeOpNew {
        TypeOpNew {
            base: new_base(
                OpCode::New,
                "new",
                PcodeOp::SPECIAL | PcodeOp::CALL | PcodeOp::NOCOLLAPSE,
                0,
                Arc::new(OpBehaviorGeneric::new_special(OpCode::New, false, true)),
            ),
        }
    }
}

impl TypeOp for TypeOpNew {
    fn base(&self) -> &TypeOpBase {
        &self.base
    }

    fn base_mut(&mut self) -> &mut TypeOpBase {
        &mut self.base
    }

    fn get_input_cast(
        &self,
        op: OpId,
        slot: i32,
        cast_strategy: &dyn CastStrategy,
        data: &mut Funcdata,
        glb: &mut Architecture,
    ) -> Result<Option<TypeId>> {
        Ok(None)
    }

    fn propagate_type(
        &self,
        alttype: TypeId,
        op: OpId,
        invn: VarnodeId,
        outvn: VarnodeId,
        inslot: i32,
        outslot: i32,
        data: &mut Funcdata,
        glb: &mut Architecture,
    ) -> Result<Option<TypeId>> {
        if inslot != 0 || outslot != -1 {
            return Ok(None);
        }
        let vn0 = data.op(op).get_in(0);
        if !data.vn(vn0).is_written() {
            return Ok(None);
        }
        if def_code(data, vn0) != Some(OpCode::Cpoolref) {
            return Ok(None);
        }
        Ok(Some(alttype))
    }

    fn print_raw(&mut self, out: &mut String, op: OpId, data: &Funcdata, glb: &Architecture) {
        let pcode = data.op(op);
        if pcode.get_out().is_some() {
            data.vn_print_raw_option(pcode.get_out(), out, glb);
            out.push_str(" = ");
        }
        out.push_str(&self.get_operator_name(op, data, glb));
        print_input_list(data, op, 0, out, glb);
    }

    fn push(
        &self,
        lng: &mut dyn PrintLanguage,
        ctx: &mut PrintContext<'_>,
        op: OpId,
        read_op: Option<OpId>,
    ) -> Result<()> {
        lng.op_new_op(ctx, op)
    }
}

pub struct TypeOpInsert {
    pub base: TypeOpBase,
    pub meta: TypeOpMeta,
}

impl Default for TypeOpInsert {
    fn default() -> Self {
        Self::new()
    }
}

impl TypeOpInsert {
    pub fn new() -> TypeOpInsert {
        TypeOpInsert {
            base: new_base(
                OpCode::Insert,
                "INSERT",
                PcodeOp::TERNARY,
                0,
                Arc::new(OpBehaviorGeneric::new(OpCode::Insert, false)),
            ),
            meta: TypeOpMeta::new(TypeMetatype::Unknown, TypeMetatype::Int),
        }
    }
}

impl TypeOp for TypeOpInsert {
    fn base(&self) -> &TypeOpBase {
        &self.base
    }

    fn base_mut(&mut self) -> &mut TypeOpBase {
        &mut self.base
    }

    fn set_metatype_in(&mut self, val: TypeMetatype) {
        self.meta.metain = val;
    }

    fn set_metatype_out(&mut self, val: TypeMetatype) {
        self.meta.metaout = val;
    }

    fn get_input_local(&self, op: OpId, slot: i32, data: &mut Funcdata, glb: &mut Architecture) -> Result<TypeId> {
        if slot <= 1 {
            let size = data.vn(data.op(op).get_in(slot)).get_size();
            return types_mut(glb).get_base(size, TypeMetatype::Unknown);
        }
        func_get_input_local(&self.meta, op, slot, data, glb)
    }

    fn get_input_cast(
        &self,
        op: OpId,
        slot: i32,
        cast_strategy: &dyn CastStrategy,
        data: &mut Funcdata,
        glb: &mut Architecture,
    ) -> Result<Option<TypeId>> {
        Ok(None)
    }

    fn get_output_token(
        &self,
        op: OpId,
        cast_strategy: &mut dyn CastStrategy,
        data: &mut Funcdata,
        glb: &mut Architecture,
    ) -> Result<TypeId> {
        let outvn = out_vn(data, op);
        data.vn_get_high_type_def_facing(outvn, glb)
    }

    fn get_output_local(&self, op: OpId, data: &mut Funcdata, glb: &mut Architecture) -> Result<TypeId> {
        func_get_output_local(&self.meta, op, data, glb)
    }

    fn print_raw(&mut self, out: &mut String, op: OpId, data: &Funcdata, glb: &Architecture) {
        func_print_raw(&self.get_operator_name(op, data, glb), out, op, data, glb)
    }

    fn push(
        &self,
        lng: &mut dyn PrintLanguage,
        ctx: &mut PrintContext<'_>,
        op: OpId,
        read_op: Option<OpId>,
    ) -> Result<()> {
        lng.op_insert_op(ctx, op)
    }
}

pub struct TypeOpZpull {
    pub base: TypeOpBase,
    pub meta: TypeOpMeta,
}

impl Default for TypeOpZpull {
    fn default() -> Self {
        Self::new()
    }
}

impl TypeOpZpull {
    pub fn new() -> TypeOpZpull {
        TypeOpZpull {
            base: new_base(
                OpCode::Zpull,
                "ZPULL",
                PcodeOp::TERNARY,
                0,
                Arc::new(OpBehaviorGeneric::new(OpCode::Zpull, false)),
            ),
            meta: TypeOpMeta::new(TypeMetatype::Uint, TypeMetatype::Int),
        }
    }
}

impl TypeOp for TypeOpZpull {
    fn base(&self) -> &TypeOpBase {
        &self.base
    }

    fn base_mut(&mut self) -> &mut TypeOpBase {
        &mut self.base
    }

    fn set_metatype_in(&mut self, val: TypeMetatype) {
        self.meta.metain = val;
    }

    fn set_metatype_out(&mut self, val: TypeMetatype) {
        self.meta.metaout = val;
    }

    fn get_input_local(&self, op: OpId, slot: i32, data: &mut Funcdata, glb: &mut Architecture) -> Result<TypeId> {
        if slot == 0 {
            let size = data.vn(data.op(op).get_in(slot)).get_size();
            return types_mut(glb).get_base(size, TypeMetatype::Unknown);
        }
        func_get_input_local(&self.meta, op, slot, data, glb)
    }

    fn get_input_cast(
        &self,
        op: OpId,
        slot: i32,
        cast_strategy: &dyn CastStrategy,
        data: &mut Funcdata,
        glb: &mut Architecture,
    ) -> Result<Option<TypeId>> {
        Ok(None)
    }

    fn get_output_token(
        &self,
        op: OpId,
        cast_strategy: &mut dyn CastStrategy,
        data: &mut Funcdata,
        glb: &mut Architecture,
    ) -> Result<TypeId> {
        let outvn = out_vn(data, op);
        data.vn_get_high_type_def_facing(outvn, glb)
    }

    fn get_output_local(&self, op: OpId, data: &mut Funcdata, glb: &mut Architecture) -> Result<TypeId> {
        func_get_output_local(&self.meta, op, data, glb)
    }

    fn print_raw(&mut self, out: &mut String, op: OpId, data: &Funcdata, glb: &Architecture) {
        func_print_raw(&self.get_operator_name(op, data, glb), out, op, data, glb)
    }

    fn push(
        &self,
        lng: &mut dyn PrintLanguage,
        ctx: &mut PrintContext<'_>,
        op: OpId,
        read_op: Option<OpId>,
    ) -> Result<()> {
        lng.op_zpull_op(ctx, op)
    }
}

pub struct TypeOpSpull {
    pub base: TypeOpBase,
    pub meta: TypeOpMeta,
}

impl Default for TypeOpSpull {
    fn default() -> Self {
        Self::new()
    }
}

impl TypeOpSpull {
    pub fn new() -> TypeOpSpull {
        TypeOpSpull {
            base: new_base(
                OpCode::Spull,
                "SPULL",
                PcodeOp::TERNARY,
                0,
                Arc::new(OpBehaviorGeneric::new(OpCode::Spull, false)),
            ),
            meta: TypeOpMeta::new(TypeMetatype::Int, TypeMetatype::Int),
        }
    }
}

impl TypeOp for TypeOpSpull {
    fn base(&self) -> &TypeOpBase {
        &self.base
    }

    fn base_mut(&mut self) -> &mut TypeOpBase {
        &mut self.base
    }

    fn set_metatype_in(&mut self, val: TypeMetatype) {
        self.meta.metain = val;
    }

    fn set_metatype_out(&mut self, val: TypeMetatype) {
        self.meta.metaout = val;
    }

    fn get_input_local(&self, op: OpId, slot: i32, data: &mut Funcdata, glb: &mut Architecture) -> Result<TypeId> {
        if slot == 0 {
            let size = data.vn(data.op(op).get_in(slot)).get_size();
            return types_mut(glb).get_base(size, TypeMetatype::Unknown);
        }
        func_get_input_local(&self.meta, op, slot, data, glb)
    }

    fn get_input_cast(
        &self,
        op: OpId,
        slot: i32,
        cast_strategy: &dyn CastStrategy,
        data: &mut Funcdata,
        glb: &mut Architecture,
    ) -> Result<Option<TypeId>> {
        Ok(None)
    }

    fn get_output_token(
        &self,
        op: OpId,
        cast_strategy: &mut dyn CastStrategy,
        data: &mut Funcdata,
        glb: &mut Architecture,
    ) -> Result<TypeId> {
        let outvn = out_vn(data, op);
        data.vn_get_high_type_def_facing(outvn, glb)
    }

    fn get_output_local(&self, op: OpId, data: &mut Funcdata, glb: &mut Architecture) -> Result<TypeId> {
        func_get_output_local(&self.meta, op, data, glb)
    }

    fn print_raw(&mut self, out: &mut String, op: OpId, data: &Funcdata, glb: &Architecture) {
        func_print_raw(&self.get_operator_name(op, data, glb), out, op, data, glb)
    }

    fn push(
        &self,
        lng: &mut dyn PrintLanguage,
        ctx: &mut PrintContext<'_>,
        op: OpId,
        read_op: Option<OpId>,
    ) -> Result<()> {
        lng.op_spull_op(ctx, op)
    }
}

pub struct TypeOpPopcount {
    pub base: TypeOpBase,
    pub meta: TypeOpMeta,
}

impl Default for TypeOpPopcount {
    fn default() -> Self {
        Self::new()
    }
}

impl TypeOpPopcount {
    pub fn new() -> TypeOpPopcount {
        TypeOpPopcount {
            base: new_base(
                OpCode::Popcount,
                "POPCOUNT",
                PcodeOp::UNARY,
                0,
                Arc::new(OpBehaviorPopcount::new()),
            ),
            meta: TypeOpMeta::new(TypeMetatype::Int, TypeMetatype::Unknown),
        }
    }
}

impl TypeOp for TypeOpPopcount {
    fn base(&self) -> &TypeOpBase {
        &self.base
    }

    fn base_mut(&mut self) -> &mut TypeOpBase {
        &mut self.base
    }

    fn set_metatype_in(&mut self, val: TypeMetatype) {
        self.meta.metain = val;
    }

    fn set_metatype_out(&mut self, val: TypeMetatype) {
        self.meta.metaout = val;
    }

    fn get_output_local(&self, op: OpId, data: &mut Funcdata, glb: &mut Architecture) -> Result<TypeId> {
        func_get_output_local(&self.meta, op, data, glb)
    }

    fn get_input_local(&self, op: OpId, slot: i32, data: &mut Funcdata, glb: &mut Architecture) -> Result<TypeId> {
        func_get_input_local(&self.meta, op, slot, data, glb)
    }

    fn print_raw(&mut self, out: &mut String, op: OpId, data: &Funcdata, glb: &Architecture) {
        func_print_raw(&self.get_operator_name(op, data, glb), out, op, data, glb)
    }

    fn push(
        &self,
        lng: &mut dyn PrintLanguage,
        ctx: &mut PrintContext<'_>,
        op: OpId,
        read_op: Option<OpId>,
    ) -> Result<()> {
        lng.op_popcount_op(ctx, op)
    }
}

pub struct TypeOpLzcount {
    pub base: TypeOpBase,
    pub meta: TypeOpMeta,
}

impl Default for TypeOpLzcount {
    fn default() -> Self {
        Self::new()
    }
}

impl TypeOpLzcount {
    pub fn new() -> TypeOpLzcount {
        TypeOpLzcount {
            base: new_base(
                OpCode::Lzcount,
                "LZCOUNT",
                PcodeOp::UNARY,
                0,
                Arc::new(OpBehaviorLzcount::new()),
            ),
            meta: TypeOpMeta::new(TypeMetatype::Int, TypeMetatype::Unknown),
        }
    }
}

impl TypeOp for TypeOpLzcount {
    fn base(&self) -> &TypeOpBase {
        &self.base
    }

    fn base_mut(&mut self) -> &mut TypeOpBase {
        &mut self.base
    }

    fn set_metatype_in(&mut self, val: TypeMetatype) {
        self.meta.metain = val;
    }

    fn set_metatype_out(&mut self, val: TypeMetatype) {
        self.meta.metaout = val;
    }

    fn get_output_local(&self, op: OpId, data: &mut Funcdata, glb: &mut Architecture) -> Result<TypeId> {
        func_get_output_local(&self.meta, op, data, glb)
    }

    fn get_input_local(&self, op: OpId, slot: i32, data: &mut Funcdata, glb: &mut Architecture) -> Result<TypeId> {
        func_get_input_local(&self.meta, op, slot, data, glb)
    }

    fn print_raw(&mut self, out: &mut String, op: OpId, data: &Funcdata, glb: &Architecture) {
        func_print_raw(&self.get_operator_name(op, data, glb), out, op, data, glb)
    }

    fn push(
        &self,
        lng: &mut dyn PrintLanguage,
        ctx: &mut PrintContext<'_>,
        op: OpId,
        read_op: Option<OpId>,
    ) -> Result<()> {
        lng.op_lzcount_op(ctx, op)
    }
}

pub fn binary_get_output_local(
    meta: &TypeOpMeta,
    op: OpId,
    data: &mut Funcdata,
    glb: &mut Architecture,
) -> Result<TypeId> {
    let size = data.vn(out_vn(data, op)).get_size();
    types_mut(glb).get_base(size, meta.metaout)
}

pub fn binary_get_input_local(
    meta: &TypeOpMeta,
    op: OpId,
    slot: i32,
    data: &mut Funcdata,
    glb: &mut Architecture,
) -> Result<TypeId> {
    let size = data.vn(data.op(op).get_in(slot)).get_size();
    types_mut(glb).get_base(size, meta.metain)
}

pub fn binary_print_raw(name: &str, out: &mut String, op: OpId, data: &Funcdata, glb: &Architecture) {
    let pcode = data.op(op);
    data.vn_print_raw_option(pcode.get_out(), out, glb);
    out.push_str(" = ");
    data.vn_print_raw_option(pcode.get_in_option(0), out, glb);
    out.push(' ');
    out.push_str(name);
    out.push(' ');
    data.vn_print_raw_option(pcode.get_in_option(1), out, glb);
}

pub fn unary_get_output_local(
    meta: &TypeOpMeta,
    op: OpId,
    data: &mut Funcdata,
    glb: &mut Architecture,
) -> Result<TypeId> {
    let size = data.vn(out_vn(data, op)).get_size();
    types_mut(glb).get_base(size, meta.metaout)
}

pub fn unary_get_input_local(
    meta: &TypeOpMeta,
    op: OpId,
    slot: i32,
    data: &mut Funcdata,
    glb: &mut Architecture,
) -> Result<TypeId> {
    let size = data.vn(data.op(op).get_in(slot)).get_size();
    types_mut(glb).get_base(size, meta.metain)
}

pub fn unary_print_raw(name: &str, out: &mut String, op: OpId, data: &Funcdata, glb: &Architecture) {
    let pcode = data.op(op);
    data.vn_print_raw_option(pcode.get_out(), out, glb);
    out.push_str(" = ");
    out.push_str(name);
    out.push(' ');
    data.vn_print_raw_option(pcode.get_in_option(0), out, glb);
}

pub fn func_get_output_local(
    meta: &TypeOpMeta,
    op: OpId,
    data: &mut Funcdata,
    glb: &mut Architecture,
) -> Result<TypeId> {
    let size = data.vn(out_vn(data, op)).get_size();
    types_mut(glb).get_base(size, meta.metaout)
}

pub fn func_get_input_local(
    meta: &TypeOpMeta,
    op: OpId,
    slot: i32,
    data: &mut Funcdata,
    glb: &mut Architecture,
) -> Result<TypeId> {
    let size = data.vn(data.op(op).get_in(slot)).get_size();
    types_mut(glb).get_base(size, meta.metain)
}

pub fn func_print_raw(name: &str, out: &mut String, op: OpId, data: &Funcdata, glb: &Architecture) {
    let pcode = data.op(op);
    data.vn_print_raw_option(pcode.get_out(), out, glb);
    out.push_str(" = ");
    out.push_str(name);
    out.push('(');
    data.vn_print_raw_option(pcode.get_in_option(0), out, glb);
    for index in 1..pcode.num_input() {
        out.push(',');
        data.vn_print_raw_option(pcode.get_in_option(index), out, glb);
    }
    out.push(')');
}

fn new_base(opc: OpCode, name: &str, opflags: u32, addlflags: u32, behave: OpBehaviorRef) -> TypeOpBase {
    let mut base = TypeOpBase::new(opc, name);
    base.opflags = opflags;
    base.addlflags = addlflags;
    base.behave = Some(behave);
    base
}

fn float_format_table(trans: &dyn Translate) -> Arc<FloatFormatTable> {
    Arc::new(FloatFormatTable::new(&trans.translate_base().floatformats))
}

fn types(glb: &Architecture) -> &TypeFactory {
    glb.types.as_deref().expect("missing TypeFactory")
}

fn types_mut(glb: &mut Architecture) -> &mut TypeFactory {
    glb.types.as_deref_mut().expect("missing TypeFactory")
}

fn out_vn(data: &Funcdata, op: OpId) -> VarnodeId {
    data.op(op).get_out().expect("p-code op has no output varnode")
}

fn def_code(data: &Funcdata, vn: VarnodeId) -> Option<OpCode> {
    data.vn(vn).get_def().map(|def| data.op(def).code())
}

fn const_space(data: &Funcdata, vn: VarnodeId, glb: &Architecture) -> SpaceRef {
    data.vn(vn)
        .get_space_from_const(&glb.manager)
        .expect("constant does not encode an address space")
}

fn is_fspec_varnode(data: &Funcdata, vn: VarnodeId) -> bool {
    data.vn(vn)
        .get_space()
        .is_some_and(|spc| spc.get_type() == SpaceType::Fspec)
}

fn default_output_local(op: OpId, data: &Funcdata, glb: &mut Architecture) -> Result<TypeId> {
    let size = data.vn(out_vn(data, op)).get_size();
    types_mut(glb).get_base(size, TypeMetatype::Unknown)
}

fn default_input_local(op: OpId, slot: i32, data: &Funcdata, glb: &mut Architecture) -> Result<TypeId> {
    let size = data.vn(data.op(op).get_in(slot)).get_size();
    types_mut(glb).get_base(size, TypeMetatype::Unknown)
}

fn base_input_cast<T: TypeOp + ?Sized>(
    top: &T,
    op: OpId,
    slot: i32,
    cast_strategy: &dyn CastStrategy,
    data: &mut Funcdata,
    glb: &mut Architecture,
) -> Result<Option<TypeId>> {
    let vn = data.op(op).get_in(slot);
    if data.vn(vn).is_annotation() {
        return Ok(None);
    }
    let reqtype = top.get_input_local(op, slot, data, glb)?;
    let curtype = data.vn_get_high_type_read_facing(vn, op, glb)?;
    Ok(cast_strategy.cast_standard(reqtype, curtype, false, true, types_mut(glb)))
}

fn spacebase_pointer(alttype: TypeId, glb: &mut Architecture) -> Result<TypeId> {
    let wordsize = glb
        .manager
        .get_default_data_space()
        .expect("missing default data space")
        .get_word_size();
    let size = types(glb).get(alttype).get_size();
    let unknown = types_mut(glb).get_base(1, TypeMetatype::Unknown)?;
    types_mut(glb).get_type_pointer(size, unknown, wordsize)
}

fn pass_through_type(alttype: TypeId, invn: VarnodeId, data: &Funcdata, glb: &mut Architecture) -> Result<TypeId> {
    if data.vn(invn).is_spacebase() {
        spacebase_pointer(alttype, glb)
    } else {
        Ok(alttype)
    }
}

fn equality_input_cast(
    op: OpId,
    slot: i32,
    cast_strategy: &dyn CastStrategy,
    data: &mut Funcdata,
    glb: &mut Architecture,
) -> Result<Option<TypeId>> {
    let in0 = data.op(op).get_in(0);
    let in1 = data.op(op).get_in(1);
    let mut reqtype = data.vn_get_high_type_read_facing(in0, op, glb)?;
    let othertype = data.vn_get_high_type_read_facing(in1, op, glb)?;
    let factory = types(glb);
    if 0 > factory.get(othertype).type_order(factory.get(reqtype), factory) {
        reqtype = othertype;
    }
    if cast_strategy.check_int_promotion_for_compare(op, slot, data, glb)? {
        return Ok(Some(reqtype));
    }
    let slotvn = data.op(op).get_in(slot);
    let othertype = data.vn_get_high_type_read_facing(slotvn, op, glb)?;
    Ok(cast_strategy.cast_standard(reqtype, othertype, false, false, types_mut(glb)))
}

fn compare_input_cast<T: TypeOp + ?Sized>(
    top: &T,
    op: OpId,
    slot: i32,
    cast_strategy: &dyn CastStrategy,
    care_ptr_uint: bool,
    data: &mut Funcdata,
    glb: &mut Architecture,
) -> Result<Option<TypeId>> {
    let reqtype = top.get_input_local(op, slot, data, glb)?;
    if cast_strategy.check_int_promotion_for_compare(op, slot, data, glb)? {
        return Ok(Some(reqtype));
    }
    let invn = data.op(op).get_in(slot);
    let curtype = data.vn_get_high_type_read_facing(invn, op, glb)?;
    Ok(cast_strategy.cast_standard(reqtype, curtype, true, care_ptr_uint, types_mut(glb)))
}

fn extension_input_cast<T: TypeOp + ?Sized>(
    top: &T,
    op: OpId,
    slot: i32,
    cast_strategy: &dyn CastStrategy,
    extension: i32,
    data: &mut Funcdata,
    glb: &mut Architecture,
) -> Result<Option<TypeId>> {
    let vn = data.op(op).get_in(slot);
    let reqtype = top.get_input_local(op, slot, data, glb)?;
    let curtype = data.vn_get_high_type_read_facing(vn, op, glb)?;
    let promo_type = cast_strategy.int_promotion_type(vn, data, glb)?;
    if promo_type != NO_PROMOTION && (promo_type & extension) == 0 {
        return Ok(Some(reqtype));
    }
    Ok(cast_strategy.cast_standard(reqtype, curtype, true, true, types_mut(glb)))
}

fn locked_param_type(
    data: &mut Funcdata,
    fc: CallSpecId,
    slot: i32,
    max_size: Option<i32>,
    glb: &Architecture,
) -> Option<TypeId> {
    let param = data.call_spec_mut(fc).get_param(slot - 1, glb)?;
    let factory = types(glb);
    if param.is_type_locked(glb) {
        let ct = param.get_type(glb);
        let fits = max_size.is_none_or(|size| factory.get(ct).get_size() <= size);
        if factory.get(ct).get_metatype() != TypeMetatype::Void && fits {
            return Some(ct);
        }
    } else if param.is_this_pointer(glb) {
        let ct = param.get_type(glb);
        if factory.get(ct).get_metatype() == TypeMetatype::Ptr
            && factory.get(factory.get(ct).get_ptr_to()).get_metatype() == TypeMetatype::Struct
        {
            return Some(ct);
        }
    }
    None
}

fn locked_output_type(op: OpId, fc: CallSpecId, data: &mut Funcdata, glb: &mut Architecture) -> Result<TypeId> {
    let spec = data.call_spec(fc);
    if !spec.is_output_locked(glb) {
        return default_output_local(op, data, glb);
    }
    let ct = spec.get_output_type(glb);
    if types(glb).get(ct).get_metatype() == TypeMetatype::Void {
        return default_output_local(op, data, glb);
    }
    Ok(ct)
}

fn callother_userop(op: OpId, data: &Funcdata, glb: &Architecture) -> Result<Arc<UserPcodeOp>> {
    let index = data.vn(data.op(op).get_in(0)).get_offset() as i32;
    glb.userops
        .get_op(index as u32)
        .cloned()
        .ok_or_else(|| Error::Lowlevel(format!("unknown user-defined p-code op index {}", index)))
}

fn cpool_refs(op: OpId, data: &Funcdata) -> Vec<u64> {
    let pcode = data.op(op);
    (1..pcode.num_input())
        .map(|slot| data.vn(pcode.get_in(slot)).get_offset())
        .collect()
}

fn print_input_list(data: &Funcdata, op: OpId, first: i32, out: &mut String, glb: &Architecture) {
    let pcode = data.op(op);
    out.push('(');
    data.vn_print_raw_option(pcode.get_in_option(first), out, glb);
    for index in (first + 1)..pcode.num_input() {
        out.push(',');
        data.vn_print_raw_option(pcode.get_in_option(index), out, glb);
    }
    out.push(')');
}

fn descend_to_size(start: Option<TypeId>, byte_off: i64, size: i32, glb: &Architecture) -> Option<TypeId> {
    let mut current = start;
    let mut byte_off = byte_off;
    while let Some(tp) = current {
        let datatype = types(glb).get(tp);
        if byte_off == 0 && datatype.get_size() == size {
            break;
        }
        let mut newoff = byte_off;
        current = datatype.get_sub_type(byte_off, &mut newoff, glb);
        byte_off = newoff;
    }
    current
}

#[cfg(test)]
mod tests {
    use super::*;

    fn java_test_table() -> Vec<Option<Box<dyn TypeOp>>> {
        let mut inst: Vec<Option<Box<dyn TypeOp>>> = (0..OpCode::Max.index()).map(|_slot| None).collect();
        inst[OpCode::IntZext.index()] = Some(Box::new(TypeOpIntZext::new()));
        inst[OpCode::IntNegate.index()] = Some(Box::new(TypeOpIntNegate::new()));
        inst[OpCode::IntXor.index()] = Some(Box::new(TypeOpIntXor::new()));
        inst[OpCode::IntOr.index()] = Some(Box::new(TypeOpIntOr::new()));
        inst[OpCode::IntAnd.index()] = Some(Box::new(TypeOpIntAnd::new()));
        inst[OpCode::IntRight.index()] = Some(Box::new(TypeOpIntRight::new()));
        inst
    }

    #[test]
    fn constructor_flags_follow_cpp() {
        let add = TypeOpIntAdd::new();
        assert_eq!(add.get_name(), "+");
        assert_eq!(add.get_opcode(), OpCode::IntAdd);
        assert!(add.is_commutative());
        assert!(add.is_arithmetic_op());
        assert!(add.inherits_sign());
        assert_eq!(add.meta, TypeOpMeta::new(TypeMetatype::Int, TypeMetatype::Int));
        assert_eq!(
            add.evaluate_binary(4, 4, 0xffffffff, 2).expect("add evaluation failed"),
            1
        );

        let sub = TypeOpIntSub::new();
        assert!(!sub.is_commutative());

        let rem = TypeOpIntRem::new();
        assert!(rem.inherits_sign_first_param_only());

        let call = TypeOpCall::new();
        assert_eq!(
            call.get_flags(),
            PcodeOp::SPECIAL | PcodeOp::CALL | PcodeOp::HAS_CALLSPEC | PcodeOp::CODEREF | PcodeOp::NOCOLLAPSE
        );
        assert!(call.get_behavior().expect("missing behavior").is_special());

        let insert = TypeOpInsert::new();
        assert!(!insert.get_behavior().expect("missing behavior").is_special());
        assert_eq!(insert.meta, TypeOpMeta::new(TypeMetatype::Unknown, TypeMetatype::Int));

        let ptradd = TypeOpPtradd::new();
        assert_eq!(ptradd.get_flags(), PcodeOp::TERNARY | PcodeOp::NOCOLLAPSE);
        assert_eq!(TypeOpMulti::new().get_name(), "?");
        assert_eq!(TypeOpIndirect::new().get_name(), "[]");
        assert_eq!(TypeOpCast::new().get_name(), "(cast)");
    }

    #[test]
    fn java_operator_selection() {
        let mut inst = java_test_table();
        select_java_operators(&mut inst, true);
        let right = inst[OpCode::IntRight.index()].as_ref().expect("missing IntRight");
        assert_eq!(right.get_name(), ">>>");
        select_java_operators(&mut inst, false);
        let right = inst[OpCode::IntRight.index()].as_ref().expect("missing IntRight");
        assert_eq!(right.get_name(), ">>");
    }

    #[test]
    fn preferred_zext_sizes() {
        assert_eq!(TypeOpFloatInt2Float::preferred_zext_size(1), 4);
        assert_eq!(TypeOpFloatInt2Float::preferred_zext_size(3), 4);
        assert_eq!(TypeOpFloatInt2Float::preferred_zext_size(4), 8);
        assert_eq!(TypeOpFloatInt2Float::preferred_zext_size(7), 8);
        assert_eq!(TypeOpFloatInt2Float::preferred_zext_size(8), 9);
        assert_eq!(TypeOpFloatInt2Float::preferred_zext_size(16), 17);
    }
}
