use std::sync::Arc;

use crate::address::{
    calc_mask, count_leading_zeros, popcount, sign_extend, sign_extend_size, signbit_negative, uintb_negate,
    zero_extend,
};
use crate::error::{Error, Result};
use crate::float::FloatFormat;
use crate::opcodes::{OpCode, get_opname};

pub type OpBehaviorRef = Arc<dyn OpBehavior>;

pub trait OpBehavior: Send + Sync {
    fn get_opcode(&self) -> OpCode;

    fn is_special(&self) -> bool {
        false
    }

    fn is_unary(&self) -> bool;

    fn evaluate_unary(&self, _sizeout: i32, _sizein: i32, _in1: u64) -> Result<u64> {
        Err(Error::Lowlevel(format!(
            "Unary emulation unimplemented for {}",
            get_opname(self.get_opcode())
        )))
    }

    fn evaluate_binary(&self, _sizeout: i32, _sizein: i32, _in1: u64, _in2: u64) -> Result<u64> {
        Err(Error::Lowlevel(format!(
            "Binary emulation unimplemented for {}",
            get_opname(self.get_opcode())
        )))
    }

    fn evaluate_ternary(&self, _sizeout: i32, _sizein: i32, _in1: u64, _in2: u64, _in3: u64) -> Result<u64> {
        Err(Error::Lowlevel(format!(
            "Ternary emulation unimplemented for {}",
            get_opname(self.get_opcode())
        )))
    }

    fn recover_input_binary(&self, _slot: i32, _sizeout: i32, _out: u64, _sizein: i32, _input: u64) -> Result<u64> {
        Err(lossy_recovery())
    }

    fn recover_input_unary(&self, _sizeout: i32, _out: u64, _sizein: i32) -> Result<u64> {
        Err(lossy_recovery())
    }
}

fn lossy_recovery() -> Error {
    Error::Lowlevel("Cannot recover input parameter without loss of information".to_string())
}

fn unary_unimplemented(opcode: OpCode) -> Error {
    Error::Lowlevel(format!("Unary emulation unimplemented for {}", get_opname(opcode)))
}

fn binary_unimplemented(opcode: OpCode) -> Error {
    Error::Lowlevel(format!("Binary emulation unimplemented for {}", get_opname(opcode)))
}

fn cxx_int(value: i32) -> u64 {
    value as i64 as u64
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct OpBehaviorGeneric {
    opcode: OpCode,
    isunary: bool,
    isspecial: bool,
}

impl OpBehaviorGeneric {
    pub fn new(opcode: OpCode, isunary: bool) -> OpBehaviorGeneric {
        OpBehaviorGeneric {
            opcode,
            isunary,
            isspecial: false,
        }
    }

    pub fn new_special(opcode: OpCode, isunary: bool, isspecial: bool) -> OpBehaviorGeneric {
        OpBehaviorGeneric {
            opcode,
            isunary,
            isspecial,
        }
    }
}

impl OpBehavior for OpBehaviorGeneric {
    fn get_opcode(&self) -> OpCode {
        self.opcode
    }

    fn is_special(&self) -> bool {
        self.isspecial
    }

    fn is_unary(&self) -> bool {
        self.isunary
    }
}

macro_rules! simple_behavior {
    ($name:ident, $opcode:expr, $unary:expr, { $($body:tt)* }) => {
        #[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
        pub struct $name;

        impl $name {
            pub fn new() -> $name {
                $name
            }
        }

        impl OpBehavior for $name {
            fn get_opcode(&self) -> OpCode {
                $opcode
            }

            fn is_unary(&self) -> bool {
                $unary
            }

            $($body)*
        }
    };
}

simple_behavior!(OpBehaviorCopy, OpCode::Copy, true, {
    fn evaluate_unary(&self, _sizeout: i32, _sizein: i32, in1: u64) -> Result<u64> {
        Ok(in1)
    }

    fn recover_input_unary(&self, _sizeout: i32, out: u64, _sizein: i32) -> Result<u64> {
        Ok(out)
    }
});

simple_behavior!(OpBehaviorEqual, OpCode::IntEqual, false, {
    fn evaluate_binary(&self, _sizeout: i32, _sizein: i32, in1: u64, in2: u64) -> Result<u64> {
        Ok((in1 == in2) as u64)
    }
});

simple_behavior!(OpBehaviorNotEqual, OpCode::IntNotequal, false, {
    fn evaluate_binary(&self, _sizeout: i32, _sizein: i32, in1: u64, in2: u64) -> Result<u64> {
        Ok((in1 != in2) as u64)
    }
});

fn signed_less(sizein: i32, in1: u64, in2: u64, or_equal: bool) -> u64 {
    if sizein <= 0 {
        return 0;
    }
    let mask = 0x80u64.wrapping_shl((8 * (sizein - 1)) as u32);
    let bit1 = in1 & mask;
    let bit2 = in2 & mask;
    if bit1 != bit2 {
        (bit1 != 0) as u64
    } else if or_equal {
        (in1 <= in2) as u64
    } else {
        (in1 < in2) as u64
    }
}

simple_behavior!(OpBehaviorIntSless, OpCode::IntSless, false, {
    fn evaluate_binary(&self, _sizeout: i32, sizein: i32, in1: u64, in2: u64) -> Result<u64> {
        Ok(signed_less(sizein, in1, in2, false))
    }
});

simple_behavior!(OpBehaviorIntSlessEqual, OpCode::IntSlessequal, false, {
    fn evaluate_binary(&self, _sizeout: i32, sizein: i32, in1: u64, in2: u64) -> Result<u64> {
        Ok(signed_less(sizein, in1, in2, true))
    }
});

simple_behavior!(OpBehaviorIntLess, OpCode::IntLess, false, {
    fn evaluate_binary(&self, _sizeout: i32, _sizein: i32, in1: u64, in2: u64) -> Result<u64> {
        Ok((in1 < in2) as u64)
    }
});

simple_behavior!(OpBehaviorIntLessEqual, OpCode::IntLessequal, false, {
    fn evaluate_binary(&self, _sizeout: i32, _sizein: i32, in1: u64, in2: u64) -> Result<u64> {
        Ok((in1 <= in2) as u64)
    }
});

simple_behavior!(OpBehaviorIntZext, OpCode::IntZext, true, {
    fn evaluate_unary(&self, _sizeout: i32, _sizein: i32, in1: u64) -> Result<u64> {
        Ok(in1)
    }

    fn recover_input_unary(&self, _sizeout: i32, out: u64, sizein: i32) -> Result<u64> {
        let mask = calc_mask(sizein);
        if (mask & out) != out {
            return Err(Error::Evaluation(
                "Output is not in range of zext operation".to_string(),
            ));
        }
        Ok(out)
    }
});

simple_behavior!(OpBehaviorIntSext, OpCode::IntSext, true, {
    fn evaluate_unary(&self, sizeout: i32, sizein: i32, in1: u64) -> Result<u64> {
        Ok(sign_extend_size(in1, sizein, sizeout))
    }

    fn recover_input_unary(&self, sizeout: i32, out: u64, sizein: i32) -> Result<u64> {
        let masklong = calc_mask(sizeout);
        let maskshort = calc_mask(sizein);
        if (out & (maskshort ^ (maskshort >> 1))) == 0 {
            if (out & maskshort) != out {
                return Err(Error::Evaluation(
                    "Output is not in range of sext operation".to_string(),
                ));
            }
        } else if (out & (masklong ^ maskshort)) != (masklong ^ maskshort) {
            return Err(Error::Evaluation(
                "Output is not in range of sext operation".to_string(),
            ));
        }
        Ok(out & maskshort)
    }
});

simple_behavior!(OpBehaviorIntAdd, OpCode::IntAdd, false, {
    fn evaluate_binary(&self, sizeout: i32, _sizein: i32, in1: u64, in2: u64) -> Result<u64> {
        Ok(in1.wrapping_add(in2) & calc_mask(sizeout))
    }

    fn recover_input_binary(&self, _slot: i32, sizeout: i32, out: u64, _sizein: i32, input: u64) -> Result<u64> {
        Ok(out.wrapping_sub(input) & calc_mask(sizeout))
    }
});

simple_behavior!(OpBehaviorIntSub, OpCode::IntSub, false, {
    fn evaluate_binary(&self, sizeout: i32, _sizein: i32, in1: u64, in2: u64) -> Result<u64> {
        Ok(in1.wrapping_sub(in2) & calc_mask(sizeout))
    }

    fn recover_input_binary(&self, slot: i32, sizeout: i32, out: u64, _sizein: i32, input: u64) -> Result<u64> {
        let res = if slot == 0 {
            input.wrapping_add(out)
        } else {
            input.wrapping_sub(out)
        };
        Ok(res & calc_mask(sizeout))
    }
});

simple_behavior!(OpBehaviorIntCarry, OpCode::IntCarry, false, {
    fn evaluate_binary(&self, _sizeout: i32, sizein: i32, in1: u64, in2: u64) -> Result<u64> {
        Ok((in1 > (in1.wrapping_add(in2) & calc_mask(sizein))) as u64)
    }
});

fn sign_bit_of(value: u64, sizein: i32) -> u32 {
    (value.wrapping_shr((sizein.wrapping_mul(8).wrapping_sub(1)) as u32) & 1) as u32
}

simple_behavior!(OpBehaviorIntScarry, OpCode::IntScarry, false, {
    fn evaluate_binary(&self, _sizeout: i32, sizein: i32, in1: u64, in2: u64) -> Result<u64> {
        let res = in1.wrapping_add(in2);
        let mut first = sign_bit_of(in1, sizein);
        let second = sign_bit_of(in2, sizein);
        let mut result = sign_bit_of(res, sizein);
        result ^= first;
        first ^= second;
        first ^= 1;
        result &= first;
        Ok(result as u64)
    }
});

simple_behavior!(OpBehaviorIntSborrow, OpCode::IntSborrow, false, {
    fn evaluate_binary(&self, _sizeout: i32, sizein: i32, in1: u64, in2: u64) -> Result<u64> {
        let res = in1.wrapping_sub(in2);
        let mut first = sign_bit_of(in1, sizein);
        let second = sign_bit_of(in2, sizein);
        let mut result = sign_bit_of(res, sizein);
        first ^= result;
        result ^= second;
        result ^= 1;
        first &= result;
        Ok(first as u64)
    }
});

simple_behavior!(OpBehaviorInt2Comp, OpCode::Int2comp, true, {
    fn evaluate_unary(&self, _sizeout: i32, sizein: i32, in1: u64) -> Result<u64> {
        Ok(uintb_negate(in1.wrapping_sub(1), sizein))
    }

    fn recover_input_unary(&self, _sizeout: i32, out: u64, sizein: i32) -> Result<u64> {
        Ok(uintb_negate(out.wrapping_sub(1), sizein))
    }
});

simple_behavior!(OpBehaviorIntNegate, OpCode::IntNegate, true, {
    fn evaluate_unary(&self, _sizeout: i32, sizein: i32, in1: u64) -> Result<u64> {
        Ok(uintb_negate(in1, sizein))
    }

    fn recover_input_unary(&self, _sizeout: i32, out: u64, sizein: i32) -> Result<u64> {
        Ok(uintb_negate(out, sizein))
    }
});

simple_behavior!(OpBehaviorIntXor, OpCode::IntXor, false, {
    fn evaluate_binary(&self, _sizeout: i32, _sizein: i32, in1: u64, in2: u64) -> Result<u64> {
        Ok(in1 ^ in2)
    }
});

simple_behavior!(OpBehaviorIntAnd, OpCode::IntAnd, false, {
    fn evaluate_binary(&self, _sizeout: i32, _sizein: i32, in1: u64, in2: u64) -> Result<u64> {
        Ok(in1 & in2)
    }
});

simple_behavior!(OpBehaviorIntOr, OpCode::IntOr, false, {
    fn evaluate_binary(&self, _sizeout: i32, _sizein: i32, in1: u64, in2: u64) -> Result<u64> {
        Ok(in1 | in2)
    }
});

simple_behavior!(OpBehaviorIntLeft, OpCode::IntLeft, false, {
    fn evaluate_binary(&self, sizeout: i32, _sizein: i32, in1: u64, in2: u64) -> Result<u64> {
        if in2 >= cxx_int(sizeout.wrapping_mul(8)) {
            return Ok(0);
        }
        Ok(in1.wrapping_shl(in2 as u32) & calc_mask(sizeout))
    }

    fn recover_input_binary(&self, slot: i32, sizeout: i32, out: u64, _sizein: i32, input: u64) -> Result<u64> {
        if slot != 0 || input >= cxx_int(sizeout.wrapping_mul(8)) {
            return Err(lossy_recovery());
        }
        let shift_amount = input as i32;
        let shifted = out.wrapping_shl(sizeout.wrapping_mul(8).wrapping_sub(shift_amount) as u32);
        if (shifted & calc_mask(sizeout)) != 0 {
            return Err(Error::Evaluation(
                "Output is not in range of left shift operation".to_string(),
            ));
        }
        Ok(out.wrapping_shr(shift_amount as u32))
    }
});

simple_behavior!(OpBehaviorIntRight, OpCode::IntRight, false, {
    fn evaluate_binary(&self, sizeout: i32, _sizein: i32, in1: u64, in2: u64) -> Result<u64> {
        if in2 >= cxx_int(sizeout.wrapping_mul(8)) {
            return Ok(0);
        }
        Ok((in1 & calc_mask(sizeout)).wrapping_shr(in2 as u32))
    }

    fn recover_input_binary(&self, slot: i32, sizeout: i32, out: u64, sizein: i32, input: u64) -> Result<u64> {
        if slot != 0 || input >= cxx_int(sizeout.wrapping_mul(8)) {
            return Err(lossy_recovery());
        }
        let shift_amount = input as i32;
        if out.wrapping_shr(sizein.wrapping_mul(8).wrapping_sub(shift_amount) as u32) != 0 {
            return Err(Error::Evaluation(
                "Output is not in range of right shift operation".to_string(),
            ));
        }
        Ok(out.wrapping_shl(shift_amount as u32))
    }
});

simple_behavior!(OpBehaviorIntSright, OpCode::IntSright, false, {
    fn evaluate_binary(&self, sizeout: i32, sizein: i32, in1: u64, in2: u64) -> Result<u64> {
        if in2 >= cxx_int(sizeout.wrapping_mul(8)) {
            return Ok(if signbit_negative(in1, sizein) {
                calc_mask(sizeout)
            } else {
                0
            });
        }
        let shift_amount = in2 as u32;
        let mut res = in1.wrapping_shr(shift_amount);
        if signbit_negative(in1, sizein) {
            let mask = calc_mask(sizein);
            res |= mask.wrapping_shr(shift_amount) ^ mask;
        }
        Ok(res)
    }

    fn recover_input_binary(&self, slot: i32, sizeout: i32, out: u64, sizein: i32, input: u64) -> Result<u64> {
        if slot != 0 || input >= cxx_int(sizeout.wrapping_mul(8)) {
            return Err(lossy_recovery());
        }
        let shift_amount = input as i32;
        let mut testval = out.wrapping_shr(sizein.wrapping_mul(8).wrapping_sub(shift_amount).wrapping_sub(1) as u32);
        let mut count = 0;
        for _bit in 0..=shift_amount {
            if (testval & 1) != 0 {
                count += 1;
            }
            testval >>= 1;
        }
        if count != shift_amount + 1 {
            return Err(Error::Evaluation(
                "Output is not in range of right shift operation".to_string(),
            ));
        }
        Ok(out.wrapping_shl(shift_amount as u32))
    }
});

simple_behavior!(OpBehaviorIntMult, OpCode::IntMult, false, {
    fn evaluate_binary(&self, sizeout: i32, _sizein: i32, in1: u64, in2: u64) -> Result<u64> {
        Ok(in1.wrapping_mul(in2) & calc_mask(sizeout))
    }
});

simple_behavior!(OpBehaviorIntDiv, OpCode::IntDiv, false, {
    fn evaluate_binary(&self, _sizeout: i32, _sizein: i32, in1: u64, in2: u64) -> Result<u64> {
        if in2 == 0 {
            return Err(Error::Evaluation("Divide by 0".to_string()));
        }
        Ok(in1 / in2)
    }
});

simple_behavior!(OpBehaviorIntSdiv, OpCode::IntSdiv, false, {
    fn evaluate_binary(&self, sizeout: i32, sizein: i32, in1: u64, in2: u64) -> Result<u64> {
        if in2 == 0 {
            return Err(Error::Evaluation("Divide by 0".to_string()));
        }
        let num = sign_extend(in1 as i64, sizein.wrapping_mul(8).wrapping_sub(1));
        let denom = sign_extend(in2 as i64, sizein.wrapping_mul(8).wrapping_sub(1));
        if denom == 0 {
            return Err(Error::Evaluation("Divide by 0".to_string()));
        }
        let sres = num.wrapping_div(denom);
        Ok(zero_extend(sres, sizeout.wrapping_mul(8).wrapping_sub(1)) as u64)
    }
});

simple_behavior!(OpBehaviorIntRem, OpCode::IntRem, false, {
    fn evaluate_binary(&self, _sizeout: i32, _sizein: i32, in1: u64, in2: u64) -> Result<u64> {
        if in2 == 0 {
            return Err(Error::Evaluation("Remainder by 0".to_string()));
        }
        Ok(in1 % in2)
    }
});

simple_behavior!(OpBehaviorIntSrem, OpCode::IntSrem, false, {
    fn evaluate_binary(&self, sizeout: i32, sizein: i32, in1: u64, in2: u64) -> Result<u64> {
        if in2 == 0 {
            return Err(Error::Evaluation("Remainder by 0".to_string()));
        }
        let val = sign_extend(in1 as i64, sizein.wrapping_mul(8).wrapping_sub(1));
        let modulus = sign_extend(in2 as i64, sizein.wrapping_mul(8).wrapping_sub(1));
        if modulus == 0 {
            return Err(Error::Evaluation("Remainder by 0".to_string()));
        }
        let sres = val.wrapping_rem(modulus);
        Ok(zero_extend(sres, sizeout.wrapping_mul(8).wrapping_sub(1)) as u64)
    }
});

simple_behavior!(OpBehaviorBoolNegate, OpCode::BoolNegate, true, {
    fn evaluate_unary(&self, _sizeout: i32, _sizein: i32, in1: u64) -> Result<u64> {
        Ok(in1 ^ 1)
    }
});

simple_behavior!(OpBehaviorBoolXor, OpCode::BoolXor, false, {
    fn evaluate_binary(&self, _sizeout: i32, _sizein: i32, in1: u64, in2: u64) -> Result<u64> {
        Ok(in1 ^ in2)
    }
});

simple_behavior!(OpBehaviorBoolAnd, OpCode::BoolAnd, false, {
    fn evaluate_binary(&self, _sizeout: i32, _sizein: i32, in1: u64, in2: u64) -> Result<u64> {
        Ok(in1 & in2)
    }
});

simple_behavior!(OpBehaviorBoolOr, OpCode::BoolOr, false, {
    fn evaluate_binary(&self, _sizeout: i32, _sizein: i32, in1: u64, in2: u64) -> Result<u64> {
        Ok(in1 | in2)
    }
});

simple_behavior!(OpBehaviorPiece, OpCode::Piece, false, {
    fn evaluate_binary(&self, sizeout: i32, sizein: i32, in1: u64, in2: u64) -> Result<u64> {
        let shift_amount = sizeout.wrapping_sub(sizein).wrapping_mul(8);
        Ok(in1.wrapping_shl(shift_amount as u32) | in2)
    }
});

simple_behavior!(OpBehaviorSubpiece, OpCode::Subpiece, false, {
    fn evaluate_binary(&self, sizeout: i32, _sizein: i32, in1: u64, in2: u64) -> Result<u64> {
        if in2 >= 8 {
            return Ok(0);
        }
        Ok(in1.wrapping_shr((in2 * 8) as u32) & calc_mask(sizeout))
    }
});

simple_behavior!(OpBehaviorPtradd, OpCode::Ptradd, false, {
    fn evaluate_ternary(&self, sizeout: i32, _sizein: i32, in1: u64, in2: u64, in3: u64) -> Result<u64> {
        Ok(in1.wrapping_add(in2.wrapping_mul(in3)) & calc_mask(sizeout))
    }
});

simple_behavior!(OpBehaviorPtrsub, OpCode::Ptrsub, false, {
    fn evaluate_binary(&self, sizeout: i32, _sizein: i32, in1: u64, in2: u64) -> Result<u64> {
        Ok(in1.wrapping_add(in2) & calc_mask(sizeout))
    }
});

simple_behavior!(OpBehaviorPopcount, OpCode::Popcount, true, {
    fn evaluate_unary(&self, _sizeout: i32, _sizein: i32, in1: u64) -> Result<u64> {
        Ok(popcount(in1) as u64)
    }
});

simple_behavior!(OpBehaviorLzcount, OpCode::Lzcount, true, {
    fn evaluate_unary(&self, _sizeout: i32, sizein: i32, in1: u64) -> Result<u64> {
        let unused_bits = 8u64.wrapping_mul(8u64.wrapping_sub(cxx_int(sizein)));
        Ok(cxx_int(count_leading_zeros(in1)).wrapping_sub(unused_bits))
    }
});

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct FloatFormatTable {
    formats: Vec<FloatFormat>,
}

impl FloatFormatTable {
    pub fn new(formats: &[FloatFormat]) -> FloatFormatTable {
        FloatFormatTable {
            formats: formats.to_vec(),
        }
    }

    pub fn get_float_format(&self, size: i32) -> Option<&FloatFormat> {
        self.formats.iter().find(|format| format.get_size() == size)
    }
}

macro_rules! float_behavior {
    ($name:ident, $opcode:expr, $unary:expr, { $($body:tt)* }) => {
        #[derive(Clone, Debug)]
        pub struct $name {
            formats: Arc<FloatFormatTable>,
        }

        impl $name {
            pub fn new(formats: Arc<FloatFormatTable>) -> $name {
                $name { formats }
            }
        }

        impl OpBehavior for $name {
            fn get_opcode(&self) -> OpCode {
                $opcode
            }

            fn is_unary(&self) -> bool {
                $unary
            }

            $($body)*
        }
    };
}

macro_rules! float_binary {
    ($name:ident, $opcode:expr, $method:ident) => {
        float_behavior!($name, $opcode, false, {
            fn evaluate_binary(&self, _sizeout: i32, sizein: i32, in1: u64, in2: u64) -> Result<u64> {
                match self.formats.get_float_format(sizein) {
                    Some(format) => Ok(format.$method(in1, in2)),
                    None => Err(binary_unimplemented($opcode)),
                }
            }
        });
    };
}

macro_rules! float_unary {
    ($name:ident, $opcode:expr, $method:ident) => {
        float_behavior!($name, $opcode, true, {
            fn evaluate_unary(&self, _sizeout: i32, sizein: i32, in1: u64) -> Result<u64> {
                match self.formats.get_float_format(sizein) {
                    Some(format) => Ok(format.$method(in1)),
                    None => Err(unary_unimplemented($opcode)),
                }
            }
        });
    };
}

float_binary!(OpBehaviorFloatEqual, OpCode::FloatEqual, op_equal);
float_binary!(OpBehaviorFloatNotEqual, OpCode::FloatNotequal, op_not_equal);
float_binary!(OpBehaviorFloatLess, OpCode::FloatLess, op_less);
float_binary!(OpBehaviorFloatLessEqual, OpCode::FloatLessequal, op_less_equal);
float_unary!(OpBehaviorFloatNan, OpCode::FloatNan, op_nan);
float_binary!(OpBehaviorFloatAdd, OpCode::FloatAdd, op_add);
float_binary!(OpBehaviorFloatDiv, OpCode::FloatDiv, op_div);
float_binary!(OpBehaviorFloatMult, OpCode::FloatMult, op_mult);
float_binary!(OpBehaviorFloatSub, OpCode::FloatSub, op_sub);
float_unary!(OpBehaviorFloatNeg, OpCode::FloatNeg, op_neg);
float_unary!(OpBehaviorFloatAbs, OpCode::FloatAbs, op_abs);
float_unary!(OpBehaviorFloatSqrt, OpCode::FloatSqrt, op_sqrt);
float_unary!(OpBehaviorFloatCeil, OpCode::FloatCeil, op_ceil);
float_unary!(OpBehaviorFloatFloor, OpCode::FloatFloor, op_floor);
float_unary!(OpBehaviorFloatRound, OpCode::FloatRound, op_round);

float_behavior!(OpBehaviorFloatInt2Float, OpCode::FloatInt2float, true, {
    fn evaluate_unary(&self, sizeout: i32, sizein: i32, in1: u64) -> Result<u64> {
        match self.formats.get_float_format(sizeout) {
            Some(format) => Ok(format.op_int2float(in1, sizein)),
            None => Err(unary_unimplemented(OpCode::FloatInt2float)),
        }
    }
});

float_behavior!(OpBehaviorFloatFloat2Float, OpCode::FloatFloat2float, true, {
    fn evaluate_unary(&self, sizeout: i32, sizein: i32, in1: u64) -> Result<u64> {
        let Some(formatout) = self.formats.get_float_format(sizeout) else {
            return Err(unary_unimplemented(OpCode::FloatFloat2float));
        };
        let Some(formatin) = self.formats.get_float_format(sizein) else {
            return Err(unary_unimplemented(OpCode::FloatFloat2float));
        };
        Ok(formatin.op_float2float(in1, formatout))
    }
});

float_behavior!(OpBehaviorFloatTrunc, OpCode::FloatTrunc, true, {
    fn evaluate_unary(&self, sizeout: i32, sizein: i32, in1: u64) -> Result<u64> {
        match self.formats.get_float_format(sizein) {
            Some(format) => Ok(format.op_trunc(in1, sizeout)),
            None => Err(unary_unimplemented(OpCode::FloatTrunc)),
        }
    }
});

pub fn register_instructions(inst: &mut Vec<Option<OpBehaviorRef>>, float_formats: &[FloatFormat]) {
    inst.extend((0..OpCode::Max.index()).map(|_slot| None));
    let formats = Arc::new(FloatFormatTable::new(float_formats));
    let special = |opcode: OpCode| -> Option<OpBehaviorRef> {
        Some(Arc::new(OpBehaviorGeneric::new_special(opcode, false, true)))
    };
    let plain = |opcode: OpCode| -> Option<OpBehaviorRef> { Some(Arc::new(OpBehaviorGeneric::new(opcode, false))) };
    fn wrap<T: OpBehavior + 'static>(behavior: T) -> Option<OpBehaviorRef> {
        Some(Arc::new(behavior))
    }

    inst[OpCode::Copy.index()] = wrap(OpBehaviorCopy);
    inst[OpCode::Load.index()] = special(OpCode::Load);
    inst[OpCode::Store.index()] = special(OpCode::Store);
    inst[OpCode::Branch.index()] = special(OpCode::Branch);
    inst[OpCode::Cbranch.index()] = special(OpCode::Cbranch);
    inst[OpCode::Branchind.index()] = special(OpCode::Branchind);
    inst[OpCode::Call.index()] = special(OpCode::Call);
    inst[OpCode::Callind.index()] = special(OpCode::Callind);
    inst[OpCode::Callother.index()] = special(OpCode::Callother);
    inst[OpCode::Return.index()] = special(OpCode::Return);

    inst[OpCode::Multiequal.index()] = special(OpCode::Multiequal);
    inst[OpCode::Indirect.index()] = special(OpCode::Indirect);

    inst[OpCode::Piece.index()] = wrap(OpBehaviorPiece);
    inst[OpCode::Subpiece.index()] = wrap(OpBehaviorSubpiece);
    inst[OpCode::IntEqual.index()] = wrap(OpBehaviorEqual);
    inst[OpCode::IntNotequal.index()] = wrap(OpBehaviorNotEqual);
    inst[OpCode::IntSless.index()] = wrap(OpBehaviorIntSless);
    inst[OpCode::IntSlessequal.index()] = wrap(OpBehaviorIntSlessEqual);
    inst[OpCode::IntLess.index()] = wrap(OpBehaviorIntLess);
    inst[OpCode::IntLessequal.index()] = wrap(OpBehaviorIntLessEqual);
    inst[OpCode::IntZext.index()] = wrap(OpBehaviorIntZext);
    inst[OpCode::IntSext.index()] = wrap(OpBehaviorIntSext);
    inst[OpCode::IntAdd.index()] = wrap(OpBehaviorIntAdd);
    inst[OpCode::IntSub.index()] = wrap(OpBehaviorIntSub);
    inst[OpCode::IntCarry.index()] = wrap(OpBehaviorIntCarry);
    inst[OpCode::IntScarry.index()] = wrap(OpBehaviorIntScarry);
    inst[OpCode::IntSborrow.index()] = wrap(OpBehaviorIntSborrow);
    inst[OpCode::Int2comp.index()] = wrap(OpBehaviorInt2Comp);
    inst[OpCode::IntNegate.index()] = wrap(OpBehaviorIntNegate);
    inst[OpCode::IntXor.index()] = wrap(OpBehaviorIntXor);
    inst[OpCode::IntAnd.index()] = wrap(OpBehaviorIntAnd);
    inst[OpCode::IntOr.index()] = wrap(OpBehaviorIntOr);
    inst[OpCode::IntLeft.index()] = wrap(OpBehaviorIntLeft);
    inst[OpCode::IntRight.index()] = wrap(OpBehaviorIntRight);
    inst[OpCode::IntSright.index()] = wrap(OpBehaviorIntSright);
    inst[OpCode::IntMult.index()] = wrap(OpBehaviorIntMult);
    inst[OpCode::IntDiv.index()] = wrap(OpBehaviorIntDiv);
    inst[OpCode::IntSdiv.index()] = wrap(OpBehaviorIntSdiv);
    inst[OpCode::IntRem.index()] = wrap(OpBehaviorIntRem);
    inst[OpCode::IntSrem.index()] = wrap(OpBehaviorIntSrem);

    inst[OpCode::BoolNegate.index()] = wrap(OpBehaviorBoolNegate);
    inst[OpCode::BoolXor.index()] = wrap(OpBehaviorBoolXor);
    inst[OpCode::BoolAnd.index()] = wrap(OpBehaviorBoolAnd);
    inst[OpCode::BoolOr.index()] = wrap(OpBehaviorBoolOr);

    inst[OpCode::Cast.index()] = special(OpCode::Cast);
    inst[OpCode::Ptradd.index()] = plain(OpCode::Ptradd);
    inst[OpCode::Ptrsub.index()] = plain(OpCode::Ptrsub);

    inst[OpCode::FloatEqual.index()] = wrap(OpBehaviorFloatEqual::new(formats.clone()));
    inst[OpCode::FloatNotequal.index()] = wrap(OpBehaviorFloatNotEqual::new(formats.clone()));
    inst[OpCode::FloatLess.index()] = wrap(OpBehaviorFloatLess::new(formats.clone()));
    inst[OpCode::FloatLessequal.index()] = wrap(OpBehaviorFloatLessEqual::new(formats.clone()));
    inst[OpCode::FloatNan.index()] = wrap(OpBehaviorFloatNan::new(formats.clone()));

    inst[OpCode::FloatAdd.index()] = wrap(OpBehaviorFloatAdd::new(formats.clone()));
    inst[OpCode::FloatDiv.index()] = wrap(OpBehaviorFloatDiv::new(formats.clone()));
    inst[OpCode::FloatMult.index()] = wrap(OpBehaviorFloatMult::new(formats.clone()));
    inst[OpCode::FloatSub.index()] = wrap(OpBehaviorFloatSub::new(formats.clone()));
    inst[OpCode::FloatNeg.index()] = wrap(OpBehaviorFloatNeg::new(formats.clone()));
    inst[OpCode::FloatAbs.index()] = wrap(OpBehaviorFloatAbs::new(formats.clone()));
    inst[OpCode::FloatSqrt.index()] = wrap(OpBehaviorFloatSqrt::new(formats.clone()));

    inst[OpCode::FloatInt2float.index()] = wrap(OpBehaviorFloatInt2Float::new(formats.clone()));
    inst[OpCode::FloatFloat2float.index()] = wrap(OpBehaviorFloatFloat2Float::new(formats.clone()));
    inst[OpCode::FloatTrunc.index()] = wrap(OpBehaviorFloatTrunc::new(formats.clone()));
    inst[OpCode::FloatCeil.index()] = wrap(OpBehaviorFloatCeil::new(formats.clone()));
    inst[OpCode::FloatFloor.index()] = wrap(OpBehaviorFloatFloor::new(formats.clone()));
    inst[OpCode::FloatRound.index()] = wrap(OpBehaviorFloatRound::new(formats));
    inst[OpCode::Segmentop.index()] = special(OpCode::Segmentop);
    inst[OpCode::Cpoolref.index()] = special(OpCode::Cpoolref);
    inst[OpCode::New.index()] = special(OpCode::New);
    inst[OpCode::Insert.index()] = plain(OpCode::Insert);
    inst[OpCode::Zpull.index()] = plain(OpCode::Zpull);
    inst[OpCode::Popcount.index()] = wrap(OpBehaviorPopcount);
    inst[OpCode::Lzcount.index()] = wrap(OpBehaviorLzcount);
    inst[OpCode::Spull.index()] = plain(OpCode::Spull);
}

pub fn build_behaviors(float_formats: &[FloatFormat]) -> Vec<Option<OpBehaviorRef>> {
    let mut inst = Vec::new();
    register_instructions(&mut inst, float_formats);
    inst
}
