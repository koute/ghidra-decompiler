use crate::address::{byte_swap_signed, sign_extend, zero_extend};
use crate::context::{ConstructorRef, ParserWalker};
use crate::error::{Error, Result};
use crate::marshal::Decoder;
use crate::slaformat::*;
use crate::slghsymbol::{SymbolId, SymbolTable};
use crate::space::AddrSpace;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TokenField {
    pub bigendian: bool,
    pub signbit: bool,
    pub bitstart: i32,
    pub bitend: i32,
    pub bytestart: i32,
    pub byteend: i32,
    pub shift: i32,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ContextField {
    pub startbit: i32,
    pub endbit: i32,
    pub startbyte: i32,
    pub endbyte: i32,
    pub shift: i32,
    pub signbit: bool,
}

impl ContextField {
    pub fn new(signbit: bool, startbit: i32, endbit: i32) -> ContextField {
        ContextField {
            startbit,
            endbit,
            startbyte: startbit / 8,
            endbyte: endbit / 8,
            shift: 7 - (endbit % 8),
            signbit,
        }
    }

    pub fn get_start_bit(&self) -> i32 {
        self.startbit
    }

    pub fn get_end_bit(&self) -> i32 {
        self.endbit
    }

    pub fn get_sign_bit(&self) -> bool {
        self.signbit
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum BinaryOperator {
    Plus,
    Sub,
    Mult,
    LeftShift,
    RightShift,
    And,
    Or,
    Xor,
    Div,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum UnaryOperator {
    Minus,
    Not,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum PatternExpression {
    TokenField(TokenField),
    ContextField(ContextField),
    Constant(i64),
    Operand { index: i32, ct: ConstructorRef },
    StartInstruction,
    EndInstruction,
    Next2Instruction,
    Binary(BinaryOperator, Box<PatternExpression>, Box<PatternExpression>),
    Unary(UnaryOperator, Box<PatternExpression>),
}

pub static CONSTANT_ZERO: PatternExpression = PatternExpression::Constant(0);
pub static START_INSTRUCTION_VALUE: PatternExpression = PatternExpression::StartInstruction;
pub static END_INSTRUCTION_VALUE: PatternExpression = PatternExpression::EndInstruction;
pub static NEXT2_INSTRUCTION_VALUE: PatternExpression = PatternExpression::Next2Instruction;

fn get_instruction_bytes(walker: &ParserWalker<'_>, mut bytestart: i32, byteend: i32, bigendian: bool) -> Result<i64> {
    let mut res: i64 = 0;
    let size = byteend - bytestart + 1;
    let mut tmpsize = size;
    while tmpsize >= 4 {
        let tmp = walker.get_instruction_bytes(bytestart, 4)?;
        res = res.wrapping_shl(32);
        res |= tmp as i64;
        bytestart += 4;
        tmpsize -= 4;
    }
    if tmpsize > 0 {
        let tmp = walker.get_instruction_bytes(bytestart, tmpsize)?;
        res = res.wrapping_shl((8 * tmpsize) as u32);
        res |= tmp as i64;
    }
    if !bigendian {
        res = byte_swap_signed(res, size);
    }
    Ok(res)
}

fn get_context_bytes(walker: &ParserWalker<'_>, mut bytestart: i32, byteend: i32) -> i64 {
    let mut res: i64 = 0;
    let mut size = byteend - bytestart + 1;
    while size >= 4 {
        let tmp = walker.get_context_bytes(bytestart, 4);
        res = res.wrapping_shl(32);
        res |= tmp as i64;
        bytestart += 4;
        size = byteend - bytestart + 1;
    }
    if size > 0 {
        let tmp = walker.get_context_bytes(bytestart, size);
        res = res.wrapping_shl((8 * size) as u32);
        res |= tmp as i64;
    }
    res
}

impl PatternExpression {
    pub fn get_value(&self, walker: &ParserWalker<'_>) -> Result<i64> {
        match self {
            PatternExpression::TokenField(field) => {
                let mut res = get_instruction_bytes(walker, field.bytestart, field.byteend, field.bigendian)?;
                res = res.wrapping_shr(field.shift as u32);
                if field.signbit {
                    Ok(sign_extend(res, field.bitend - field.bitstart))
                } else {
                    Ok(zero_extend(res, field.bitend - field.bitstart))
                }
            }
            PatternExpression::ContextField(field) => {
                let mut res = get_context_bytes(walker, field.startbyte, field.endbyte);
                res = res.wrapping_shr(field.shift as u32);
                if field.signbit {
                    Ok(sign_extend(res, field.endbit - field.startbit))
                } else {
                    Ok(zero_extend(res, field.endbit - field.startbit))
                }
            }
            PatternExpression::Constant(val) => Ok(*val),
            PatternExpression::Operand { index, ct } => operand_value_get_value(*index, *ct, walker),
            PatternExpression::StartInstruction => {
                let addr = walker.get_addr();
                let wordsize = addr.get_space().map(|spc| spc.get_word_size()).unwrap_or(1);
                Ok(AddrSpace::byte_to_address(addr.get_offset(), wordsize) as i64)
            }
            PatternExpression::EndInstruction => {
                let addr = walker.get_naddr();
                let wordsize = addr.get_space().map(|spc| spc.get_word_size()).unwrap_or(1);
                Ok(AddrSpace::byte_to_address(addr.get_offset(), wordsize) as i64)
            }
            PatternExpression::Next2Instruction => {
                let addr = walker.get_n2addr()?;
                let wordsize = addr.get_space().map(|spc| spc.get_word_size()).unwrap_or(1);
                Ok(AddrSpace::byte_to_address(addr.get_offset(), wordsize) as i64)
            }
            PatternExpression::Binary(op, left, right) => {
                let leftval = left.get_value(walker)?;
                let rightval = right.get_value(walker)?;
                binary_value(*op, leftval, rightval)
            }
            PatternExpression::Unary(op, unary) => {
                let val = unary.get_value(walker)?;
                match op {
                    UnaryOperator::Minus => Ok(val.wrapping_neg()),
                    UnaryOperator::Not => Ok(!val),
                }
            }
        }
    }

    pub fn min_value(&self) -> Result<i64> {
        match self {
            PatternExpression::TokenField(_) | PatternExpression::ContextField(_) => Ok(0),
            PatternExpression::Constant(val) => Ok(*val),
            PatternExpression::Operand { .. } => Err(Error::Sleigh("Operand used in pattern expression".to_string())),
            PatternExpression::StartInstruction
            | PatternExpression::EndInstruction
            | PatternExpression::Next2Instruction => Ok(0),
            _ => Ok(0),
        }
    }

    pub fn max_value(&self) -> Result<i64> {
        match self {
            PatternExpression::TokenField(field) => Ok(zero_extend(!0i64, field.bitend - field.bitstart)),
            PatternExpression::ContextField(field) => Ok(zero_extend(!0i64, field.endbit - field.startbit)),
            PatternExpression::Constant(val) => Ok(*val),
            PatternExpression::Operand { .. } => Err(Error::Sleigh("Operand used in pattern expression".to_string())),
            _ => Ok(0),
        }
    }

    pub fn as_context_field(&self) -> Option<&ContextField> {
        match self {
            PatternExpression::ContextField(field) => Some(field),
            _ => None,
        }
    }

    pub fn decode_expression(decoder: &mut dyn Decoder, symtab: &SymbolTable) -> Result<PatternExpression> {
        let el = decoder.peek_element()?;
        if el == ELEM_TOKENFIELD {
            let el = decoder.open_element_expect(ELEM_TOKENFIELD)?;
            let bigendian = decoder.read_bool_attr(ATTRIB_BIGENDIAN)?;
            let signbit = decoder.read_bool_attr(ATTRIB_SIGNBIT)?;
            let bitstart = decoder.read_signed_integer_attr(ATTRIB_STARTBIT)? as i32;
            let bitend = decoder.read_signed_integer_attr(ATTRIB_ENDBIT)? as i32;
            let bytestart = decoder.read_signed_integer_attr(ATTRIB_STARTBYTE)? as i32;
            let byteend = decoder.read_signed_integer_attr(ATTRIB_ENDBYTE)? as i32;
            let shift = decoder.read_signed_integer_attr(ATTRIB_SHIFT)? as i32;
            decoder.close_element(el)?;
            return Ok(PatternExpression::TokenField(TokenField {
                bigendian,
                signbit,
                bitstart,
                bitend,
                bytestart,
                byteend,
                shift,
            }));
        }
        if el == ELEM_CONTEXTFIELD {
            let el = decoder.open_element_expect(ELEM_CONTEXTFIELD)?;
            let signbit = decoder.read_bool_attr(ATTRIB_SIGNBIT)?;
            let startbit = decoder.read_signed_integer_attr(ATTRIB_STARTBIT)? as i32;
            let endbit = decoder.read_signed_integer_attr(ATTRIB_ENDBIT)? as i32;
            let startbyte = decoder.read_signed_integer_attr(ATTRIB_STARTBYTE)? as i32;
            let endbyte = decoder.read_signed_integer_attr(ATTRIB_ENDBYTE)? as i32;
            let shift = decoder.read_signed_integer_attr(ATTRIB_SHIFT)? as i32;
            decoder.close_element(el)?;
            return Ok(PatternExpression::ContextField(ContextField {
                startbit,
                endbit,
                startbyte,
                endbyte,
                shift,
                signbit,
            }));
        }
        if el == ELEM_INTB {
            let el = decoder.open_element_expect(ELEM_INTB)?;
            let val = decoder.read_signed_integer_attr(ATTRIB_VAL)?;
            decoder.close_element(el)?;
            return Ok(PatternExpression::Constant(val));
        }
        if el == ELEM_OPERAND_EXP {
            let el = decoder.open_element_expect(ELEM_OPERAND_EXP)?;
            let index = decoder.read_signed_integer_attr(ATTRIB_INDEX)? as i32;
            let tabid = decoder.read_unsigned_integer_attr(ATTRIB_TABLE)? as u32;
            let ctid = decoder.read_unsigned_integer_attr(ATTRIB_CT)? as u32;
            let numct = symtab.find_symbol_by_id(tabid)?.subtable_num_constructors();
            if ctid as i64 >= numct as i64 {
                return Err(Error::Decoder("Invalid constructor id".to_string()));
            }
            decoder.close_element(el)?;
            return Ok(PatternExpression::Operand {
                index,
                ct: ConstructorRef {
                    table: tabid as SymbolId,
                    index: ctid,
                },
            });
        }
        if el == ELEM_START_EXP {
            let el = decoder.open_element_expect(ELEM_START_EXP)?;
            decoder.close_element(el)?;
            return Ok(PatternExpression::StartInstruction);
        }
        if el == ELEM_END_EXP {
            let el = decoder.open_element_expect(ELEM_END_EXP)?;
            decoder.close_element(el)?;
            return Ok(PatternExpression::EndInstruction);
        }
        let binary = if el == ELEM_PLUS_EXP {
            Some(BinaryOperator::Plus)
        } else if el == ELEM_SUB_EXP {
            Some(BinaryOperator::Sub)
        } else if el == ELEM_MULT_EXP {
            Some(BinaryOperator::Mult)
        } else if el == ELEM_LSHIFT_EXP {
            Some(BinaryOperator::LeftShift)
        } else if el == ELEM_RSHIFT_EXP {
            Some(BinaryOperator::RightShift)
        } else if el == ELEM_AND_EXP {
            Some(BinaryOperator::And)
        } else if el == ELEM_OR_EXP {
            Some(BinaryOperator::Or)
        } else if el == ELEM_XOR_EXP {
            Some(BinaryOperator::Xor)
        } else if el == ELEM_DIV_EXP {
            Some(BinaryOperator::Div)
        } else {
            None
        };
        if let Some(op) = binary {
            let el = decoder.open_element()?;
            let left = PatternExpression::decode_expression(decoder, symtab)?;
            let right = PatternExpression::decode_expression(decoder, symtab)?;
            decoder.close_element(el)?;
            return Ok(PatternExpression::Binary(op, Box::new(left), Box::new(right)));
        }
        let unary = if el == ELEM_MINUS_EXP {
            Some(UnaryOperator::Minus)
        } else if el == ELEM_NOT_EXP {
            Some(UnaryOperator::Not)
        } else {
            None
        };
        if let Some(op) = unary {
            let el = decoder.open_element()?;
            let inner = PatternExpression::decode_expression(decoder, symtab)?;
            decoder.close_element(el)?;
            return Ok(PatternExpression::Unary(op, Box::new(inner)));
        }
        Err(Error::Decoder("Invalid pattern expression element".to_string()))
    }
}

fn binary_value(op: BinaryOperator, leftval: i64, rightval: i64) -> Result<i64> {
    Ok(match op {
        BinaryOperator::Plus => leftval.wrapping_add(rightval),
        BinaryOperator::Sub => leftval.wrapping_sub(rightval),
        BinaryOperator::Mult => leftval.wrapping_mul(rightval),
        BinaryOperator::LeftShift => leftval.wrapping_shl(rightval as u32),
        BinaryOperator::RightShift => leftval.wrapping_shr(rightval as u32),
        BinaryOperator::And => leftval & rightval,
        BinaryOperator::Or => leftval | rightval,
        BinaryOperator::Xor => leftval ^ rightval,
        BinaryOperator::Div => {
            if rightval == 0 {
                return Err(Error::Lowlevel("divide by 0".to_string()));
            }
            leftval.wrapping_div(rightval)
        }
    })
}

fn operand_value_get_value(index: i32, ct: ConstructorRef, walker: &ParserWalker<'_>) -> Result<i64> {
    let symtab = walker.symtab();
    let constructor = symtab.get_constructor(ct);
    let Some(symid) = constructor.get_operand(index) else {
        return Ok(0);
    };
    let Some(sym) = symtab.get(symid).operand() else {
        return Ok(0);
    };
    let mut patexp = sym.get_defining_expression();
    if patexp.is_none() {
        if let Some(defsym) = sym.get_defining_symbol() {
            patexp = symtab.get(defsym).get_pattern_expression()?;
        }
        if patexp.is_none() {
            return Ok(0);
        }
    }
    let Some(patexp) = patexp else {
        return Ok(0);
    };
    let mut newwalker = ParserWalker::new(walker.get_parser_context(), symtab);
    newwalker.set_oracle(walker.get_oracle());
    newwalker.set_out_of_band_state(ct, index, walker);
    patexp.get_value(&newwalker)
}
