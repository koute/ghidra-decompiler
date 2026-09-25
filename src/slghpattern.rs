use crate::context::ParserWalker;
use crate::error::Result;
use crate::marshal::{Decoder, ElementId};
use crate::slaformat::*;

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct PatternBlock {
    offset: i32,
    nonzerosize: i32,
    maskvec: Vec<u32>,
    valvec: Vec<u32>,
}

impl PatternBlock {
    pub fn new_bool(tf: bool) -> PatternBlock {
        PatternBlock {
            offset: 0,
            nonzerosize: if tf { 0 } else { -1 },
            maskvec: Vec::new(),
            valvec: Vec::new(),
        }
    }

    fn normalize(&mut self) {
        if self.nonzerosize <= 0 {
            self.offset = 0;
            self.maskvec.clear();
            self.valvec.clear();
            return;
        }
        let mut cut = 0;
        while cut < self.maskvec.len() && self.maskvec[cut] == 0 {
            cut += 1;
            self.offset += 4;
        }
        self.maskvec.drain(0..cut);
        self.valvec.drain(0..cut.min(self.valvec.len()));
        if !self.maskvec.is_empty() {
            let mut suboff = 0;
            let mut tmp = self.maskvec[0];
            while tmp != 0 {
                suboff += 1;
                tmp >>= 8;
            }
            suboff = 4 - suboff;
            if suboff != 0 {
                self.offset += suboff;
                let shift_left = (suboff * 8) as u32;
                let shift_right = ((4 - suboff) * 8) as u32;
                for index in 0..self.maskvec.len() - 1 {
                    let mut value = self.maskvec[index].wrapping_shl(shift_left);
                    value |= self.maskvec[index + 1].wrapping_shr(shift_right);
                    self.maskvec[index] = value;
                }
                if let Some(last) = self.maskvec.last_mut() {
                    *last = last.wrapping_shl(shift_left);
                }
                if !self.valvec.is_empty() {
                    for index in 0..self.valvec.len() - 1 {
                        let mut value = self.valvec[index].wrapping_shl(shift_left);
                        value |= self.valvec[index + 1].wrapping_shr(shift_right);
                        self.valvec[index] = value;
                    }
                    if let Some(last) = self.valvec.last_mut() {
                        *last = last.wrapping_shl(shift_left);
                    }
                }
            }
            let mut end = self.maskvec.len();
            while end > 0 && self.maskvec[end - 1] == 0 {
                end -= 1;
            }
            self.maskvec.truncate(end);
            self.valvec.truncate(end);
        }
        if self.maskvec.is_empty() {
            self.offset = 0;
            self.nonzerosize = 0;
            return;
        }
        self.nonzerosize = (self.maskvec.len() * 4) as i32;
        let mut tmp = *self.maskvec.last().unwrap_or(&1);
        while (tmp & 0xff) == 0 {
            self.nonzerosize -= 1;
            tmp >>= 8;
        }
    }

    pub fn get_length(&self) -> i32 {
        self.offset + self.nonzerosize
    }

    fn get_bits(vec: &[u32], offset: i32, startbit: i32, size: i32) -> u32 {
        let startbit = startbit - 8 * offset;
        let wordnum1 = (startbit as u32 / 32) as i32;
        let shift = (startbit as u32 % 32) as i32;
        let wordnum2 = ((startbit + size - 1) as u32 / 32) as i32;
        let mut res = if wordnum1 < 0 || wordnum1 as usize >= vec.len() {
            0
        } else {
            vec[wordnum1 as usize]
        };
        res = res.wrapping_shl(shift as u32);
        if wordnum1 != wordnum2 {
            let tmp = if wordnum2 < 0 || wordnum2 as usize >= vec.len() {
                0
            } else {
                vec[wordnum2 as usize]
            };
            res |= tmp.wrapping_shr((32 - shift) as u32);
        }
        res.wrapping_shr((32 - size) as u32)
    }

    pub fn get_mask(&self, startbit: i32, size: i32) -> u32 {
        PatternBlock::get_bits(&self.maskvec, self.offset, startbit, size)
    }

    pub fn get_value(&self, startbit: i32, size: i32) -> u32 {
        PatternBlock::get_bits(&self.valvec, self.offset, startbit, size)
    }

    pub fn always_true(&self) -> bool {
        self.nonzerosize == 0
    }

    pub fn always_false(&self) -> bool {
        self.nonzerosize == -1
    }

    pub fn is_instruction_match(&self, walker: &ParserWalker<'_>) -> Result<bool> {
        if self.nonzerosize <= 0 {
            return Ok(self.nonzerosize == 0);
        }
        let mut off = self.offset;
        for (mask, val) in self.maskvec.iter().zip(self.valvec.iter()) {
            let data = walker.get_instruction_bytes(off, 4)?;
            if (mask & data) != *val {
                return Ok(false);
            }
            off += 4;
        }
        Ok(true)
    }

    pub fn is_context_match(&self, walker: &ParserWalker<'_>) -> bool {
        if self.nonzerosize <= 0 {
            return self.nonzerosize == 0;
        }
        let mut off = self.offset;
        for (mask, val) in self.maskvec.iter().zip(self.valvec.iter()) {
            let data = walker.get_context_bytes(off, 4);
            if (mask & data) != *val {
                return false;
            }
            off += 4;
        }
        true
    }

    pub fn decode(&mut self, decoder: &mut dyn Decoder) -> Result<()> {
        let el = decoder.open_element_expect(ELEM_PAT_BLOCK)?;
        self.offset = decoder.read_signed_integer_attr(ATTRIB_OFF)? as i32;
        self.nonzerosize = decoder.read_signed_integer_attr(ATTRIB_NONZERO)? as i32;
        while decoder.peek_element()? != 0 {
            let subel = decoder.open_element_expect(ELEM_MASK_WORD)?;
            let mask = decoder.read_unsigned_integer_attr(ATTRIB_MASK)? as u32;
            let val = decoder.read_unsigned_integer_attr(ATTRIB_VAL)? as u32;
            self.maskvec.push(mask);
            self.valvec.push(val);
            decoder.close_element(subel)?;
        }
        self.normalize();
        decoder.close_element(el)
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum DisjointPattern {
    Instruction(PatternBlock),
    Context(PatternBlock),
    Combine { context: PatternBlock, instr: PatternBlock },
}

impl DisjointPattern {
    fn get_block(&self, context: bool) -> Option<&PatternBlock> {
        match self {
            DisjointPattern::Instruction(block) => {
                if context {
                    None
                } else {
                    Some(block)
                }
            }
            DisjointPattern::Context(block) => {
                if context {
                    Some(block)
                } else {
                    None
                }
            }
            DisjointPattern::Combine { context: cblock, instr } => {
                if context {
                    Some(cblock)
                } else {
                    Some(instr)
                }
            }
        }
    }

    pub fn get_mask(&self, startbit: i32, size: i32, context: bool) -> u32 {
        match self.get_block(context) {
            Some(block) => block.get_mask(startbit, size),
            None => 0,
        }
    }

    pub fn get_value(&self, startbit: i32, size: i32, context: bool) -> u32 {
        match self.get_block(context) {
            Some(block) => block.get_value(startbit, size),
            None => 0,
        }
    }

    pub fn get_length(&self, context: bool) -> i32 {
        match self.get_block(context) {
            Some(block) => block.get_length(),
            None => 0,
        }
    }

    pub fn is_match(&self, walker: &ParserWalker<'_>) -> Result<bool> {
        match self {
            DisjointPattern::Instruction(block) => block.is_instruction_match(walker),
            DisjointPattern::Context(block) => Ok(block.is_context_match(walker)),
            DisjointPattern::Combine { context, instr } => {
                if !instr.is_instruction_match(walker)? {
                    return Ok(false);
                }
                Ok(context.is_context_match(walker))
            }
        }
    }

    fn decode_block(decoder: &mut dyn Decoder, elem: ElementId) -> Result<PatternBlock> {
        let el = decoder.open_element_expect(elem)?;
        let mut block = PatternBlock::new_bool(true);
        block.decode(decoder)?;
        decoder.close_element(el)?;
        Ok(block)
    }

    pub fn decode_disjoint(decoder: &mut dyn Decoder) -> Result<DisjointPattern> {
        let el = decoder.peek_element()?;
        if el == ELEM_INSTRUCT_PAT {
            return Ok(DisjointPattern::Instruction(DisjointPattern::decode_block(
                decoder,
                ELEM_INSTRUCT_PAT,
            )?));
        }
        if el == ELEM_CONTEXT_PAT {
            return Ok(DisjointPattern::Context(DisjointPattern::decode_block(
                decoder,
                ELEM_CONTEXT_PAT,
            )?));
        }
        let el = decoder.open_element_expect(ELEM_COMBINE_PAT)?;
        let context = DisjointPattern::decode_block(decoder, ELEM_CONTEXT_PAT)?;
        let instr = DisjointPattern::decode_block(decoder, ELEM_INSTRUCT_PAT)?;
        decoder.close_element(el)?;
        Ok(DisjointPattern::Combine { context, instr })
    }
}
