use std::cmp::Ordering;

use crate::context::{FixedHandle, ParserWalker};
use crate::error::{Error, Result};
use crate::marshal::{Decoder, Encoder};
use crate::opcodes::OpCode;
use crate::slaformat::*;
use crate::space::{AddrSpace, SpaceRef, SpaceType};

pub const BUILD: OpCode = OpCode::Multiequal;
pub const DELAY_SLOT: OpCode = OpCode::Indirect;
pub const CROSSBUILD: OpCode = OpCode::Ptrsub;
pub const MACROBUILD: OpCode = OpCode::Cast;
pub const LABELBUILD: OpCode = OpCode::Ptradd;

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum ConstType {
    Real = 0,
    Handle = 1,
    JStart = 2,
    JNext = 3,
    JNext2 = 4,
    JCurspace = 5,
    JCurspaceSize = 6,
    Spaceid = 7,
    JRelative = 8,
    JFlowref = 9,
    JFlowrefSize = 10,
    JFlowdest = 11,
    JFlowdestSize = 12,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum VField {
    VSpace = 0,
    VOffset = 1,
    VSize = 2,
    VOffsetPlus = 3,
}

#[derive(Clone, Debug)]
pub struct ConstTpl {
    const_type: ConstType,
    spaceid: Option<SpaceRef>,
    handle_index: i32,
    value_real: u64,
    select: VField,
}

impl Default for ConstTpl {
    fn default() -> ConstTpl {
        ConstTpl::new()
    }
}

fn space_code(spc: Option<&SpaceRef>) -> u64 {
    match spc {
        Some(spc) => spc.get_index() as u64,
        None => 0,
    }
}

fn space_order(spc: &Option<SpaceRef>) -> i64 {
    match spc {
        Some(spc) => spc.get_index() as i64,
        None => -1,
    }
}

impl ConstTpl {
    pub fn new() -> ConstTpl {
        ConstTpl {
            const_type: ConstType::Real,
            spaceid: None,
            handle_index: 0,
            value_real: 0,
            select: VField::VSpace,
        }
    }

    pub fn new_value(tp: ConstType, val: u64) -> ConstTpl {
        ConstTpl {
            const_type: tp,
            spaceid: None,
            handle_index: 0,
            value_real: val,
            select: VField::VSpace,
        }
    }

    pub fn new_type(tp: ConstType) -> ConstTpl {
        ConstTpl {
            const_type: tp,
            spaceid: None,
            handle_index: 0,
            value_real: 0,
            select: VField::VSpace,
        }
    }

    pub fn new_space(sid: SpaceRef) -> ConstTpl {
        ConstTpl {
            const_type: ConstType::Spaceid,
            spaceid: Some(sid),
            handle_index: 0,
            value_real: 0,
            select: VField::VSpace,
        }
    }

    pub fn new_handle(ht: i32, vf: VField) -> ConstTpl {
        ConstTpl {
            const_type: ConstType::Handle,
            spaceid: None,
            handle_index: ht,
            value_real: 0,
            select: vf,
        }
    }

    pub fn new_handle_plus(ht: i32, vf: VField, plus: u64) -> ConstTpl {
        ConstTpl {
            const_type: ConstType::Handle,
            spaceid: None,
            handle_index: ht,
            value_real: plus,
            select: vf,
        }
    }

    pub fn is_const_space(&self) -> bool {
        if self.const_type == ConstType::Spaceid {
            return self
                .spaceid
                .as_ref()
                .is_some_and(|spc| spc.get_type() == SpaceType::Constant);
        }
        false
    }

    pub fn is_unique_space(&self) -> bool {
        if self.const_type == ConstType::Spaceid {
            return self
                .spaceid
                .as_ref()
                .is_some_and(|spc| spc.get_type() == SpaceType::Internal);
        }
        false
    }

    pub fn get_real(&self) -> u64 {
        self.value_real
    }

    pub fn get_space(&self) -> Option<&SpaceRef> {
        self.spaceid.as_ref()
    }

    pub fn get_handle_index(&self) -> i32 {
        self.handle_index
    }

    pub fn get_type(&self) -> ConstType {
        self.const_type
    }

    pub fn get_select(&self) -> VField {
        self.select
    }

    pub fn is_zero(&self) -> bool {
        self.const_type == ConstType::Real && self.value_real == 0
    }

    pub fn fix(&self, walker: &ParserWalker<'_>) -> Result<u64> {
        match self.const_type {
            ConstType::JStart => Ok(walker.get_addr().get_offset()),
            ConstType::JNext => Ok(walker.get_naddr().get_offset()),
            ConstType::JNext2 => Ok(walker.get_n2addr()?.get_offset()),
            ConstType::JFlowref => Ok(walker.get_ref_addr().get_offset()),
            ConstType::JFlowrefSize => Ok(walker.get_ref_addr().get_addr_size() as u64),
            ConstType::JFlowdest => Ok(walker.get_dest_addr().get_offset()),
            ConstType::JFlowdestSize => Ok(walker.get_dest_addr().get_addr_size() as u64),
            ConstType::JCurspaceSize => Ok(walker
                .get_cur_space()
                .map(|spc| spc.get_addr_size() as u64)
                .unwrap_or(0)),
            ConstType::JCurspace => Ok(space_code(walker.get_cur_space())),
            ConstType::Handle => {
                let hand = walker.get_fixed_handle(self.handle_index);
                match self.select {
                    VField::VSpace => {
                        if hand.offset_space.is_none() {
                            Ok(space_code(hand.space.as_ref()))
                        } else {
                            Ok(space_code(hand.temp_space.as_ref()))
                        }
                    }
                    VField::VOffset => {
                        if hand.offset_space.is_none() {
                            Ok(hand.offset_offset)
                        } else {
                            Ok(hand.temp_offset)
                        }
                    }
                    VField::VSize => Ok(hand.size as u64),
                    VField::VOffsetPlus => {
                        let is_const = match (&hand.space, walker.get_const_space()) {
                            (Some(first), Some(second)) => first.get_index() == second.get_index(),
                            (None, None) => true,
                            _ => false,
                        };
                        if !is_const {
                            if hand.offset_space.is_none() {
                                return Ok(hand.offset_offset.wrapping_add(self.value_real & 0xffff));
                            }
                            Ok(hand.temp_offset.wrapping_add(self.value_real & 0xffff))
                        } else {
                            let val = if hand.offset_space.is_none() {
                                hand.offset_offset
                            } else {
                                hand.temp_offset
                            };
                            Ok(val.wrapping_shr((8 * (self.value_real >> 16)) as u32))
                        }
                    }
                }
            }
            ConstType::JRelative | ConstType::Real => Ok(self.value_real),
            ConstType::Spaceid => Ok(space_code(self.spaceid.as_ref())),
        }
    }

    pub fn fix_space(&self, walker: &ParserWalker<'_>) -> Result<SpaceRef> {
        let res = match self.const_type {
            ConstType::JCurspace => walker.get_cur_space().cloned(),
            ConstType::Handle => {
                let hand = walker.get_fixed_handle(self.handle_index);
                match self.select {
                    VField::VSpace => {
                        if hand.offset_space.is_none() {
                            hand.space.clone()
                        } else {
                            hand.temp_space.clone()
                        }
                    }
                    _ => {
                        return Err(Error::Lowlevel("ConstTpl is not a spaceid as expected".to_string()));
                    }
                }
            }
            ConstType::Spaceid => self.spaceid.clone(),
            ConstType::JFlowref => walker.get_ref_addr().get_space().cloned(),
            _ => {
                return Err(Error::Lowlevel("ConstTpl is not a spaceid as expected".to_string()));
            }
        };
        res.ok_or_else(|| Error::BadData("ConstTpl space is not defined".to_string()))
    }

    pub fn fillin_space(&self, hand: &mut FixedHandle, walker: &ParserWalker<'_>) -> Result<()> {
        match self.const_type {
            ConstType::JCurspace => {
                hand.space = walker.get_cur_space().cloned();
                return Ok(());
            }
            ConstType::Handle => {
                let otherhand = walker.get_fixed_handle(self.handle_index);
                if self.select == VField::VSpace {
                    hand.space = otherhand.space.clone();
                    return Ok(());
                }
            }
            ConstType::Spaceid => {
                hand.space = self.spaceid.clone();
                return Ok(());
            }
            _ => {}
        }
        Err(Error::Lowlevel("ConstTpl is not a spaceid as expected".to_string()))
    }

    pub fn fillin_offset(&self, hand: &mut FixedHandle, walker: &ParserWalker<'_>) -> Result<()> {
        if self.const_type == ConstType::Handle {
            let otherhand = walker.get_fixed_handle(self.handle_index);
            hand.offset_space = otherhand.offset_space.clone();
            hand.offset_offset = otherhand.offset_offset;
            hand.offset_size = otherhand.offset_size;
            hand.temp_space = otherhand.temp_space.clone();
            hand.temp_offset = otherhand.temp_offset;
        } else {
            hand.offset_space = None;
            let val = self.fix(walker)?;
            hand.offset_offset = match &hand.space {
                Some(spc) => spc.wrap_offset(val),
                None => val,
            };
        }
        Ok(())
    }

    pub fn transfer(&mut self, params: &[HandleTpl]) -> Result<()> {
        if self.const_type != ConstType::Handle {
            return Ok(());
        }
        let newhandle = &params[self.handle_index as usize];
        match self.select {
            VField::VSpace => {
                *self = newhandle.get_space().clone();
            }
            VField::VOffset => {
                *self = newhandle.get_ptr_offset().clone();
            }
            VField::VOffsetPlus => {
                let tmp = self.value_real;
                *self = newhandle.get_ptr_offset().clone();
                if self.const_type == ConstType::Real {
                    self.value_real = self.value_real.wrapping_add(tmp & 0xffff);
                } else if self.const_type == ConstType::Handle && self.select == VField::VOffset {
                    self.select = VField::VOffsetPlus;
                    self.value_real = tmp;
                } else {
                    return Err(Error::Lowlevel("Cannot truncate macro input in this way".to_string()));
                }
            }
            VField::VSize => {
                *self = newhandle.get_size().clone();
            }
        }
        Ok(())
    }

    pub fn change_handle_index(&mut self, handmap: &[i32]) {
        if self.const_type == ConstType::Handle {
            self.handle_index = handmap[self.handle_index as usize];
        }
    }

    pub fn encode(&self, encoder: &mut dyn Encoder) {
        match self.const_type {
            ConstType::Real => {
                encoder.open_element(ELEM_CONST_REAL);
                encoder.write_unsigned_integer(ATTRIB_VAL, self.value_real);
                encoder.close_element(ELEM_CONST_REAL);
            }
            ConstType::Handle => {
                encoder.open_element(ELEM_CONST_HANDLE);
                encoder.write_signed_integer(ATTRIB_VAL, self.handle_index as i64);
                encoder.write_signed_integer(ATTRIB_S, self.select as i64);
                if self.select == VField::VOffsetPlus {
                    encoder.write_unsigned_integer(ATTRIB_PLUS, self.value_real);
                }
                encoder.close_element(ELEM_CONST_HANDLE);
            }
            ConstType::JStart => {
                encoder.open_element(ELEM_CONST_START);
                encoder.close_element(ELEM_CONST_START);
            }
            ConstType::JNext => {
                encoder.open_element(ELEM_CONST_NEXT);
                encoder.close_element(ELEM_CONST_NEXT);
            }
            ConstType::JNext2 => {
                encoder.open_element(ELEM_CONST_NEXT2);
                encoder.close_element(ELEM_CONST_NEXT2);
            }
            ConstType::JCurspace => {
                encoder.open_element(ELEM_CONST_CURSPACE);
                encoder.close_element(ELEM_CONST_CURSPACE);
            }
            ConstType::JCurspaceSize => {
                encoder.open_element(ELEM_CONST_CURSPACE_SIZE);
                encoder.close_element(ELEM_CONST_CURSPACE_SIZE);
            }
            ConstType::Spaceid => {
                encoder.open_element(ELEM_CONST_SPACEID);
                if let Some(spc) = &self.spaceid {
                    encoder.write_space(ATTRIB_SPACE, spc);
                }
                encoder.close_element(ELEM_CONST_SPACEID);
            }
            ConstType::JRelative => {
                encoder.open_element(ELEM_CONST_RELATIVE);
                encoder.write_unsigned_integer(ATTRIB_VAL, self.value_real);
                encoder.close_element(ELEM_CONST_RELATIVE);
            }
            ConstType::JFlowref => {
                encoder.open_element(ELEM_CONST_FLOWREF);
                encoder.close_element(ELEM_CONST_FLOWREF);
            }
            ConstType::JFlowrefSize => {
                encoder.open_element(ELEM_CONST_FLOWREF_SIZE);
                encoder.close_element(ELEM_CONST_FLOWREF_SIZE);
            }
            ConstType::JFlowdest => {
                encoder.open_element(ELEM_CONST_FLOWDEST);
                encoder.close_element(ELEM_CONST_FLOWDEST);
            }
            ConstType::JFlowdestSize => {
                encoder.open_element(ELEM_CONST_FLOWDEST_SIZE);
                encoder.close_element(ELEM_CONST_FLOWDEST_SIZE);
            }
        }
    }

    pub fn decode(&mut self, decoder: &mut dyn Decoder) -> Result<()> {
        let el = decoder.open_element()?;
        if el == ELEM_CONST_REAL {
            self.const_type = ConstType::Real;
            self.value_real = decoder.read_unsigned_integer_attr(ATTRIB_VAL)?;
        } else if el == ELEM_CONST_HANDLE {
            self.const_type = ConstType::Handle;
            self.handle_index = decoder.read_signed_integer_attr(ATTRIB_VAL)? as i32;
            let select_int = decoder.read_signed_integer_attr(ATTRIB_S)? as u32;
            self.select = match select_int {
                0 => VField::VSpace,
                1 => VField::VOffset,
                2 => VField::VSize,
                3 => VField::VOffsetPlus,
                _ => {
                    return Err(Error::Decoder("Bad handle selector encoding".to_string()));
                }
            };
            if self.select == VField::VOffsetPlus {
                self.value_real = decoder.read_unsigned_integer_attr(ATTRIB_PLUS)?;
            }
        } else if el == ELEM_CONST_START {
            self.const_type = ConstType::JStart;
        } else if el == ELEM_CONST_NEXT {
            self.const_type = ConstType::JNext;
        } else if el == ELEM_CONST_NEXT2 {
            self.const_type = ConstType::JNext2;
        } else if el == ELEM_CONST_CURSPACE {
            self.const_type = ConstType::JCurspace;
        } else if el == ELEM_CONST_CURSPACE_SIZE {
            self.const_type = ConstType::JCurspaceSize;
        } else if el == ELEM_CONST_SPACEID {
            self.const_type = ConstType::Spaceid;
            self.spaceid = Some(decoder.read_space_attr(ATTRIB_SPACE)?);
        } else if el == ELEM_CONST_RELATIVE {
            self.const_type = ConstType::JRelative;
            self.value_real = decoder.read_unsigned_integer_attr(ATTRIB_VAL)?;
        } else if el == ELEM_CONST_FLOWREF {
            self.const_type = ConstType::JFlowref;
        } else if el == ELEM_CONST_FLOWREF_SIZE {
            self.const_type = ConstType::JFlowrefSize;
        } else if el == ELEM_CONST_FLOWDEST {
            self.const_type = ConstType::JFlowdest;
        } else if el == ELEM_CONST_FLOWDEST_SIZE {
            self.const_type = ConstType::JFlowdestSize;
        } else {
            return Err(Error::Lowlevel("Bad constant type".to_string()));
        }
        decoder.close_element(el)
    }
}

impl PartialEq for ConstTpl {
    fn eq(&self, op2: &ConstTpl) -> bool {
        if self.const_type != op2.const_type {
            return false;
        }
        match self.const_type {
            ConstType::Real => self.value_real == op2.value_real,
            ConstType::Handle => self.handle_index == op2.handle_index && self.select == op2.select,
            ConstType::Spaceid => space_order(&self.spaceid) == space_order(&op2.spaceid),
            _ => true,
        }
    }
}

impl Eq for ConstTpl {}

impl PartialOrd for ConstTpl {
    fn partial_cmp(&self, other: &ConstTpl) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for ConstTpl {
    fn cmp(&self, op2: &ConstTpl) -> Ordering {
        if self.const_type != op2.const_type {
            return self.const_type.cmp(&op2.const_type);
        }
        match self.const_type {
            ConstType::Real => self.value_real.cmp(&op2.value_real),
            ConstType::Handle => {
                if self.handle_index != op2.handle_index {
                    return self.handle_index.cmp(&op2.handle_index);
                }
                self.select.cmp(&op2.select)
            }
            ConstType::Spaceid => space_order(&self.spaceid).cmp(&space_order(&op2.spaceid)),
            _ => Ordering::Equal,
        }
    }
}

#[derive(Clone, Debug, Default)]
pub struct VarnodeTpl {
    space: ConstTpl,
    offset: ConstTpl,
    size: ConstTpl,
    unnamed_flag: bool,
}

impl VarnodeTpl {
    pub fn new_handle(hand: i32, zerosize: bool) -> VarnodeTpl {
        let mut res = VarnodeTpl {
            space: ConstTpl::new_handle(hand, VField::VSpace),
            offset: ConstTpl::new_handle(hand, VField::VOffset),
            size: ConstTpl::new_handle(hand, VField::VSize),
            unnamed_flag: false,
        };
        if zerosize {
            res.size = ConstTpl::new_value(ConstType::Real, 0);
        }
        res
    }

    pub fn new(sp: ConstTpl, off: ConstTpl, sz: ConstTpl) -> VarnodeTpl {
        VarnodeTpl {
            space: sp,
            offset: off,
            size: sz,
            unnamed_flag: false,
        }
    }

    pub fn get_space(&self) -> &ConstTpl {
        &self.space
    }

    pub fn get_offset(&self) -> &ConstTpl {
        &self.offset
    }

    pub fn get_size(&self) -> &ConstTpl {
        &self.size
    }

    pub fn is_dynamic(&self, walker: &ParserWalker<'_>) -> bool {
        if self.offset.get_type() != ConstType::Handle {
            return false;
        }
        let hand = walker.get_fixed_handle(self.offset.get_handle_index());
        hand.offset_space.is_some()
    }

    pub fn transfer(&mut self, params: &[HandleTpl]) -> Result<i32> {
        let mut does_offset_plus = false;
        let mut handle_index = 0;
        let mut plus = 0;
        if self.offset.get_type() == ConstType::Handle && self.offset.get_select() == VField::VOffsetPlus {
            handle_index = self.offset.get_handle_index();
            plus = self.offset.get_real() as i32;
            does_offset_plus = true;
        }
        self.space.transfer(params)?;
        self.offset.transfer(params)?;
        self.size.transfer(params)?;
        if does_offset_plus {
            if self.is_local_temp() {
                return Ok(plus);
            }
            if params[handle_index as usize].get_size().is_zero() {
                return Ok(plus);
            }
        }
        Ok(-1)
    }

    pub fn is_zero_size(&self) -> bool {
        self.size.is_zero()
    }

    pub fn set_offset(&mut self, const_val: u64) {
        self.offset = ConstTpl::new_value(ConstType::Real, const_val);
    }

    pub fn set_relative(&mut self, const_val: u64) {
        self.offset = ConstTpl::new_value(ConstType::JRelative, const_val);
    }

    pub fn set_size(&mut self, sz: ConstTpl) {
        self.size = sz;
    }

    pub fn is_unnamed(&self) -> bool {
        self.unnamed_flag
    }

    pub fn set_unnamed(&mut self, val: bool) {
        self.unnamed_flag = val;
    }

    pub fn is_local_temp(&self) -> bool {
        if self.space.get_type() != ConstType::Spaceid {
            return false;
        }
        self.space
            .get_space()
            .is_some_and(|spc| spc.get_type() == SpaceType::Internal)
    }

    pub fn is_relative(&self) -> bool {
        self.offset.get_type() == ConstType::JRelative
    }

    pub fn change_handle_index(&mut self, handmap: &[i32]) {
        self.space.change_handle_index(handmap);
        self.offset.change_handle_index(handmap);
        self.size.change_handle_index(handmap);
    }

    pub fn adjust_truncation(&mut self, sz: i32, isbigendian: bool) -> bool {
        if self.size.get_type() != ConstType::Real {
            return false;
        }
        let numbytes = self.size.get_real() as i32;
        let byteoffset = self.offset.get_real() as i32;
        if numbytes + byteoffset > sz {
            return false;
        }
        let mut val = byteoffset as i64 as u64;
        val <<= 16;
        if isbigendian {
            val |= (sz - (numbytes + byteoffset)) as i64 as u64;
        } else {
            val |= byteoffset as i64 as u64;
        }
        self.offset = ConstTpl::new_handle_plus(self.offset.get_handle_index(), VField::VOffsetPlus, val);
        true
    }

    pub fn encode(&self, encoder: &mut dyn Encoder) {
        encoder.open_element(ELEM_VARNODE_TPL);
        self.space.encode(encoder);
        self.offset.encode(encoder);
        self.size.encode(encoder);
        encoder.close_element(ELEM_VARNODE_TPL);
    }

    pub fn decode(&mut self, decoder: &mut dyn Decoder) -> Result<()> {
        let el = decoder.open_element_expect(ELEM_VARNODE_TPL)?;
        self.space.decode(decoder)?;
        self.offset.decode(decoder)?;
        self.size.decode(decoder)?;
        decoder.close_element(el)
    }
}

impl PartialEq for VarnodeTpl {
    fn eq(&self, op2: &VarnodeTpl) -> bool {
        self.space == op2.space && self.offset == op2.offset && self.size == op2.size
    }
}

impl Eq for VarnodeTpl {}

impl PartialOrd for VarnodeTpl {
    fn partial_cmp(&self, other: &VarnodeTpl) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for VarnodeTpl {
    fn cmp(&self, op2: &VarnodeTpl) -> Ordering {
        if self.space != op2.space {
            return self.space.cmp(&op2.space);
        }
        if self.offset != op2.offset {
            return self.offset.cmp(&op2.offset);
        }
        if self.size != op2.size {
            return self.size.cmp(&op2.size);
        }
        Ordering::Equal
    }
}

#[derive(Clone, Debug, Default)]
pub struct HandleTpl {
    space: ConstTpl,
    size: ConstTpl,
    ptrspace: ConstTpl,
    ptroffset: ConstTpl,
    ptrsize: ConstTpl,
    temp_space: ConstTpl,
    temp_offset: ConstTpl,
}

impl HandleTpl {
    pub fn new() -> HandleTpl {
        HandleTpl::default()
    }

    pub fn from_varnode(vn: &VarnodeTpl) -> HandleTpl {
        HandleTpl {
            space: vn.get_space().clone(),
            size: vn.get_size().clone(),
            ptrspace: ConstTpl::new_value(ConstType::Real, 0),
            ptroffset: vn.get_offset().clone(),
            ptrsize: ConstTpl::new(),
            temp_space: ConstTpl::new(),
            temp_offset: ConstTpl::new(),
        }
    }

    pub fn new_dynamic(spc: &ConstTpl, sz: &ConstTpl, vn: &VarnodeTpl, t_space: SpaceRef, t_offset: u64) -> HandleTpl {
        HandleTpl {
            space: spc.clone(),
            size: sz.clone(),
            ptrspace: vn.get_space().clone(),
            ptroffset: vn.get_offset().clone(),
            ptrsize: vn.get_size().clone(),
            temp_space: ConstTpl::new_space(t_space),
            temp_offset: ConstTpl::new_value(ConstType::Real, t_offset),
        }
    }

    pub fn get_space(&self) -> &ConstTpl {
        &self.space
    }

    pub fn get_ptr_space(&self) -> &ConstTpl {
        &self.ptrspace
    }

    pub fn get_ptr_offset(&self) -> &ConstTpl {
        &self.ptroffset
    }

    pub fn get_ptr_size(&self) -> &ConstTpl {
        &self.ptrsize
    }

    pub fn get_size(&self) -> &ConstTpl {
        &self.size
    }

    pub fn get_temp_space(&self) -> &ConstTpl {
        &self.temp_space
    }

    pub fn get_temp_offset(&self) -> &ConstTpl {
        &self.temp_offset
    }

    pub fn set_size(&mut self, sz: ConstTpl) {
        self.size = sz;
    }

    pub fn set_ptr_size(&mut self, sz: ConstTpl) {
        self.ptrsize = sz;
    }

    pub fn set_ptr_offset(&mut self, val: u64) {
        self.ptroffset = ConstTpl::new_value(ConstType::Real, val);
    }

    pub fn set_temp_offset(&mut self, val: u64) {
        self.temp_offset = ConstTpl::new_value(ConstType::Real, val);
    }

    pub fn fix(&self, hand: &mut FixedHandle, walker: &ParserWalker<'_>) -> Result<()> {
        if self.ptrspace.get_type() == ConstType::Real {
            self.space.fillin_space(hand, walker)?;
            hand.size = self.size.fix(walker)? as u32;
            self.ptroffset.fillin_offset(hand, walker)?;
        } else {
            let space = self.space.fix_space(walker)?;
            hand.size = self.size.fix(walker)? as u32;
            hand.offset_offset = self.ptroffset.fix(walker)?;
            let offset_space = self.ptrspace.fix_space(walker)?;
            if offset_space.get_type() == SpaceType::Constant {
                hand.offset_space = None;
                hand.offset_offset = AddrSpace::address_to_byte(hand.offset_offset, space.get_word_size());
                hand.offset_offset = space.wrap_offset(hand.offset_offset);
            } else {
                hand.offset_space = Some(offset_space);
                hand.offset_size = self.ptrsize.fix(walker)? as u32;
                hand.temp_space = Some(self.temp_space.fix_space(walker)?);
                hand.temp_offset = self.temp_offset.fix(walker)?;
            }
            hand.space = Some(space);
        }
        Ok(())
    }

    pub fn change_handle_index(&mut self, handmap: &[i32]) {
        self.space.change_handle_index(handmap);
        self.size.change_handle_index(handmap);
        self.ptrspace.change_handle_index(handmap);
        self.ptroffset.change_handle_index(handmap);
        self.ptrsize.change_handle_index(handmap);
        self.temp_space.change_handle_index(handmap);
        self.temp_offset.change_handle_index(handmap);
    }

    pub fn encode(&self, encoder: &mut dyn Encoder) {
        encoder.open_element(ELEM_HANDLE_TPL);
        self.space.encode(encoder);
        self.size.encode(encoder);
        self.ptrspace.encode(encoder);
        self.ptroffset.encode(encoder);
        self.ptrsize.encode(encoder);
        self.temp_space.encode(encoder);
        self.temp_offset.encode(encoder);
        encoder.close_element(ELEM_HANDLE_TPL);
    }

    pub fn decode(&mut self, decoder: &mut dyn Decoder) -> Result<()> {
        let el = decoder.open_element_expect(ELEM_HANDLE_TPL)?;
        self.space.decode(decoder)?;
        self.size.decode(decoder)?;
        self.ptrspace.decode(decoder)?;
        self.ptroffset.decode(decoder)?;
        self.ptrsize.decode(decoder)?;
        self.temp_space.decode(decoder)?;
        self.temp_offset.decode(decoder)?;
        decoder.close_element(el)
    }
}

#[derive(Clone, Debug)]
pub struct OpTpl {
    output: Option<VarnodeTpl>,
    opc: OpCode,
    input: Vec<VarnodeTpl>,
}

impl Default for OpTpl {
    fn default() -> OpTpl {
        OpTpl::new(OpCode::Blank)
    }
}

impl OpTpl {
    pub fn new(oc: OpCode) -> OpTpl {
        OpTpl {
            output: None,
            opc: oc,
            input: Vec::new(),
        }
    }

    pub fn get_out(&self) -> Option<&VarnodeTpl> {
        self.output.as_ref()
    }

    pub fn get_out_mut(&mut self) -> Option<&mut VarnodeTpl> {
        self.output.as_mut()
    }

    pub fn num_input(&self) -> i32 {
        self.input.len() as i32
    }

    pub fn get_in(&self, index: i32) -> &VarnodeTpl {
        &self.input[index as usize]
    }

    pub fn get_in_mut(&mut self, index: i32) -> &mut VarnodeTpl {
        &mut self.input[index as usize]
    }

    pub fn get_inputs(&self) -> &[VarnodeTpl] {
        &self.input
    }

    pub fn get_opcode(&self) -> OpCode {
        self.opc
    }

    pub fn is_zero_size(&self) -> bool {
        if let Some(output) = &self.output
            && output.is_zero_size()
        {
            return true;
        }
        self.input.iter().any(|vn| vn.is_zero_size())
    }

    pub fn set_opcode(&mut self, opc: OpCode) {
        self.opc = opc;
    }

    pub fn set_output(&mut self, vt: Option<VarnodeTpl>) {
        self.output = vt;
    }

    pub fn clear_output(&mut self) {
        self.output = None;
    }

    pub fn add_input(&mut self, vt: VarnodeTpl) {
        self.input.push(vt);
    }

    pub fn set_input(&mut self, vt: VarnodeTpl, slot: i32) {
        self.input[slot as usize] = vt;
    }

    pub fn remove_input(&mut self, index: i32) {
        self.input.remove(index as usize);
    }

    pub fn change_handle_index(&mut self, handmap: &[i32]) {
        if let Some(output) = &mut self.output {
            output.change_handle_index(handmap);
        }
        for vn in self.input.iter_mut() {
            vn.change_handle_index(handmap);
        }
    }

    pub fn encode(&self, encoder: &mut dyn Encoder) {
        encoder.open_element(ELEM_OP_TPL);
        encoder.write_opcode(ATTRIB_CODE, self.opc);
        match &self.output {
            None => {
                encoder.open_element(ELEM_NULL);
                encoder.close_element(ELEM_NULL);
            }
            Some(output) => output.encode(encoder),
        }
        for vn in self.input.iter() {
            vn.encode(encoder);
        }
        encoder.close_element(ELEM_OP_TPL);
    }

    pub fn decode(&mut self, decoder: &mut dyn Decoder) -> Result<()> {
        let el = decoder.open_element_expect(ELEM_OP_TPL)?;
        self.opc = decoder.read_opcode_attr(ATTRIB_CODE)?;
        let subel = decoder.peek_element()?;
        if subel == ELEM_NULL {
            decoder.open_element()?;
            decoder.close_element(subel)?;
            self.output = None;
        } else {
            let mut output = VarnodeTpl::default();
            output.decode(decoder)?;
            self.output = Some(output);
        }
        while decoder.peek_element()? != 0 {
            let mut vn = VarnodeTpl::default();
            vn.decode(decoder)?;
            self.input.push(vn);
        }
        decoder.close_element(el)
    }
}

#[derive(Clone, Debug, Default)]
pub struct ConstructTpl {
    delayslot: u32,
    numlabels: u32,
    vec: Vec<OpTpl>,
    result: Option<HandleTpl>,
}

impl ConstructTpl {
    pub fn new() -> ConstructTpl {
        ConstructTpl::default()
    }

    pub fn delay_slot(&self) -> u32 {
        self.delayslot
    }

    pub fn num_labels(&self) -> u32 {
        self.numlabels
    }

    pub fn get_opvec(&self) -> &[OpTpl] {
        &self.vec
    }

    pub fn get_opvec_mut(&mut self) -> &mut Vec<OpTpl> {
        &mut self.vec
    }

    pub fn get_result(&self) -> Option<&HandleTpl> {
        self.result.as_ref()
    }

    pub fn set_opvec(&mut self, opvec: Vec<OpTpl>) {
        self.vec = opvec;
    }

    pub fn set_num_labels(&mut self, val: u32) {
        self.numlabels = val;
    }

    pub fn add_op(&mut self, ot: OpTpl) -> std::result::Result<(), OpTpl> {
        if ot.get_opcode() == DELAY_SLOT {
            if self.delayslot != 0 {
                return Err(ot);
            }
            self.delayslot = ot.get_in(0).get_offset().get_real() as u32;
        } else if ot.get_opcode() == LABELBUILD {
            self.numlabels += 1;
        }
        self.vec.push(ot);
        Ok(())
    }

    pub fn add_op_list(&mut self, oplist: Vec<OpTpl>) -> bool {
        for op in oplist {
            if self.add_op(op).is_err() {
                return false;
            }
        }
        true
    }

    pub fn set_result(&mut self, handle: Option<HandleTpl>) {
        self.result = handle;
    }

    pub fn fillin_build(&mut self, check: &mut [i32], const_space: &SpaceRef) -> i32 {
        for op in self.vec.iter() {
            if op.get_opcode() == BUILD {
                let index = op.get_in(0).get_offset().get_real() as usize;
                if check[index] != 0 {
                    return check[index];
                }
                check[index] = 1;
            }
        }
        for (index, value) in check.iter().enumerate() {
            if *value == 0 {
                let mut op = OpTpl::new(BUILD);
                let indvn = VarnodeTpl::new(
                    ConstTpl::new_space(const_space.clone()),
                    ConstTpl::new_value(ConstType::Real, index as u64),
                    ConstTpl::new_value(ConstType::Real, 4),
                );
                op.add_input(indvn);
                self.vec.insert(0, op);
            }
        }
        0
    }

    pub fn build_only(&self) -> bool {
        self.vec.iter().all(|op| op.get_opcode() == BUILD)
    }

    pub fn change_handle_index(&mut self, handmap: &[i32]) {
        for op in self.vec.iter_mut() {
            if op.get_opcode() == BUILD {
                let index = op.get_in(0).get_offset().get_real() as usize;
                let mapped = handmap[index];
                op.get_in_mut(0).set_offset(mapped as i64 as u64);
            } else {
                op.change_handle_index(handmap);
            }
        }
        if let Some(result) = &mut self.result {
            result.change_handle_index(handmap);
        }
    }

    pub fn set_input(&mut self, vn: VarnodeTpl, index: i32, slot: i32) {
        self.vec[index as usize].set_input(vn, slot);
    }

    pub fn set_output(&mut self, vn: VarnodeTpl, index: i32) {
        self.vec[index as usize].set_output(Some(vn));
    }

    pub fn delete_ops(&mut self, indices: &[i32]) {
        let mut retained = vec![true; self.vec.len()];
        for index in indices {
            retained[*index as usize] = false;
        }
        let mut position = 0;
        self.vec.retain(|_| {
            let res = retained[position];
            position += 1;
            res
        });
    }

    pub fn encode(&self, encoder: &mut dyn Encoder, sectionid: i32) {
        encoder.open_element(ELEM_CONSTRUCT_TPL);
        if sectionid >= 0 {
            encoder.write_signed_integer(ATTRIB_SECTION, sectionid as i64);
        }
        if self.delayslot != 0 {
            encoder.write_signed_integer(ATTRIB_DELAY, self.delayslot as i64);
        }
        if self.numlabels != 0 {
            encoder.write_signed_integer(ATTRIB_LABELS, self.numlabels as i64);
        }
        match &self.result {
            Some(result) => result.encode(encoder),
            None => {
                encoder.open_element(ELEM_NULL);
                encoder.close_element(ELEM_NULL);
            }
        }
        for op in self.vec.iter() {
            op.encode(encoder);
        }
        encoder.close_element(ELEM_CONSTRUCT_TPL);
    }

    pub fn decode(&mut self, decoder: &mut dyn Decoder) -> Result<i32> {
        let el = decoder.open_element_expect(ELEM_CONSTRUCT_TPL)?;
        let mut sectionid = -1;
        let mut attrib = decoder.get_next_attribute_id()?;
        while attrib != 0 {
            if attrib == ATTRIB_DELAY {
                self.delayslot = decoder.read_signed_integer()? as u32;
            } else if attrib == ATTRIB_LABELS {
                self.numlabels = decoder.read_signed_integer()? as u32;
            } else if attrib == ATTRIB_SECTION {
                sectionid = decoder.read_signed_integer()? as i32;
            }
            attrib = decoder.get_next_attribute_id()?;
        }
        let subel = decoder.peek_element()?;
        if subel == ELEM_NULL {
            decoder.open_element()?;
            decoder.close_element(subel)?;
            self.result = None;
        } else {
            let mut result = HandleTpl::new();
            result.decode(decoder)?;
            self.result = Some(result);
        }
        while decoder.peek_element()? != 0 {
            let mut op = OpTpl::default();
            op.decode(decoder)?;
            self.vec.push(op);
        }
        decoder.close_element(el)?;
        Ok(sectionid)
    }
}

#[derive(Clone, Copy, Debug, Default)]
pub struct LabelCounter {
    pub labelbase: u32,
    pub labelcount: u32,
}

impl LabelCounter {
    pub fn new(lbcnt: u32) -> LabelCounter {
        LabelCounter {
            labelbase: lbcnt,
            labelcount: lbcnt,
        }
    }
}

pub trait PcodeBuilder {
    fn label_counter(&mut self) -> &mut LabelCounter;

    fn dump(&mut self, op: &OpTpl) -> Result<()>;

    fn append_build(&mut self, bld: &OpTpl, secnum: i32) -> Result<()>;

    fn delay_slot(&mut self, op: &OpTpl) -> Result<()>;

    fn set_label(&mut self, op: &OpTpl) -> Result<()>;

    fn append_cross_build(&mut self, bld: &OpTpl, secnum: i32) -> Result<()>;

    fn get_label_base(&mut self) -> u32 {
        self.label_counter().labelbase
    }

    fn build(&mut self, construct: Option<&ConstructTpl>, secnum: i32) -> Result<()> {
        let Some(construct) = construct else {
            return Err(Error::Unimpl {
                message: String::new(),
                instruction_length: 0,
            });
        };
        let oldbase = self.label_counter().labelbase;
        {
            let counter = self.label_counter();
            counter.labelbase = counter.labelcount;
            counter.labelcount = counter.labelcount.wrapping_add(construct.num_labels());
        }
        for op in construct.get_opvec() {
            match op.get_opcode() {
                BUILD => self.append_build(op, secnum)?,
                DELAY_SLOT => self.delay_slot(op)?,
                LABELBUILD => self.set_label(op)?,
                CROSSBUILD => self.append_cross_build(op, secnum)?,
                _ => self.dump(op)?,
            }
        }
        self.label_counter().labelbase = oldbase;
        Ok(())
    }
}
