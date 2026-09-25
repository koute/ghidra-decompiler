use std::fmt::Write as _;
use std::sync::atomic::{AtomicI32, AtomicU8, AtomicU32, AtomicU64, Ordering};
use std::sync::{Arc, OnceLock, RwLock};

use crate::address::calc_mask;
use crate::error::{Error, Result};
use crate::istream::{self, Basefield};
use crate::marshal::{
    ATTRIB_BIGENDIAN, ATTRIB_INDEX, ATTRIB_NAME, ATTRIB_OFFSET, ATTRIB_SIZE, ATTRIB_SPACE, ATTRIB_UNKNOWN,
    ATTRIB_WORDSIZE, AttributeId, Decoder, Encoder,
};
use crate::pcoderaw::VarnodeData;
use crate::translate::{AddrSpaceManager, ELEM_SPACE_BASE, ELEM_SPACE_OVERLAY, JoinRecord, JoinTable, Translate};

pub type SpaceRef = Arc<AddrSpace>;

pub const ATTRIB_BASE: AttributeId = AttributeId::new("base", 89);
pub const ATTRIB_DEADCODEDELAY: AttributeId = AttributeId::new("deadcodedelay", 90);
pub const ATTRIB_DELAY: AttributeId = AttributeId::new("delay", 91);
pub const ATTRIB_LOGICALSIZE: AttributeId = AttributeId::new("logicalsize", 92);
pub const ATTRIB_PHYSICAL: AttributeId = AttributeId::new("physical", 93);
pub const ATTRIB_PIECE: AttributeId = AttributeId::new("piece", 94);

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum SpaceType {
    Constant = 0,
    Processor = 1,
    Spacebase = 2,
    Internal = 3,
    Fspec = 4,
    Iop = 5,
    Join = 6,
}

#[derive(Clone, Debug, Default)]
pub struct SpacebaseRegister {
    pub hasbaseregister: bool,
    pub is_negative_stack: bool,
    pub baseloc: VarnodeData,
    pub base_orig: VarnodeData,
}

#[derive(Debug)]
pub enum SpaceKind {
    Base,
    Constant,
    Other,
    Unique,
    Join {
        table: Arc<JoinTable>,
    },
    Overlay {
        base_space: SpaceRef,
    },
    Spacebase {
        contain: Option<SpaceRef>,
        register: RwLock<SpacebaseRegister>,
    },
    Fspec,
    Iop,
    Maximal,
}

#[derive(Debug)]
pub struct AddrSpace {
    kind: SpaceKind,
    space_type: SpaceType,
    flags: AtomicU32,
    shortcut: AtomicU8,
    highest: AtomicU64,
    pointer_lower_bound: AtomicU64,
    pointer_upper_bound: AtomicU64,
    name: String,
    address_size: AtomicU32,
    wordsize: u32,
    minimum_pointer_size: AtomicI32,
    index: i32,
    delay: i32,
    deadcodedelay: AtomicI32,
}

pub const CONSTANT_SPACE_NAME: &str = "const";
pub const CONSTANT_SPACE_INDEX: i32 = 0;
pub const OTHER_SPACE_NAME: &str = "OTHER";
pub const OTHER_SPACE_INDEX: i32 = 1;
pub const UNIQUE_SPACE_NAME: &str = "unique";
pub const UNIQUE_SPACE_SIZE: u32 = 4;
pub const JOIN_SPACE_NAME: &str = "join";
pub const FSPEC_SPACE_NAME: &str = "fspec";
pub const IOP_SPACE_NAME: &str = "iop";
const JOIN_MAX_PIECES: i32 = 64;

impl AddrSpace {
    pub const BIG_ENDIAN: u32 = 1;
    pub const HERITAGED: u32 = 2;
    pub const DOES_DEADCODE: u32 = 4;
    pub const PROGRAMSPECIFIC: u32 = 8;
    pub const REVERSE_JUSTIFICATION: u32 = 16;
    pub const FORMAL_STACKSPACE: u32 = 0x20;
    pub const OVERLAY: u32 = 0x40;
    pub const OVERLAYBASE: u32 = 0x80;
    pub const TRUNCATED: u32 = 0x100;
    pub const HASPHYSICAL: u32 = 0x200;
    pub const IS_OTHERSPACE: u32 = 0x400;
    pub const HAS_NEARPOINTERS: u32 = 0x800;
    pub const ALLOWS_WRAPPED_RANGE: u32 = 0x1000;
    pub const ADDRESSABLE_ALL: u32 = 0x2000;
    pub const ADDRESSABLE_NONE: u32 = 0x4000;

    pub fn new(
        kind: SpaceKind,
        tp: SpaceType,
        nm: &str,
        big_end: bool,
        size: u32,
        ws: u32,
        ind: i32,
        fl: u32,
        dl: i32,
        dead: i32,
    ) -> AddrSpace {
        let mut flags = fl & AddrSpace::HASPHYSICAL;
        if big_end {
            flags |= AddrSpace::BIG_ENDIAN;
        }
        flags |= AddrSpace::HERITAGED | AddrSpace::DOES_DEADCODE;
        let spc = AddrSpace {
            kind,
            space_type: tp,
            flags: AtomicU32::new(flags),
            shortcut: AtomicU8::new(b' '),
            highest: AtomicU64::new(0),
            pointer_lower_bound: AtomicU64::new(0),
            pointer_upper_bound: AtomicU64::new(0),
            name: nm.to_string(),
            address_size: AtomicU32::new(size),
            wordsize: ws,
            minimum_pointer_size: AtomicI32::new(0),
            index: ind,
            delay: dl,
            deadcodedelay: AtomicI32::new(dead),
        };
        spc.calc_scale_mask();
        let extra = if spc.delay == 0 {
            AddrSpace::ADDRESSABLE_NONE
        } else {
            AddrSpace::ADDRESSABLE_ALL
        };
        spc.set_flags(extra);
        spc
    }

    fn new_for_decode(kind: SpaceKind, tp: SpaceType) -> AddrSpace {
        AddrSpace {
            kind,
            space_type: tp,
            flags: AtomicU32::new(AddrSpace::HERITAGED | AddrSpace::DOES_DEADCODE),
            shortcut: AtomicU8::new(b' '),
            highest: AtomicU64::new(0),
            pointer_lower_bound: AtomicU64::new(0),
            pointer_upper_bound: AtomicU64::new(0),
            name: String::new(),
            address_size: AtomicU32::new(0),
            wordsize: 1,
            minimum_pointer_size: AtomicI32::new(0),
            index: 0,
            delay: 0,
            deadcodedelay: AtomicI32::new(0),
        }
    }

    pub fn new_processor(
        nm: &str,
        big_end: bool,
        size: u32,
        ws: u32,
        ind: i32,
        fl: u32,
        dl: i32,
        dead: i32,
    ) -> AddrSpace {
        AddrSpace::new(
            SpaceKind::Base,
            SpaceType::Processor,
            nm,
            big_end,
            size,
            ws,
            ind,
            fl,
            dl,
            dead,
        )
    }

    pub fn new_constant() -> AddrSpace {
        let spc = AddrSpace::new(
            SpaceKind::Constant,
            SpaceType::Constant,
            CONSTANT_SPACE_NAME,
            false,
            8,
            1,
            CONSTANT_SPACE_INDEX,
            0,
            0,
            0,
        );
        spc.clear_flags(AddrSpace::HERITAGED | AddrSpace::DOES_DEADCODE | AddrSpace::BIG_ENDIAN);
        spc
    }

    pub fn new_other(_ind: i32) -> AddrSpace {
        let spc = AddrSpace::new(
            SpaceKind::Other,
            SpaceType::Processor,
            OTHER_SPACE_NAME,
            false,
            8,
            1,
            OTHER_SPACE_INDEX,
            0,
            0,
            0,
        );
        spc.clear_flags(AddrSpace::HERITAGED | AddrSpace::DOES_DEADCODE);
        spc.set_flags(AddrSpace::IS_OTHERSPACE);
        spc
    }

    pub fn new_unique(big_end: bool, ind: i32, fl: u32) -> AddrSpace {
        let spc = AddrSpace::new(
            SpaceKind::Unique,
            SpaceType::Internal,
            UNIQUE_SPACE_NAME,
            big_end,
            UNIQUE_SPACE_SIZE,
            1,
            ind,
            fl,
            0,
            0,
        );
        spc.set_flags(AddrSpace::HASPHYSICAL);
        spc
    }

    pub fn new_join(manager: &AddrSpaceManager, big_end: bool, ind: i32) -> AddrSpace {
        let table = manager.get_join_table().clone();
        let spc = AddrSpace::new(
            SpaceKind::Join { table },
            SpaceType::Join,
            JOIN_SPACE_NAME,
            big_end,
            4,
            1,
            ind,
            0,
            0,
            0,
        );
        spc.clear_flags(AddrSpace::HERITAGED);
        spc
    }

    pub fn new_spacebase(
        nm: &str,
        big_end: bool,
        ind: i32,
        sz: u32,
        base: &SpaceRef,
        dl: i32,
        is_formal: bool,
    ) -> AddrSpace {
        let register = RwLock::new(SpacebaseRegister {
            is_negative_stack: true,
            ..SpacebaseRegister::default()
        });
        let spc = AddrSpace::new(
            SpaceKind::Spacebase {
                contain: Some(base.clone()),
                register,
            },
            SpaceType::Spacebase,
            nm,
            big_end,
            sz,
            base.get_word_size(),
            ind,
            0,
            dl,
            dl,
        );
        spc.set_flags(AddrSpace::ALLOWS_WRAPPED_RANGE);
        if is_formal {
            spc.set_flags(AddrSpace::FORMAL_STACKSPACE);
        }
        spc
    }

    pub fn new_fspec(ind: i32) -> AddrSpace {
        let spc = AddrSpace::new(
            SpaceKind::Fspec,
            SpaceType::Fspec,
            FSPEC_SPACE_NAME,
            false,
            8,
            1,
            ind,
            0,
            1,
            1,
        );
        spc.clear_flags(AddrSpace::HERITAGED | AddrSpace::DOES_DEADCODE | AddrSpace::BIG_ENDIAN);
        spc
    }

    pub fn new_iop(ind: i32) -> AddrSpace {
        let spc = AddrSpace::new(
            SpaceKind::Iop,
            SpaceType::Iop,
            IOP_SPACE_NAME,
            false,
            8,
            1,
            ind,
            0,
            1,
            1,
        );
        spc.clear_flags(AddrSpace::HERITAGED | AddrSpace::DOES_DEADCODE | AddrSpace::BIG_ENDIAN);
        spc
    }

    pub fn maximal() -> SpaceRef {
        static MAXIMAL: OnceLock<SpaceRef> = OnceLock::new();
        MAXIMAL
            .get_or_init(|| {
                let mut spc = AddrSpace::new_for_decode(SpaceKind::Maximal, SpaceType::Processor);
                spc.index = i32::MAX;
                Arc::new(spc)
            })
            .clone()
    }

    pub fn is_maximal(&self) -> bool {
        matches!(self.kind, SpaceKind::Maximal)
    }

    pub fn decode_processor(decoder: &mut dyn Decoder) -> Result<AddrSpace> {
        let mut spc = AddrSpace::new_for_decode(SpaceKind::Base, SpaceType::Processor);
        spc.decode_default(decoder)?;
        Ok(spc)
    }

    pub fn decode_other(decoder: &mut dyn Decoder) -> Result<AddrSpace> {
        let mut spc = AddrSpace::new_for_decode(SpaceKind::Other, SpaceType::Processor);
        spc.clear_flags(AddrSpace::HERITAGED | AddrSpace::DOES_DEADCODE);
        spc.set_flags(AddrSpace::IS_OTHERSPACE);
        spc.decode_default(decoder)?;
        Ok(spc)
    }

    pub fn decode_unique(decoder: &mut dyn Decoder) -> Result<AddrSpace> {
        let mut spc = AddrSpace::new_for_decode(SpaceKind::Unique, SpaceType::Internal);
        spc.set_flags(AddrSpace::HASPHYSICAL);
        spc.decode_default(decoder)?;
        Ok(spc)
    }

    pub fn decode_overlay(decoder: &mut dyn Decoder) -> Result<AddrSpace> {
        let elem_id = decoder.open_element_expect(ELEM_SPACE_OVERLAY)?;
        let name = decoder.read_string_attr(ATTRIB_NAME)?;
        let index = decoder.read_signed_integer_attr(ATTRIB_INDEX)? as i32;
        let base_space = decoder.read_space_attr(ATTRIB_BASE)?;
        decoder.close_element(elem_id)?;
        let mut spc = AddrSpace::new_for_decode(
            SpaceKind::Overlay {
                base_space: base_space.clone(),
            },
            SpaceType::Processor,
        );
        spc.set_flags(AddrSpace::OVERLAY);
        spc.name = name;
        spc.index = index;
        spc.address_size = AtomicU32::new(base_space.get_addr_size());
        spc.wordsize = base_space.get_word_size();
        spc.delay = base_space.get_delay();
        spc.deadcodedelay = AtomicI32::new(base_space.get_deadcode_delay());
        spc.calc_scale_mask();
        if base_space.is_big_endian() {
            spc.set_flags(AddrSpace::BIG_ENDIAN);
        }
        if base_space.has_physical() {
            spc.set_flags(AddrSpace::HASPHYSICAL);
        }
        Ok(spc)
    }

    pub fn decode_spacebase(decoder: &mut dyn Decoder) -> Result<AddrSpace> {
        let elem_id = decoder.open_element_expect(ELEM_SPACE_BASE)?;
        let register = RwLock::new(SpacebaseRegister {
            is_negative_stack: true,
            ..SpacebaseRegister::default()
        });
        let mut spc = AddrSpace::new_for_decode(
            SpaceKind::Spacebase {
                contain: None,
                register,
            },
            SpaceType::Spacebase,
        );
        spc.set_flags(AddrSpace::PROGRAMSPECIFIC | AddrSpace::ALLOWS_WRAPPED_RANGE);
        spc.decode_basic_attributes(decoder)?;
        let contain = decoder.read_space_attr(crate::translate::ATTRIB_CONTAIN)?;
        if let SpaceKind::Spacebase { contain: slot, .. } = &mut spc.kind {
            *slot = Some(contain);
        }
        decoder.close_element(elem_id)?;
        Ok(spc)
    }

    fn decode_default(&mut self, decoder: &mut dyn Decoder) -> Result<()> {
        let elem_id = decoder.open_element()?;
        self.decode_basic_attributes(decoder)?;
        decoder.close_element(elem_id)
    }

    fn decode_basic_attributes(&mut self, decoder: &mut dyn Decoder) -> Result<()> {
        let mut deadcodedelay = -1;
        loop {
            let attrib_id = decoder.get_next_attribute_id()?;
            if attrib_id == 0 {
                break;
            }
            if attrib_id == ATTRIB_NAME {
                self.name = decoder.read_string()?;
            }
            if attrib_id == ATTRIB_INDEX {
                self.index = decoder.read_signed_integer()? as i32;
            } else if attrib_id == ATTRIB_SIZE {
                self.address_size
                    .store(decoder.read_signed_integer()? as u32, Ordering::Relaxed);
            } else if attrib_id == ATTRIB_WORDSIZE {
                self.wordsize = decoder.read_unsigned_integer()? as u32;
            } else if attrib_id == ATTRIB_BIGENDIAN {
                if decoder.read_bool()? {
                    self.set_flags(AddrSpace::BIG_ENDIAN);
                }
            } else if attrib_id == ATTRIB_DELAY {
                self.delay = decoder.read_signed_integer()? as i32;
            } else if attrib_id == ATTRIB_DEADCODEDELAY {
                deadcodedelay = decoder.read_signed_integer()? as i32;
            } else if attrib_id == ATTRIB_PHYSICAL && decoder.read_bool()? {
                self.set_flags(AddrSpace::HASPHYSICAL);
            }
        }
        if deadcodedelay == -1 {
            deadcodedelay = self.delay;
        }
        self.deadcodedelay.store(deadcodedelay, Ordering::Relaxed);
        self.calc_scale_mask();
        Ok(())
    }

    pub(crate) fn calc_scale_mask(&self) {
        let address_size = self.get_addr_size();
        let wordsize = self.wordsize as u64;
        let mut highest = calc_mask(address_size as i32);
        highest = highest.wrapping_mul(wordsize).wrapping_add(wordsize.wrapping_sub(1));
        self.highest.store(highest, Ordering::Relaxed);
        let buffer_size: u64 = if address_size < 3 { 0x100 } else { 0x1000 };
        self.pointer_lower_bound.store(buffer_size, Ordering::Relaxed);
        self.pointer_upper_bound
            .store(highest.wrapping_sub(buffer_size), Ordering::Relaxed);
    }

    pub fn set_flags(&self, fl: u32) {
        self.flags.fetch_or(fl, Ordering::Relaxed);
    }

    pub fn clear_flags(&self, fl: u32) {
        self.flags.fetch_and(!fl, Ordering::Relaxed);
    }

    pub fn get_flags(&self) -> u32 {
        self.flags.load(Ordering::Relaxed)
    }

    pub fn truncate_space(&self, newsize: u32) {
        self.set_flags(AddrSpace::TRUNCATED);
        self.address_size.store(newsize, Ordering::Relaxed);
        self.minimum_pointer_size.store(newsize as i32, Ordering::Relaxed);
        self.calc_scale_mask();
    }

    pub(crate) fn set_shortcut(&self, shortcut: u8) {
        self.shortcut.store(shortcut, Ordering::Relaxed);
    }

    pub(crate) fn set_minimum_ptr_size(&self, size: i32) {
        self.minimum_pointer_size.store(size, Ordering::Relaxed);
    }

    pub(crate) fn set_deadcode_delay(&self, delay: i32) {
        self.deadcodedelay.store(delay, Ordering::Relaxed);
    }

    pub(crate) fn set_pointer_bounds(&self, lower: u64, upper: u64) {
        self.pointer_lower_bound.store(lower, Ordering::Relaxed);
        self.pointer_upper_bound.store(upper, Ordering::Relaxed);
    }

    pub fn get_kind(&self) -> &SpaceKind {
        &self.kind
    }

    pub fn get_name(&self) -> &str {
        &self.name
    }

    pub fn get_type(&self) -> SpaceType {
        self.space_type
    }

    pub fn get_delay(&self) -> i32 {
        self.delay
    }

    pub fn get_deadcode_delay(&self) -> i32 {
        self.deadcodedelay.load(Ordering::Relaxed)
    }

    pub fn get_index(&self) -> i32 {
        self.index
    }

    pub fn get_word_size(&self) -> u32 {
        self.wordsize
    }

    pub fn get_addr_size(&self) -> u32 {
        self.address_size.load(Ordering::Relaxed)
    }

    pub fn get_highest(&self) -> u64 {
        self.highest.load(Ordering::Relaxed)
    }

    pub fn get_pointer_lower_bound(&self) -> u64 {
        self.pointer_lower_bound.load(Ordering::Relaxed)
    }

    pub fn get_pointer_upper_bound(&self) -> u64 {
        self.pointer_upper_bound.load(Ordering::Relaxed)
    }

    pub fn get_minimum_ptr_size(&self) -> i32 {
        self.minimum_pointer_size.load(Ordering::Relaxed)
    }

    pub fn wrap_offset(&self, off: u64) -> u64 {
        let highest = self.get_highest();
        if off <= highest {
            return off;
        }
        let modulus = highest.wrapping_add(1) as i64;
        if modulus == 0 {
            return off;
        }
        let mut res = (off as i64).wrapping_rem(modulus);
        if res < 0 {
            res = res.wrapping_add(modulus);
        }
        res as u64
    }

    pub fn get_shortcut(&self) -> char {
        self.shortcut.load(Ordering::Relaxed) as char
    }

    pub fn get_shortcut_byte(&self) -> u8 {
        self.shortcut.load(Ordering::Relaxed)
    }

    fn has_flag(&self, fl: u32) -> bool {
        (self.get_flags() & fl) != 0
    }

    pub fn is_heritaged(&self) -> bool {
        self.has_flag(AddrSpace::HERITAGED)
    }

    pub fn does_deadcode(&self) -> bool {
        self.has_flag(AddrSpace::DOES_DEADCODE)
    }

    pub fn has_physical(&self) -> bool {
        self.has_flag(AddrSpace::HASPHYSICAL)
    }

    pub fn is_big_endian(&self) -> bool {
        self.has_flag(AddrSpace::BIG_ENDIAN)
    }

    pub fn is_reverse_justified(&self) -> bool {
        self.has_flag(AddrSpace::REVERSE_JUSTIFICATION)
    }

    pub fn is_formal_stack_space(&self) -> bool {
        self.has_flag(AddrSpace::FORMAL_STACKSPACE)
    }

    pub fn is_overlay(&self) -> bool {
        self.has_flag(AddrSpace::OVERLAY)
    }

    pub fn is_overlay_base(&self) -> bool {
        self.has_flag(AddrSpace::OVERLAYBASE)
    }

    pub fn is_other_space(&self) -> bool {
        self.has_flag(AddrSpace::IS_OTHERSPACE)
    }

    pub fn is_truncated(&self) -> bool {
        self.has_flag(AddrSpace::TRUNCATED)
    }

    pub fn no_high_ptr_possible(&self) -> bool {
        self.has_flag(AddrSpace::ADDRESSABLE_NONE)
    }

    pub fn has_near_pointers(&self) -> bool {
        self.has_flag(AddrSpace::HAS_NEARPOINTERS)
    }

    pub fn allows_wrapped_range(&self) -> bool {
        self.has_flag(AddrSpace::ALLOWS_WRAPPED_RANGE)
    }

    pub fn print_offset(&self, out: &mut String, offset: u64) {
        let _ = write!(out, "0x{offset:x}");
    }

    pub fn join_table(&self) -> Option<&Arc<JoinTable>> {
        match &self.kind {
            SpaceKind::Join { table } => Some(table),
            _ => None,
        }
    }

    pub fn find_join(&self, offset: u64) -> Result<Option<Arc<JoinRecord>>> {
        if self.space_type != SpaceType::Join {
            return Ok(None);
        }
        match self.join_table() {
            Some(table) => Ok(Some(table.find_join(offset)?)),
            None => Ok(None),
        }
    }

    fn required_join(&self, offset: u64) -> Result<Arc<JoinRecord>> {
        match self.join_table() {
            Some(table) => table.find_join(offset),
            None => Err(Error::Lowlevel("Unlinked join address".to_string())),
        }
    }

    pub fn num_spacebase(&self) -> i32 {
        match &self.kind {
            SpaceKind::Spacebase { register, .. }
                if register
                    .read()
                    .expect("spacebase register lock poisoned")
                    .hasbaseregister =>
            {
                1
            }
            _ => 0,
        }
    }

    pub fn get_spacebase(&self, index: i32) -> Result<VarnodeData> {
        match &self.kind {
            SpaceKind::Spacebase { register, .. } => {
                let state = register.read().expect("spacebase register lock poisoned");
                if !state.hasbaseregister || index != 0 {
                    return Err(Error::Lowlevel(format!(
                        "No base register specified for space: {}",
                        self.name
                    )));
                }
                Ok(state.baseloc.clone())
            }
            _ => Err(Error::Lowlevel(format!(
                "{} space is not virtual and has no associated base register",
                self.name
            ))),
        }
    }

    pub fn get_spacebase_full(&self, index: i32) -> Result<VarnodeData> {
        match &self.kind {
            SpaceKind::Spacebase { register, .. } => {
                let state = register.read().expect("spacebase register lock poisoned");
                if !state.hasbaseregister || index != 0 {
                    return Err(Error::Lowlevel(format!(
                        "No base register specified for space: {}",
                        self.name
                    )));
                }
                Ok(state.base_orig.clone())
            }
            _ => Err(Error::Lowlevel(format!("{} has no truncated registers", self.name))),
        }
    }

    pub fn stack_grows_negative(&self) -> bool {
        match &self.kind {
            SpaceKind::Spacebase { register, .. } => {
                register
                    .read()
                    .expect("spacebase register lock poisoned")
                    .is_negative_stack
            }
            _ => true,
        }
    }

    pub fn get_contain(&self) -> Option<SpaceRef> {
        match &self.kind {
            SpaceKind::Spacebase { contain, .. } => contain.clone(),
            SpaceKind::Overlay { base_space } => Some(base_space.clone()),
            _ => None,
        }
    }

    pub(crate) fn set_base_register(&self, data: &VarnodeData, trunc_size: i32, stack_growth: bool) -> Result<()> {
        let SpaceKind::Spacebase { register, .. } = &self.kind else {
            return Err(Error::Lowlevel(format!("Space {} is not a spacebase space", self.name)));
        };
        let mut state = register.write().expect("spacebase register lock poisoned");
        if state.hasbaseregister && (state.baseloc != *data || state.is_negative_stack != stack_growth) {
            return Err(Error::Lowlevel(format!(
                "Attempt to assign more than one base register to space: {}",
                self.name
            )));
        }
        state.hasbaseregister = true;
        state.is_negative_stack = stack_growth;
        state.base_orig = data.clone();
        state.baseloc = data.clone();
        if trunc_size as u32 != state.baseloc.size {
            if state.baseloc.space.as_ref().is_some_and(|spc| spc.is_big_endian()) {
                state.baseloc.offset = state
                    .baseloc
                    .offset
                    .wrapping_add((state.baseloc.size as u64).wrapping_sub(trunc_size as u64));
            }
            state.baseloc.size = trunc_size as u32;
        }
        Ok(())
    }

    pub fn overlap_join(
        &self,
        offset: u64,
        size: i32,
        point_space: &SpaceRef,
        point_off: u64,
        point_skip: i32,
    ) -> Result<i32> {
        match &self.kind {
            SpaceKind::Constant => Ok(-1),
            SpaceKind::Join { table } => {
                let mut point_space = point_space.clone();
                let mut point_offset = point_off;
                if self.index == point_space.index {
                    let piece_record = table.find_join(point_offset)?;
                    let (addr, _pos) =
                        piece_record.get_equivalent_address(point_offset.wrapping_add(point_skip as i64 as u64));
                    match addr.get_space() {
                        Some(spc) => point_space = spc.clone(),
                        None => return Ok(-1),
                    }
                    point_offset = addr.get_offset();
                } else {
                    if point_space.get_type() == SpaceType::Constant {
                        return Ok(-1);
                    }
                    point_offset = point_space.wrap_offset(point_offset.wrapping_add(point_skip as i64 as u64));
                }
                let join_record = table.find_join(offset)?;
                let num = join_record.num_pieces();
                let (start_piece, end_piece, dir) = if self.is_big_endian() {
                    (0, num, 1)
                } else {
                    (num - 1, -1, -1)
                };
                let mut bytes_accum: i32 = 0;
                let mut slot = start_piece;
                while slot != end_piece {
                    let v_data = join_record.get_piece(slot);
                    let same_space = v_data.space.as_ref().is_some_and(|spc| spc.index == point_space.index);
                    if same_space
                        && point_offset >= v_data.offset
                        && point_offset <= v_data.offset.wrapping_add((v_data.size as u64).wrapping_sub(1))
                    {
                        let res = (point_offset.wrapping_sub(v_data.offset) as i32).wrapping_add(bytes_accum);
                        if res >= size {
                            return Ok(-1);
                        }
                        return Ok(res);
                    }
                    bytes_accum = bytes_accum.wrapping_add(v_data.size as i32);
                    slot += dir;
                }
                Ok(-1)
            }
            _ => {
                if self.index != point_space.index {
                    return Ok(-1);
                }
                let dist = self.wrap_offset(point_off.wrapping_add(point_skip as i64 as u64).wrapping_sub(offset));
                if dist >= size as i64 as u64 {
                    return Ok(-1);
                }
                Ok(dist as i32)
            }
        }
    }

    pub fn encode_attributes(&self, encoder: &mut dyn Encoder, offset: u64) -> Result<()> {
        if let SpaceKind::Join { .. } = &self.kind {
            let rec = self.required_join(offset)?;
            encoder.write_space(ATTRIB_SPACE, self);
            let num = rec.num_pieces();
            if num > JOIN_MAX_PIECES {
                return Err(Error::Lowlevel(
                    "Exceeded maximum pieces in one join address".to_string(),
                ));
            }
            for slot in 0..num {
                let vdata = rec.get_piece(slot);
                let space_name = vdata.space.as_ref().map_or("", |spc| spc.get_name());
                let text = format!("{}:0x{:x}:{}", space_name, vdata.offset, vdata.size);
                encoder.write_string_indexed(ATTRIB_PIECE, slot as u32, &text);
            }
            if num == 1 {
                encoder.write_unsigned_integer(ATTRIB_LOGICALSIZE, rec.get_unified().size as u64);
            }
            return Ok(());
        }
        encoder.write_space(ATTRIB_SPACE, self);
        encoder.write_unsigned_integer(ATTRIB_OFFSET, offset);
        Ok(())
    }

    pub fn encode_attributes_size(&self, encoder: &mut dyn Encoder, offset: u64, size: i32) -> Result<()> {
        if let SpaceKind::Join { .. } = &self.kind {
            return self.encode_attributes(encoder, offset);
        }
        encoder.write_space(ATTRIB_SPACE, self);
        encoder.write_unsigned_integer(ATTRIB_OFFSET, offset);
        encoder.write_signed_integer(ATTRIB_SIZE, size as i64);
        Ok(())
    }

    pub fn decode_attributes(&self, decoder: &mut dyn Decoder, size: &mut u32) -> Result<u64> {
        if let SpaceKind::Join { table } = &self.kind {
            return self.decode_join_attributes(table, decoder, size);
        }
        let mut offset = 0;
        let mut foundoffset = false;
        loop {
            let attrib_id = decoder.get_next_attribute_id()?;
            if attrib_id == 0 {
                break;
            }
            if attrib_id == ATTRIB_OFFSET {
                foundoffset = true;
                offset = decoder.read_unsigned_integer()?;
            } else if attrib_id == ATTRIB_SIZE {
                *size = decoder.read_signed_integer()? as u32;
            }
        }
        if !foundoffset {
            return Err(Error::Lowlevel("Address is missing offset".to_string()));
        }
        Ok(offset)
    }

    fn decode_join_attributes(&self, table: &Arc<JoinTable>, decoder: &mut dyn Decoder, size: &mut u32) -> Result<u64> {
        let mut pieces: Vec<VarnodeData> = Vec::new();
        let mut logicalsize: u32 = 0;
        loop {
            let mut attrib_id = decoder.get_next_attribute_id()?;
            if attrib_id == 0 {
                break;
            }
            if attrib_id == ATTRIB_LOGICALSIZE {
                logicalsize = decoder.read_unsigned_integer()? as u32;
                continue;
            } else if attrib_id == ATTRIB_UNKNOWN {
                attrib_id = decoder.get_indexed_attribute_id(ATTRIB_PIECE)?;
            }
            if attrib_id < ATTRIB_PIECE.get_id() {
                continue;
            }
            let pos = attrib_id.wrapping_sub(ATTRIB_PIECE.get_id()) as i32;
            if pos > JOIN_MAX_PIECES {
                continue;
            }
            while pieces.len() as i32 <= pos {
                pieces.push(VarnodeData::default());
            }
            let attr_val = decoder.read_string()?;
            let vdat = match attr_val.find(':') {
                None => decoder.get_register(&attr_val)?,
                Some(offpos) => {
                    let Some(szpos) = attr_val[offpos + 1..].find(':').map(|found| found + offpos + 1) else {
                        return Err(Error::Lowlevel("join address piece attribute is malformed".to_string()));
                    };
                    let spcname = &attr_val[..offpos];
                    let space = decoder.manager()?.get_space_by_name(spcname);
                    let offset_text = &attr_val[offpos + 1..];
                    let size_text = &attr_val[szpos + 1..];
                    let previous = &pieces[pos as usize];
                    VarnodeData {
                        space,
                        offset: istream::read_u64(offset_text, Basefield::Auto, previous.offset),
                        size: istream::read_u32(size_text, Basefield::Auto, previous.size),
                    }
                }
            };
            pieces[pos as usize] = vdat;
        }
        let rec = table.find_add_join(&pieces, logicalsize)?;
        *size = rec.get_unified().size;
        Ok(rec.get_unified().offset)
    }

    pub fn print_raw(&self, out: &mut String, offset: u64) {
        match &self.kind {
            SpaceKind::Constant | SpaceKind::Other | SpaceKind::Fspec | SpaceKind::Iop => {
                let _ = write!(out, "0x{offset:x}");
            }
            SpaceKind::Join { table } => {
                let Ok(rec) = table.find_join(offset) else {
                    return;
                };
                let num = rec.num_pieces();
                out.push('{');
                for slot in 0..num {
                    let vdat = rec.get_piece(slot);
                    if slot != 0 {
                        out.push(',');
                    }
                    if let Some(spc) = &vdat.space {
                        spc.print_raw(out, vdat.offset);
                    }
                }
                if num == 1 {
                    let vdat = rec.get_piece(0);
                    let hex_mode = vdat
                        .space
                        .as_ref()
                        .is_none_or(|spc| spc.print_raw_leaves_hex(vdat.offset));
                    let size = rec.get_unified().size as i32;
                    if hex_mode {
                        let _ = write!(out, ":{size:x}");
                    } else {
                        let _ = write!(out, ":{size}");
                    }
                }
                out.push('}');
            }
            _ => {
                let mut sz = self.get_addr_size() as i32;
                if sz > 4 {
                    if (offset >> 32) == 0 {
                        sz = 4;
                    } else if (offset >> 48) == 0 {
                        sz = 6;
                    }
                }
                let width = (2 * sz).max(0) as usize;
                let value = AddrSpace::byte_to_address(offset, self.wordsize);
                let _ = write!(out, "0x{value:0width$x}");
                if self.wordsize > 1 {
                    let cut = (offset % self.wordsize as u64) as i32;
                    if cut != 0 {
                        let _ = write!(out, "+{cut}");
                    }
                }
            }
        }
    }

    pub fn print_raw_leaves_hex(&self, offset: u64) -> bool {
        match &self.kind {
            SpaceKind::Join { table } => match table.find_join(offset) {
                Ok(rec) if rec.num_pieces() > 0 => {
                    let vdat = rec.get_piece(rec.num_pieces() - 1);
                    vdat.space
                        .as_ref()
                        .is_none_or(|spc| spc.print_raw_leaves_hex(vdat.offset))
                }
                _ => true,
            },
            SpaceKind::Constant | SpaceKind::Other | SpaceKind::Fspec | SpaceKind::Iop => true,
            _ => self.wordsize <= 1 || offset.is_multiple_of(self.wordsize as u64),
        }
    }

    pub fn print_raw_string(&self, offset: u64) -> String {
        let mut out = String::new();
        self.print_raw(&mut out, offset);
        out
    }

    pub fn read(&self, text: &str, manager: &AddrSpaceManager, trans: Option<&dyn Translate>) -> Result<(u64, i32)> {
        if let SpaceKind::Join { table } = &self.kind {
            return self.read_join(table, text, manager, trans);
        }
        let bytes = text.as_bytes();
        let append = text.find([':', '+']);
        let front = match append {
            None => text,
            Some(pos) => &text[..pos],
        };
        let register = match trans {
            Some(translate) => translate.get_register(front),
            None => Err(Error::Lowlevel(format!("unknown register {front}"))),
        };
        let mut offset;
        let mut size;
        match register {
            Ok(point) => {
                offset = point.offset;
                size = point.size as i32;
            }
            Err(err) if err.is_lowlevel() => {
                let (value, end) = istream::strtoul(bytes, 0);
                offset = AddrSpace::address_to_byte(value, self.wordsize);
                size = manager.get_default_size();
                if end == bytes.len() {
                    return Ok((offset, size));
                }
            }
            Err(err) => return Err(err),
        }
        if let Some(pos) = append {
            let (expsize, adjusted) = get_offset_size(&bytes[pos..], offset);
            offset = adjusted;
            if expsize != -1 {
                size = expsize;
                return Ok((offset, size));
            }
        }
        Ok((offset, size))
    }

    fn read_join(
        &self,
        table: &Arc<JoinTable>,
        text: &str,
        manager: &AddrSpaceManager,
        trans: Option<&dyn Translate>,
    ) -> Result<(u64, i32)> {
        let bytes = text.as_bytes();
        let mut pieces: Vec<VarnodeData> = Vec::new();
        let mut szsum: i32 = 0;
        let mut pos = 0;
        while pos < bytes.len() {
            let start = pos;
            while pos < bytes.len() && bytes[pos] != b',' {
                pos += 1;
            }
            let token = &text[start..pos];
            pos += 1;
            let register = match trans {
                Some(translate) => translate.get_register(token),
                None => Err(Error::Lowlevel(format!("unknown register {token}"))),
            };
            let piece = match register {
                Ok(point) => point,
                Err(err) if err.is_lowlevel() => {
                    let try_shortcut = token.chars().next().unwrap_or('\0');
                    let Some(spc) = manager.get_space_by_shortcut(try_shortcut) else {
                        return Err(Error::Lowlevel("Could not parse join string".to_string()));
                    };
                    let rest = token.get(try_shortcut.len_utf8()..).unwrap_or("");
                    let (offset, subsize) = spc.read(rest, manager, trans)?;
                    VarnodeData {
                        space: Some(spc.clone()),
                        offset,
                        size: subsize as u32,
                    }
                }
                Err(err) => return Err(err),
            };
            szsum = szsum.wrapping_add(piece.size as i32);
            pieces.push(piece);
        }
        let rec = table.find_add_join(&pieces, 0)?;
        Ok((rec.get_unified().offset, szsum))
    }

    pub fn address_to_byte(val: u64, ws: u32) -> u64 {
        val.wrapping_mul(ws as u64)
    }

    pub fn byte_to_address(val: u64, ws: u32) -> u64 {
        val / ws as u64
    }

    pub fn address_to_byte_int(val: i64, ws: u32) -> i64 {
        val.wrapping_mul(ws as i64)
    }

    pub fn byte_to_address_int(val: i64, ws: u32) -> i64 {
        val / ws as i64
    }

    pub fn compare_by_index(first: &AddrSpace, second: &AddrSpace) -> bool {
        first.index < second.index
    }
}

fn get_offset_size(text: &[u8], offset: u64) -> (i32, u64) {
    let mut size: i32 = -1;
    let mut val: u32 = 0;
    if text.first() == Some(&b':') {
        let (parsed, end) = istream::strtoul(&text[1..], 0);
        size = parsed as i32;
        let end_index = end + 1;
        if text.get(end_index) == Some(&b'+') {
            val = istream::strtoul(&text[end_index + 1..], 0).0 as u32;
        }
    }
    if text.first() == Some(&b'+') {
        val = istream::strtoul(&text[1..], 0).0 as u32;
    }
    (size, offset.wrapping_add(val as u64))
}

pub fn same_space(first: &Option<SpaceRef>, second: &Option<SpaceRef>) -> bool {
    match (first, second) {
        (None, None) => true,
        (Some(left), Some(right)) => left.index == right.index,
        _ => false,
    }
}
