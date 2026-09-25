use std::cmp::Ordering;
use std::collections::BTreeSet;
use std::fmt;
use std::fmt::Write as _;
use std::hash::{Hash, Hasher};
use std::ops::Bound;

use crate::error::{Error, Result};
use crate::marshal::{ATTRIB_NAME, ATTRIB_SPACE, AttributeId, Decoder, ElementId, Encoder};
use crate::pcoderaw::VarnodeData;
use crate::space::{AddrSpace, SpaceRef, SpaceType};
use crate::translate::{AddrSpaceManager, Translate};

pub const ATTRIB_FIRST: AttributeId = AttributeId::new("first", 27);
pub const ATTRIB_LAST: AttributeId = AttributeId::new("last", 28);
pub const ATTRIB_UNIQ: AttributeId = AttributeId::new("uniq", 29);

pub const ELEM_ADDR: ElementId = ElementId::new("addr", 11);
pub const ELEM_RANGE: ElementId = ElementId::new("range", 12);
pub const ELEM_RANGELIST: ElementId = ElementId::new("rangelist", 13);
pub const ELEM_REGISTER: ElementId = ElementId::new("register", 14);
pub const ELEM_SEQNUM: ElementId = ElementId::new("seqnum", 15);
pub const ELEM_VARNODE: ElementId = ElementId::new("varnode", 16);

pub const HOST_ENDIAN: i32 = 0;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum MachExtreme {
    Minimal,
    Maximal,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct AddressKey {
    space_index: i64,
    offset: u64,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct SeqKey {
    pc: AddressKey,
    uniq: u32,
}

impl SeqKey {
    pub fn new(pc: &Address, uniq: u32) -> SeqKey {
        SeqKey {
            pc: pc.ordering_key(),
            uniq,
        }
    }
}

#[derive(Clone, Debug, Default)]
pub struct Address {
    space: Option<SpaceRef>,
    offset: u64,
}

fn space_index(space: &Option<SpaceRef>) -> Option<i32> {
    space.as_ref().map(|spc| spc.get_index())
}

impl Address {
    pub fn new(space: SpaceRef, offset: u64) -> Address {
        Address {
            space: Some(space),
            offset,
        }
    }

    pub fn from_parts(space: Option<SpaceRef>, offset: u64) -> Address {
        Address { space, offset }
    }

    pub fn invalid() -> Address {
        Address { space: None, offset: 0 }
    }

    pub fn extreme(ex: MachExtreme) -> Address {
        match ex {
            MachExtreme::Minimal => Address { space: None, offset: 0 },
            MachExtreme::Maximal => Address {
                space: Some(AddrSpace::maximal()),
                offset: u64::MAX,
            },
        }
    }

    pub fn is_invalid(&self) -> bool {
        self.space.is_none()
    }

    pub fn ordering_key(&self) -> AddressKey {
        AddressKey {
            space_index: self.space.as_ref().map_or(-1, |space| i64::from(space.get_index())),
            offset: self.offset,
        }
    }

    fn base(&self) -> &SpaceRef {
        self.space.as_ref().expect("operation on invalid address")
    }

    pub fn get_addr_size(&self) -> i32 {
        self.base().get_addr_size() as i32
    }

    pub fn is_big_endian(&self) -> bool {
        self.base().is_big_endian()
    }

    pub fn print_raw(&self, out: &mut String) {
        match &self.space {
            None => out.push_str("invalid_addr"),
            Some(spc) => spc.print_raw(out, self.offset),
        }
    }

    pub fn print_raw_leaves_hex(&self) -> Option<bool> {
        self.space.as_ref().map(|spc| spc.print_raw_leaves_hex(self.offset))
    }

    pub fn read(&mut self, text: &str, manager: &AddrSpaceManager, trans: Option<&dyn Translate>) -> Result<i32> {
        let (offset, size) = self.base().read(text, manager, trans)?;
        self.offset = offset;
        Ok(size)
    }

    pub fn get_space(&self) -> Option<&SpaceRef> {
        self.space.as_ref()
    }

    pub fn get_offset(&self) -> u64 {
        self.offset
    }

    pub fn get_shortcut(&self) -> char {
        self.base().get_shortcut()
    }

    pub fn add(&self, off: i64) -> Address {
        let base = self.base();
        Address {
            space: self.space.clone(),
            offset: base.wrap_offset(self.offset.wrapping_add(off as u64)),
        }
    }

    pub fn sub(&self, off: i64) -> Address {
        let base = self.base();
        Address {
            space: self.space.clone(),
            offset: base.wrap_offset(self.offset.wrapping_sub(off as u64)),
        }
    }

    pub fn is_valid_range(&self, size: u64) -> bool {
        size.wrapping_sub(1) <= self.base().get_highest().wrapping_sub(self.offset)
    }

    fn same_base(&self, op2: &Address) -> bool {
        space_index(&self.space) == space_index(&op2.space)
    }

    pub fn contained_by(&self, sz: i32, op2: &Address, sz2: i32) -> bool {
        if !self.same_base(op2) {
            return false;
        }
        if op2.offset > self.offset {
            return false;
        }
        let off1 = self.offset.wrapping_add((sz as i64 - 1) as u64);
        let off2 = op2.offset.wrapping_add((sz2 as i64 - 1) as u64);
        off2 >= off1
    }

    pub fn justified_contain(&self, sz: i32, op2: &Address, sz2: i32, forceleft: bool) -> i32 {
        if !self.same_base(op2) {
            return -1;
        }
        if op2.offset < self.offset {
            return -1;
        }
        let off1 = self.offset.wrapping_add((sz as i64 - 1) as u64);
        let off2 = op2.offset.wrapping_add((sz2 as i64 - 1) as u64);
        if off2 > off1 {
            return -1;
        }
        if self.base().is_big_endian() && !forceleft {
            return off1.wrapping_sub(off2) as i32;
        }
        op2.offset.wrapping_sub(self.offset) as i32
    }

    pub fn overlap(&self, skip: i32, op: &Address, size: i32) -> i32 {
        if !self.same_base(op) {
            return -1;
        }
        let base = self.base();
        if base.get_type() == SpaceType::Constant {
            return -1;
        }
        let dist = base.wrap_offset(self.offset.wrapping_add(skip as i64 as u64).wrapping_sub(op.offset));
        if dist >= size as i64 as u64 {
            return -1;
        }
        dist as i32
    }

    pub fn overlap_join(&self, skip: i32, op: &Address, size: i32) -> Result<i32> {
        op.base()
            .overlap_join(op.get_offset(), size, self.base(), self.offset, skip)
    }

    pub fn is_contiguous(&self, sz: i32, loaddr: &Address, losz: i32) -> bool {
        if !self.same_base(loaddr) {
            return false;
        }
        let base = self.base();
        if base.is_big_endian() {
            let nextoff = base.wrap_offset(self.offset.wrapping_add(sz as i64 as u64));
            if nextoff == loaddr.offset {
                return true;
            }
        } else {
            let nextoff = base.wrap_offset(loaddr.offset.wrapping_add(losz as i64 as u64));
            if nextoff == self.offset {
                return true;
            }
        }
        false
    }

    pub fn is_constant(&self) -> bool {
        self.base().get_type() == SpaceType::Constant
    }

    pub fn high_ptr_possible(&self, size: i32, manager: &AddrSpaceManager) -> bool {
        manager.high_ptr_possible(self, size)
    }

    pub fn renormalize(&mut self, size: i32) -> Result<()> {
        if self.base().get_type() == SpaceType::Join {
            let table = self.base().join_table().cloned();
            if let Some(table) = table {
                table.renormalize_join_address(self, size)?;
            }
        }
        Ok(())
    }

    pub fn is_join(&self) -> bool {
        self.base().get_type() == SpaceType::Join
    }

    pub fn encode(&self, encoder: &mut dyn Encoder) -> Result<()> {
        encoder.open_element(ELEM_ADDR);
        if let Some(base) = &self.space {
            base.encode_attributes(encoder, self.offset)?;
        }
        encoder.close_element(ELEM_ADDR);
        Ok(())
    }

    pub fn encode_size(&self, encoder: &mut dyn Encoder, size: i32) -> Result<()> {
        encoder.open_element(ELEM_ADDR);
        if let Some(base) = &self.space {
            base.encode_attributes_size(encoder, self.offset, size)?;
        }
        encoder.close_element(ELEM_ADDR);
        Ok(())
    }

    pub fn decode(decoder: &mut dyn Decoder) -> Result<Address> {
        let var = VarnodeData::decode(decoder)?;
        Ok(Address {
            space: var.space,
            offset: var.offset,
        })
    }

    pub fn decode_size(decoder: &mut dyn Decoder) -> Result<(Address, i32)> {
        let var = VarnodeData::decode(decoder)?;
        Ok((
            Address {
                space: var.space,
                offset: var.offset,
            },
            var.size as i32,
        ))
    }
}

impl PartialEq for Address {
    fn eq(&self, other: &Address) -> bool {
        self.same_base(other) && self.offset == other.offset
    }
}

impl Eq for Address {}

impl Hash for Address {
    fn hash<H: Hasher>(&self, state: &mut H) {
        space_index(&self.space).hash(state);
        self.offset.hash(state);
    }
}

impl PartialOrd for Address {
    fn partial_cmp(&self, other: &Address) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for Address {
    fn cmp(&self, other: &Address) -> Ordering {
        match (&self.space, &other.space) {
            (None, None) => self.offset.cmp(&other.offset),
            (None, Some(_)) => Ordering::Less,
            (Some(_), None) => Ordering::Greater,
            (Some(left), Some(right)) => left
                .get_index()
                .cmp(&right.get_index())
                .then(self.offset.cmp(&other.offset)),
        }
    }
}

impl std::ops::Add<i64> for &Address {
    type Output = Address;

    fn add(self, off: i64) -> Address {
        Address::add(self, off)
    }
}

impl std::ops::Sub<i64> for &Address {
    type Output = Address;

    fn sub(self, off: i64) -> Address {
        Address::sub(self, off)
    }
}

impl fmt::Display for Address {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut text = String::new();
        self.print_raw(&mut text);
        formatter.write_str(&text)
    }
}

#[derive(Clone, Debug, Default)]
pub struct SeqNum {
    pc: Address,
    uniq: u32,
    order: u32,
}

impl SeqNum {
    pub fn new(pc: Address, uniq: u32) -> SeqNum {
        SeqNum { pc, uniq, order: 0 }
    }

    pub fn extreme(ex: MachExtreme) -> SeqNum {
        let uniq = if ex == MachExtreme::Minimal { 0 } else { u32::MAX };
        SeqNum {
            pc: Address::extreme(ex),
            uniq,
            order: 0,
        }
    }

    pub fn ordering_key(&self) -> SeqKey {
        SeqKey {
            pc: self.pc.ordering_key(),
            uniq: self.uniq,
        }
    }

    pub fn get_addr(&self) -> &Address {
        &self.pc
    }

    pub fn get_time(&self) -> u32 {
        self.uniq
    }

    pub fn get_order(&self) -> u32 {
        self.order
    }

    pub fn set_order(&mut self, ord: u32) {
        self.order = ord;
    }

    pub fn encode(&self, encoder: &mut dyn Encoder) -> Result<()> {
        encoder.open_element(ELEM_SEQNUM);
        self.pc.base().encode_attributes(encoder, self.pc.get_offset())?;
        encoder.write_unsigned_integer(ATTRIB_UNIQ, self.uniq as u64);
        encoder.close_element(ELEM_SEQNUM);
        Ok(())
    }

    pub fn decode(decoder: &mut dyn Decoder) -> Result<SeqNum> {
        let mut uniq = u32::MAX;
        let elem_id = decoder.open_element_expect(ELEM_SEQNUM)?;
        let pc = Address::decode(decoder)?;
        loop {
            let attrib_id = decoder.get_next_attribute_id()?;
            if attrib_id == 0 {
                break;
            }
            if attrib_id == ATTRIB_UNIQ {
                uniq = decoder.read_unsigned_integer()? as u32;
                break;
            }
        }
        decoder.close_element(elem_id)?;
        Ok(SeqNum::new(pc, uniq))
    }
}

impl PartialEq for SeqNum {
    fn eq(&self, other: &SeqNum) -> bool {
        self.uniq == other.uniq
    }
}

impl Eq for SeqNum {}

impl PartialOrd for SeqNum {
    fn partial_cmp(&self, other: &SeqNum) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for SeqNum {
    fn cmp(&self, other: &SeqNum) -> Ordering {
        if self.pc == other.pc {
            return self.uniq.cmp(&other.uniq);
        }
        self.pc.cmp(&other.pc)
    }
}

impl fmt::Display for SeqNum {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.pc.print_raw_leaves_hex() == Some(true) {
            write!(formatter, "{}:{:x}", self.pc, self.uniq)
        } else {
            write!(formatter, "{}:{}", self.pc, self.uniq)
        }
    }
}

#[derive(Clone, Debug)]
pub struct Range {
    spc: SpaceRef,
    first: u64,
    last: u64,
}

#[derive(Clone, Debug, Default)]
pub struct RangeProperties {
    space_name: String,
    first: u64,
    last: u64,
    is_register: bool,
    seen_last: bool,
}

impl RangeProperties {
    pub fn new() -> RangeProperties {
        RangeProperties::default()
    }

    pub fn decode(&mut self, decoder: &mut dyn Decoder) -> Result<()> {
        let elem_id = decoder.open_element()?;
        if elem_id != ELEM_RANGE && elem_id != ELEM_REGISTER {
            return Err(Error::Decoder("Expecting <range> or <register> element".to_string()));
        }
        loop {
            let attrib_id = decoder.get_next_attribute_id()?;
            if attrib_id == 0 {
                break;
            }
            if attrib_id == ATTRIB_SPACE {
                self.space_name = decoder.read_string()?;
            } else if attrib_id == ATTRIB_FIRST {
                self.first = decoder.read_unsigned_integer()?;
            } else if attrib_id == ATTRIB_LAST {
                self.last = decoder.read_unsigned_integer()?;
                self.seen_last = true;
            } else if attrib_id == ATTRIB_NAME {
                self.space_name = decoder.read_string()?;
                self.is_register = true;
            }
        }
        decoder.close_element(elem_id)
    }
}

impl Range {
    pub fn new(spc: SpaceRef, first: u64, last: u64) -> Range {
        Range { spc, first, last }
    }

    pub fn from_properties(
        properties: &RangeProperties,
        manager: &AddrSpaceManager,
        trans: Option<&dyn Translate>,
    ) -> Result<Range> {
        if properties.is_register {
            let point = match trans {
                Some(translate) => translate.get_register(&properties.space_name)?,
                None => {
                    return Err(Error::Lowlevel(format!(
                        "no register table for resolving register {}",
                        properties.space_name
                    )));
                }
            };
            let spc = point
                .space
                .clone()
                .ok_or_else(|| Error::Lowlevel("No address space indicated in range tag".to_string()))?;
            let first = point.offset;
            let last = first.wrapping_sub(1).wrapping_add(point.size as u64);
            return Ok(Range { spc, first, last });
        }
        let Some(spc) = manager.get_space_by_name(&properties.space_name) else {
            return Err(Error::Lowlevel(format!("Undefined space: {}", properties.space_name)));
        };
        let first = properties.first;
        let mut last = properties.last;
        if !properties.seen_last {
            last = spc.get_highest();
        }
        if first > spc.get_highest() || last > spc.get_highest() || last < first {
            return Err(Error::Lowlevel("Illegal range tag".to_string()));
        }
        Ok(Range { spc, first, last })
    }

    pub fn get_space(&self) -> &SpaceRef {
        &self.spc
    }

    pub fn get_first(&self) -> u64 {
        self.first
    }

    pub fn get_last(&self) -> u64 {
        self.last
    }

    pub fn get_first_addr(&self) -> Address {
        Address::new(self.spc.clone(), self.first)
    }

    pub fn get_last_addr(&self) -> Address {
        Address::new(self.spc.clone(), self.last)
    }

    pub fn get_last_addr_open(&self, manager: &AddrSpaceManager) -> Address {
        let mut curspc = Some(self.spc.clone());
        let mut curlast = self.last;
        if curlast == self.spc.get_highest() {
            curspc = manager.get_next_space_in_order(curspc.as_ref());
            curlast = 0;
        } else {
            curlast = curlast.wrapping_add(1);
        }
        match curspc {
            None => Address::extreme(MachExtreme::Maximal),
            Some(spc) => Address::new(spc, curlast),
        }
    }

    pub fn contains(&self, addr: &Address) -> bool {
        match addr.get_space() {
            Some(spc) if spc.get_index() == self.spc.get_index() => {}
            _ => return false,
        }
        if self.first > addr.get_offset() {
            return false;
        }
        if self.last < addr.get_offset() {
            return false;
        }
        true
    }

    pub fn print_bounds(&self, out: &mut String) {
        let _ = write!(out, "{}: {:x}-{:x}", self.spc.get_name(), self.first, self.last);
    }

    pub fn encode(&self, encoder: &mut dyn Encoder) {
        encoder.open_element(ELEM_RANGE);
        encoder.write_space(ATTRIB_SPACE, &self.spc);
        encoder.write_unsigned_integer(ATTRIB_FIRST, self.first);
        encoder.write_unsigned_integer(ATTRIB_LAST, self.last);
        encoder.close_element(ELEM_RANGE);
    }

    pub fn decode(decoder: &mut dyn Decoder) -> Result<Range> {
        let elem_id = decoder.open_element()?;
        if elem_id != ELEM_RANGE && elem_id != ELEM_REGISTER {
            return Err(Error::Decoder("Expecting <range> or <register> element".to_string()));
        }
        let range = Range::decode_from_attributes(decoder)?;
        decoder.close_element(elem_id)?;
        Ok(range)
    }

    pub fn decode_from_attributes(decoder: &mut dyn Decoder) -> Result<Range> {
        let mut spc: Option<SpaceRef> = None;
        let mut seen_last = false;
        let mut first = 0;
        let mut last = 0;
        loop {
            let attrib_id = decoder.get_next_attribute_id()?;
            if attrib_id == 0 {
                break;
            }
            if attrib_id == ATTRIB_SPACE {
                spc = Some(decoder.read_space()?);
            } else if attrib_id == ATTRIB_FIRST {
                first = decoder.read_unsigned_integer()?;
            } else if attrib_id == ATTRIB_LAST {
                last = decoder.read_unsigned_integer()?;
                seen_last = true;
            } else if attrib_id == ATTRIB_NAME {
                let name = decoder.read_string()?;
                let point = decoder.get_register(&name)?;
                let spc = point
                    .space
                    .clone()
                    .ok_or_else(|| Error::Lowlevel("No address space indicated in range tag".to_string()))?;
                let first = point.offset;
                let last = first.wrapping_sub(1).wrapping_add(point.size as u64);
                return Ok(Range { spc, first, last });
            }
        }
        let Some(spc) = spc else {
            return Err(Error::Lowlevel("No address space indicated in range tag".to_string()));
        };
        if !seen_last {
            last = spc.get_highest();
        }
        if first > spc.get_highest() || last > spc.get_highest() || last < first {
            return Err(Error::Lowlevel("Illegal range tag".to_string()));
        }
        Ok(Range { spc, first, last })
    }
}

impl PartialEq for Range {
    fn eq(&self, other: &Range) -> bool {
        self.cmp(other) == Ordering::Equal
    }
}

impl Eq for Range {}

impl PartialOrd for Range {
    fn partial_cmp(&self, other: &Range) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for Range {
    fn cmp(&self, other: &Range) -> Ordering {
        self.spc
            .get_index()
            .cmp(&other.spc.get_index())
            .then(self.first.cmp(&other.first))
    }
}

#[derive(Clone, Debug, Default)]
pub struct RangeList {
    tree: BTreeSet<Range>,
}

impl RangeList {
    pub fn new() -> RangeList {
        RangeList::default()
    }

    pub fn clear(&mut self) {
        self.tree.clear();
    }

    pub fn empty(&self) -> bool {
        self.tree.is_empty()
    }

    pub fn iter(&self) -> impl DoubleEndedIterator<Item = &Range> {
        self.tree.iter()
    }

    pub fn num_ranges(&self) -> i32 {
        self.tree.len() as i32
    }

    pub fn get_first_range(&self) -> Option<&Range> {
        self.tree.first()
    }

    pub fn get_last_range(&self) -> Option<&Range> {
        self.tree.last()
    }

    fn upper_bound(&self, key: &Range) -> Option<&Range> {
        self.tree.range((Bound::Excluded(key), Bound::Unbounded)).next()
    }

    fn before_upper_bound(&self, key: &Range) -> Option<&Range> {
        self.tree.range((Bound::Unbounded, Bound::Included(key))).next_back()
    }

    pub fn get_last_signed_range(&self, spaceid: &SpaceRef) -> Option<&Range> {
        let midway = spaceid.get_highest() / 2;
        let range = Range::new(spaceid.clone(), midway, midway);
        if let Some(found) = self.before_upper_bound(&range)
            && found.spc.get_index() == spaceid.get_index()
        {
            return Some(found);
        }
        let range = Range::new(spaceid.clone(), spaceid.get_highest(), spaceid.get_highest());
        if let Some(found) = self.before_upper_bound(&range)
            && found.spc.get_index() == spaceid.get_index()
        {
            return Some(found);
        }
        None
    }

    pub fn get_range(&self, spaceid: &SpaceRef, offset: u64) -> Option<&Range> {
        if self.tree.is_empty() {
            return None;
        }
        let key = Range::new(spaceid.clone(), offset, offset);
        let found = self.before_upper_bound(&key)?;
        if found.spc.get_index() != spaceid.get_index() {
            return None;
        }
        if found.last >= offset {
            return Some(found);
        }
        None
    }

    pub fn get_nearest_range(&self, spaceid: &SpaceRef, offset: u64) -> Option<&Range> {
        if self.tree.is_empty() {
            return None;
        }
        let key = Range::new(spaceid.clone(), offset, offset);
        let after = self
            .upper_bound(&key)
            .filter(|range| range.spc.get_index() == spaceid.get_index());
        let Some(before) = self.before_upper_bound(&key) else {
            return after;
        };
        if before.spc.get_index() != spaceid.get_index() {
            return after;
        }
        let Some(after) = after else {
            return Some(before);
        };
        if before.last >= offset {
            return Some(before);
        }
        let distafter = after.first.wrapping_sub(offset);
        let distbefore = offset.wrapping_sub(before.last);
        if distafter < distbefore {
            Some(after)
        } else {
            Some(before)
        }
    }

    fn overlapping_start(&self, spc: &SpaceRef, first: u64) -> Option<Range> {
        let key = Range::new(spc.clone(), first, first);
        if let Some(prev) = self.before_upper_bound(&key)
            && prev.spc.get_index() == spc.get_index()
            && prev.last >= first
        {
            return Some(prev.clone());
        }
        self.upper_bound(&key).cloned()
    }

    fn collect_span(&self, spc: &SpaceRef, first: u64, last: u64) -> Vec<Range> {
        let Some(start) = self.overlapping_start(spc, first) else {
            return Vec::new();
        };
        let end = Range::new(spc.clone(), last, last);
        if start > end {
            return Vec::new();
        }
        self.tree
            .range((Bound::Included(&start), Bound::Included(&end)))
            .cloned()
            .collect()
    }

    pub fn insert_range(&mut self, spc: &SpaceRef, first: u64, last: u64) {
        let mut first = first;
        let mut last = last;
        for range in self.collect_span(spc, first, last) {
            if range.first < first {
                first = range.first;
            }
            if range.last > last {
                last = range.last;
            }
            self.tree.remove(&range);
        }
        self.tree.insert(Range::new(spc.clone(), first, last));
    }

    pub fn insert(&mut self, rng: &Range) {
        self.insert_range(&rng.spc, rng.first, rng.last);
    }

    pub fn remove_range(&mut self, spc: &SpaceRef, first: u64, last: u64) {
        if self.tree.is_empty() {
            return;
        }
        for range in self.collect_span(spc, first, last) {
            let lower = range.first;
            let upper = range.last;
            self.tree.remove(&range);
            if lower < first {
                self.tree.insert(Range::new(spc.clone(), lower, first.wrapping_sub(1)));
            }
            if upper > last {
                self.tree.insert(Range::new(spc.clone(), last.wrapping_add(1), upper));
            }
        }
    }

    pub fn remove(&mut self, rng: &Range) {
        self.remove_range(&rng.spc, rng.first, rng.last);
    }

    pub fn merge(&mut self, op2: &RangeList) {
        for range in op2.tree.iter() {
            self.insert(range);
        }
    }

    pub fn in_range(&self, addr: &Address, size: u64) -> bool {
        let Some(spc) = addr.get_space() else {
            return true;
        };
        if self.tree.is_empty() {
            return false;
        }
        let key = Range::new(spc.clone(), addr.get_offset(), addr.get_offset());
        let Some(found) = self.before_upper_bound(&key) else {
            return false;
        };
        if found.spc.get_index() != spc.get_index() {
            return false;
        }
        let end = addr.get_offset().wrapping_add(size).wrapping_sub(1);
        if end < addr.get_offset() {
            return false;
        }
        found.last >= end
    }

    pub fn in_range_range(&self, rng: &Range) -> bool {
        if self.tree.is_empty() {
            return false;
        }
        let Some(found) = self.before_upper_bound(rng) else {
            return false;
        };
        if found.spc.get_index() != rng.spc.get_index() {
            return false;
        }
        found.last >= rng.last
    }

    pub fn longest_fit(&self, addr: &Address, maxsize: u64) -> u64 {
        let Some(spc) = addr.get_space() else {
            return 0;
        };
        if self.tree.is_empty() {
            return 0;
        }
        let mut offset = addr.get_offset();
        let key = Range::new(spc.clone(), offset, offset);
        let Some(start) = self.before_upper_bound(&key) else {
            return 0;
        };
        let mut sizeres: u64 = 0;
        if start.last < offset {
            return sizeres;
        }
        for range in self.tree.range((Bound::Included(start), Bound::Unbounded)) {
            if range.spc.get_index() != spc.get_index() {
                break;
            }
            if range.first > offset {
                break;
            }
            sizeres = sizeres.wrapping_add(range.last.wrapping_add(1).wrapping_sub(offset));
            offset = range.last.wrapping_add(1);
            if sizeres >= maxsize {
                break;
            }
        }
        sizeres
    }

    pub fn print_bounds(&self, out: &mut String) {
        if self.tree.is_empty() {
            out.push_str("all\n");
        } else {
            for range in self.tree.iter() {
                range.print_bounds(out);
                out.push('\n');
            }
        }
    }

    pub fn encode(&self, encoder: &mut dyn Encoder) {
        encoder.open_element(ELEM_RANGELIST);
        for range in self.tree.iter() {
            range.encode(encoder);
        }
        encoder.close_element(ELEM_RANGELIST);
    }

    pub fn decode(&mut self, decoder: &mut dyn Decoder) -> Result<()> {
        let elem_id = decoder.open_element_expect(ELEM_RANGELIST)?;
        while decoder.peek_element()? != 0 {
            let range = Range::decode(decoder)?;
            self.tree.insert(range);
        }
        decoder.close_element(elem_id)
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct BitRange {
    pub byte_offset: i32,
    pub byte_size: i32,
    pub least_sig_bit: i32,
    pub num_bits: i32,
    pub is_big_endian: bool,
}

impl Default for BitRange {
    fn default() -> BitRange {
        BitRange {
            byte_offset: -1,
            byte_size: -1,
            least_sig_bit: -1,
            num_bits: -1,
            is_big_endian: false,
        }
    }
}

impl BitRange {
    pub fn new_bytes(b_off: i32, b_size: i32, big_endian: bool) -> BitRange {
        BitRange {
            byte_offset: b_off,
            byte_size: b_size,
            least_sig_bit: 0,
            num_bits: b_size * 8,
            is_big_endian: big_endian,
        }
    }

    pub fn new(b_off: i32, b_size: i32, least: i32, num: i32, big_endian: bool) -> BitRange {
        BitRange {
            byte_offset: b_off,
            byte_size: b_size,
            least_sig_bit: least,
            num_bits: num,
            is_big_endian: big_endian,
        }
    }

    pub fn from_container(op2: &BitRange, off: i32, sz: i32) -> BitRange {
        let mut res = BitRange {
            byte_offset: off,
            byte_size: sz,
            least_sig_bit: 0,
            num_bits: op2.num_bits,
            is_big_endian: op2.is_big_endian,
        };
        res.least_sig_bit = res.translate_lsb(op2);
        res
    }

    pub fn empty(&self) -> bool {
        self.num_bits <= 0
    }

    pub fn compare(&self, op2: &BitRange) -> i32 {
        if self.byte_offset != op2.byte_offset {
            return if self.byte_offset < op2.byte_offset { -1 } else { 1 };
        }
        if self.byte_size != op2.byte_size {
            return if self.byte_size < op2.byte_size { -1 } else { 1 };
        }
        if self.least_sig_bit != op2.least_sig_bit {
            return if self.least_sig_bit < op2.least_sig_bit { -1 } else { 1 };
        }
        if self.num_bits != op2.num_bits {
            return if self.num_bits < op2.num_bits { -1 } else { 1 };
        }
        0
    }

    pub fn translate_lsb(&self, op2: &BitRange) -> i32 {
        let mut op2_sig = op2.least_sig_bit;
        if self.is_big_endian {
            let this_pos = self.byte_offset + self.byte_size;
            let op2_pos = op2.byte_offset + op2.byte_size;
            op2_sig += 8 * (this_pos - op2_pos);
        } else {
            op2_sig += 8 * (op2.byte_offset - self.byte_offset);
        }
        op2_sig
    }

    pub fn overlap_test(&self, op2: &BitRange) -> i32 {
        let op2_sig = self.translate_lsb(op2);
        let this_most = self.least_sig_bit + self.num_bits;
        let op2_most = op2_sig + op2.num_bits;
        if self.is_big_endian {
            if self.least_sig_bit >= op2_most {
                return -1;
            }
            if op2_sig >= this_most {
                return 1;
            }
        } else {
            if this_most <= op2_sig {
                return -1;
            }
            if op2_most <= self.least_sig_bit {
                return 1;
            }
        }
        if self.least_sig_bit == op2_sig && this_most == op2_most {
            return 0;
        }
        if op2_sig <= self.least_sig_bit && op2_most >= this_most {
            return 2;
        }
        if self.least_sig_bit <= op2_sig && this_most >= op2_most {
            return 3;
        }
        4
    }

    pub fn intersection(&mut self, op2: &BitRange) {
        let op2_sig = self.translate_lsb(op2);
        let op2_most = op2_sig + op2.num_bits;
        let this_most = self.least_sig_bit + self.num_bits;
        if op2_sig > self.least_sig_bit {
            self.num_bits -= op2_sig - self.least_sig_bit;
            self.least_sig_bit = op2_sig;
        }
        if op2_most < this_most {
            self.num_bits -= this_most - op2_most;
        }
        if self.num_bits < 0 {
            self.least_sig_bit = 0;
            self.num_bits = 0;
        }
    }

    pub fn intersect_mask(&mut self, mask: u64) {
        let mask = mask & self.get_mask();
        if mask == 0 {
            self.least_sig_bit = 0;
            self.num_bits = 0;
            return;
        }
        let new_least_sig = leastsigbit_set(mask);
        let new_most_sig = mostsigbit_set(mask) + 1;
        let this_most = self.least_sig_bit + self.num_bits;
        if new_least_sig > self.least_sig_bit {
            self.num_bits -= new_least_sig - self.least_sig_bit;
            self.least_sig_bit = new_least_sig;
        }
        if new_most_sig < this_most {
            self.num_bits -= this_most - new_most_sig;
        }
    }

    pub fn shift(&mut self, left_shift_amount: i32) {
        self.least_sig_bit += left_shift_amount;
        let most = self.least_sig_bit + self.num_bits;
        if self.least_sig_bit < 0 {
            self.num_bits += self.least_sig_bit;
            self.least_sig_bit = 0;
        } else if most > self.byte_size * 8 {
            self.num_bits -= most - self.byte_size * 8;
        }
        if self.num_bits < 0 {
            self.least_sig_bit = 0;
            self.num_bits = 0;
        }
    }

    pub fn truncate_most_sig_bytes(&mut self, num: i32) {
        if self.is_big_endian {
            self.byte_offset += num;
        }
        self.byte_size -= num;
        let max_offset = self.least_sig_bit + self.num_bits;
        if max_offset > self.byte_size * 8 {
            self.num_bits -= max_offset - self.byte_size * 8;
        }
        if self.num_bits < 0 {
            self.num_bits = 0;
        }
    }

    pub fn truncate_least_sig_bytes(&mut self, num: i32) {
        if !self.is_big_endian {
            self.byte_offset += num;
        }
        self.byte_size -= num;
        self.least_sig_bit -= num * 8;
        if self.least_sig_bit < 0 {
            self.num_bits += self.least_sig_bit;
            self.least_sig_bit = 0;
            if self.num_bits < 0 {
                self.num_bits = 0;
            }
        }
    }

    pub fn extend_bytes(&mut self, num: i32) {
        if self.is_big_endian {
            self.byte_offset -= num;
        }
        self.byte_size += num;
    }

    pub fn get_mask(&self) -> u64 {
        let mut res: u64 = if self.num_bits as u32 >= 64 {
            0
        } else {
            1u64.wrapping_shl(self.num_bits as u32)
        };
        res = res.wrapping_sub(1);
        res.wrapping_shl(self.least_sig_bit as u32)
    }

    pub fn is_byte_range(&self) -> bool {
        (self.num_bits & 7) == 0 && (self.least_sig_bit & 7) == 0
    }

    pub fn is_most_significant(&self) -> bool {
        8 * self.byte_size == self.least_sig_bit + self.num_bits
    }

    pub fn minimize_container(&mut self) {
        let trunc = self.least_sig_bit / 8;
        if self.is_big_endian {
            self.byte_size -= trunc;
        } else {
            self.byte_offset += trunc;
        }
        self.least_sig_bit &= 7;
        let num = self.byte_size - ((self.least_sig_bit + self.num_bits + 7) / 8);
        if num > 0 {
            if self.is_big_endian {
                self.byte_offset += num;
            }
            self.byte_size -= num;
        }
    }

    pub fn expand_to_most(&mut self) {
        self.num_bits = 8 * self.byte_size - self.least_sig_bit;
    }
}

pub const UINTBMASKS: [u64; 9] = [
    0,
    0xff,
    0xffff,
    0xffffff,
    0xffffffff,
    0xffffffffff,
    0xffffffffffff,
    0xffffffffffffff,
    0xffffffffffffffff,
];

pub fn calc_mask(size: i32) -> u64 {
    UINTBMASKS[if (size as u32) < 8 { size as usize } else { 8 }]
}

pub fn calc_uint_max(size: i32) -> u64 {
    calc_mask(size)
}

pub fn calc_int_max(size: i32) -> u64 {
    calc_mask(size) >> 1
}

pub fn calc_int_min(size: i32) -> u64 {
    1u64.wrapping_shl((size.wrapping_mul(8).wrapping_sub(1)) as u32)
}

pub fn pcode_right(val: u64, sa: i32) -> u64 {
    if !(0..64).contains(&sa) {
        return 0;
    }
    val >> sa
}

pub fn pcode_left(val: u64, sa: i32) -> u64 {
    if !(0..64).contains(&sa) {
        return 0;
    }
    val << sa
}

pub fn minimalmask(val: u64) -> u64 {
    if val > 0xffffffff {
        return u64::MAX;
    }
    if val > 0xffff {
        return 0xffffffff;
    }
    if val > 0xff {
        return 0xffff;
    }
    0xff
}

pub fn sign_extend(val: i64, bit: i32) -> i64 {
    let sa = (64 - (bit + 1)) as u32;
    val.wrapping_shl(sa).wrapping_shr(sa)
}

pub fn zero_extend(val: i64, bit: i32) -> i64 {
    let sa = (64 - (bit + 1)) as u32;
    (val as u64).wrapping_shl(sa).wrapping_shr(sa) as i64
}

pub fn signbit_negative(val: u64, size: i32) -> bool {
    let mask: u64 = 0x80u64.wrapping_shl((8 * (size - 1)) as u32);
    (val & mask) != 0
}

pub fn uintb_negate(input: u64, size: i32) -> u64 {
    (!input) & calc_mask(size)
}

pub fn sign_extend_size(input: u64, sizein: i32, sizeout: i32) -> u64 {
    let sizein = if (sizein as u32) < 8 { sizein } else { 8 };
    let sizeout = if (sizeout as u32) < 8 { sizeout } else { 8 };
    let mut sval = input as i64;
    sval = sval.wrapping_shl(((8 - sizein) * 8) as u32);
    let mut res = sval.wrapping_shr(((sizeout - sizein) * 8) as u32) as u64;
    res = res.wrapping_shr(((8 - sizeout) * 8) as u32);
    res
}

pub fn extend_signbit(val: u64, numbits: i32, size: i32) -> u64 {
    let mut val = val;
    if numbits < size * 8 {
        let sa = (64 - numbits) as u32;
        let sval = val as i64;
        val = sval.wrapping_shl(sa).wrapping_shr(sa) as u64;
        val &= calc_mask(size);
    }
    val
}

pub fn byte_swap_signed(val: i64, size: i32) -> i64 {
    let mut res: i64 = 0;
    let mut val = val;
    let mut size = size;
    while size > 0 {
        res = res.wrapping_shl(8);
        res |= val & 0xff;
        val >>= 8;
        size -= 1;
    }
    res
}

pub fn byte_swap(val: u64, size: i32) -> u64 {
    let mut res: u64 = 0;
    let mut val = val;
    let mut size = size;
    while size > 0 {
        res = res.wrapping_shl(8);
        res |= val & 0xff;
        val >>= 8;
        size -= 1;
    }
    res
}

pub fn leastsigbit_set(val: u64) -> i32 {
    if val == 0 {
        return -1;
    }
    val.trailing_zeros() as i32
}

pub fn mostsigbit_set(val: u64) -> i32 {
    if val == 0 {
        return -1;
    }
    63 - val.leading_zeros() as i32
}

pub fn popcount(val: u64) -> i32 {
    val.count_ones() as i32
}

pub fn count_leading_zeros(val: u64) -> i32 {
    val.leading_zeros() as i32
}

pub fn coveringmask(val: u64) -> u64 {
    let mut res = val;
    let mut sz = 1;
    while sz < 64 {
        res |= res >> sz;
        sz <<= 1;
    }
    res
}

pub fn bit_transitions(val: u64, sz: i32) -> i32 {
    let mut res = 0;
    let mut val = val;
    let mut last = (val & 1) as i32;
    for _ in 1..8 * sz {
        val >>= 1;
        let cur = (val & 1) as i32;
        if cur != last {
            res += 1;
            last = cur;
        }
        if val == 0 {
            break;
        }
    }
    res
}
