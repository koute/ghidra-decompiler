use std::collections::BTreeMap;

use crate::address::{Address, Range, calc_mask};
use crate::error::{Error, Result};
use crate::marshal::{ATTRIB_NAME, ATTRIB_VAL, Decoder, ElementId, Encoder};
use crate::partmap::PartMap;
use crate::pcoderaw::VarnodeData;

pub const ELEM_CONTEXT_DATA: ElementId = ElementId::new("context_data", 120);
pub const ELEM_CONTEXT_POINTS: ElementId = ElementId::new("context_points", 121);
pub const ELEM_CONTEXT_POINTSET: ElementId = ElementId::new("context_pointset", 122);
pub const ELEM_CONTEXT_SET: ElementId = ElementId::new("context_set", 123);
pub const ELEM_SET: ElementId = ElementId::new("set", 124);
pub const ELEM_TRACKED_POINTSET: ElementId = ElementId::new("tracked_pointset", 125);
pub const ELEM_TRACKED_SET: ElementId = ElementId::new("tracked_set", 126);

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct ContextBitRange {
    word: i32,
    startbit: i32,
    endbit: i32,
    shift: i32,
    mask: u32,
}

impl ContextBitRange {
    pub fn new(sbit: i32, ebit: i32) -> ContextBitRange {
        let word = sbit / 32;
        let startbit = sbit - word * 32;
        let endbit = ebit - word * 32;
        let shift = 32 - endbit - 1;
        let mask = u32::MAX.wrapping_shr((startbit + shift) as u32);
        ContextBitRange {
            word,
            startbit,
            endbit,
            shift,
            mask,
        }
    }

    pub fn get_shift(&self) -> i32 {
        self.shift
    }

    pub fn get_mask(&self) -> u32 {
        self.mask
    }

    pub fn get_word(&self) -> i32 {
        self.word
    }

    pub fn set_value(&self, vec: &mut [u32], val: u32) {
        let slot = self.word as usize;
        let mut newval = vec[slot];
        newval &= !self.mask.wrapping_shl(self.shift as u32);
        newval |= (val & self.mask).wrapping_shl(self.shift as u32);
        vec[slot] = newval;
    }

    pub fn get_value(&self, vec: &[u32]) -> u32 {
        vec[self.word as usize].wrapping_shr(self.shift as u32) & self.mask
    }
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct TrackedContext {
    pub loc: VarnodeData,
    pub val: u64,
}

impl TrackedContext {
    pub fn decode(&mut self, decoder: &mut dyn Decoder) -> Result<()> {
        let elem_id = decoder.open_element_expect(ELEM_SET)?;
        self.loc = VarnodeData::decode_from_attributes(decoder)?;
        self.val = decoder.read_unsigned_integer_attr(ATTRIB_VAL)?;
        decoder.close_element(elem_id)
    }

    pub fn encode(&self, encoder: &mut dyn Encoder) -> Result<()> {
        encoder.open_element(ELEM_SET);
        if let Some(space) = &self.loc.space {
            space.encode_attributes_size(encoder, self.loc.offset, self.loc.size as i32)?;
        }
        encoder.write_unsigned_integer(ATTRIB_VAL, self.val);
        encoder.close_element(ELEM_SET);
        Ok(())
    }
}

pub type TrackedSet = Vec<TrackedContext>;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ContextBounds {
    pub first: u64,
    pub last: u64,
    pub key: Option<Address>,
}

pub fn encode_tracked(encoder: &mut dyn Encoder, addr: &Address, vec: &TrackedSet) -> Result<()> {
    if vec.is_empty() {
        return Ok(());
    }
    encoder.open_element(ELEM_TRACKED_POINTSET);
    if let Some(space) = addr.get_space() {
        space.encode_attributes(encoder, addr.get_offset())?;
    }
    for tracked in vec {
        tracked.encode(encoder)?;
    }
    encoder.close_element(ELEM_TRACKED_POINTSET);
    Ok(())
}

pub fn decode_tracked(decoder: &mut dyn Decoder, vec: &mut TrackedSet) -> Result<()> {
    vec.clear();
    while decoder.peek_element()? != 0 {
        let mut tracked = TrackedContext::default();
        tracked.decode(decoder)?;
        vec.push(tracked);
    }
    Ok(())
}

pub trait ContextDatabase {
    fn get_context_size(&self) -> i32;

    fn register_variable(&mut self, nm: &str, sbit: i32, ebit: i32) -> Result<()>;

    fn get_context(&self, addr: &Address) -> &[u32];

    fn get_context_bounds(&self, addr: &Address) -> ContextBounds;

    fn get_context_by_key(&self, key: Option<&Address>) -> &[u32];

    fn get_tracked_default(&mut self) -> &mut TrackedSet;

    fn get_tracked_set(&self, addr: &Address) -> &TrackedSet;

    fn create_set(&mut self, addr1: &Address, addr2: &Address) -> &mut TrackedSet;

    fn encode(&self, encoder: &mut dyn Encoder) -> Result<()>;

    fn decode(&mut self, decoder: &mut dyn Decoder) -> Result<()>;

    fn decode_from_spec(&mut self, decoder: &mut dyn Decoder) -> Result<()>;

    fn get_variable(&self, nm: &str) -> Result<ContextBitRange>;

    fn get_region_for_set(
        &mut self,
        addr1: &Address,
        addr2: &Address,
        num: i32,
        mask: u32,
        apply: &mut dyn FnMut(&mut [u32]),
    );

    fn get_region_to_change_point(&mut self, addr: &Address, num: i32, mask: u32, apply: &mut dyn FnMut(&mut [u32]));

    fn get_default_value(&self) -> &[u32];

    fn get_default_value_mut(&mut self) -> &mut [u32];

    fn set_variable_default(&mut self, nm: &str, val: u32) -> Result<()> {
        let var = self.get_variable(nm)?;
        var.set_value(self.get_default_value_mut(), val);
        Ok(())
    }

    fn get_default_value_by_name(&self, nm: &str) -> Result<u32> {
        let var = self.get_variable(nm)?;
        Ok(var.get_value(self.get_default_value()))
    }

    fn set_variable(&mut self, nm: &str, addr: &Address, value: u32) -> Result<()> {
        let bitrange = self.get_variable(nm)?;
        let num = bitrange.get_word();
        let mask = bitrange.get_mask().wrapping_shl(bitrange.get_shift() as u32);
        self.get_region_to_change_point(addr, num, mask, &mut |context| bitrange.set_value(context, value));
        Ok(())
    }

    fn get_variable_value(&self, nm: &str, addr: &Address) -> Result<u32> {
        let bitrange = self.get_variable(nm)?;
        Ok(bitrange.get_value(self.get_context(addr)))
    }

    fn set_context_change_point(&mut self, addr: &Address, num: i32, mask: u32, value: u32) {
        let slot = num as usize;
        self.get_region_to_change_point(addr, num, mask, &mut |context| {
            let mut val = context[slot];
            val &= !mask;
            val |= value;
            context[slot] = val;
        });
    }

    fn set_context_region(&mut self, addr1: &Address, addr2: &Address, num: i32, mask: u32, value: u32) {
        let slot = num as usize;
        self.get_region_for_set(addr1, addr2, num, mask, &mut |context| {
            context[slot] = (context[slot] & !mask) | value;
        });
    }

    fn set_variable_region(&mut self, nm: &str, begad: &Address, endad: &Address, value: u32) -> Result<()> {
        let bitrange = self.get_variable(nm)?;
        let mask = bitrange.get_mask().wrapping_shl(bitrange.get_shift() as u32);
        self.get_region_for_set(begad, endad, bitrange.get_word(), mask, &mut |context| {
            bitrange.set_value(context, value)
        });
        Ok(())
    }

    fn get_tracked_value(&self, mem: &VarnodeData, point: &Address) -> u64 {
        let tset = self.get_tracked_set(point);
        let endoff = mem.offset.wrapping_add(mem.size as u64).wrapping_sub(1);
        let mem_space = mem.space.as_ref().map(|spc| spc.get_index());
        for tcont in tset {
            if tcont.loc.space.as_ref().map(|spc| spc.get_index()) != mem_space {
                continue;
            }
            if tcont.loc.offset > mem.offset {
                continue;
            }
            let tendoff = tcont.loc.offset.wrapping_add(tcont.loc.size as u64).wrapping_sub(1);
            if tendoff < endoff {
                continue;
            }
            let mut res = tcont.val;
            let big_endian = tcont.loc.space.as_ref().is_some_and(|spc| spc.is_big_endian());
            if big_endian {
                if endoff != tendoff {
                    res = res.wrapping_shr((8 * tendoff.wrapping_sub(mem.offset)) as u32);
                }
            } else if mem.offset != tcont.loc.offset {
                res = res.wrapping_shr((8 * mem.offset.wrapping_sub(tcont.loc.offset)) as u32);
            }
            res &= calc_mask(mem.size as i32);
            return res;
        }
        0
    }
}

#[derive(Debug, Default)]
struct FreeArray {
    array: Vec<u32>,
    mask: Vec<u32>,
}

impl FreeArray {
    fn exact_copy(&self) -> FreeArray {
        FreeArray {
            array: self.array.clone(),
            mask: self.mask.clone(),
        }
    }

    fn reset(&mut self, sz: i32) {
        let size = sz.max(0) as usize;
        let mut newarray = vec![0u32; size];
        let mut newmask = vec![0u32; size];
        let min = size.min(self.array.len());
        newarray[..min].copy_from_slice(&self.array[..min]);
        newmask[..min].copy_from_slice(&self.mask[..min]);
        self.array = newarray;
        self.mask = newmask;
    }
}

impl Clone for FreeArray {
    fn clone(&self) -> FreeArray {
        FreeArray {
            array: self.array.clone(),
            mask: vec![0u32; self.mask.len()],
        }
    }
}

#[derive(Debug, Default)]
pub struct ContextInternal {
    size: i32,
    variables: BTreeMap<String, ContextBitRange>,
    database: PartMap<Address, FreeArray>,
    trackbase: PartMap<Address, TrackedSet>,
}

impl ContextInternal {
    pub fn new() -> ContextInternal {
        ContextInternal::default()
    }

    pub fn duplicate(&self) -> ContextInternal {
        ContextInternal {
            size: self.size,
            variables: self.variables.clone(),
            database: self.database.duplicate(FreeArray::exact_copy),
            trackbase: self.trackbase.duplicate(TrackedSet::clone),
        }
    }

    fn encode_context(&self, encoder: &mut dyn Encoder, addr: &Address, vec: &[u32]) -> Result<()> {
        encoder.open_element(ELEM_CONTEXT_POINTSET);
        if let Some(space) = addr.get_space() {
            space.encode_attributes(encoder, addr.get_offset())?;
        }
        for (name, bitrange) in self.variables.iter() {
            let val = bitrange.get_value(vec);
            encoder.open_element(ELEM_SET);
            encoder.write_string(ATTRIB_NAME, name);
            encoder.write_unsigned_integer(ATTRIB_VAL, val as u64);
            encoder.close_element(ELEM_SET);
        }
        encoder.close_element(ELEM_CONTEXT_POINTSET);
        Ok(())
    }

    fn decode_context(&mut self, decoder: &mut dyn Decoder, addr1: &Address, addr2: &Address) -> Result<()> {
        loop {
            let sub_id = decoder.open_element()?;
            if sub_id != ELEM_SET {
                break;
            }
            let val = decoder.read_unsigned_integer_attr(ATTRIB_VAL)? as u32;
            let var = self.get_variable(&decoder.read_string_attr(ATTRIB_NAME)?)?;
            if addr1.is_invalid() {
                let default_buffer = self.get_default_value_mut();
                for slot in default_buffer.iter_mut() {
                    *slot = 0;
                }
                var.set_value(default_buffer, val);
            } else {
                let mask = var.get_mask().wrapping_shl(var.get_shift() as u32);
                self.get_region_for_set(addr1, addr2, var.get_word(), mask, &mut |context| {
                    var.set_value(context, val)
                });
            }
            decoder.close_element(sub_id)?;
        }
        Ok(())
    }
}

impl ContextDatabase for ContextInternal {
    fn get_context_size(&self) -> i32 {
        self.size
    }

    fn register_variable(&mut self, nm: &str, sbit: i32, ebit: i32) -> Result<()> {
        if !self.database.empty() {
            return Err(Error::Lowlevel(
                "Cannot register new context variables after database is initialized".to_string(),
            ));
        }
        let bitrange = ContextBitRange::new(sbit, ebit);
        let sz = sbit / 32 + 1;
        if ebit / 32 + 1 != sz {
            return Err(Error::Lowlevel("Context variable does not fit in one word".to_string()));
        }
        if sz > self.size {
            self.size = sz;
            self.database.default_value_mut().reset(sz);
        }
        self.variables.insert(nm.to_string(), bitrange);
        Ok(())
    }

    fn get_context(&self, addr: &Address) -> &[u32] {
        &self.database.get_value(addr).array
    }

    fn get_context_bounds(&self, addr: &Address) -> ContextBounds {
        let (_, bounds) = self.database.bounds(addr);
        let addr_space = addr.get_space().map(|spc| spc.get_index());
        let before_space = bounds
            .before
            .as_ref()
            .and_then(|before| before.get_space().map(|spc| spc.get_index()));
        let after_space = bounds
            .after
            .as_ref()
            .and_then(|after| after.get_space().map(|spc| spc.get_index()));
        let first = if (bounds.valid & 1) != 0 || before_space != addr_space {
            0
        } else {
            bounds.before.as_ref().map_or(0, |before| before.get_offset())
        };
        let last = if (bounds.valid & 2) != 0 || after_space != addr_space {
            addr.get_space().map_or(0, |spc| spc.get_highest())
        } else {
            bounds
                .after
                .as_ref()
                .map_or(0, |after| after.get_offset().wrapping_sub(1))
        };
        let key = if (bounds.valid & 1) != 0 { None } else { bounds.before };
        ContextBounds { first, last, key }
    }

    fn get_context_by_key(&self, key: Option<&Address>) -> &[u32] {
        &self.database.get_by_key(key).array
    }

    fn get_tracked_default(&mut self) -> &mut TrackedSet {
        self.trackbase.default_value_mut()
    }

    fn get_tracked_set(&self, addr: &Address) -> &TrackedSet {
        self.trackbase.get_value(addr)
    }

    fn create_set(&mut self, addr1: &Address, addr2: &Address) -> &mut TrackedSet {
        let res = self.trackbase.clear_range(addr1, addr2);
        res.clear();
        res
    }

    fn encode(&self, encoder: &mut dyn Encoder) -> Result<()> {
        if self.database.empty() && self.trackbase.empty() {
            return Ok(());
        }
        encoder.open_element(ELEM_CONTEXT_POINTS);
        for (addr, free_array) in self.database.iter() {
            self.encode_context(encoder, addr, &free_array.array)?;
        }
        for (addr, tracked) in self.trackbase.iter() {
            encode_tracked(encoder, addr, tracked)?;
        }
        encoder.close_element(ELEM_CONTEXT_POINTS);
        Ok(())
    }

    fn decode(&mut self, decoder: &mut dyn Decoder) -> Result<()> {
        let elem_id = decoder.open_element_expect(ELEM_CONTEXT_POINTS)?;
        loop {
            let sub_id = decoder.open_element()?;
            if sub_id == 0 {
                break;
            }
            if sub_id == ELEM_CONTEXT_POINTSET {
                let attrib_id = decoder.get_next_attribute_id()?;
                decoder.rewind_attributes();
                if attrib_id == 0 {
                    self.decode_context(decoder, &Address::invalid(), &Address::invalid())?;
                } else {
                    let v_data = VarnodeData::decode_from_attributes(decoder)?;
                    self.decode_context(decoder, &v_data.get_addr(), &Address::invalid())?;
                }
            } else if sub_id == ELEM_TRACKED_POINTSET {
                let v_data = VarnodeData::decode_from_attributes(decoder)?;
                let tracked = self.trackbase.split(&v_data.get_addr());
                decode_tracked(decoder, tracked)?;
            } else {
                return Err(Error::Lowlevel("Bad <context_points> tag".to_string()));
            }
            decoder.close_element(sub_id)?;
        }
        decoder.close_element(elem_id)
    }

    fn decode_from_spec(&mut self, decoder: &mut dyn Decoder) -> Result<()> {
        let elem_id = decoder.open_element_expect(ELEM_CONTEXT_DATA)?;
        loop {
            let sub_id = decoder.open_element()?;
            if sub_id == 0 {
                break;
            }
            let range = Range::decode_from_attributes(decoder)?;
            let addr1 = range.get_first_addr();
            let addr2 = range.get_last_addr_open(decoder.manager()?);
            if sub_id == ELEM_CONTEXT_SET {
                self.decode_context(decoder, &addr1, &addr2)?;
            } else if sub_id == ELEM_TRACKED_SET {
                let tracked = self.create_set(&addr1, &addr2);
                decode_tracked(decoder, tracked)?;
            } else {
                return Err(Error::Lowlevel("Bad <context_data> tag".to_string()));
            }
            decoder.close_element(sub_id)?;
        }
        decoder.close_element(elem_id)
    }

    fn get_variable(&self, nm: &str) -> Result<ContextBitRange> {
        self.variables
            .get(nm)
            .copied()
            .ok_or_else(|| Error::Lowlevel(format!("Non-existent context variable: {nm}")))
    }

    fn get_region_for_set(
        &mut self,
        addr1: &Address,
        addr2: &Address,
        num: i32,
        mask: u32,
        apply: &mut dyn FnMut(&mut [u32]),
    ) {
        self.database.split(addr1);
        let bounded = !addr2.is_invalid();
        if bounded {
            self.database.split(addr2);
        }
        if bounded && addr1 == addr2 {
            return;
        }
        let stop_at_end = bounded && addr1 < addr2;
        let slot = num as usize;
        for key in self.database.keys_from(addr1) {
            if stop_at_end && key >= *addr2 {
                break;
            }
            let entry = self.database.get_mut(&key).expect("partition key exists");
            entry.mask[slot] |= mask;
            apply(&mut entry.array);
        }
    }

    fn get_region_to_change_point(&mut self, addr: &Address, num: i32, mask: u32, apply: &mut dyn FnMut(&mut [u32])) {
        self.database.split(addr);
        let slot = num as usize;
        let keys = self.database.keys_from(addr);
        let mut iter = keys.into_iter();
        let Some(first_key) = iter.next() else {
            return;
        };
        {
            let entry = self.database.get_mut(&first_key).expect("partition key exists");
            apply(&mut entry.array);
            entry.mask[slot] |= mask;
        }
        for key in iter {
            let entry = self.database.get_mut(&key).expect("partition key exists");
            if (entry.mask[slot] & mask) != 0 {
                break;
            }
            apply(&mut entry.array);
        }
    }

    fn get_default_value(&self) -> &[u32] {
        &self.database.default_value().array
    }

    fn get_default_value_mut(&mut self) -> &mut [u32] {
        &mut self.database.default_value_mut().array
    }
}

#[derive(Clone, Debug)]
struct CacheWindow {
    space_index: i32,
    first: u64,
    last: u64,
    key: Option<Address>,
}

#[derive(Clone, Debug)]
pub struct ContextCache {
    allowset: bool,
    window: Option<CacheWindow>,
    first: u64,
    last: u64,
}

impl Default for ContextCache {
    fn default() -> ContextCache {
        ContextCache::new()
    }
}

impl ContextCache {
    pub fn new() -> ContextCache {
        ContextCache {
            allowset: true,
            window: None,
            first: 0,
            last: 0,
        }
    }

    pub fn allow_set(&mut self, val: bool) {
        self.allowset = val;
    }

    pub fn get_context(&mut self, database: &dyn ContextDatabase, addr: &Address, buf: &mut [u32]) {
        let addr_space = addr.get_space().map(|spc| spc.get_index());
        let offset = addr.get_offset();
        let hit = match &self.window {
            Some(window) => Some(window.space_index) == addr_space && window.first <= offset && window.last >= offset,
            None => false,
        };
        if !hit {
            let bounds = database.get_context_bounds(addr);
            self.first = bounds.first;
            self.last = bounds.last;
            self.window = addr_space.map(|space_index| CacheWindow {
                space_index,
                first: bounds.first,
                last: bounds.last,
                key: bounds.key.clone(),
            });
            let context = database.get_context_by_key(bounds.key.as_ref());
            let size = database.get_context_size().max(0) as usize;
            buf[..size].copy_from_slice(&context[..size]);
            return;
        }
        let key = self.window.as_ref().and_then(|window| window.key.clone());
        let context = database.get_context_by_key(key.as_ref());
        let size = database.get_context_size().max(0) as usize;
        buf[..size].copy_from_slice(&context[..size]);
    }

    fn in_window(&self, addr: &Address) -> bool {
        match &self.window {
            Some(window) => {
                addr.get_space().map(|spc| spc.get_index()) == Some(window.space_index)
                    && self.first <= addr.get_offset()
                    && self.last >= addr.get_offset()
            }
            None => false,
        }
    }

    pub fn set_context(&mut self, database: &mut dyn ContextDatabase, addr: &Address, num: i32, mask: u32, value: u32) {
        if !self.allowset {
            return;
        }
        database.set_context_change_point(addr, num, mask, value);
        if self.in_window(addr) {
            self.window = None;
        }
    }

    pub fn set_context_region(
        &mut self,
        database: &mut dyn ContextDatabase,
        addr1: &Address,
        addr2: &Address,
        num: i32,
        mask: u32,
        value: u32,
    ) {
        if !self.allowset {
            return;
        }
        database.set_context_region(addr1, addr2, num, mask, value);
        if self.in_window(addr1) {
            self.window = None;
        }
        if self.first <= addr2.get_offset() && self.last >= addr2.get_offset() {
            self.window = None;
        }
        if self.first >= addr1.get_offset() && self.first <= addr2.get_offset() {
            self.window = None;
        }
    }
}
