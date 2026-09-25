use std::collections::{BTreeMap, BTreeSet};
use std::fmt::Write;
use std::sync::{Arc, RwLock, RwLockReadGuard, RwLockWriteGuard};

use crate::address::{Address, RangeList};
use crate::error::{Error, Result};
use crate::loadimage::{LoadImage, LoadImageFunc};
use crate::marshal::{
    ATTRIB_CONTENT, ATTRIB_NAME, ATTRIB_READONLY, ATTRIB_SPACE, AttributeId, Decoder, ELEM_SYMBOL, ElementId, Encoder,
    XmlDecode,
};
use crate::sleigh_arch::AdjustableLoadImage;
use crate::space::AddrSpace;
use crate::translate::AddrSpaceManager;
use crate::xml::Element;

pub const ATTRIB_ARCH: AttributeId = AttributeId::new("arch", 135);

pub const ELEM_BINARYIMAGE: ElementId = ElementId::new("binaryimage", 230);
pub const ELEM_BYTECHUNK: ElementId = ElementId::new("bytechunk", 231);

#[derive(Debug, Default)]
struct LoadImageXmlState {
    archtype: String,
    readonlyset: BTreeSet<Address>,
    chunk: BTreeMap<Address, Vec<u8>>,
    addrtosymbol: BTreeMap<Address, String>,
    cursymbol: Option<Address>,
    symbols_open: bool,
}

#[derive(Debug)]
pub struct LoadImageXml {
    filename: String,
    rootel: Arc<Element>,
    state: RwLock<LoadImageXmlState>,
}

fn hex_digit_value(character: i32) -> i32 {
    if character <= b'9' as i32 {
        character - b'0' as i32
    } else if character <= b'F' as i32 {
        character + 10 - b'A' as i32
    } else {
        character + 10 - b'a' as i32
    }
}

fn is_stream_space(byte: u8) -> bool {
    matches!(byte, b' ' | b'\t' | b'\n' | 0x0b | 0x0c | b'\r')
}

impl LoadImageXml {
    pub fn new(filename: &str, el: Arc<Element>) -> Result<LoadImageXml> {
        if el.get_name() != "binaryimage" {
            return Err(Error::Lowlevel(format!("Missing binaryimage tag in {filename}")));
        }
        let archtype = el.get_attribute_value("arch")?.to_string();
        Ok(LoadImageXml {
            filename: filename.to_string(),
            rootel: el,
            state: RwLock::new(LoadImageXmlState {
                archtype,
                ..LoadImageXmlState::default()
            }),
        })
    }

    fn read_state(&self) -> RwLockReadGuard<'_, LoadImageXmlState> {
        self.state.read().unwrap_or_else(|poisoned| poisoned.into_inner())
    }

    fn write_state(&self) -> RwLockWriteGuard<'_, LoadImageXmlState> {
        self.state.write().unwrap_or_else(|poisoned| poisoned.into_inner())
    }

    pub fn encode(&self, encoder: &mut dyn Encoder) -> Result<()> {
        let state = self.read_state();
        encoder.open_element(ELEM_BINARYIMAGE);
        encoder.write_string(ATTRIB_ARCH, &state.archtype);
        for (addr, vec) in state.chunk.iter() {
            if vec.is_empty() {
                continue;
            }
            encoder.open_element(ELEM_BYTECHUNK);
            let space = addr
                .get_space()
                .ok_or_else(|| Error::Lowlevel("byte chunk with invalid address".to_string()))?;
            space.encode_attributes(encoder, addr.get_offset())?;
            if state.readonlyset.contains(addr) {
                encoder.write_bool(ATTRIB_READONLY, true);
            }
            let mut text = String::from("\n");
            for (index, byte) in vec.iter().enumerate() {
                let _ = write!(text, "{byte:02x}");
                if index % 20 == 19 {
                    text.push('\n');
                }
            }
            text.push('\n');
            encoder.write_string(ATTRIB_CONTENT, &text);
            encoder.close_element(ELEM_BYTECHUNK);
        }
        for (addr, name) in state.addrtosymbol.iter() {
            encoder.open_element(ELEM_SYMBOL);
            let space = addr
                .get_space()
                .ok_or_else(|| Error::Lowlevel("symbol with invalid address".to_string()))?;
            space.encode_attributes(encoder, addr.get_offset())?;
            encoder.write_string(ATTRIB_NAME, name);
            encoder.close_element(ELEM_SYMBOL);
        }
        encoder.close_element(ELEM_BINARYIMAGE);
        Ok(())
    }

    pub fn open(&self, manager: &AddrSpaceManager) -> Result<()> {
        let mut state = self.write_state();
        let mut size: u32 = 0;
        let mut decoder = XmlDecode::with_root(Some(manager), self.rootel.clone(), 0);
        let elem_id = decoder.open_element_expect(ELEM_BINARYIMAGE)?;
        loop {
            let sub_id = decoder.open_element()?;
            if sub_id == 0 {
                break;
            }
            if sub_id == ELEM_SYMBOL {
                let base = decoder.read_space_attr(ATTRIB_SPACE)?;
                let offset = base.decode_attributes(&mut decoder, &mut size)?;
                let addr = Address::new(base, offset);
                let nm = decoder.read_string_attr(ATTRIB_NAME)?;
                state.addrtosymbol.insert(addr, nm);
            } else if sub_id == ELEM_BYTECHUNK {
                let base = decoder.read_space_attr(ATTRIB_SPACE)?;
                let offset = base.decode_attributes(&mut decoder, &mut size)?;
                let addr = Address::new(base, offset);
                let mut vec = Vec::new();
                decoder.rewind_attributes();
                loop {
                    let attrib_id = decoder.get_next_attribute_id()?;
                    if attrib_id == 0 {
                        break;
                    }
                    if attrib_id == ATTRIB_READONLY && decoder.read_bool()? {
                        state.readonlyset.insert(addr.clone());
                    }
                }
                let content = decoder.read_string_attr(ATTRIB_CONTENT)?;
                let bytes = content.as_bytes();
                let mut pos = 0usize;
                let next_char = |pos: &mut usize| -> i32 {
                    if *pos < bytes.len() {
                        let value = bytes[*pos] as i8 as i32;
                        *pos += 1;
                        value
                    } else {
                        -1
                    }
                };
                while pos < bytes.len() && is_stream_space(bytes[pos]) {
                    pos += 1;
                }
                let mut first = next_char(&mut pos);
                let mut second = next_char(&mut pos);
                while first > 0 && second > 0 {
                    let high = hex_digit_value(first);
                    let low = hex_digit_value(second);
                    let val = high.wrapping_mul(16).wrapping_add(low);
                    vec.push(val as u8);
                    while pos < bytes.len() && is_stream_space(bytes[pos]) {
                        pos += 1;
                    }
                    first = next_char(&mut pos);
                    second = next_char(&mut pos);
                }
                state.chunk.insert(addr, vec);
            } else {
                return Err(Error::Lowlevel("Unknown LoadImageXml tag".to_string()));
            }
            decoder.close_element(sub_id)?;
        }
        decoder.close_element(elem_id)?;
        LoadImageXml::pad(&mut state);
        Ok(())
    }

    pub fn clear(&self) {
        let mut state = self.write_state();
        state.archtype.clear();
        state.chunk.clear();
        state.addrtosymbol.clear();
    }

    fn same_space(first: &Address, second: &Address) -> bool {
        match (first.get_space(), second.get_space()) {
            (Some(one), Some(two)) => one.get_index() == two.get_index(),
            (None, None) => true,
            _ => false,
        }
    }

    fn pad(state: &mut LoadImageXmlState) {
        if state.chunk.is_empty() {
            return;
        }
        let keys: Vec<Address> = state.chunk.keys().cloned().collect();
        let mut lastkey = keys[0].clone();
        for key in keys.iter().skip(1) {
            if LoadImageXml::same_space(&lastkey, key) {
                let lastlen = state.chunk[&lastkey].len() as u64;
                let curlen = state.chunk[key].len() as u64;
                let end1 = lastkey.get_offset().wrapping_add(lastlen).wrapping_sub(1);
                let end2 = key.get_offset().wrapping_add(curlen).wrapping_sub(1);
                if end1 >= end2 {
                    state.chunk.remove(key);
                    continue;
                }
            }
            lastkey = key.clone();
        }
        let keys: Vec<Address> = state.chunk.keys().cloned().collect();
        for (index, key) in keys.iter().enumerate() {
            let len = state.chunk[key].len();
            let endaddr = key.add(len as i64);
            if endaddr < *key {
                continue;
            }
            let space = endaddr.get_space().expect("chunk address has a space").clone();
            let mut maxsize: i32 = 512;
            let mut room = space.get_highest().wrapping_sub(endaddr.get_offset()).wrapping_add(1);
            if (maxsize as u64) > room {
                maxsize = room as i32;
            }
            if let Some(nextkey) = keys.get(index + 1)
                && LoadImageXml::same_space(nextkey, &endaddr)
            {
                if endaddr.get_offset() >= nextkey.get_offset() {
                    continue;
                }
                room = nextkey.get_offset() - endaddr.get_offset();
                if (maxsize as u64) > room {
                    maxsize = room as i32;
                }
            }
            let vec = state.chunk.entry(endaddr).or_default();
            for _slot in 0..maxsize {
                vec.push(0);
            }
        }
    }

    pub fn adjust_vma_shared(&self, adjust: i64) {
        let mut state = self.write_state();
        let mut newchunk = BTreeMap::new();
        for (addr, vec) in state.chunk.iter() {
            let space = addr.get_space().expect("chunk address has a space");
            let off = AddrSpace::address_to_byte_int(adjust, space.get_word_size()) as i32;
            newchunk.insert(addr.add(off as i64), vec.clone());
        }
        state.chunk = newchunk;
        let mut newsymbol = BTreeMap::new();
        for (addr, name) in state.addrtosymbol.iter() {
            let space = addr.get_space().expect("symbol address has a space");
            let off = AddrSpace::address_to_byte_int(adjust, space.get_word_size()) as i32;
            newsymbol.insert(addr.add(off as i64), name.clone());
        }
        state.addrtosymbol = newsymbol;
    }
}

impl LoadImage for LoadImageXml {
    fn get_file_name(&self) -> &str {
        &self.filename
    }

    fn load_fill(&self, ptr: &mut [u8], addr: &Address) -> Result<()> {
        let state = self.read_state();
        let mut size = ptr.len() as i32;
        let mut curaddr = addr.clone();
        let mut emptyhit = false;
        let mut outpos = 0usize;
        let mut iter = state.chunk.range(..=curaddr.clone()).next_back();
        if iter.is_none() {
            iter = state.chunk.iter().next();
        }
        let mut current = iter.map(|(key, _)| key.clone());
        while size > 0 {
            let Some(key) = current.clone() else {
                break;
            };
            let chnk = &state.chunk[&key];
            let mut chnksize = chnk.len() as i32;
            let over = curaddr.overlap(0, &key, chnksize);
            if over != -1 {
                if chnksize - over > size {
                    chnksize = over + size;
                }
                for index in over..chnksize {
                    ptr[outpos] = chnk[index as usize];
                    outpos += 1;
                }
                size -= chnksize - over;
                curaddr = curaddr.add((chnksize - over) as i64);
                current = state
                    .chunk
                    .range((std::ops::Bound::Excluded(key), std::ops::Bound::Unbounded))
                    .next()
                    .map(|(next, _)| next.clone());
            } else {
                emptyhit = true;
                break;
            }
        }
        if size > 0 || emptyhit {
            let mut errmsg = String::from("Bytes at ");
            curaddr.print_raw(&mut errmsg);
            errmsg.push_str(" are not mapped");
            return Err(Error::DataUnavail(errmsg));
        }
        Ok(())
    }

    fn open_symbols(&self) {
        let mut state = self.write_state();
        state.cursymbol = state.addrtosymbol.keys().next().cloned();
        state.symbols_open = true;
    }

    fn get_next_symbol(&self, record: &mut LoadImageFunc) -> bool {
        let mut state = self.write_state();
        let Some(key) = state.cursymbol.clone() else {
            return false;
        };
        record.name = state.addrtosymbol[&key].clone();
        record.address = key.clone();
        state.cursymbol = state
            .addrtosymbol
            .range((std::ops::Bound::Excluded(key), std::ops::Bound::Unbounded))
            .next()
            .map(|(next, _)| next.clone());
        true
    }

    fn get_readonly(&self, list: &mut RangeList) {
        let state = self.read_state();
        for (addr, chnk) in state.chunk.iter() {
            if state.readonlyset.contains(addr) {
                let start = addr.get_offset();
                let stop = start.wrapping_add(chnk.len() as u64).wrapping_sub(1);
                let space = addr.get_space().expect("chunk address has a space");
                list.insert_range(space, start, stop);
            }
        }
    }

    fn get_arch_type(&self) -> String {
        self.read_state().archtype.clone()
    }

    fn adjust_vma(&mut self, adjust: i64) {
        self.adjust_vma_shared(adjust);
    }
}

impl AdjustableLoadImage for LoadImageXml {
    fn adjust_vma_shared(&self, adjust: i64) {
        LoadImageXml::adjust_vma_shared(self, adjust);
    }
}
