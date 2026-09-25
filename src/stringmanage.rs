use std::collections::BTreeMap;
use std::fmt::Write as _;

use crate::address::{Address, mostsigbit_set};
use crate::crc32::crc_update;
use crate::error::{Error, Result};
use crate::loadimage::LoadImage;
use crate::marshal::{ATTRIB_CONTENT, AttributeId, Decoder, ElementId, Encoder};
use crate::translate::AddrSpaceManager;
use crate::types::{TypeFactory, TypeId};

pub const ATTRIB_TRUNC: AttributeId = AttributeId::new("trunc", 69);
pub const ELEM_BYTES: ElementId = ElementId::new("bytes", 83);
pub const ELEM_STRING: ElementId = ElementId::new("string", 84);
pub const ELEM_STRINGMANAGE: ElementId = ElementId::new("stringmanage", 85);

#[derive(Clone, Debug, Default)]
pub struct StringData {
    pub is_truncated: bool,
    pub byte_data: Vec<u8>,
}

#[derive(Clone, Debug, Default)]
pub struct StringManagerBase {
    pub string_map: BTreeMap<Address, StringData>,
    pub maximum_chars: i32,
}

fn byte_at(buf: &[u8], index: usize) -> u8 {
    buf.get(index).copied().unwrap_or(0)
}

fn is_space_char(byte: i32) -> bool {
    matches!(byte, 0x20 | 0x09 | 0x0a | 0x0b | 0x0c | 0x0d)
}

impl StringManagerBase {
    pub fn new(max: i32) -> StringManagerBase {
        StringManagerBase {
            string_map: BTreeMap::new(),
            maximum_chars: max,
        }
    }

    pub fn calc_internal_hash(addr: &Address, buf: &[u8], size: i32) -> u64 {
        let mut reg: u32 = 0x7b7c66a9;
        for index in 0..size.max(0) as usize {
            reg = crc_update(reg, byte_at(buf, index) as u32);
        }
        let mut res = addr.get_offset();
        res ^= (reg as u64) << 32;
        res
    }

    pub fn has_char_terminator(buffer: &[u8], size: i32, charsize: i32) -> bool {
        let mut index = 0;
        while index < size {
            let mut is_terminator = true;
            for inner in 0..charsize {
                if byte_at(buffer, (index + inner) as usize) != 0 {
                    is_terminator = false;
                    break;
                }
            }
            if is_terminator {
                return true;
            }
            index += charsize;
        }
        false
    }

    pub fn read_utf16(buf: &[u8], bigend: bool) -> i32 {
        let mut codepoint: i32;
        if bigend {
            codepoint = byte_at(buf, 0) as i32;
            codepoint <<= 8;
            codepoint += byte_at(buf, 1) as i32;
        } else {
            codepoint = byte_at(buf, 1) as i32;
            codepoint <<= 8;
            codepoint += byte_at(buf, 0) as i32;
        }
        codepoint
    }

    pub fn write_utf8(out: &mut Vec<u8>, codepoint: i32) -> Result<()> {
        if codepoint < 0 {
            return Err(Error::Lowlevel("Negative unicode codepoint".to_string()));
        }
        if codepoint < 128 {
            out.push(codepoint as u8);
            return Ok(());
        }
        let bits = mostsigbit_set(codepoint as u64) + 1;
        if bits > 21 {
            return Err(Error::Lowlevel("Bad unicode codepoint".to_string()));
        }
        if bits < 12 {
            out.push(0xc0 ^ ((codepoint >> 6) & 0x1f) as u8);
            out.push(0x80 ^ (codepoint & 0x3f) as u8);
        } else if bits < 17 {
            out.push(0xe0 ^ ((codepoint >> 12) & 0xf) as u8);
            out.push(0x80 ^ ((codepoint >> 6) & 0x3f) as u8);
            out.push(0x80 ^ (codepoint & 0x3f) as u8);
        } else {
            out.push(0xf0 ^ ((codepoint >> 18) & 7) as u8);
            out.push(0x80 ^ ((codepoint >> 12) & 0x3f) as u8);
            out.push(0x80 ^ ((codepoint >> 6) & 0x3f) as u8);
            out.push(0x80 ^ (codepoint & 0x3f) as u8);
        }
        Ok(())
    }

    pub fn check_characters(buf: &[u8], size: i32, charsize: i32, bigend: bool) -> i32 {
        let mut index = 0;
        let mut count = 0;
        let mut skip = charsize;
        while index < size {
            let codepoint =
                StringManagerBase::get_codepoint(&buf[(index as usize).min(buf.len())..], charsize, bigend, &mut skip);
            if codepoint < 0 {
                return -1;
            }
            if codepoint == 0 {
                break;
            }
            count += 1;
            index += skip;
        }
        count
    }

    pub fn get_codepoint(buf: &[u8], charsize: i32, bigend: bool, skip: &mut i32) -> i32 {
        let mut codepoint: i32;
        let mut sk = 0;
        if charsize == 2 {
            codepoint = StringManagerBase::read_utf16(buf, bigend);
            sk += 2;
            if (0xD800..=0xDBFF).contains(&codepoint) {
                let trail = StringManagerBase::read_utf16(&buf[2.min(buf.len())..], bigend);
                sk += 2;
                if !(0xDC00..=0xDFFF).contains(&trail) {
                    return -1;
                }
                codepoint = (codepoint << 10) + trail + (0x10000 - (0xD800 << 10) - 0xDC00);
            } else if (0xDC00..=0xDFFF).contains(&codepoint) {
                return -1;
            }
        } else if charsize == 1 {
            let val = byte_at(buf, 0) as i32;
            if (val & 0x80) == 0 {
                codepoint = val;
                sk = 1;
            } else if (val & 0xe0) == 0xc0 {
                let val2 = byte_at(buf, 1) as i32;
                sk = 2;
                if (val2 & 0xc0) != 0x80 {
                    return -1;
                }
                codepoint = ((val & 0x1f) << 6) | (val2 & 0x3f);
            } else if (val & 0xf0) == 0xe0 {
                let val2 = byte_at(buf, 1) as i32;
                let val3 = byte_at(buf, 2) as i32;
                sk = 3;
                if (val2 & 0xc0) != 0x80 || (val3 & 0xc0) != 0x80 {
                    return -1;
                }
                codepoint = ((val & 0xf) << 12) | ((val2 & 0x3f) << 6) | (val3 & 0x3f);
            } else if (val & 0xf8) == 0xf0 {
                let val2 = byte_at(buf, 1) as i32;
                let val3 = byte_at(buf, 2) as i32;
                let val4 = byte_at(buf, 3) as i32;
                sk = 4;
                if (val2 & 0xc0) != 0x80 || (val3 & 0xc0) != 0x80 || (val4 & 0xc0) != 0x80 {
                    return -1;
                }
                codepoint = ((val & 7) << 18) | ((val2 & 0x3f) << 12) | ((val3 & 0x3f) << 6) | (val4 & 0x3f);
            } else {
                return -1;
            }
        } else if charsize == 4 {
            sk = 4;
            let bytes = [byte_at(buf, 0), byte_at(buf, 1), byte_at(buf, 2), byte_at(buf, 3)];
            if bigend {
                codepoint = i32::from_be_bytes(bytes);
            } else {
                codepoint = i32::from_le_bytes(bytes);
            }
        } else {
            return -1;
        }
        if codepoint >= 0xd800 {
            if codepoint > 0x10ffff {
                return -1;
            }
            if codepoint <= 0xdfff {
                return -1;
            }
        }
        *skip = sk;
        codepoint
    }

    pub fn write_unicode_with(
        maximum_chars: i32,
        out: &mut Vec<u8>,
        buffer: &[u8],
        size: i32,
        charsize: i32,
        bigend: bool,
    ) -> Result<bool> {
        let mut index = 0;
        let mut count = 0;
        let mut skip = charsize;
        while index < size {
            let codepoint = StringManagerBase::get_codepoint(
                &buffer[(index as usize).min(buffer.len())..],
                charsize,
                bigend,
                &mut skip,
            );
            if codepoint < 0 {
                return Ok(false);
            }
            if codepoint == 0 {
                break;
            }
            StringManagerBase::write_utf8(out, codepoint)?;
            index += skip;
            count += 1;
            if count >= maximum_chars {
                break;
            }
        }
        Ok(true)
    }

    pub fn assign_string_data_with(
        maximum_chars: i32,
        data: &mut StringData,
        buf: &[u8],
        size: i32,
        charsize: i32,
        num_chars: i32,
        bigend: bool,
    ) -> Result<()> {
        if charsize == 1 && num_chars < maximum_chars {
            data.byte_data = (0..size.max(0) as usize).map(|index| byte_at(buf, index)).collect();
        } else {
            let mut bytes: Vec<u8> = Vec::new();
            if !StringManagerBase::write_unicode_with(maximum_chars, &mut bytes, buf, size, charsize, bigend)? {
                return Ok(());
            }
            data.byte_data = bytes;
            data.byte_data.push(0);
        }
        data.is_truncated = num_chars >= maximum_chars;
        Ok(())
    }
}

pub trait StringManager: Send {
    fn base(&self) -> &StringManagerBase;

    fn base_mut(&mut self) -> &mut StringManagerBase;

    fn get_string_data(
        &mut self,
        addr: &Address,
        char_type: TypeId,
        types: &TypeFactory,
        loader: &dyn LoadImage,
    ) -> Result<(&Vec<u8>, bool)>;

    fn write_unicode(&self, out: &mut Vec<u8>, buffer: &[u8], size: i32, charsize: i32, bigend: bool) -> Result<bool> {
        StringManagerBase::write_unicode_with(self.base().maximum_chars, out, buffer, size, charsize, bigend)
    }

    fn assign_string_data(
        &self,
        data: &mut StringData,
        buf: &[u8],
        size: i32,
        charsize: i32,
        num_chars: i32,
        bigend: bool,
    ) -> Result<()> {
        StringManagerBase::assign_string_data_with(
            self.base().maximum_chars,
            data,
            buf,
            size,
            charsize,
            num_chars,
            bigend,
        )
    }

    fn clear(&mut self) {
        self.base_mut().string_map.clear();
    }

    fn is_string(
        &mut self,
        addr: &Address,
        char_type: TypeId,
        types: &TypeFactory,
        loader: &dyn LoadImage,
    ) -> Result<bool> {
        let (buffer, _) = self.get_string_data(addr, char_type, types, loader)?;
        Ok(!buffer.is_empty())
    }

    fn register_internal_string_data(
        &mut self,
        addr: &Address,
        buf: &[u8],
        size: i32,
        char_type: TypeId,
        types: &TypeFactory,
        manager: &AddrSpaceManager,
    ) -> Result<u64> {
        let charsize = types.get(char_type).get_size();
        let num_chars = StringManagerBase::check_characters(buf, size, charsize, addr.is_big_endian());
        if num_chars < 0 {
            return Ok(0);
        }
        let hash = StringManagerBase::calc_internal_hash(addr, buf, size);
        let const_addr = manager.get_constant(hash);
        let maximum_chars = self.base().maximum_chars;
        let string_data = self.base_mut().string_map.entry(const_addr).or_default();
        string_data.byte_data.clear();
        string_data.is_truncated = false;
        StringManagerBase::assign_string_data_with(
            maximum_chars,
            string_data,
            buf,
            size,
            charsize,
            num_chars,
            addr.is_big_endian(),
        )?;
        Ok(hash)
    }

    fn encode(&self, encoder: &mut dyn Encoder) -> Result<()> {
        encoder.open_element(ELEM_STRINGMANAGE);
        for (addr, string_data) in self.base().string_map.iter() {
            encoder.open_element(ELEM_STRING);
            addr.encode(encoder)?;
            encoder.open_element(ELEM_BYTES);
            encoder.write_bool(ATTRIB_TRUNC, string_data.is_truncated);
            let mut text = String::new();
            text.push('\n');
            for (index, byte) in string_data.byte_data.iter().enumerate() {
                let _ = write!(text, "{:02x}", byte);
                if index % 20 == 19 {
                    text.push_str("\n  ");
                }
            }
            text.push('\n');
            encoder.write_string(ATTRIB_CONTENT, &text);
            encoder.close_element(ELEM_BYTES);
        }
        encoder.close_element(ELEM_STRINGMANAGE);
        Ok(())
    }

    fn decode(&mut self, decoder: &mut dyn Decoder) -> Result<()> {
        let elem_id = decoder.open_element_expect(ELEM_STRINGMANAGE)?;
        loop {
            let sub_id = decoder.open_element()?;
            if sub_id != ELEM_STRING {
                break;
            }
            let addr = Address::decode(decoder)?;
            let sub_id2 = decoder.open_element_expect(ELEM_BYTES)?;
            let is_truncated = decoder.read_bool_attr(ATTRIB_TRUNC)?;
            let content = decoder.read_string_attr(ATTRIB_CONTENT)?;
            let string_data = self.base_mut().string_map.entry(addr).or_default();
            string_data.is_truncated = is_truncated;
            let bytes = content.as_bytes();
            let mut pos = 0usize;
            let next_char = |pos: &mut usize| -> i32 {
                if *pos < bytes.len() {
                    let byte = bytes[*pos];
                    *pos += 1;
                    byte as i32
                } else {
                    -1
                }
            };
            let skip_space = |pos: &mut usize| {
                while *pos < bytes.len() && is_space_char(bytes[*pos] as i32) {
                    *pos += 1;
                }
            };
            skip_space(&mut pos);
            let mut c1 = next_char(&mut pos) as i8;
            let mut c2 = next_char(&mut pos) as i8;
            while c1 > 0 && c2 > 0 {
                if c1 <= b'9' as i8 {
                    c1 = c1.wrapping_sub(b'0' as i8);
                } else if c1 <= b'F' as i8 {
                    c1 = c1.wrapping_add(10).wrapping_sub(b'A' as i8);
                } else {
                    c1 = c1.wrapping_add(10).wrapping_sub(b'a' as i8);
                }
                if c2 <= b'9' as i8 {
                    c2 = c2.wrapping_sub(b'0' as i8);
                } else if c2 <= b'F' as i8 {
                    c2 = c2.wrapping_add(10).wrapping_sub(b'A' as i8);
                } else {
                    c2 = c2.wrapping_add(10).wrapping_sub(b'a' as i8);
                }
                let val = (c1 as i32) * 16 + (c2 as i32);
                string_data.byte_data.push(val as u8);
                skip_space(&mut pos);
                c1 = next_char(&mut pos) as i8;
                c2 = next_char(&mut pos) as i8;
            }
            decoder.close_element(sub_id2)?;
            decoder.close_element(sub_id)?;
        }
        decoder.close_element(elem_id)
    }
}

pub struct StringManagerUnicode {
    base: StringManagerBase,
    test_buffer: Vec<u8>,
}

impl StringManagerUnicode {
    pub fn new(max: i32) -> StringManagerUnicode {
        StringManagerUnicode {
            base: StringManagerBase::new(max),
            test_buffer: vec![0u8; max.max(0) as usize],
        }
    }

    fn fill_test_buffer(&mut self, addr: &Address, charsize: i32, loader: &dyn LoadImage) -> Result<Option<i32>> {
        let maximum_chars = self.base.maximum_chars;
        let mut cur_buffer_size: i32 = 0;
        loop {
            let mut amount: i32 = 32;
            let mut new_buffer_size = (cur_buffer_size + amount) as u32;
            if new_buffer_size > maximum_chars as u32 {
                new_buffer_size = maximum_chars as u32;
                amount = new_buffer_size as i32 - cur_buffer_size;
                if amount == 0 {
                    return Ok(None);
                }
            }
            let start = cur_buffer_size as usize;
            let end = start + amount as usize;
            match loader.load_fill(&mut self.test_buffer[start..end], &addr.add(cur_buffer_size as i64)) {
                Ok(()) => {}
                Err(Error::DataUnavail(_)) => return Ok(None),
                Err(err) => return Err(err),
            }
            let found_terminator = StringManagerBase::has_char_terminator(&self.test_buffer[start..], amount, charsize);
            cur_buffer_size = new_buffer_size as i32;
            if found_terminator {
                return Ok(Some(cur_buffer_size));
            }
        }
    }
}

impl StringManager for StringManagerUnicode {
    fn base(&self) -> &StringManagerBase {
        &self.base
    }

    fn base_mut(&mut self) -> &mut StringManagerBase {
        &mut self.base
    }

    fn get_string_data(
        &mut self,
        addr: &Address,
        char_type: TypeId,
        types: &TypeFactory,
        loader: &dyn LoadImage,
    ) -> Result<(&Vec<u8>, bool)> {
        if self.base.string_map.contains_key(addr) {
            let string_data = &self.base.string_map[addr];
            return Ok((&string_data.byte_data, string_data.is_truncated));
        }
        let string_data = self.base.string_map.entry(addr.clone()).or_default();
        string_data.is_truncated = false;
        let char_dt = types.get(char_type);
        if char_dt.is_opaque_string() {
            let string_data = &self.base.string_map[addr];
            return Ok((&string_data.byte_data, false));
        }
        let charsize = char_dt.get_size();
        let cur_buffer_size = self.fill_test_buffer(addr, charsize, loader)?;
        let Some(cur_buffer_size) = cur_buffer_size else {
            let string_data = &self.base.string_map[addr];
            return Ok((&string_data.byte_data, false));
        };
        let num_chars =
            StringManagerBase::check_characters(&self.test_buffer, cur_buffer_size, charsize, addr.is_big_endian());
        if num_chars < 0 {
            let string_data = &self.base.string_map[addr];
            return Ok((&string_data.byte_data, false));
        }
        let maximum_chars = self.base.maximum_chars;
        let string_data = self.base.string_map.get_mut(addr).expect("string data entry");
        StringManagerBase::assign_string_data_with(
            maximum_chars,
            string_data,
            &self.test_buffer,
            cur_buffer_size,
            charsize,
            num_chars,
            addr.is_big_endian(),
        )?;
        let string_data = &self.base.string_map[addr];
        Ok((&string_data.byte_data, string_data.is_truncated))
    }
}
