use std::collections::BTreeMap;

use crate::architecture::Architecture;
use crate::error::{Error, Result};
use crate::istream::{Basefield, extract_u32};
use crate::marshal::{
    ATTRIB_CONSTRUCTOR, ATTRIB_CONTENT, ATTRIB_DESTRUCTOR, AttributeId, Decoder, ELEM_DATA, ELEM_VALUE, ElementId,
    Encoder,
};
use crate::types::{TypeFactory, TypeId, types_of};

pub const ATTRIB_A: AttributeId = AttributeId::new("a", 80);
pub const ATTRIB_B: AttributeId = AttributeId::new("b", 81);
pub const ATTRIB_LENGTH: AttributeId = AttributeId::new("length", 82);
pub const ATTRIB_TAG: AttributeId = AttributeId::new("tag", 83);
pub const ELEM_CONSTANTPOOL: ElementId = ElementId::new("constantpool", 109);
pub const ELEM_CPOOLREC: ElementId = ElementId::new("cpoolrec", 110);
pub const ELEM_REF: ElementId = ElementId::new("ref", 111);
pub const ELEM_TOKEN: ElementId = ElementId::new("token", 112);

#[derive(Clone, Debug, Default)]
pub struct CPoolRecord {
    pub(crate) tag: u32,
    pub(crate) flags: u32,
    pub(crate) token: String,
    pub(crate) value: u64,
    pub(crate) tp: Option<TypeId>,
    pub(crate) byte_data: Option<Vec<u8>>,
    pub(crate) byte_data_len: i32,
}

impl CPoolRecord {
    pub const PRIMITIVE: u32 = 0;
    pub const STRING_LITERAL: u32 = 1;
    pub const CLASS_REFERENCE: u32 = 2;
    pub const POINTER_METHOD: u32 = 3;
    pub const POINTER_FIELD: u32 = 4;
    pub const ARRAY_LENGTH: u32 = 5;
    pub const INSTANCE_OF: u32 = 6;
    pub const CHECK_CAST: u32 = 7;

    pub const IS_CONSTRUCTOR: u32 = 0x1;
    pub const IS_DESTRUCTOR: u32 = 0x2;

    pub const MAX_STRING_SIZE: i64 = 0x100000;

    pub fn new() -> CPoolRecord {
        CPoolRecord {
            tag: 0,
            flags: 0,
            token: String::new(),
            value: 0,
            tp: None,
            byte_data: None,
            byte_data_len: 0,
        }
    }

    pub fn get_tag(&self) -> u32 {
        self.tag
    }

    pub fn get_token(&self) -> &str {
        &self.token
    }

    pub fn get_byte_data(&self) -> Option<&[u8]> {
        self.byte_data.as_deref()
    }

    pub fn get_byte_data_length(&self) -> i32 {
        self.byte_data_len
    }

    pub fn get_type(&self) -> Option<TypeId> {
        self.tp
    }

    pub fn get_value(&self) -> u64 {
        self.value
    }

    pub fn is_constructor(&self) -> bool {
        (self.flags & CPoolRecord::IS_CONSTRUCTOR) != 0
    }

    pub fn is_destructor(&self) -> bool {
        (self.flags & CPoolRecord::IS_DESTRUCTOR) != 0
    }

    pub fn encode(&self, encoder: &mut dyn Encoder, glb: &Architecture) -> Result<()> {
        encoder.open_element(ELEM_CPOOLREC);
        let tag_name = match self.tag {
            CPoolRecord::POINTER_METHOD => "method",
            CPoolRecord::POINTER_FIELD => "field",
            CPoolRecord::INSTANCE_OF => "instanceof",
            CPoolRecord::ARRAY_LENGTH => "arraylength",
            CPoolRecord::CHECK_CAST => "checkcast",
            CPoolRecord::STRING_LITERAL => "string",
            CPoolRecord::CLASS_REFERENCE => "classref",
            _ => "primitive",
        };
        encoder.write_string(ATTRIB_TAG, tag_name);
        if self.is_constructor() {
            encoder.write_bool(ATTRIB_CONSTRUCTOR, true);
        }
        if self.is_destructor() {
            encoder.write_bool(ATTRIB_DESTRUCTOR, true);
        }
        if self.tag == CPoolRecord::PRIMITIVE {
            encoder.open_element(ELEM_VALUE);
            encoder.write_unsigned_integer(ATTRIB_CONTENT, self.value);
            encoder.close_element(ELEM_VALUE);
        }
        if let Some(byte_data) = &self.byte_data {
            encoder.open_element(ELEM_DATA);
            encoder.write_signed_integer(ATTRIB_LENGTH, self.byte_data_len as i64);
            let mut wrap = 0;
            let mut text = String::new();
            for byte in byte_data.iter().take(self.byte_data_len.max(0) as usize) {
                text.push('0');
                text.push(*byte as char);
                text.push(' ');
                wrap += 1;
                if wrap > 15 {
                    text.push('\n');
                    wrap = 0;
                }
            }
            encoder.write_string(ATTRIB_CONTENT, &text);
            encoder.close_element(ELEM_DATA);
        } else {
            encoder.open_element(ELEM_TOKEN);
            encoder.write_string(ATTRIB_CONTENT, &self.token);
            encoder.close_element(ELEM_TOKEN);
        }
        let tp = self.tp.expect("constant pool record without data-type");
        types_of(glb).get(tp).encode_ref(encoder, glb)?;
        encoder.close_element(ELEM_CPOOLREC);
        Ok(())
    }

    pub fn decode(&mut self, decoder: &mut dyn Decoder, glb: &mut Architecture) -> Result<()> {
        self.tag = CPoolRecord::PRIMITIVE;
        self.value = 0;
        self.flags = 0;
        let elem_id = decoder.open_element_expect(ELEM_CPOOLREC)?;
        loop {
            let attrib_id = decoder.get_next_attribute_id()?;
            if attrib_id == 0 {
                break;
            }
            if attrib_id == ATTRIB_TAG {
                let tagstring = decoder.read_string()?;
                match tagstring.as_str() {
                    "method" => self.tag = CPoolRecord::POINTER_METHOD,
                    "field" => self.tag = CPoolRecord::POINTER_FIELD,
                    "instanceof" => self.tag = CPoolRecord::INSTANCE_OF,
                    "arraylength" => self.tag = CPoolRecord::ARRAY_LENGTH,
                    "checkcast" => self.tag = CPoolRecord::CHECK_CAST,
                    "string" => self.tag = CPoolRecord::STRING_LITERAL,
                    "classref" => self.tag = CPoolRecord::CLASS_REFERENCE,
                    _ => {}
                }
            } else if attrib_id == ATTRIB_CONSTRUCTOR {
                if decoder.read_bool()? {
                    self.flags |= CPoolRecord::IS_CONSTRUCTOR;
                }
            } else if attrib_id == ATTRIB_DESTRUCTOR && decoder.read_bool()? {
                self.flags |= CPoolRecord::IS_DESTRUCTOR;
            }
        }
        if self.tag == CPoolRecord::PRIMITIVE {
            let sub_id = decoder.open_element_expect(ELEM_VALUE)?;
            self.value = decoder.read_unsigned_integer_attr(ATTRIB_CONTENT)?;
            decoder.close_element(sub_id)?;
        }
        let sub_id = decoder.open_element()?;
        if sub_id == ELEM_TOKEN {
            self.token = decoder.read_string_attr(ATTRIB_CONTENT)?;
        } else {
            let val = decoder.read_signed_integer_attr(ATTRIB_LENGTH)?;
            if !(0..CPoolRecord::MAX_STRING_SIZE).contains(&val) {
                return Err(Error::Lowlevel("Bad constant pool record: bad <data> size".to_string()));
            }
            self.byte_data_len = val as i32;
            let content = decoder.read_string_attr(ATTRIB_CONTENT)?;
            let mut byte_data = vec![0u8; self.byte_data_len as usize];
            let mut pos = 0usize;
            let mut stream_failed = false;
            for slot in byte_data.iter_mut() {
                if stream_failed {
                    continue;
                }
                match extract_u32(&content[pos..], Basefield::Hex) {
                    Some(extraction) => {
                        pos += extraction.consumed;
                        *slot = extraction.value as u32 as u8;
                        if extraction.failed {
                            stream_failed = true;
                        }
                    }
                    None => stream_failed = true,
                }
            }
            self.byte_data = Some(byte_data);
        }
        decoder.close_element(sub_id)?;
        if self.tag == CPoolRecord::STRING_LITERAL && self.byte_data.is_none() {
            return Err(Error::Lowlevel("Bad constant pool record: missing <data>".to_string()));
        }
        if self.flags != 0 {
            let is_constructor = (self.flags & CPoolRecord::IS_CONSTRUCTOR) != 0;
            let is_destructor = (self.flags & CPoolRecord::IS_DESTRUCTOR) != 0;
            self.tp = Some(TypeFactory::decode_type_with_code_flags(
                glb,
                decoder,
                is_constructor,
                is_destructor,
            )?);
        } else {
            self.tp = Some(TypeFactory::decode_type(glb, decoder)?);
        }
        decoder.close_element(elem_id)
    }
}

pub trait ConstantPool: Send {
    fn create_record(&mut self, refs: &[u64]) -> Result<&mut CPoolRecord>;

    fn get_record(&self, refs: &[u64]) -> Option<&CPoolRecord>;

    fn empty(&self) -> bool;

    fn clear(&mut self);

    fn encode(&self, encoder: &mut dyn Encoder, glb: &Architecture) -> Result<()>;

    fn decode(&mut self, decoder: &mut dyn Decoder, glb: &mut Architecture) -> Result<()>;

    fn put_record(&mut self, refs: &[u64], tag: u32, tok: &str, ct: Option<TypeId>) -> Result<()> {
        let newrec = self.create_record(refs)?;
        newrec.tag = tag;
        newrec.token = tok.to_string();
        newrec.tp = ct;
        Ok(())
    }

    fn decode_record(
        &mut self,
        refs: &[u64],
        decoder: &mut dyn Decoder,
        glb: &mut Architecture,
    ) -> Result<&CPoolRecord> {
        let newrec = self.create_record(refs)?;
        newrec.decode(decoder, glb)?;
        Ok(newrec)
    }
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, PartialOrd, Ord)]
pub struct CheapSorter {
    pub first: u64,
    pub second: u64,
}

impl CheapSorter {
    pub fn new() -> CheapSorter {
        CheapSorter { first: 0, second: 0 }
    }

    pub fn from_refs(refs: &[u64]) -> CheapSorter {
        CheapSorter {
            first: refs[0],
            second: if refs.len() > 1 { refs[1] } else { 0 },
        }
    }

    pub fn apply(&self, refs: &mut Vec<u64>) {
        refs.push(self.first);
        refs.push(self.second);
    }

    pub fn encode(&self, encoder: &mut dyn Encoder) -> Result<()> {
        encoder.open_element(ELEM_REF);
        encoder.write_unsigned_integer(ATTRIB_A, self.first);
        encoder.write_unsigned_integer(ATTRIB_B, self.second);
        encoder.close_element(ELEM_REF);
        Ok(())
    }

    pub fn decode(&mut self, decoder: &mut dyn Decoder) -> Result<()> {
        let elem_id = decoder.open_element_expect(ELEM_REF)?;
        self.first = decoder.read_unsigned_integer_attr(ATTRIB_A)?;
        self.second = decoder.read_unsigned_integer_attr(ATTRIB_B)?;
        decoder.close_element(elem_id)
    }
}

#[derive(Default)]
pub struct ConstantPoolInternal {
    cpool_map: BTreeMap<CheapSorter, CPoolRecord>,
}

impl ConstantPoolInternal {
    pub fn new() -> ConstantPoolInternal {
        ConstantPoolInternal {
            cpool_map: BTreeMap::new(),
        }
    }
}

impl ConstantPool for ConstantPoolInternal {
    fn create_record(&mut self, refs: &[u64]) -> Result<&mut CPoolRecord> {
        let sorter = CheapSorter::from_refs(refs);
        if let Some(existing) = self.cpool_map.get(&sorter) {
            return Err(Error::Lowlevel(format!(
                "Creating duplicate entry in constant pool: {}",
                existing.get_token()
            )));
        }
        Ok(self.cpool_map.entry(sorter).or_default())
    }

    fn get_record(&self, refs: &[u64]) -> Option<&CPoolRecord> {
        let sorter = CheapSorter::from_refs(refs);
        self.cpool_map.get(&sorter)
    }

    fn empty(&self) -> bool {
        self.cpool_map.is_empty()
    }

    fn clear(&mut self) {
        self.cpool_map.clear();
    }

    fn encode(&self, encoder: &mut dyn Encoder, glb: &Architecture) -> Result<()> {
        encoder.open_element(ELEM_CONSTANTPOOL);
        for (sorter, record) in self.cpool_map.iter() {
            sorter.encode(encoder)?;
            record.encode(encoder, glb)?;
        }
        encoder.close_element(ELEM_CONSTANTPOOL);
        Ok(())
    }

    fn decode(&mut self, decoder: &mut dyn Decoder, glb: &mut Architecture) -> Result<()> {
        let elem_id = decoder.open_element_expect(ELEM_CONSTANTPOOL)?;
        while decoder.peek_element()? != 0 {
            let mut sorter = CheapSorter::new();
            sorter.decode(decoder)?;
            let mut refs = Vec::new();
            sorter.apply(&mut refs);
            let newrec = self.create_record(&refs)?;
            newrec.decode(decoder, glb)?;
        }
        decoder.close_element(elem_id)
    }
}
