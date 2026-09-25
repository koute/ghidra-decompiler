use std::collections::HashMap;
use std::fmt::Write as _;
use std::sync::{Arc, OnceLock};

use crate::error::{Error, Result};
use crate::istream::{self, Basefield};
use crate::marshal_registry::{ATTRIBUTE_IDS, ELEMENT_IDS};
use crate::opcodes::{OpCode, get_opcode, get_opname};
use crate::pcoderaw::VarnodeData;
use crate::space::{AddrSpace, SpaceRef, SpaceType};
use crate::translate::{AddrSpaceManager, Translate};
use crate::xml::{self, Document, Element, a_v, a_v_b, a_v_i, a_v_u, xml_escape, xml_readbool};

#[derive(Clone, Copy, Debug)]
pub struct AttributeId {
    name: &'static str,
    id: u32,
}

impl AttributeId {
    pub const fn new(name: &'static str, id: u32) -> AttributeId {
        AttributeId { name, id }
    }

    pub fn get_name(&self) -> &'static str {
        self.name
    }

    pub fn get_id(&self) -> u32 {
        self.id
    }

    pub fn find(nm: &str, scope: i32) -> u32 {
        if scope == 0
            && let Some(id) = attribute_lookup().get(nm)
        {
            return *id;
        }
        ATTRIB_UNKNOWN.id
    }
}

impl PartialEq for AttributeId {
    fn eq(&self, other: &AttributeId) -> bool {
        self.id == other.id
    }
}

impl Eq for AttributeId {}

impl PartialEq<u32> for AttributeId {
    fn eq(&self, other: &u32) -> bool {
        self.id == *other
    }
}

impl PartialEq<AttributeId> for u32 {
    fn eq(&self, other: &AttributeId) -> bool {
        *self == other.id
    }
}

#[derive(Clone, Copy, Debug)]
pub struct ElementId {
    name: &'static str,
    id: u32,
}

impl ElementId {
    pub const fn new(name: &'static str, id: u32) -> ElementId {
        ElementId { name, id }
    }

    pub fn get_name(&self) -> &'static str {
        self.name
    }

    pub fn get_id(&self) -> u32 {
        self.id
    }

    pub fn find(nm: &str, scope: i32) -> u32 {
        if scope == 0
            && let Some(id) = element_lookup().get(nm)
        {
            return *id;
        }
        ELEM_UNKNOWN.id
    }
}

impl PartialEq for ElementId {
    fn eq(&self, other: &ElementId) -> bool {
        self.id == other.id
    }
}

impl Eq for ElementId {}

impl PartialEq<u32> for ElementId {
    fn eq(&self, other: &u32) -> bool {
        self.id == *other
    }
}

impl PartialEq<ElementId> for u32 {
    fn eq(&self, other: &ElementId) -> bool {
        *self == other.id
    }
}

fn attribute_lookup() -> &'static HashMap<&'static str, u32> {
    static LOOKUP: OnceLock<HashMap<&'static str, u32>> = OnceLock::new();
    LOOKUP.get_or_init(|| ATTRIBUTE_IDS.iter().map(|attrib| (attrib.name, attrib.id)).collect())
}

fn element_lookup() -> &'static HashMap<&'static str, u32> {
    static LOOKUP: OnceLock<HashMap<&'static str, u32>> = OnceLock::new();
    LOOKUP.get_or_init(|| ELEMENT_IDS.iter().map(|elem| (elem.name, elem.id)).collect())
}

pub const ATTRIB_CONTENT: AttributeId = AttributeId::new("XMLcontent", 1);
pub const ATTRIB_ALIGN: AttributeId = AttributeId::new("align", 2);
pub const ATTRIB_BIGENDIAN: AttributeId = AttributeId::new("bigendian", 3);
pub const ATTRIB_CONSTRUCTOR: AttributeId = AttributeId::new("constructor", 4);
pub const ATTRIB_DESTRUCTOR: AttributeId = AttributeId::new("destructor", 5);
pub const ATTRIB_EXTRAPOP: AttributeId = AttributeId::new("extrapop", 6);
pub const ATTRIB_FORMAT: AttributeId = AttributeId::new("format", 7);
pub const ATTRIB_HIDDENRETPARM: AttributeId = AttributeId::new("hiddenretparm", 8);
pub const ATTRIB_ID: AttributeId = AttributeId::new("id", 9);
pub const ATTRIB_INDEX: AttributeId = AttributeId::new("index", 10);
pub const ATTRIB_INDIRECTSTORAGE: AttributeId = AttributeId::new("indirectstorage", 11);
pub const ATTRIB_METATYPE: AttributeId = AttributeId::new("metatype", 12);
pub const ATTRIB_MODEL: AttributeId = AttributeId::new("model", 13);
pub const ATTRIB_NAME: AttributeId = AttributeId::new("name", 14);
pub const ATTRIB_NAMELOCK: AttributeId = AttributeId::new("namelock", 15);
pub const ATTRIB_OFFSET: AttributeId = AttributeId::new("offset", 16);
pub const ATTRIB_READONLY: AttributeId = AttributeId::new("readonly", 17);
pub const ATTRIB_REF: AttributeId = AttributeId::new("ref", 18);
pub const ATTRIB_SIZE: AttributeId = AttributeId::new("size", 19);
pub const ATTRIB_SPACE: AttributeId = AttributeId::new("space", 20);
pub const ATTRIB_THISPTR: AttributeId = AttributeId::new("thisptr", 21);
pub const ATTRIB_TYPE: AttributeId = AttributeId::new("type", 22);
pub const ATTRIB_TYPELOCK: AttributeId = AttributeId::new("typelock", 23);
pub const ATTRIB_VAL: AttributeId = AttributeId::new("val", 24);
pub const ATTRIB_VALUE: AttributeId = AttributeId::new("value", 25);
pub const ATTRIB_WORDSIZE: AttributeId = AttributeId::new("wordsize", 26);
pub const ATTRIB_STORAGE: AttributeId = AttributeId::new("storage", 149);
pub const ATTRIB_STACKSPILL: AttributeId = AttributeId::new("stackspill", 150);
pub const ATTRIB_UNKNOWN: AttributeId = AttributeId::new("XMLunknown", 159);

pub const ELEM_DATA: ElementId = ElementId::new("data", 1);
pub const ELEM_INPUT: ElementId = ElementId::new("input", 2);
pub const ELEM_OFF: ElementId = ElementId::new("off", 3);
pub const ELEM_OUTPUT: ElementId = ElementId::new("output", 4);
pub const ELEM_RETURNADDRESS: ElementId = ElementId::new("returnaddress", 5);
pub const ELEM_SYMBOL: ElementId = ElementId::new("symbol", 6);
pub const ELEM_TARGET: ElementId = ElementId::new("target", 7);
pub const ELEM_VAL: ElementId = ElementId::new("val", 8);
pub const ELEM_VALUE: ElementId = ElementId::new("value", 9);
pub const ELEM_VOID: ElementId = ElementId::new("void", 10);
pub const ELEM_UNKNOWN: ElementId = ElementId::new("XMLunknown", 291);

pub trait Decoder {
    fn get_addr_space_manager(&self) -> Option<&AddrSpaceManager>;

    fn get_translate(&self) -> Option<&dyn Translate>;

    fn ingest_stream(&mut self, data: &[u8]) -> Result<()>;

    fn peek_element(&mut self) -> Result<u32>;

    fn open_element(&mut self) -> Result<u32>;

    fn open_element_expect(&mut self, elem_id: ElementId) -> Result<u32>;

    fn close_element(&mut self, id: u32) -> Result<()>;

    fn close_element_skipping(&mut self, id: u32) -> Result<()>;

    fn get_next_attribute_id(&mut self) -> Result<u32>;

    fn get_indexed_attribute_id(&mut self, attrib_id: AttributeId) -> Result<u32>;

    fn rewind_attributes(&mut self);

    fn read_bool(&mut self) -> Result<bool>;

    fn read_bool_attr(&mut self, attrib_id: AttributeId) -> Result<bool>;

    fn read_signed_integer(&mut self) -> Result<i64>;

    fn read_signed_integer_attr(&mut self, attrib_id: AttributeId) -> Result<i64>;

    fn read_signed_integer_expect_string(&mut self, expect: &str, expectval: i64) -> Result<i64>;

    fn read_signed_integer_expect_string_attr(
        &mut self,
        attrib_id: AttributeId,
        expect: &str,
        expectval: i64,
    ) -> Result<i64>;

    fn read_unsigned_integer(&mut self) -> Result<u64>;

    fn read_unsigned_integer_attr(&mut self, attrib_id: AttributeId) -> Result<u64>;

    fn read_string(&mut self) -> Result<String>;

    fn read_string_attr(&mut self, attrib_id: AttributeId) -> Result<String>;

    fn read_space(&mut self) -> Result<SpaceRef>;

    fn read_space_attr(&mut self, attrib_id: AttributeId) -> Result<SpaceRef>;

    fn read_opcode(&mut self) -> Result<OpCode>;

    fn read_opcode_attr(&mut self, attrib_id: AttributeId) -> Result<OpCode>;

    fn skip_element(&mut self) -> Result<()> {
        let elem_id = self.open_element()?;
        self.close_element_skipping(elem_id)
    }

    fn manager(&self) -> Result<&AddrSpaceManager> {
        self.get_addr_space_manager()
            .ok_or_else(|| Error::Decoder("decoder has no address space manager".to_string()))
    }

    fn get_register(&self, nm: &str) -> Result<VarnodeData> {
        match self.get_translate() {
            Some(trans) => trans.get_register(nm),
            None => Err(Error::Lowlevel(format!(
                "no register table for resolving register {nm}"
            ))),
        }
    }
}

pub trait Encoder {
    fn open_element(&mut self, elem_id: ElementId);

    fn close_element(&mut self, elem_id: ElementId);

    fn write_bool(&mut self, attrib_id: AttributeId, val: bool);

    fn write_signed_integer(&mut self, attrib_id: AttributeId, val: i64);

    fn write_unsigned_integer(&mut self, attrib_id: AttributeId, val: u64);

    fn write_string(&mut self, attrib_id: AttributeId, val: &str);

    fn write_string_indexed(&mut self, attrib_id: AttributeId, index: u32, val: &str);

    fn write_space(&mut self, attrib_id: AttributeId, spc: &AddrSpace);

    fn write_opcode(&mut self, attrib_id: AttributeId, opc: OpCode);
}

pub struct XmlDecode<'a> {
    manager: Option<&'a AddrSpaceManager>,
    translate: Option<&'a dyn Translate>,
    document: Option<Arc<Document>>,
    root_element: Option<Arc<Element>>,
    el_stack: Vec<Arc<Element>>,
    iter_stack: Vec<usize>,
    attribute_index: i32,
    scope: i32,
}

impl<'a> XmlDecode<'a> {
    pub fn new(manager: Option<&'a AddrSpaceManager>, scope: i32) -> XmlDecode<'a> {
        XmlDecode {
            manager,
            translate: None,
            document: None,
            root_element: None,
            el_stack: Vec::new(),
            iter_stack: Vec::new(),
            attribute_index: -1,
            scope,
        }
    }

    pub fn with_root(manager: Option<&'a AddrSpaceManager>, root: Arc<Element>, scope: i32) -> XmlDecode<'a> {
        let mut decoder = XmlDecode::new(manager, scope);
        decoder.root_element = Some(root);
        decoder
    }

    pub fn set_translate(&mut self, translate: Option<&'a dyn Translate>) {
        self.translate = translate;
    }

    pub fn get_document(&self) -> Option<&Arc<Document>> {
        self.document.as_ref()
    }

    pub fn get_current_xml_element(&self) -> Option<&Arc<Element>> {
        self.el_stack.last()
    }

    fn current(&self) -> &Arc<Element> {
        self.el_stack.last().expect("no open element in decoder")
    }

    fn current_attribute_value(&self) -> &str {
        self.current().get_attribute_value_index(self.attribute_index)
    }

    fn find_matching_attribute(el: &Element, attrib_name: &str) -> Result<i32> {
        for slot in 0..el.get_num_attributes() {
            if el.get_attribute_name(slot) == attrib_name {
                return Ok(slot);
            }
        }
        Err(Error::Decoder(format!("Attribute missing: {attrib_name}")))
    }

    fn attribute_text(&self, attrib_id: AttributeId) -> Result<String> {
        let el = self.current();
        if attrib_id == ATTRIB_CONTENT {
            return Ok(el.get_content().to_string());
        }
        let index = XmlDecode::find_matching_attribute(el, attrib_id.get_name())?;
        Ok(el.get_attribute_value_index(index).to_string())
    }

    fn lookup_space(&self, nm: &str) -> Result<SpaceRef> {
        let manager = self.manager()?;
        manager
            .get_space_by_name(nm)
            .ok_or_else(|| Error::Decoder(format!("Unknown address space name: {nm}")))
    }
}

impl Decoder for XmlDecode<'_> {
    fn get_addr_space_manager(&self) -> Option<&AddrSpaceManager> {
        self.manager
    }

    fn get_translate(&self) -> Option<&dyn Translate> {
        self.translate
    }

    fn ingest_stream(&mut self, data: &[u8]) -> Result<()> {
        let doc = Arc::new(xml::xml_tree(data)?);
        self.root_element = Some(doc.get_root().clone());
        self.document = Some(doc);
        Ok(())
    }

    fn peek_element(&mut self) -> Result<u32> {
        let el = match self.el_stack.last() {
            None => match &self.root_element {
                None => return Ok(0),
                Some(root) => root.clone(),
            },
            Some(parent) => {
                let position = *self.iter_stack.last().expect("iterator stack mismatch");
                match parent.get_children().get(position) {
                    None => return Ok(0),
                    Some(child) => child.clone(),
                }
            }
        };
        Ok(ElementId::find(el.get_name(), self.scope))
    }

    fn open_element(&mut self) -> Result<u32> {
        let el = match self.el_stack.last() {
            None => match self.root_element.take() {
                None => return Ok(0),
                Some(root) => root,
            },
            Some(parent) => {
                let position = *self.iter_stack.last().expect("iterator stack mismatch");
                match parent.get_children().get(position) {
                    None => return Ok(0),
                    Some(child) => {
                        let child = child.clone();
                        *self.iter_stack.last_mut().expect("iterator stack mismatch") += 1;
                        child
                    }
                }
            }
        };
        let id = ElementId::find(el.get_name(), self.scope);
        self.el_stack.push(el);
        self.iter_stack.push(0);
        self.attribute_index = -1;
        Ok(id)
    }

    fn open_element_expect(&mut self, elem_id: ElementId) -> Result<u32> {
        let el = match self.el_stack.last() {
            None => match self.root_element.take() {
                None => {
                    return Err(Error::Decoder(format!(
                        "Expecting <{}> but reached end of document",
                        elem_id.get_name()
                    )));
                }
                Some(root) => root,
            },
            Some(parent) => {
                let position = *self.iter_stack.last().expect("iterator stack mismatch");
                match parent.get_children().get(position) {
                    Some(child) => {
                        let child = child.clone();
                        *self.iter_stack.last_mut().expect("iterator stack mismatch") += 1;
                        child
                    }
                    None => {
                        return Err(Error::Decoder(format!(
                            "Expecting <{}> but no remaining children in current element",
                            elem_id.get_name()
                        )));
                    }
                }
            }
        };
        if el.get_name() != elem_id.get_name() {
            return Err(Error::Decoder(format!(
                "Expecting <{}> but got <{}>",
                elem_id.get_name(),
                el.get_name()
            )));
        }
        self.el_stack.push(el);
        self.iter_stack.push(0);
        self.attribute_index = -1;
        Ok(elem_id.get_id())
    }

    fn close_element(&mut self, _id: u32) -> Result<()> {
        self.el_stack.pop();
        self.iter_stack.pop();
        self.attribute_index = 1000;
        Ok(())
    }

    fn close_element_skipping(&mut self, _id: u32) -> Result<()> {
        self.el_stack.pop();
        self.iter_stack.pop();
        self.attribute_index = 1000;
        Ok(())
    }

    fn get_next_attribute_id(&mut self) -> Result<u32> {
        let el = self.current();
        let next_index = self.attribute_index + 1;
        if next_index < el.get_num_attributes() {
            let id = AttributeId::find(el.get_attribute_name(next_index), self.scope);
            self.attribute_index = next_index;
            return Ok(id);
        }
        Ok(0)
    }

    fn get_indexed_attribute_id(&mut self, attrib_id: AttributeId) -> Result<u32> {
        let el = self.current();
        if self.attribute_index < 0 || self.attribute_index >= el.get_num_attributes() {
            return Ok(ATTRIB_UNKNOWN.get_id());
        }
        let attrib_name = el.get_attribute_name(self.attribute_index);
        let base_name = attrib_id.get_name();
        if !attrib_name.as_bytes().starts_with(base_name.as_bytes()) {
            return Ok(ATTRIB_UNKNOWN.get_id());
        }
        let val = istream::read_u32(&attrib_name[base_name.len()..], Basefield::Dec, 0);
        if val == 0 {
            return Err(Error::Lowlevel(format!("Bad indexed attribute: {base_name}")));
        }
        Ok(attrib_id.get_id().wrapping_add(val - 1))
    }

    fn rewind_attributes(&mut self) {
        self.attribute_index = -1;
    }

    fn read_bool(&mut self) -> Result<bool> {
        Ok(xml_readbool(self.current_attribute_value()))
    }

    fn read_bool_attr(&mut self, attrib_id: AttributeId) -> Result<bool> {
        Ok(xml_readbool(&self.attribute_text(attrib_id)?))
    }

    fn read_signed_integer(&mut self) -> Result<i64> {
        Ok(istream::read_i64(self.current_attribute_value(), Basefield::Auto, 0))
    }

    fn read_signed_integer_attr(&mut self, attrib_id: AttributeId) -> Result<i64> {
        Ok(istream::read_i64(&self.attribute_text(attrib_id)?, Basefield::Auto, 0))
    }

    fn read_signed_integer_expect_string(&mut self, expect: &str, expectval: i64) -> Result<i64> {
        let value = self.current_attribute_value();
        if value == expect {
            return Ok(expectval);
        }
        Ok(istream::read_i64(value, Basefield::Auto, 0))
    }

    fn read_signed_integer_expect_string_attr(
        &mut self,
        attrib_id: AttributeId,
        expect: &str,
        expectval: i64,
    ) -> Result<i64> {
        let value = self.read_string_attr(attrib_id)?;
        if value == expect {
            return Ok(expectval);
        }
        Ok(istream::read_i64(&value, Basefield::Auto, 0))
    }

    fn read_unsigned_integer(&mut self) -> Result<u64> {
        Ok(istream::read_u64(self.current_attribute_value(), Basefield::Auto, 0))
    }

    fn read_unsigned_integer_attr(&mut self, attrib_id: AttributeId) -> Result<u64> {
        Ok(istream::read_u64(&self.attribute_text(attrib_id)?, Basefield::Auto, 0))
    }

    fn read_string(&mut self) -> Result<String> {
        Ok(self.current_attribute_value().to_string())
    }

    fn read_string_attr(&mut self, attrib_id: AttributeId) -> Result<String> {
        self.attribute_text(attrib_id)
    }

    fn read_space(&mut self) -> Result<SpaceRef> {
        let nm = self.current_attribute_value().to_string();
        self.lookup_space(&nm)
    }

    fn read_space_attr(&mut self, attrib_id: AttributeId) -> Result<SpaceRef> {
        let nm = self.attribute_text(attrib_id)?;
        self.lookup_space(&nm)
    }

    fn read_opcode(&mut self) -> Result<OpCode> {
        let opc = get_opcode(self.current_attribute_value());
        if opc == OpCode::Blank {
            return Err(Error::Decoder("Bad encoded OpCode".to_string()));
        }
        Ok(opc)
    }

    fn read_opcode_attr(&mut self, attrib_id: AttributeId) -> Result<OpCode> {
        let opc = get_opcode(&self.attribute_text(attrib_id)?);
        if opc == OpCode::Blank {
            return Err(Error::Decoder("Bad encoded OpCode".to_string()));
        }
        Ok(opc)
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum TagStatus {
    Start,
    Content,
    Stop,
}

const XML_SPACES: &str = "\n                        ";
const XML_MAX_SPACES: i32 = 24 + 1;

pub struct XmlEncode {
    out: String,
    tag_status: TagStatus,
    depth: i32,
    do_formatting: bool,
}

impl XmlEncode {
    pub fn new(do_format: bool) -> XmlEncode {
        XmlEncode {
            out: String::new(),
            tag_status: TagStatus::Stop,
            depth: 0,
            do_formatting: do_format,
        }
    }

    pub fn as_str(&self) -> &str {
        &self.out
    }

    pub fn as_bytes(&self) -> &[u8] {
        self.out.as_bytes()
    }

    pub fn into_string(self) -> String {
        self.out
    }

    pub fn take(&mut self) -> String {
        std::mem::take(&mut self.out)
    }

    fn new_line(&mut self) {
        if !self.do_formatting {
            return;
        }
        let num_spaces = (self.depth * 2 + 1).min(XML_MAX_SPACES);
        self.out.push_str(&XML_SPACES[..num_spaces as usize]);
    }

    fn start_content(&mut self) {
        if self.tag_status == TagStatus::Start {
            self.out.push('>');
        }
    }
}

impl Encoder for XmlEncode {
    fn open_element(&mut self, elem_id: ElementId) {
        if self.tag_status == TagStatus::Start {
            self.out.push('>');
        } else {
            self.tag_status = TagStatus::Start;
        }
        self.new_line();
        self.out.push('<');
        self.out.push_str(elem_id.get_name());
        self.depth += 1;
    }

    fn close_element(&mut self, elem_id: ElementId) {
        self.depth -= 1;
        if self.tag_status == TagStatus::Start {
            self.out.push_str("/>");
            self.tag_status = TagStatus::Stop;
            return;
        }
        if self.tag_status != TagStatus::Content {
            self.new_line();
        } else {
            self.tag_status = TagStatus::Stop;
        }
        self.out.push_str("</");
        self.out.push_str(elem_id.get_name());
        self.out.push('>');
    }

    fn write_bool(&mut self, attrib_id: AttributeId, val: bool) {
        if attrib_id == ATTRIB_CONTENT {
            self.start_content();
            self.out.push_str(if val { "true" } else { "false" });
            self.tag_status = TagStatus::Content;
            return;
        }
        a_v_b(&mut self.out, attrib_id.get_name(), val);
    }

    fn write_signed_integer(&mut self, attrib_id: AttributeId, val: i64) {
        if attrib_id == ATTRIB_CONTENT {
            self.start_content();
            let _ = write!(self.out, "{val}");
            self.tag_status = TagStatus::Content;
            return;
        }
        a_v_i(&mut self.out, attrib_id.get_name(), val);
    }

    fn write_unsigned_integer(&mut self, attrib_id: AttributeId, val: u64) {
        if attrib_id == ATTRIB_CONTENT {
            self.start_content();
            let _ = write!(self.out, "0x{val:x}");
            self.tag_status = TagStatus::Content;
            return;
        }
        a_v_u(&mut self.out, attrib_id.get_name(), val);
    }

    fn write_string(&mut self, attrib_id: AttributeId, val: &str) {
        if attrib_id == ATTRIB_CONTENT {
            self.start_content();
            xml_escape(&mut self.out, val);
            self.tag_status = TagStatus::Content;
            return;
        }
        a_v(&mut self.out, attrib_id.get_name(), val);
    }

    fn write_string_indexed(&mut self, attrib_id: AttributeId, index: u32, val: &str) {
        let _ = write!(self.out, " {}{}=\"", attrib_id.get_name(), index.wrapping_add(1));
        xml_escape(&mut self.out, val);
        self.out.push('"');
    }

    fn write_space(&mut self, attrib_id: AttributeId, spc: &AddrSpace) {
        if attrib_id == ATTRIB_CONTENT {
            self.start_content();
            xml_escape(&mut self.out, spc.get_name());
            self.tag_status = TagStatus::Content;
            return;
        }
        a_v(&mut self.out, attrib_id.get_name(), spc.get_name());
    }

    fn write_opcode(&mut self, attrib_id: AttributeId, opc: OpCode) {
        let name = get_opname(opc);
        if attrib_id == ATTRIB_CONTENT {
            self.start_content();
            self.out.push_str(name);
            self.tag_status = TagStatus::Content;
            return;
        }
        let _ = write!(self.out, " {}=\"{}\"", attrib_id.get_name(), name);
    }
}

pub mod packed_format {
    pub const HEADER_MASK: u8 = 0xc0;
    pub const ELEMENT_START: u8 = 0x40;
    pub const ELEMENT_END: u8 = 0x80;
    pub const ATTRIBUTE: u8 = 0xc0;
    pub const HEADEREXTEND_MASK: u8 = 0x20;
    pub const ELEMENTID_MASK: u8 = 0x1f;
    pub const RAWDATA_MASK: u8 = 0x7f;
    pub const RAWDATA_BITSPERBYTE: u32 = 7;
    pub const RAWDATA_MARKER: u8 = 0x80;
    pub const TYPECODE_SHIFT: u32 = 4;
    pub const LENGTHCODE_MASK: u8 = 0xf;
    pub const TYPECODE_BOOLEAN: u8 = 1;
    pub const TYPECODE_SIGNEDINT_POSITIVE: u8 = 2;
    pub const TYPECODE_SIGNEDINT_NEGATIVE: u8 = 3;
    pub const TYPECODE_UNSIGNEDINT: u8 = 4;
    pub const TYPECODE_ADDRESSSPACE: u8 = 5;
    pub const TYPECODE_SPECIALSPACE: u8 = 6;
    pub const TYPECODE_STRING: u8 = 7;
    pub const SPECIALSPACE_STACK: u32 = 0;
    pub const SPECIALSPACE_JOIN: u32 = 1;
    pub const SPECIALSPACE_FSPEC: u32 = 2;
    pub const SPECIALSPACE_IOP: u32 = 3;
    pub const SPECIALSPACE_SPACEBASE: u32 = 4;
}

use packed_format::*;

fn end_of_stream() -> Error {
    Error::Decoder("Unexpected end of stream".to_string())
}

pub struct PackedDecode<'a> {
    manager: Option<&'a AddrSpaceManager>,
    translate: Option<&'a dyn Translate>,
    buffer: Vec<u8>,
    limit: usize,
    start_pos: usize,
    cur_pos: usize,
    end_pos: usize,
    attribute_read: bool,
}

impl<'a> PackedDecode<'a> {
    pub const BUFFER_SIZE: i32 = 1024;

    pub fn new(manager: Option<&'a AddrSpaceManager>) -> PackedDecode<'a> {
        PackedDecode {
            manager,
            translate: None,
            buffer: Vec::new(),
            limit: 0,
            start_pos: 0,
            cur_pos: 0,
            end_pos: 0,
            attribute_read: true,
        }
    }

    pub fn set_translate(&mut self, translate: Option<&'a dyn Translate>) {
        self.translate = translate;
    }

    pub fn end_ingest(&mut self, data: Option<Vec<u8>>) -> Result<()> {
        let Some(mut bytes) = data else {
            return Err(Error::Decoder("Ended ingestion without any input".to_string()));
        };
        let size = PackedDecode::BUFFER_SIZE as usize;
        let data_length = bytes.len();
        self.limit = if data_length % size == 0 {
            data_length + 1
        } else {
            data_length.div_ceil(size) * size
        };
        bytes.push(ELEMENT_END);
        self.buffer = bytes;
        self.end_pos = 0;
        self.start_pos = 0;
        self.cur_pos = 0;
        Ok(())
    }

    fn get_byte(&self, pos: usize) -> u8 {
        self.buffer.get(pos).copied().unwrap_or(0)
    }

    fn get_byte_plus1(&self, pos: usize) -> Result<u8> {
        let next = pos + 1;
        if next >= self.limit {
            return Err(end_of_stream());
        }
        Ok(self.get_byte(next))
    }

    fn get_next_byte(buffer: &[u8], limit: usize, pos: &mut usize) -> Result<u8> {
        let res = buffer.get(*pos).copied().unwrap_or(0);
        *pos += 1;
        if *pos >= limit {
            return Err(end_of_stream());
        }
        Ok(res)
    }

    fn advance_position(limit: usize, pos: &mut usize, skip: u64) -> Result<()> {
        let remaining = limit.saturating_sub(*pos) as u64;
        if remaining <= skip {
            *pos = limit;
            return Err(end_of_stream());
        }
        *pos += skip as usize;
        Ok(())
    }

    fn next_cur(&mut self) -> Result<u8> {
        PackedDecode::get_next_byte(&self.buffer, self.limit, &mut self.cur_pos)
    }

    fn next_end(&mut self) -> Result<u8> {
        PackedDecode::get_next_byte(&self.buffer, self.limit, &mut self.end_pos)
    }

    fn read_integer(&mut self, len: u32) -> Result<u64> {
        let mut res: u64 = 0;
        let mut remaining = len;
        while remaining > 0 {
            res <<= RAWDATA_BITSPERBYTE;
            res |= (self.next_cur()? & RAWDATA_MASK) as u64;
            remaining -= 1;
        }
        Ok(res)
    }

    fn read_length_code(type_byte: u8) -> u32 {
        (type_byte & LENGTHCODE_MASK) as u32
    }

    fn find_matching_attribute(&mut self, attrib_id: AttributeId) -> Result<()> {
        self.cur_pos = self.start_pos;
        loop {
            let header1 = self.get_byte(self.cur_pos);
            if (header1 & HEADER_MASK) != ATTRIBUTE {
                break;
            }
            let mut id = (header1 & ELEMENTID_MASK) as u32;
            if (header1 & HEADEREXTEND_MASK) != 0 {
                id <<= RAWDATA_BITSPERBYTE;
                id |= (self.get_byte_plus1(self.cur_pos)? & RAWDATA_MASK) as u32;
            }
            if attrib_id.get_id() == id {
                return Ok(());
            }
            self.skip_attribute()?;
        }
        Err(Error::Decoder(format!(
            "Attribute {} is not present",
            attrib_id.get_name()
        )))
    }

    fn skip_attribute(&mut self) -> Result<()> {
        let header1 = self.next_cur()?;
        if (header1 & HEADEREXTEND_MASK) != 0 {
            self.next_cur()?;
        }
        let type_byte = self.next_cur()?;
        self.skip_attribute_remaining(type_byte)
    }

    fn skip_attribute_remaining(&mut self, type_byte: u8) -> Result<()> {
        let attrib_type = type_byte >> TYPECODE_SHIFT;
        if attrib_type == TYPECODE_BOOLEAN || attrib_type == TYPECODE_SPECIALSPACE {
            return Ok(());
        }
        let mut length = PackedDecode::read_length_code(type_byte) as u64;
        if attrib_type == TYPECODE_STRING {
            length = self.read_integer(length as u32)? as u32 as u64;
        }
        PackedDecode::advance_position(self.limit, &mut self.cur_pos, length)
    }

    fn read_attribute_header(&mut self) -> Result<u8> {
        let header1 = self.next_cur()?;
        if (header1 & HEADEREXTEND_MASK) != 0 {
            self.next_cur()?;
        }
        self.next_cur()
    }

    fn manager_ref(&self) -> Result<&'a AddrSpaceManager> {
        self.manager
            .ok_or_else(|| Error::Decoder("decoder has no address space manager".to_string()))
    }
}

impl Decoder for PackedDecode<'_> {
    fn get_addr_space_manager(&self) -> Option<&AddrSpaceManager> {
        self.manager
    }

    fn get_translate(&self) -> Option<&dyn Translate> {
        self.translate
    }

    fn ingest_stream(&mut self, data: &[u8]) -> Result<()> {
        let length = data.iter().position(|byte| *byte == 0).unwrap_or(data.len());
        if length == 0 {
            return self.end_ingest(None);
        }
        self.end_ingest(Some(data[..length].to_vec()))
    }

    fn peek_element(&mut self) -> Result<u32> {
        let header1 = self.get_byte(self.end_pos);
        if (header1 & HEADER_MASK) != ELEMENT_START {
            return Ok(0);
        }
        let mut id = (header1 & ELEMENTID_MASK) as u32;
        if (header1 & HEADEREXTEND_MASK) != 0 {
            id <<= RAWDATA_BITSPERBYTE;
            id |= (self.get_byte_plus1(self.end_pos)? & RAWDATA_MASK) as u32;
        }
        Ok(id)
    }

    fn open_element(&mut self) -> Result<u32> {
        let mut header1 = self.get_byte(self.end_pos);
        if (header1 & HEADER_MASK) != ELEMENT_START {
            return Ok(0);
        }
        self.next_end()?;
        let mut id = (header1 & ELEMENTID_MASK) as u32;
        if (header1 & HEADEREXTEND_MASK) != 0 {
            id <<= RAWDATA_BITSPERBYTE;
            id |= (self.next_end()? & RAWDATA_MASK) as u32;
        }
        self.start_pos = self.end_pos;
        self.cur_pos = self.end_pos;
        header1 = self.get_byte(self.cur_pos);
        while (header1 & HEADER_MASK) == ATTRIBUTE {
            self.skip_attribute()?;
            header1 = self.get_byte(self.cur_pos);
        }
        self.end_pos = self.cur_pos;
        self.cur_pos = self.start_pos;
        self.attribute_read = true;
        Ok(id)
    }

    fn open_element_expect(&mut self, elem_id: ElementId) -> Result<u32> {
        let id = self.open_element()?;
        if id != elem_id.get_id() {
            if id == 0 {
                return Err(Error::Decoder(format!(
                    "Expecting <{}> but did not scan an element",
                    elem_id.get_name()
                )));
            }
            return Err(Error::Decoder(format!(
                "Expecting <{}> but id did not match",
                elem_id.get_name()
            )));
        }
        Ok(id)
    }

    fn close_element(&mut self, id: u32) -> Result<()> {
        let header1 = self.next_end()?;
        if (header1 & HEADER_MASK) != ELEMENT_END {
            return Err(Error::Decoder("Expecting element close".to_string()));
        }
        let mut close_id = (header1 & ELEMENTID_MASK) as u32;
        if (header1 & HEADEREXTEND_MASK) != 0 {
            close_id <<= RAWDATA_BITSPERBYTE;
            close_id |= (self.next_end()? & RAWDATA_MASK) as u32;
        }
        if id != close_id {
            return Err(Error::Decoder("Did not see expected closing element".to_string()));
        }
        Ok(())
    }

    fn close_element_skipping(&mut self, id: u32) -> Result<()> {
        let mut idstack = vec![id];
        loop {
            let header1 = self.get_byte(self.end_pos) & HEADER_MASK;
            if header1 == ELEMENT_END {
                let top = *idstack.last().expect("element id stack is empty");
                self.close_element(top)?;
                idstack.pop();
            } else if header1 == ELEMENT_START {
                let opened = self.open_element()?;
                idstack.push(opened);
            } else {
                return Err(Error::Decoder("Corrupt stream".to_string()));
            }
            if idstack.is_empty() {
                return Ok(());
            }
        }
    }

    fn get_next_attribute_id(&mut self) -> Result<u32> {
        if !self.attribute_read {
            self.skip_attribute()?;
        }
        let header1 = self.get_byte(self.cur_pos);
        if (header1 & HEADER_MASK) != ATTRIBUTE {
            return Ok(0);
        }
        let mut id = (header1 & ELEMENTID_MASK) as u32;
        if (header1 & HEADEREXTEND_MASK) != 0 {
            id <<= RAWDATA_BITSPERBYTE;
            id |= (self.get_byte_plus1(self.cur_pos)? & RAWDATA_MASK) as u32;
        }
        self.attribute_read = false;
        Ok(id)
    }

    fn get_indexed_attribute_id(&mut self, _attrib_id: AttributeId) -> Result<u32> {
        Ok(ATTRIB_UNKNOWN.get_id())
    }

    fn rewind_attributes(&mut self) {
        self.cur_pos = self.start_pos;
        self.attribute_read = true;
    }

    fn read_bool(&mut self) -> Result<bool> {
        let type_byte = self.read_attribute_header()?;
        self.attribute_read = true;
        if (type_byte >> TYPECODE_SHIFT) != TYPECODE_BOOLEAN {
            return Err(Error::Decoder("Expecting boolean attribute".to_string()));
        }
        Ok((type_byte & LENGTHCODE_MASK) != 0)
    }

    fn read_bool_attr(&mut self, attrib_id: AttributeId) -> Result<bool> {
        self.find_matching_attribute(attrib_id)?;
        let res = self.read_bool()?;
        self.cur_pos = self.start_pos;
        Ok(res)
    }

    fn read_signed_integer(&mut self) -> Result<i64> {
        let type_byte = self.read_attribute_header()?;
        let type_code = type_byte >> TYPECODE_SHIFT;
        let res = if type_code == TYPECODE_SIGNEDINT_POSITIVE {
            self.read_integer(PackedDecode::read_length_code(type_byte))? as i64
        } else if type_code == TYPECODE_SIGNEDINT_NEGATIVE {
            (self.read_integer(PackedDecode::read_length_code(type_byte))? as i64).wrapping_neg()
        } else {
            self.skip_attribute_remaining(type_byte)?;
            self.attribute_read = true;
            return Err(Error::Decoder("Expecting signed integer attribute".to_string()));
        };
        self.attribute_read = true;
        Ok(res)
    }

    fn read_signed_integer_attr(&mut self, attrib_id: AttributeId) -> Result<i64> {
        self.find_matching_attribute(attrib_id)?;
        let res = self.read_signed_integer()?;
        self.cur_pos = self.start_pos;
        Ok(res)
    }

    fn read_signed_integer_expect_string(&mut self, expect: &str, expectval: i64) -> Result<i64> {
        let mut tmp_pos = self.cur_pos;
        let header1 = PackedDecode::get_next_byte(&self.buffer, self.limit, &mut tmp_pos)?;
        if (header1 & HEADEREXTEND_MASK) != 0 {
            PackedDecode::get_next_byte(&self.buffer, self.limit, &mut tmp_pos)?;
        }
        let type_byte = PackedDecode::get_next_byte(&self.buffer, self.limit, &mut tmp_pos)?;
        let type_code = type_byte >> TYPECODE_SHIFT;
        if type_code == TYPECODE_STRING {
            let val = self.read_string()?;
            if val != expect {
                return Err(Error::Decoder(format!(
                    "Expecting string \"{expect}\" but read \"{val}\""
                )));
            }
            Ok(expectval)
        } else {
            self.read_signed_integer()
        }
    }

    fn read_signed_integer_expect_string_attr(
        &mut self,
        attrib_id: AttributeId,
        expect: &str,
        expectval: i64,
    ) -> Result<i64> {
        self.find_matching_attribute(attrib_id)?;
        let res = self.read_signed_integer_expect_string(expect, expectval)?;
        self.cur_pos = self.start_pos;
        Ok(res)
    }

    fn read_unsigned_integer(&mut self) -> Result<u64> {
        let type_byte = self.read_attribute_header()?;
        let type_code = type_byte >> TYPECODE_SHIFT;
        if type_code != TYPECODE_UNSIGNEDINT {
            self.skip_attribute_remaining(type_byte)?;
            self.attribute_read = true;
            return Err(Error::Decoder("Expecting unsigned integer attribute".to_string()));
        }
        let res = self.read_integer(PackedDecode::read_length_code(type_byte))?;
        self.attribute_read = true;
        Ok(res)
    }

    fn read_unsigned_integer_attr(&mut self, attrib_id: AttributeId) -> Result<u64> {
        self.find_matching_attribute(attrib_id)?;
        let res = self.read_unsigned_integer()?;
        self.cur_pos = self.start_pos;
        Ok(res)
    }

    fn read_string(&mut self) -> Result<String> {
        let type_byte = self.read_attribute_header()?;
        let type_code = type_byte >> TYPECODE_SHIFT;
        if type_code != TYPECODE_STRING {
            self.skip_attribute_remaining(type_byte)?;
            self.attribute_read = true;
            return Err(Error::Decoder("Expecting string attribute".to_string()));
        }
        let length = self.read_integer(PackedDecode::read_length_code(type_byte))?;
        self.attribute_read = true;
        let start = self.cur_pos.min(self.buffer.len());
        let available = self.buffer.len().saturating_sub(start) as u64;
        let take = length.min(available) as usize;
        let mut bytes = self.buffer[start..start + take].to_vec();
        let padding = length.min(self.limit.saturating_sub(start) as u64) as usize;
        bytes.resize(padding.max(take), 0);
        PackedDecode::advance_position(self.limit, &mut self.cur_pos, length)?;
        Ok(match String::from_utf8(bytes) {
            Ok(text) => text,
            Err(err) => String::from_utf8_lossy(err.as_bytes()).into_owned(),
        })
    }

    fn read_string_attr(&mut self, attrib_id: AttributeId) -> Result<String> {
        self.find_matching_attribute(attrib_id)?;
        let res = self.read_string()?;
        self.cur_pos = self.start_pos;
        Ok(res)
    }

    fn read_space(&mut self) -> Result<SpaceRef> {
        let type_byte = self.read_attribute_header()?;
        let type_code = type_byte >> TYPECODE_SHIFT;
        let spc = if type_code == TYPECODE_ADDRESSSPACE {
            let res = self.read_integer(PackedDecode::read_length_code(type_byte))?;
            let manager = self.manager_ref()?;
            if res >= manager.num_spaces() as u64 {
                return Err(Error::Decoder("Invalid address space index".to_string()));
            }
            match manager.get_space(res as i32) {
                Some(spc) => spc,
                None => return Err(Error::Decoder("Unknown address space index".to_string())),
            }
        } else if type_code == TYPECODE_SPECIALSPACE {
            let special_code = PackedDecode::read_length_code(type_byte);
            let manager = self.manager_ref()?;
            let found = if special_code == SPECIALSPACE_STACK {
                manager.get_stack_space()
            } else if special_code == SPECIALSPACE_JOIN {
                manager.get_join_space()
            } else {
                return Err(Error::Decoder("Cannot marshal special address space".to_string()));
            };
            match found {
                Some(spc) => spc,
                None => return Err(Error::Decoder("Unknown address space index".to_string())),
            }
        } else {
            self.skip_attribute_remaining(type_byte)?;
            self.attribute_read = true;
            return Err(Error::Decoder("Expecting space attribute".to_string()));
        };
        self.attribute_read = true;
        Ok(spc)
    }

    fn read_space_attr(&mut self, attrib_id: AttributeId) -> Result<SpaceRef> {
        self.find_matching_attribute(attrib_id)?;
        let res = self.read_space()?;
        self.cur_pos = self.start_pos;
        Ok(res)
    }

    fn read_opcode(&mut self) -> Result<OpCode> {
        let val = self.read_signed_integer()? as i32;
        if !(0..OpCode::Max as i32).contains(&val) {
            return Err(Error::Decoder("Bad encoded OpCode".to_string()));
        }
        Ok(OpCode::from_index(val as i64).expect("opcode index in range"))
    }

    fn read_opcode_attr(&mut self, attrib_id: AttributeId) -> Result<OpCode> {
        self.find_matching_attribute(attrib_id)?;
        let opc = self.read_opcode()?;
        self.cur_pos = self.start_pos;
        Ok(opc)
    }
}

#[derive(Default)]
pub struct PackedEncode {
    out: Vec<u8>,
}

impl PackedEncode {
    pub fn new() -> PackedEncode {
        PackedEncode { out: Vec::new() }
    }

    pub fn as_bytes(&self) -> &[u8] {
        &self.out
    }

    pub fn into_bytes(self) -> Vec<u8> {
        self.out
    }

    pub fn take(&mut self) -> Vec<u8> {
        std::mem::take(&mut self.out)
    }

    fn write_header(&mut self, header: u8, id: u32) {
        if id > 0x1f {
            let header = header | HEADEREXTEND_MASK | ((id >> RAWDATA_BITSPERBYTE) as u8);
            let extend_byte = ((id as u8) & RAWDATA_MASK) | RAWDATA_MARKER;
            self.out.push(header);
            self.out.push(extend_byte);
        } else {
            self.out.push(header | id as u8);
        }
    }

    fn write_integer(&mut self, type_byte: u8, val: u64) {
        let (len_code, shift): (u8, i32) = if val == 0 {
            (0, -1)
        } else if val < 0x800000000 {
            if val < 0x200000 {
                if val < 0x80 {
                    (1, 0)
                } else if val < 0x4000 {
                    (2, RAWDATA_BITSPERBYTE as i32)
                } else {
                    (3, 2 * RAWDATA_BITSPERBYTE as i32)
                }
            } else if val < 0x10000000 {
                (4, 3 * RAWDATA_BITSPERBYTE as i32)
            } else {
                (5, 4 * RAWDATA_BITSPERBYTE as i32)
            }
        } else if val < 0x2000000000000 {
            if val < 0x40000000000 {
                (6, 5 * RAWDATA_BITSPERBYTE as i32)
            } else {
                (7, 6 * RAWDATA_BITSPERBYTE as i32)
            }
        } else if val < 0x100000000000000 {
            (8, 7 * RAWDATA_BITSPERBYTE as i32)
        } else if val < 0x8000000000000000 {
            (9, 8 * RAWDATA_BITSPERBYTE as i32)
        } else {
            (10, 9 * RAWDATA_BITSPERBYTE as i32)
        };
        self.out.push(type_byte | len_code);
        let mut sa = shift;
        while sa >= 0 {
            let piece = ((val >> sa) as u8 & RAWDATA_MASK) | RAWDATA_MARKER;
            self.out.push(piece);
            sa -= RAWDATA_BITSPERBYTE as i32;
        }
    }
}

impl Encoder for PackedEncode {
    fn open_element(&mut self, elem_id: ElementId) {
        self.write_header(ELEMENT_START, elem_id.get_id());
    }

    fn close_element(&mut self, elem_id: ElementId) {
        self.write_header(ELEMENT_END, elem_id.get_id());
    }

    fn write_bool(&mut self, attrib_id: AttributeId, val: bool) {
        self.write_header(ATTRIBUTE, attrib_id.get_id());
        let type_byte = if val {
            (TYPECODE_BOOLEAN << TYPECODE_SHIFT) | 1
        } else {
            TYPECODE_BOOLEAN << TYPECODE_SHIFT
        };
        self.out.push(type_byte);
    }

    fn write_signed_integer(&mut self, attrib_id: AttributeId, val: i64) {
        self.write_header(ATTRIBUTE, attrib_id.get_id());
        let (type_byte, num) = if val < 0 {
            (TYPECODE_SIGNEDINT_NEGATIVE << TYPECODE_SHIFT, val.wrapping_neg() as u64)
        } else {
            (TYPECODE_SIGNEDINT_POSITIVE << TYPECODE_SHIFT, val as u64)
        };
        self.write_integer(type_byte, num);
    }

    fn write_unsigned_integer(&mut self, attrib_id: AttributeId, val: u64) {
        self.write_header(ATTRIBUTE, attrib_id.get_id());
        self.write_integer(TYPECODE_UNSIGNEDINT << TYPECODE_SHIFT, val);
    }

    fn write_string(&mut self, attrib_id: AttributeId, val: &str) {
        self.write_header(ATTRIBUTE, attrib_id.get_id());
        self.write_integer(TYPECODE_STRING << TYPECODE_SHIFT, val.len() as u64);
        self.out.extend_from_slice(val.as_bytes());
    }

    fn write_string_indexed(&mut self, attrib_id: AttributeId, index: u32, val: &str) {
        self.write_header(ATTRIBUTE, attrib_id.get_id().wrapping_add(index));
        self.write_integer(TYPECODE_STRING << TYPECODE_SHIFT, val.len() as u64);
        self.out.extend_from_slice(val.as_bytes());
    }

    fn write_space(&mut self, attrib_id: AttributeId, spc: &AddrSpace) {
        self.write_header(ATTRIBUTE, attrib_id.get_id());
        let special = TYPECODE_SPECIALSPACE << TYPECODE_SHIFT;
        match spc.get_type() {
            SpaceType::Fspec => self.out.push(special | SPECIALSPACE_FSPEC as u8),
            SpaceType::Iop => self.out.push(special | SPECIALSPACE_IOP as u8),
            SpaceType::Join => self.out.push(special | SPECIALSPACE_JOIN as u8),
            SpaceType::Spacebase => {
                if spc.is_formal_stack_space() {
                    self.out.push(special | SPECIALSPACE_STACK as u8);
                } else {
                    self.out.push(special | SPECIALSPACE_SPACEBASE as u8);
                }
            }
            _ => {
                let spc_id = spc.get_index() as i64 as u64;
                self.write_integer(TYPECODE_ADDRESSSPACE << TYPECODE_SHIFT, spc_id);
            }
        }
    }

    fn write_opcode(&mut self, attrib_id: AttributeId, opc: OpCode) {
        self.write_header(ATTRIBUTE, attrib_id.get_id());
        self.write_integer(TYPECODE_SIGNEDINT_POSITIVE << TYPECODE_SHIFT, opc as u64);
    }
}
