use std::collections::BTreeMap;
use std::fmt::Write as _;
use std::sync::Arc;

use crate::error::{Error, Result};

#[derive(Debug, Default, Clone, PartialEq, Eq)]
pub struct Element {
    name: String,
    content: String,
    attr: Vec<String>,
    value: Vec<String>,
    children: Vec<Arc<Element>>,
}

impl Element {
    pub fn new(name: &str) -> Element {
        Element {
            name: name.to_string(),
            ..Element::default()
        }
    }

    pub fn set_name(&mut self, nm: &str) {
        self.name = nm.to_string();
    }

    pub fn add_content(&mut self, text: &str) {
        self.content.push_str(text);
    }

    pub fn add_child(&mut self, child: Arc<Element>) {
        self.children.push(child);
    }

    pub fn add_attribute(&mut self, nm: &str, vl: &str) {
        self.attr.push(nm.to_string());
        self.value.push(vl.to_string());
    }

    pub fn get_name(&self) -> &str {
        &self.name
    }

    pub fn get_children(&self) -> &[Arc<Element>] {
        &self.children
    }

    pub fn get_content(&self) -> &str {
        &self.content
    }

    pub fn get_attribute_value(&self, nm: &str) -> Result<&str> {
        for (slot, attribute_name) in self.attr.iter().enumerate() {
            if attribute_name == nm {
                return Ok(&self.value[slot]);
            }
        }
        Err(Error::Decoder(format!("Unknown attribute: {nm}")))
    }

    pub fn get_num_attributes(&self) -> i32 {
        self.attr.len() as i32
    }

    pub fn get_attribute_name(&self, index: i32) -> &str {
        &self.attr[index as usize]
    }

    pub fn get_attribute_value_index(&self, index: i32) -> &str {
        &self.value[index as usize]
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Document {
    root: Arc<Element>,
}

impl Document {
    pub fn get_root(&self) -> &Arc<Element> {
        &self.root
    }
}

#[derive(Debug, Default)]
pub struct DocumentStorage {
    doclist: Vec<Arc<Document>>,
    tagmap: BTreeMap<String, Arc<Element>>,
}

impl DocumentStorage {
    pub fn new() -> DocumentStorage {
        DocumentStorage::default()
    }

    pub fn parse_document(&mut self, data: &[u8]) -> Result<Arc<Document>> {
        let doc = Arc::new(xml_tree(data)?);
        self.doclist.push(doc.clone());
        Ok(doc)
    }

    pub fn open_document(&mut self, filename: &str) -> Result<Arc<Document>> {
        let mut file = std::fs::File::open(filename)
            .map_err(|_| Error::Decoder(format!("Unable to open xml document {filename}")))?;
        let mut data = Vec::new();
        if std::io::Read::read_to_end(&mut file, &mut data).is_err() {
            data.clear();
        }
        self.parse_document(&data)
    }

    pub fn register_tag(&mut self, el: &Arc<Element>) {
        self.tagmap.insert(el.get_name().to_string(), el.clone());
    }

    pub fn get_tag(&self, nm: &str) -> Option<Arc<Element>> {
        self.tagmap.get(nm).cloned()
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum ScanMode {
    CharData,
    CData,
    AttValueSingle,
    AttValueDouble,
    Comment,
    CharRef,
    Name,
    SName,
    Single,
}

const TOKEN_EOF: i32 = 0;
const CHAR_DATA_TOKEN: i32 = 258;
const CDATA_TOKEN: i32 = 259;
const ATT_VALUE_TOKEN: i32 = 260;
const COMMENT_TOKEN: i32 = 261;
const CHAR_REF_TOKEN: i32 = 262;
const NAME_TOKEN: i32 = 263;
const SNAME_TOKEN: i32 = 264;
const ELEMENT_BRACE_TOKEN: i32 = 265;
const COMMAND_BRACE_TOKEN: i32 = 266;

const MAX_PARSE_DEPTH: usize = 10000;

struct XmlScan<'a> {
    input: &'a [u8],
    index: usize,
    curmode: ScanMode,
    lvalue: Vec<u8>,
    lookahead: [i32; 4],
    pos: usize,
    endofstream: bool,
}

impl<'a> XmlScan<'a> {
    fn new(input: &'a [u8]) -> XmlScan<'a> {
        let mut scan = XmlScan {
            input,
            index: 0,
            curmode: ScanMode::Single,
            lvalue: Vec::new(),
            lookahead: [0; 4],
            pos: 0,
            endofstream: false,
        };
        for _ in 0..4 {
            scan.getxmlchar();
        }
        scan
    }

    fn getxmlchar(&mut self) -> i32 {
        let ret = self.lookahead[self.pos];
        if !self.endofstream {
            if self.index >= self.input.len() || self.input[self.index] == 0 {
                self.endofstream = true;
                self.lookahead[self.pos] = b'\n' as i32;
            } else {
                self.lookahead[self.pos] = self.input[self.index] as i8 as i32;
            }
            self.index += 1;
        } else {
            self.lookahead[self.pos] = -1;
        }
        self.pos = (self.pos + 1) & 3;
        ret
    }

    fn next(&self, offset: usize) -> i32 {
        self.lookahead[(self.pos + offset) & 3]
    }

    fn push_char(&mut self) {
        let value = self.getxmlchar();
        self.lvalue.push(value as u8);
    }

    fn is_letter(val: i32) -> bool {
        (0x41..=0x5a).contains(&val) || (0x61..=0x7a).contains(&val)
    }

    fn is_initial_name_char(val: i32) -> bool {
        XmlScan::is_letter(val) || val == b'_' as i32 || val == b':' as i32
    }

    fn is_name_char(val: i32) -> bool {
        if XmlScan::is_letter(val) {
            return true;
        }
        if (b'0' as i32..=b'9' as i32).contains(&val) {
            return true;
        }
        val == b'.' as i32 || val == b'-' as i32 || val == b'_' as i32 || val == b':' as i32
    }

    fn is_char(val: i32) -> bool {
        val >= 0x20 || val == 0xd || val == 0xa || val == 0x9
    }

    fn scan_single(&mut self) -> i32 {
        let res = self.getxmlchar();
        if res == b'<' as i32 {
            if XmlScan::is_initial_name_char(self.next(0)) {
                return ELEMENT_BRACE_TOKEN;
            }
            return COMMAND_BRACE_TOKEN;
        }
        res
    }

    fn scan_char_data(&mut self) -> i32 {
        self.lvalue.clear();
        while self.next(0) != -1 {
            if self.next(0) == b'<' as i32 || self.next(0) == b'&' as i32 {
                break;
            }
            if self.next(0) == b']' as i32 && self.next(1) == b']' as i32 && self.next(2) == b'>' as i32 {
                break;
            }
            self.push_char();
        }
        if self.lvalue.is_empty() {
            return self.scan_single();
        }
        CHAR_DATA_TOKEN
    }

    fn scan_cdata(&mut self) -> i32 {
        self.lvalue.clear();
        while self.next(0) != -1 {
            if self.next(0) == b']' as i32 && self.next(1) == b']' as i32 && self.next(2) == b'>' as i32 {
                break;
            }
            if !XmlScan::is_char(self.next(0)) {
                break;
            }
            self.push_char();
        }
        CDATA_TOKEN
    }

    fn scan_char_ref(&mut self) -> i32 {
        self.lvalue.clear();
        if self.next(0) == b'x' as i32 {
            self.push_char();
            while self.next(0) != -1 {
                let val = self.next(0);
                if val < b'0' as i32 {
                    break;
                }
                if val > b'9' as i32 && val < b'A' as i32 {
                    break;
                }
                if val > b'F' as i32 && val < b'a' as i32 {
                    break;
                }
                if val > b'f' as i32 {
                    break;
                }
                self.push_char();
            }
            if self.lvalue.len() == 1 {
                return b'x' as i32;
            }
        } else {
            while self.next(0) != -1 {
                let val = self.next(0);
                if val < b'0' as i32 || val > b'9' as i32 {
                    break;
                }
                self.push_char();
            }
            if self.lvalue.is_empty() {
                return self.scan_single();
            }
        }
        CHAR_REF_TOKEN
    }

    fn scan_att_value(&mut self, quote: i32) -> i32 {
        self.lvalue.clear();
        while self.next(0) != -1 {
            if self.next(0) == quote || self.next(0) == b'<' as i32 || self.next(0) == b'&' as i32 {
                break;
            }
            self.push_char();
        }
        if self.lvalue.is_empty() {
            return self.scan_single();
        }
        ATT_VALUE_TOKEN
    }

    fn scan_comment(&mut self) -> i32 {
        self.lvalue.clear();
        while self.next(0) != -1 {
            if self.next(0) == b'-' as i32 && self.next(1) == b'-' as i32 {
                break;
            }
            if !XmlScan::is_char(self.next(0)) {
                break;
            }
            self.push_char();
        }
        COMMENT_TOKEN
    }

    fn scan_name(&mut self) -> i32 {
        self.lvalue.clear();
        if !XmlScan::is_initial_name_char(self.next(0)) {
            return self.scan_single();
        }
        self.push_char();
        while self.next(0) != -1 {
            if !XmlScan::is_name_char(self.next(0)) {
                break;
            }
            self.push_char();
        }
        NAME_TOKEN
    }

    fn scan_sname(&mut self) -> i32 {
        let mut whitecount = 0;
        while matches!(self.next(0), 0x20 | 0x0a | 0x0d | 0x09) {
            whitecount += 1;
            self.getxmlchar();
        }
        self.lvalue.clear();
        if !XmlScan::is_initial_name_char(self.next(0)) {
            if whitecount > 0 {
                return b' ' as i32;
            }
            return self.scan_single();
        }
        self.push_char();
        while self.next(0) != -1 {
            if !XmlScan::is_name_char(self.next(0)) {
                break;
            }
            self.push_char();
        }
        if whitecount > 0 {
            return SNAME_TOKEN;
        }
        NAME_TOKEN
    }

    fn nexttoken(&mut self) -> i32 {
        let mode = self.curmode;
        self.curmode = ScanMode::Single;
        match mode {
            ScanMode::CharData => self.scan_char_data(),
            ScanMode::CData => self.scan_cdata(),
            ScanMode::AttValueSingle => self.scan_att_value(b'\'' as i32),
            ScanMode::AttValueDouble => self.scan_att_value(b'"' as i32),
            ScanMode::Comment => self.scan_comment(),
            ScanMode::CharRef => self.scan_char_ref(),
            ScanMode::Name => self.scan_name(),
            ScanMode::SName => self.scan_sname(),
            ScanMode::Single => self.scan_single(),
        }
    }
}

struct OpenElement {
    name: String,
    content: Vec<u8>,
    attr: Vec<String>,
    value: Vec<String>,
    children: Vec<Arc<Element>>,
}

fn bytes_to_string(bytes: Vec<u8>) -> String {
    match String::from_utf8(bytes) {
        Ok(text) => text,
        Err(err) => String::from_utf8_lossy(err.as_bytes()).into_owned(),
    }
}

fn is_whitespace_token(token: i32) -> bool {
    token == b' ' as i32 || token == b'\n' as i32 || token == b'\r' as i32 || token == b'\t' as i32
}

fn convert_entity_ref(reference: &[u8]) -> i32 {
    match reference {
        b"lt" => b'<' as i32,
        b"amp" => b'&' as i32,
        b"gt" => b'>' as i32,
        b"quot" => b'"' as i32,
        b"apos" => b'\'' as i32,
        _ => -1,
    }
}

fn convert_char_ref(reference: &[u8]) -> i32 {
    let (start, mult) = if reference.first() == Some(&b'x') {
        (1, 16i32)
    } else {
        (0, 10i32)
    };
    let mut val: i32 = 0;
    for &byte in &reference[start..] {
        let cur = if byte <= b'9' {
            byte as i32 - b'0' as i32
        } else if byte <= b'F' {
            10 + byte as i32 - b'A' as i32
        } else {
            10 + byte as i32 - b'a' as i32
        };
        val = val.wrapping_mul(mult);
        val = val.wrapping_add(cur);
    }
    val
}

struct XmlParser<'a> {
    scan: XmlScan<'a>,
    token: Option<i32>,
    token_value: Vec<u8>,
    depth: usize,
    stack: Vec<OpenElement>,
    root: Option<Arc<Element>>,
}

fn syntax_error() -> Error {
    Error::Decoder("syntax error".to_string())
}

impl<'a> XmlParser<'a> {
    fn new(input: &'a [u8]) -> XmlParser<'a> {
        XmlParser {
            scan: XmlScan::new(input),
            token: None,
            token_value: Vec::new(),
            depth: 1,
            stack: Vec::new(),
            root: None,
        }
    }

    fn set_mode(&mut self, mode: ScanMode) {
        self.scan.curmode = mode;
    }

    fn la(&mut self) -> i32 {
        if let Some(token) = self.token {
            return token;
        }
        let mut res = self.scan.nexttoken();
        if res > 255 {
            self.token_value = std::mem::take(&mut self.scan.lvalue);
        }
        if res < 0 {
            res = TOKEN_EOF;
        }
        self.token = Some(res);
        res
    }

    fn push(&mut self) -> Result<()> {
        self.depth += 1;
        if self.depth >= MAX_PARSE_DEPTH {
            return Err(Error::Decoder("memory exhausted".to_string()));
        }
        Ok(())
    }

    fn reduce(&mut self, length: usize) -> Result<()> {
        self.depth -= length;
        self.push()
    }

    fn shift(&mut self) -> Result<Vec<u8>> {
        self.token = None;
        self.push()?;
        Ok(std::mem::take(&mut self.token_value))
    }

    fn expect(&mut self, token: u8) -> Result<()> {
        if self.la() != token as i32 {
            return Err(syntax_error());
        }
        self.shift()?;
        Ok(())
    }

    fn expect_sequence(&mut self, tokens: &[u8]) -> Result<()> {
        for &token in tokens {
            self.expect(token)?;
        }
        Ok(())
    }

    fn whitespace_run(&mut self) -> Result<()> {
        self.shift()?;
        self.reduce(1)?;
        self.reduce(1)?;
        while is_whitespace_token(self.la()) {
            self.shift()?;
            self.reduce(1)?;
            self.reduce(2)?;
        }
        Ok(())
    }

    fn eq(&mut self) -> Result<()> {
        let token = self.la();
        if is_whitespace_token(token) {
            self.whitespace_run()?;
            self.expect(b'=')?;
            self.reduce(2)?;
        } else if token == b'=' as i32 {
            self.shift()?;
            self.reduce(1)?;
        } else {
            return Err(syntax_error());
        }
        while is_whitespace_token(self.la()) {
            self.whitespace_run()?;
            self.reduce(2)?;
        }
        Ok(())
    }

    fn reference(&mut self) -> Result<i32> {
        self.shift()?;
        self.set_mode(ScanMode::Name);
        self.reduce(1)?;
        let token = self.la();
        if token == NAME_TOKEN {
            let name = self.shift()?;
            self.expect(b';')?;
            self.reduce(3)?;
            self.reduce(1)?;
            Ok(convert_entity_ref(&name))
        } else if token == b'#' as i32 {
            self.shift()?;
            self.set_mode(ScanMode::CharRef);
            self.reduce(2)?;
            if self.la() != CHAR_REF_TOKEN {
                return Err(syntax_error());
            }
            let reference = self.shift()?;
            self.expect(b';')?;
            self.reduce(3)?;
            self.reduce(1)?;
            Ok(convert_char_ref(&reference))
        } else {
            Err(syntax_error())
        }
    }

    fn att_value(&mut self) -> Result<Vec<u8>> {
        let quote = self.la();
        let mode = if quote == b'"' as i32 {
            ScanMode::AttValueDouble
        } else if quote == b'\'' as i32 {
            ScanMode::AttValueSingle
        } else {
            return Err(syntax_error());
        };
        self.shift()?;
        self.set_mode(mode);
        self.reduce(1)?;
        let mut result = Vec::new();
        loop {
            let token = self.la();
            if token == ATT_VALUE_TOKEN {
                let piece = self.shift()?;
                result.extend_from_slice(&piece);
                self.set_mode(mode);
                self.reduce(2)?;
            } else if token == b'&' as i32 {
                let value = self.reference()?;
                result.push(value as u8);
                self.set_mode(mode);
                self.reduce(2)?;
            } else if token == quote {
                self.shift()?;
                self.reduce(2)?;
                return Ok(result);
            } else {
                return Err(syntax_error());
            }
        }
    }

    fn comment_body(&mut self) -> Result<()> {
        self.expect_sequence(b"--")?;
        self.set_mode(ScanMode::Comment);
        self.reduce(4)?;
        if self.la() != COMMENT_TOKEN {
            return Err(syntax_error());
        }
        self.shift()?;
        self.expect_sequence(b"-->")?;
        self.reduce(5)?;
        Ok(())
    }

    fn processing_instruction(&mut self) -> Result<()> {
        Err(Error::Decoder("Processing instructions are not supported".to_string()))
    }

    fn version_like(&mut self, keyword: &[u8], pops: usize) -> Result<()> {
        self.expect_sequence(keyword)?;
        self.eq()?;
        self.att_value()?;
        self.reduce(pops)?;
        Ok(())
    }

    fn xml_decl(&mut self) -> Result<()> {
        self.expect_sequence(b"xml")?;
        if !is_whitespace_token(self.la()) {
            return Err(syntax_error());
        }
        self.whitespace_run()?;
        self.version_like(b"version", 10)?;
        self.reduce(6)?;
        let mut rhs_length = 1;
        if is_whitespace_token(self.la()) {
            self.whitespace_run()?;
            if self.la() == b'e' as i32 {
                self.version_like(b"encoding", 11)?;
                rhs_length += 1;
                if is_whitespace_token(self.la()) {
                    self.whitespace_run()?;
                    rhs_length += 1;
                }
            } else {
                rhs_length += 1;
            }
        }
        self.expect_sequence(b"?>")?;
        self.reduce(rhs_length + 2)?;
        Ok(())
    }

    fn prolog_misc_brace(&mut self, allow_doctype: bool) -> Result<()> {
        self.shift()?;
        let token = self.la();
        if token == b'?' as i32 {
            self.shift()?;
            return self.processing_instruction();
        }
        if token != b'!' as i32 {
            return Err(syntax_error());
        }
        self.shift()?;
        let token = self.la();
        if token == b'-' as i32 {
            self.comment_body()?;
            self.reduce(1)?;
            return Ok(());
        }
        if allow_doctype && token == b'D' as i32 {
            self.expect_sequence(b"DOCTYPE")?;
            return Err(Error::Decoder("DTD's not supported".to_string()));
        }
        Err(syntax_error())
    }

    fn prolog(&mut self) -> Result<()> {
        let token = self.la();
        if token == COMMAND_BRACE_TOKEN {
            self.shift()?;
            let token = self.la();
            if token == b'?' as i32 {
                self.shift()?;
                if self.la() == b'x' as i32 {
                    self.xml_decl()?;
                    self.reduce(1)?;
                } else {
                    return self.processing_instruction();
                }
            } else if token == b'!' as i32 {
                self.shift()?;
                if self.la() != b'-' as i32 {
                    return Err(syntax_error());
                }
                self.comment_body()?;
                self.reduce(1)?;
                self.reduce(1)?;
            } else {
                return Err(syntax_error());
            }
        } else {
            self.whitespace_run()?;
            self.reduce(1)?;
            self.reduce(1)?;
        }
        loop {
            let token = self.la();
            if is_whitespace_token(token) {
                self.whitespace_run()?;
                self.reduce(1)?;
                self.reduce(2)?;
            } else if token == COMMAND_BRACE_TOKEN {
                self.prolog_misc_brace(true)?;
                self.reduce(2)?;
            } else if token == ELEMENT_BRACE_TOKEN {
                self.reduce(1)?;
                return Ok(());
            } else {
                return Err(syntax_error());
            }
        }
    }

    fn print_content(&mut self, text: &[u8]) {
        let all_white = text.iter().all(|byte| matches!(byte, b' ' | b'\n' | b'\r' | b'\t'));
        if !all_white && let Some(current) = self.stack.last_mut() {
            current.content.extend_from_slice(text);
        }
    }

    fn start_element(&mut self, name: String, attributes: Vec<(String, Vec<u8>)>) {
        let mut attr = Vec::with_capacity(attributes.len());
        let mut value = Vec::with_capacity(attributes.len());
        for (attribute_name, attribute_value) in attributes {
            attr.push(attribute_name);
            value.push(bytes_to_string(attribute_value));
        }
        self.stack.push(OpenElement {
            name,
            content: Vec::new(),
            attr,
            value,
            children: Vec::new(),
        });
    }

    fn end_element(&mut self) {
        let open = self.stack.pop().expect("element stack underflow");
        let element = Arc::new(Element {
            name: open.name,
            content: bytes_to_string(open.content),
            attr: open.attr,
            value: open.value,
            children: open.children,
        });
        match self.stack.last_mut() {
            Some(parent) => parent.children.push(element),
            None => self.root = Some(element),
        }
    }

    fn start_tag(&mut self) -> Result<bool> {
        self.shift()?;
        self.set_mode(ScanMode::Name);
        self.reduce(1)?;
        if self.la() != NAME_TOKEN {
            return Err(syntax_error());
        }
        let name = bytes_to_string(self.shift()?);
        self.set_mode(ScanMode::SName);
        self.reduce(2)?;
        let mut attributes: Vec<(String, Vec<u8>)> = Vec::new();
        loop {
            let token = self.la();
            if token == SNAME_TOKEN {
                let attribute_name = bytes_to_string(self.shift()?);
                self.eq()?;
                let attribute_value = self.att_value()?;
                self.reduce(3)?;
                attributes.push((attribute_name, attribute_value));
                self.set_mode(ScanMode::SName);
                self.reduce(2)?;
                continue;
            }
            let mut rhs_length = 1;
            let mut token = token;
            if token == b' ' as i32 {
                self.shift()?;
                self.reduce(1)?;
                self.reduce(1)?;
                rhs_length += 1;
                token = self.la();
            }
            if token == b'>' as i32 {
                self.shift()?;
                self.reduce(rhs_length + 1)?;
                self.start_element(name, attributes);
                return Ok(false);
            }
            if token == b'/' as i32 {
                self.shift()?;
                self.expect(b'>')?;
                self.reduce(rhs_length + 2)?;
                self.start_element(name, attributes);
                self.end_element();
                self.reduce(1)?;
                return Ok(true);
            }
            return Err(syntax_error());
        }
    }

    fn element(&mut self) -> Result<()> {
        let base_level = self.stack.len();
        if self.start_tag()? {
            return Ok(());
        }
        self.set_mode(ScanMode::CharData);
        self.push()?;
        loop {
            let token = self.la();
            if token == CHAR_DATA_TOKEN {
                let text = self.shift()?;
                self.print_content(&text);
                self.set_mode(ScanMode::CharData);
                self.reduce(2)?;
            } else if token == ELEMENT_BRACE_TOKEN {
                if self.start_tag()? {
                    self.set_mode(ScanMode::CharData);
                    self.reduce(2)?;
                } else {
                    self.set_mode(ScanMode::CharData);
                    self.push()?;
                }
            } else if token == b'&' as i32 {
                let value = self.reference()?;
                self.print_content(&[value as u8]);
                self.set_mode(ScanMode::CharData);
                self.reduce(2)?;
            } else if token == COMMAND_BRACE_TOKEN {
                self.shift()?;
                let token = self.la();
                if token == b'/' as i32 {
                    self.shift()?;
                    self.set_mode(ScanMode::Name);
                    self.reduce(2)?;
                    if self.la() != NAME_TOKEN {
                        return Err(syntax_error());
                    }
                    self.shift()?;
                    let mut rhs_length = 3;
                    if is_whitespace_token(self.la()) {
                        self.whitespace_run()?;
                        rhs_length += 1;
                    }
                    self.expect(b'>')?;
                    self.reduce(rhs_length)?;
                    self.reduce(3)?;
                    self.end_element();
                    if self.stack.len() == base_level {
                        return Ok(());
                    }
                    self.set_mode(ScanMode::CharData);
                    self.reduce(2)?;
                } else if token == b'!' as i32 {
                    self.shift()?;
                    let token = self.la();
                    if token == b'-' as i32 {
                        self.comment_body()?;
                        self.set_mode(ScanMode::CharData);
                        self.reduce(2)?;
                    } else if token == b'[' as i32 {
                        self.expect_sequence(b"[CDATA[")?;
                        self.set_mode(ScanMode::CData);
                        self.reduce(9)?;
                        if self.la() != CDATA_TOKEN {
                            return Err(syntax_error());
                        }
                        let text = self.shift()?;
                        self.expect_sequence(b"]]>")?;
                        self.reduce(3)?;
                        self.reduce(3)?;
                        self.print_content(&text);
                        self.set_mode(ScanMode::CharData);
                        self.reduce(2)?;
                    } else {
                        return Err(syntax_error());
                    }
                } else if token == b'?' as i32 {
                    self.shift()?;
                    return self.processing_instruction();
                } else {
                    return Err(syntax_error());
                }
            } else {
                return Err(syntax_error());
            }
        }
    }

    fn document(&mut self) -> Result<Element> {
        let token = self.la();
        if token == ELEMENT_BRACE_TOKEN {
            self.element()?;
        } else if token == COMMAND_BRACE_TOKEN || is_whitespace_token(token) {
            self.prolog()?;
            self.element()?;
        } else {
            return Err(syntax_error());
        }
        let token = self.la();
        if is_whitespace_token(token) {
            self.whitespace_run()?;
        } else if token == COMMAND_BRACE_TOKEN {
            self.prolog_misc_brace(false)?;
        } else {
            return Err(syntax_error());
        }
        if self.la() != TOKEN_EOF {
            return Err(syntax_error());
        }
        let mut document = Element::default();
        if let Some(root) = self.root.take() {
            document.children.push(root);
        }
        Ok(document)
    }
}

pub fn xml_tree(data: &[u8]) -> Result<Document> {
    let mut parser = XmlParser::new(data);
    let document = parser.document()?;
    let root = document
        .children
        .into_iter()
        .next()
        .expect("parsed document has a root element");
    Ok(Document { root })
}

pub fn xml_escape(out: &mut String, text: &str) {
    for character in text.chars() {
        match character {
            '<' => out.push_str("&lt;"),
            '>' => out.push_str("&gt;"),
            '&' => out.push_str("&amp;"),
            '"' => out.push_str("&quot;"),
            '\'' => out.push_str("&apos;"),
            _ => out.push(character),
        }
    }
}

pub fn a_v(out: &mut String, attr: &str, val: &str) {
    out.push(' ');
    out.push_str(attr);
    out.push_str("=\"");
    xml_escape(out, val);
    out.push('"');
}

pub fn a_v_i(out: &mut String, attr: &str, val: i64) {
    let _ = write!(out, " {attr}=\"{val}\"");
}

pub fn a_v_u(out: &mut String, attr: &str, val: u64) {
    let _ = write!(out, " {attr}=\"0x{val:x}\"");
}

pub fn a_v_b(out: &mut String, attr: &str, val: bool) {
    let _ = write!(out, " {attr}=\"{}\"", if val { "true" } else { "false" });
}

pub fn xml_readbool(attr: &str) -> bool {
    matches!(attr.as_bytes().first(), Some(b't') | Some(b'1') | Some(b'y'))
}
