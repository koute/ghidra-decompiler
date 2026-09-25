use std::sync::atomic::{AtomicI32, Ordering};
use std::sync::{Arc, Mutex};

use crate::address::Address;
use crate::block::BlockId;
use crate::block::ELEM_BLOCK;
use crate::comment::ELEM_COMMENT;
use crate::database::SymbolId;
use crate::error::{Error, Result};
use crate::funcdata::ELEM_FUNCTION;
use crate::marshal::{
    ATTRIB_CONTENT, ATTRIB_ID, ATTRIB_NAME, ATTRIB_SPACE, AttributeId, ELEM_VALUE, ElementId, Encoder, PackedEncode,
    XmlEncode,
};
use crate::op::OpId;
use crate::space::SpaceRef;
use crate::translate::ELEM_OP;
use crate::types::TypeId;
use crate::types::{ELEM_BITFIELD, ELEM_FIELD, ELEM_TYPE};
use crate::variable::ATTRIB_SYMREF;
use crate::varnode::VarnodeId;

pub const ATTRIB_BLOCKREF: AttributeId = AttributeId::new("blockref", 35);
pub const ATTRIB_CLOSE: AttributeId = AttributeId::new("close", 36);
pub const ATTRIB_COLOR: AttributeId = AttributeId::new("color", 37);
pub const ATTRIB_INDENT: AttributeId = AttributeId::new("indent", 38);
pub const ATTRIB_OFF: AttributeId = AttributeId::new("off", 39);
pub const ATTRIB_OPEN: AttributeId = AttributeId::new("open", 40);
pub const ATTRIB_OPREF: AttributeId = AttributeId::new("opref", 41);
pub const ATTRIB_VARREF: AttributeId = AttributeId::new("varref", 42);
pub const ELEM_BREAK: ElementId = ElementId::new("break", 17);
pub const ELEM_CLANG_DOCUMENT: ElementId = ElementId::new("clang_document", 18);
pub const ELEM_FUNCNAME: ElementId = ElementId::new("funcname", 19);
pub const ELEM_FUNCPROTO: ElementId = ElementId::new("funcproto", 20);
pub const ELEM_LABEL: ElementId = ElementId::new("label", 21);
pub const ELEM_RETURN_TYPE: ElementId = ElementId::new("return_type", 22);
pub const ELEM_STATEMENT: ElementId = ElementId::new("statement", 23);
pub const ELEM_SYNTAX: ElementId = ElementId::new("syntax", 24);
pub const ELEM_VARDECL: ElementId = ElementId::new("vardecl", 25);
pub const ELEM_VARIABLE: ElementId = ElementId::new("variable", 26);

pub const EMPTY_STRING: &str = "";

const SPACE_ARRAY: &str = "          ";

#[repr(i32)]
#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Default)]
pub enum SyntaxHighlight {
    KeywordColor = 0,
    CommentColor = 1,
    TypeColor = 2,
    FuncnameColor = 3,
    VarColor = 4,
    ConstColor = 5,
    ParamColor = 6,
    GlobalColor = 7,
    #[default]
    NoColor = 8,
    ErrorColor = 9,
    SpecialColor = 10,
}

#[repr(i32)]
#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum BraceStyle {
    SameLine = 0,
    NextLine = 1,
    SkipLine = 2,
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct VarnodeMark {
    pub id: VarnodeId,
    pub create_index: u32,
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct OpMark {
    pub id: OpId,
    pub time: u32,
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct BlockMark {
    pub id: BlockId,
    pub index: i32,
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct SymbolMark {
    pub id: SymbolId,
    pub symbol_id: u64,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TypeMark {
    pub id: TypeId,
    pub unsized_id: u64,
    pub name: String,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FuncMark {
    pub entry: Address,
}

pub type PendPrintRef = Arc<Mutex<dyn PendPrint>>;

pub struct EmitBase {
    pub indentlevel: i32,
    pub parenlevel: i32,
    pub indentincrement: i32,
    pub pend_print: Option<PendPrintRef>,
}

impl EmitBase {
    pub fn new() -> EmitBase {
        let mut base = EmitBase {
            indentlevel: 0,
            parenlevel: 0,
            indentincrement: 0,
            pend_print: None,
        };
        base.reset_defaults_internal();
        base
    }

    pub fn reset_defaults_internal(&mut self) {
        self.indentincrement = 2;
    }
}

impl Default for EmitBase {
    fn default() -> EmitBase {
        EmitBase::new()
    }
}

pub trait Emit: Send {
    fn base(&self) -> &EmitBase;

    fn base_mut(&mut self) -> &mut EmitBase;

    fn as_dyn(&mut self) -> &mut dyn Emit;

    fn begin_document(&mut self) -> Result<i32>;

    fn end_document(&mut self, id: i32) -> Result<()>;

    fn begin_function(&mut self, fd: Option<&FuncMark>) -> Result<i32>;

    fn end_function(&mut self, id: i32) -> Result<()>;

    fn begin_block(&mut self, bl: Option<BlockMark>) -> Result<i32>;

    fn end_block(&mut self, id: i32) -> Result<()>;

    fn tag_line(&mut self) -> Result<()>;

    fn tag_line_indent(&mut self, indent: i32) -> Result<()>;

    fn begin_return_type(&mut self, vn: Option<VarnodeMark>) -> Result<i32>;

    fn end_return_type(&mut self, id: i32) -> Result<()>;

    fn begin_var_decl(&mut self, sym: Option<SymbolMark>) -> Result<i32>;

    fn end_var_decl(&mut self, id: i32) -> Result<()>;

    fn begin_statement(&mut self, op: Option<OpMark>) -> Result<i32>;

    fn end_statement(&mut self, id: i32) -> Result<()>;

    fn begin_func_proto(&mut self) -> Result<i32>;

    fn end_func_proto(&mut self, id: i32) -> Result<()>;

    fn tag_variable(
        &mut self,
        name: &str,
        hl: SyntaxHighlight,
        vn: Option<VarnodeMark>,
        op: Option<OpMark>,
    ) -> Result<()>;

    fn tag_op(&mut self, name: &str, hl: SyntaxHighlight, op: Option<OpMark>) -> Result<()>;

    fn tag_func_name(
        &mut self,
        name: &str,
        hl: SyntaxHighlight,
        fd: Option<&FuncMark>,
        op: Option<OpMark>,
    ) -> Result<()>;

    fn tag_type(&mut self, name: &str, hl: SyntaxHighlight, ct: Option<&TypeMark>) -> Result<()>;

    fn tag_field(
        &mut self,
        name: &str,
        hl: SyntaxHighlight,
        ct: Option<&TypeMark>,
        off: i32,
        op: Option<OpMark>,
    ) -> Result<()>;

    fn tag_bit_field(
        &mut self,
        name: &str,
        hl: SyntaxHighlight,
        ct: Option<&TypeMark>,
        id: i32,
        op: Option<OpMark>,
    ) -> Result<()>;

    fn tag_comment(&mut self, name: &str, hl: SyntaxHighlight, spc: Option<&SpaceRef>, off: u64) -> Result<()>;

    fn tag_label(&mut self, name: &str, hl: SyntaxHighlight, spc: Option<&SpaceRef>, off: u64) -> Result<()>;

    fn tag_case_label(&mut self, name: &str, hl: SyntaxHighlight, op: Option<OpMark>, value: u64) -> Result<()>;

    fn print(&mut self, data: &str, hl: SyntaxHighlight) -> Result<()>;

    fn open_paren(&mut self, paren: &str, id: i32) -> Result<i32>;

    fn close_paren(&mut self, paren: &str, id: i32) -> Result<()>;

    fn open_group(&mut self) -> Result<i32> {
        Ok(0)
    }

    fn close_group(&mut self, _id: i32) -> Result<()> {
        Ok(())
    }

    fn clear(&mut self) {
        let base = self.base_mut();
        base.parenlevel = 0;
        base.indentlevel = 0;
        base.pend_print = None;
    }

    fn set_output_stream(&mut self, text: Vec<u8>);

    fn get_output_stream(&mut self) -> &mut Vec<u8>;

    fn take_output_stream(&mut self) -> Vec<u8> {
        std::mem::take(self.get_output_stream())
    }

    fn set_markup(&mut self, _val: bool) {}

    fn set_packed_output(&mut self, _val: bool) {}

    fn spaces(&mut self, num: i32, _bump: i32) -> Result<()> {
        if num <= 10 {
            self.print(&SPACE_ARRAY[..num.max(0) as usize], SyntaxHighlight::NoColor)
        } else {
            let spc = " ".repeat(num as usize);
            self.print(&spc, SyntaxHighlight::NoColor)
        }
    }

    fn start_indent(&mut self) -> Result<i32> {
        let base = self.base_mut();
        base.indentlevel += base.indentincrement;
        Ok(0)
    }

    fn stop_indent(&mut self, _id: i32) -> Result<()> {
        let base = self.base_mut();
        base.indentlevel -= base.indentincrement;
        Ok(())
    }

    fn start_comment(&mut self) -> Result<i32> {
        Ok(0)
    }

    fn stop_comment(&mut self, _id: i32) -> Result<()> {
        Ok(())
    }

    fn flush(&mut self) -> Result<()> {
        Ok(())
    }

    fn set_max_line_size(&mut self, _mls: i32) -> Result<()> {
        Ok(())
    }

    fn get_max_line_size(&self) -> i32 {
        -1
    }

    fn set_comment_fill(&mut self, _fill: &str) {}

    fn emits_markup(&self) -> bool;

    fn reset_defaults(&mut self) {
        self.base_mut().reset_defaults_internal();
    }

    fn emit_pending(&mut self) -> Result<()> {
        if let Some(tmp) = self.base_mut().pend_print.take() {
            tmp.lock()
                .expect("poisoned pending print lock")
                .callback(self.as_dyn())?;
        }
        Ok(())
    }

    fn get_paren_level(&self) -> i32 {
        self.base().parenlevel
    }

    fn get_indent_increment(&self) -> i32 {
        self.base().indentincrement
    }

    fn set_indent_increment(&mut self, val: i32) {
        self.base_mut().indentincrement = val;
    }

    fn set_pending_print(&mut self, pend: PendPrintRef) {
        self.base_mut().pend_print = Some(pend);
    }

    fn cancel_pending_print(&mut self) {
        self.base_mut().pend_print = None;
    }

    fn has_pending_print(&self, pend: &PendPrintRef) -> bool {
        match &self.base().pend_print {
            Some(current) => Arc::as_ptr(current) as *const u8 == Arc::as_ptr(pend) as *const u8,
            None => false,
        }
    }

    fn open_brace_indent(&mut self, brace: &str, style: BraceStyle) -> Result<i32> {
        self.brace_break(style)?;
        let id = self.start_indent()?;
        self.print(brace, SyntaxHighlight::NoColor)?;
        Ok(id)
    }

    fn open_brace(&mut self, brace: &str, style: BraceStyle) -> Result<()> {
        self.brace_break(style)?;
        self.print(brace, SyntaxHighlight::NoColor)
    }

    fn brace_break(&mut self, style: BraceStyle) -> Result<()> {
        match style {
            BraceStyle::SameLine => self.spaces(1, 0),
            BraceStyle::SkipLine => {
                self.tag_line()?;
                self.tag_line()
            }
            BraceStyle::NextLine => self.tag_line(),
        }
    }

    fn close_brace_indent(&mut self, brace: &str, id: i32) -> Result<()> {
        self.stop_indent(id)?;
        self.tag_line()?;
        self.print(brace, SyntaxHighlight::NoColor)
    }
}

pub enum MarkupEncoder {
    Xml(XmlEncode),
    Packed(PackedEncode),
}

impl MarkupEncoder {
    pub fn as_encoder(&mut self) -> &mut dyn Encoder {
        match self {
            MarkupEncoder::Xml(encoder) => encoder,
            MarkupEncoder::Packed(encoder) => encoder,
        }
    }
}

pub struct EmitMarkup {
    pub base: EmitBase,
    pub s: Vec<u8>,
    pub encoder: Option<MarkupEncoder>,
}

impl EmitMarkup {
    pub fn new() -> EmitMarkup {
        EmitMarkup {
            base: EmitBase::new(),
            s: Vec::new(),
            encoder: None,
        }
    }
}

impl Default for EmitMarkup {
    fn default() -> EmitMarkup {
        EmitMarkup::new()
    }
}

impl EmitMarkup {
    fn encoder(&mut self) -> Result<&mut dyn Encoder> {
        match self.encoder.as_mut() {
            Some(encoder) => Ok(encoder.as_encoder()),
            None => Err(Error::Lowlevel("markup emitter has no output stream".to_string())),
        }
    }

    fn sync_output(&mut self) {
        match self.encoder.as_mut() {
            Some(MarkupEncoder::Xml(encoder)) => self.s.extend_from_slice(encoder.take().as_bytes()),
            Some(MarkupEncoder::Packed(encoder)) => self.s.extend_from_slice(&encoder.take()),
            None => {}
        }
    }

    fn write_color(encoder: &mut dyn Encoder, hl: SyntaxHighlight) {
        if hl != SyntaxHighlight::NoColor {
            encoder.write_unsigned_integer(ATTRIB_COLOR, hl as i32 as u64);
        }
    }

    fn write_opref(encoder: &mut dyn Encoder, op: Option<OpMark>) {
        if let Some(mark) = op {
            encoder.write_unsigned_integer(ATTRIB_OPREF, mark.time as u64);
        }
    }
}

impl Emit for EmitMarkup {
    fn base(&self) -> &EmitBase {
        &self.base
    }

    fn base_mut(&mut self) -> &mut EmitBase {
        &mut self.base
    }

    fn as_dyn(&mut self) -> &mut dyn Emit {
        self
    }

    fn begin_document(&mut self) -> Result<i32> {
        self.encoder()?.open_element(ELEM_CLANG_DOCUMENT);
        Ok(0)
    }

    fn end_document(&mut self, _id: i32) -> Result<()> {
        self.encoder()?.close_element(ELEM_CLANG_DOCUMENT);
        Ok(())
    }

    fn begin_function(&mut self, _fd: Option<&FuncMark>) -> Result<i32> {
        self.encoder()?.open_element(ELEM_FUNCTION);
        Ok(0)
    }

    fn end_function(&mut self, _id: i32) -> Result<()> {
        self.encoder()?.close_element(ELEM_FUNCTION);
        Ok(())
    }

    fn begin_block(&mut self, bl: Option<BlockMark>) -> Result<i32> {
        let encoder = self.encoder()?;
        encoder.open_element(ELEM_BLOCK);
        let index = bl.map(|mark| mark.index).unwrap_or(0);
        encoder.write_signed_integer(ATTRIB_BLOCKREF, index as i64);
        Ok(0)
    }

    fn end_block(&mut self, _id: i32) -> Result<()> {
        self.encoder()?.close_element(ELEM_BLOCK);
        Ok(())
    }

    fn tag_line(&mut self) -> Result<()> {
        self.emit_pending()?;
        let indent = self.base.indentlevel;
        let encoder = self.encoder()?;
        encoder.open_element(ELEM_BREAK);
        encoder.write_signed_integer(ATTRIB_INDENT, indent as i64);
        encoder.close_element(ELEM_BREAK);
        Ok(())
    }

    fn tag_line_indent(&mut self, indent: i32) -> Result<()> {
        self.emit_pending()?;
        let encoder = self.encoder()?;
        encoder.open_element(ELEM_BREAK);
        encoder.write_signed_integer(ATTRIB_INDENT, indent as i64);
        encoder.close_element(ELEM_BREAK);
        Ok(())
    }

    fn begin_return_type(&mut self, vn: Option<VarnodeMark>) -> Result<i32> {
        let encoder = self.encoder()?;
        encoder.open_element(ELEM_RETURN_TYPE);
        if let Some(mark) = vn {
            encoder.write_unsigned_integer(ATTRIB_VARREF, mark.create_index as u64);
        }
        Ok(0)
    }

    fn end_return_type(&mut self, _id: i32) -> Result<()> {
        self.encoder()?.close_element(ELEM_RETURN_TYPE);
        Ok(())
    }

    fn begin_var_decl(&mut self, sym: Option<SymbolMark>) -> Result<i32> {
        let encoder = self.encoder()?;
        encoder.open_element(ELEM_VARDECL);
        let symbol_id = sym.map(|mark| mark.symbol_id).unwrap_or(0);
        encoder.write_unsigned_integer(ATTRIB_SYMREF, symbol_id);
        Ok(0)
    }

    fn end_var_decl(&mut self, _id: i32) -> Result<()> {
        self.encoder()?.close_element(ELEM_VARDECL);
        Ok(())
    }

    fn begin_statement(&mut self, op: Option<OpMark>) -> Result<i32> {
        let encoder = self.encoder()?;
        encoder.open_element(ELEM_STATEMENT);
        EmitMarkup::write_opref(encoder, op);
        Ok(0)
    }

    fn end_statement(&mut self, _id: i32) -> Result<()> {
        self.encoder()?.close_element(ELEM_STATEMENT);
        Ok(())
    }

    fn begin_func_proto(&mut self) -> Result<i32> {
        self.encoder()?.open_element(ELEM_FUNCPROTO);
        Ok(0)
    }

    fn end_func_proto(&mut self, _id: i32) -> Result<()> {
        self.encoder()?.close_element(ELEM_FUNCPROTO);
        Ok(())
    }

    fn tag_variable(
        &mut self,
        name: &str,
        hl: SyntaxHighlight,
        vn: Option<VarnodeMark>,
        op: Option<OpMark>,
    ) -> Result<()> {
        let encoder = self.encoder()?;
        encoder.open_element(ELEM_VARIABLE);
        EmitMarkup::write_color(encoder, hl);
        if let Some(mark) = vn {
            encoder.write_unsigned_integer(ATTRIB_VARREF, mark.create_index as u64);
        }
        EmitMarkup::write_opref(encoder, op);
        encoder.write_string(ATTRIB_CONTENT, name);
        encoder.close_element(ELEM_VARIABLE);
        Ok(())
    }

    fn tag_op(&mut self, name: &str, hl: SyntaxHighlight, op: Option<OpMark>) -> Result<()> {
        let encoder = self.encoder()?;
        encoder.open_element(ELEM_OP);
        EmitMarkup::write_color(encoder, hl);
        EmitMarkup::write_opref(encoder, op);
        encoder.write_string(ATTRIB_CONTENT, name);
        encoder.close_element(ELEM_OP);
        Ok(())
    }

    fn tag_func_name(
        &mut self,
        name: &str,
        hl: SyntaxHighlight,
        _fd: Option<&FuncMark>,
        op: Option<OpMark>,
    ) -> Result<()> {
        let encoder = self.encoder()?;
        encoder.open_element(ELEM_FUNCNAME);
        EmitMarkup::write_color(encoder, hl);
        EmitMarkup::write_opref(encoder, op);
        encoder.write_string(ATTRIB_CONTENT, name);
        encoder.close_element(ELEM_FUNCNAME);
        Ok(())
    }

    fn tag_type(&mut self, name: &str, hl: SyntaxHighlight, ct: Option<&TypeMark>) -> Result<()> {
        let encoder = self.encoder()?;
        encoder.open_element(ELEM_TYPE);
        EmitMarkup::write_color(encoder, hl);
        let type_id = ct.map(|mark| mark.unsized_id).unwrap_or(0);
        if type_id != 0 {
            encoder.write_unsigned_integer(ATTRIB_ID, type_id);
        }
        encoder.write_string(ATTRIB_CONTENT, name);
        encoder.close_element(ELEM_TYPE);
        Ok(())
    }

    fn tag_field(
        &mut self,
        name: &str,
        hl: SyntaxHighlight,
        ct: Option<&TypeMark>,
        off: i32,
        op: Option<OpMark>,
    ) -> Result<()> {
        let encoder = self.encoder()?;
        encoder.open_element(ELEM_FIELD);
        EmitMarkup::write_color(encoder, hl);
        if let Some(mark) = ct {
            encoder.write_string(ATTRIB_NAME, &mark.name);
            if mark.unsized_id != 0 {
                encoder.write_unsigned_integer(ATTRIB_ID, mark.unsized_id);
            }
            encoder.write_signed_integer(ATTRIB_OFF, off as i64);
            EmitMarkup::write_opref(encoder, op);
        }
        encoder.write_string(ATTRIB_CONTENT, name);
        encoder.close_element(ELEM_FIELD);
        Ok(())
    }

    fn tag_bit_field(
        &mut self,
        name: &str,
        hl: SyntaxHighlight,
        ct: Option<&TypeMark>,
        id: i32,
        op: Option<OpMark>,
    ) -> Result<()> {
        let encoder = self.encoder()?;
        encoder.open_element(ELEM_BITFIELD);
        EmitMarkup::write_color(encoder, hl);
        if let Some(mark) = ct {
            encoder.write_string(ATTRIB_NAME, &mark.name);
            if mark.unsized_id != 0 {
                encoder.write_unsigned_integer(ATTRIB_ID, mark.unsized_id);
            }
        }
        encoder.write_signed_integer(ATTRIB_OFF, id as i64);
        EmitMarkup::write_opref(encoder, op);
        encoder.write_string(ATTRIB_CONTENT, name);
        encoder.close_element(ELEM_BITFIELD);
        Ok(())
    }

    fn tag_comment(&mut self, name: &str, hl: SyntaxHighlight, spc: Option<&SpaceRef>, off: u64) -> Result<()> {
        let encoder = self.encoder()?;
        encoder.open_element(ELEM_COMMENT);
        EmitMarkup::write_color(encoder, hl);
        if let Some(space) = spc {
            encoder.write_space(ATTRIB_SPACE, space);
        }
        encoder.write_unsigned_integer(ATTRIB_OFF, off);
        encoder.write_string(ATTRIB_CONTENT, name);
        encoder.close_element(ELEM_COMMENT);
        Ok(())
    }

    fn tag_label(&mut self, name: &str, hl: SyntaxHighlight, spc: Option<&SpaceRef>, off: u64) -> Result<()> {
        let encoder = self.encoder()?;
        encoder.open_element(ELEM_LABEL);
        EmitMarkup::write_color(encoder, hl);
        if let Some(space) = spc {
            encoder.write_space(ATTRIB_SPACE, space);
        }
        encoder.write_unsigned_integer(ATTRIB_OFF, off);
        encoder.write_string(ATTRIB_CONTENT, name);
        encoder.close_element(ELEM_LABEL);
        Ok(())
    }

    fn tag_case_label(&mut self, name: &str, hl: SyntaxHighlight, op: Option<OpMark>, value: u64) -> Result<()> {
        let encoder = self.encoder()?;
        encoder.open_element(ELEM_VALUE);
        EmitMarkup::write_color(encoder, hl);
        encoder.write_unsigned_integer(ATTRIB_OFF, value);
        EmitMarkup::write_opref(encoder, op);
        encoder.write_string(ATTRIB_CONTENT, name);
        encoder.close_element(ELEM_VALUE);
        Ok(())
    }

    fn print(&mut self, data: &str, hl: SyntaxHighlight) -> Result<()> {
        let encoder = self.encoder()?;
        encoder.open_element(ELEM_SYNTAX);
        EmitMarkup::write_color(encoder, hl);
        encoder.write_string(ATTRIB_CONTENT, data);
        encoder.close_element(ELEM_SYNTAX);
        Ok(())
    }

    fn open_paren(&mut self, paren: &str, id: i32) -> Result<i32> {
        let encoder = self.encoder()?;
        encoder.open_element(ELEM_SYNTAX);
        encoder.write_signed_integer(ATTRIB_OPEN, id as i64);
        encoder.write_string(ATTRIB_CONTENT, paren);
        encoder.close_element(ELEM_SYNTAX);
        self.base.parenlevel += 1;
        Ok(0)
    }

    fn close_paren(&mut self, paren: &str, id: i32) -> Result<()> {
        let encoder = self.encoder()?;
        encoder.open_element(ELEM_SYNTAX);
        encoder.write_signed_integer(ATTRIB_CLOSE, id as i64);
        encoder.write_string(ATTRIB_CONTENT, paren);
        encoder.close_element(ELEM_SYNTAX);
        self.base.parenlevel -= 1;
        Ok(())
    }

    fn set_output_stream(&mut self, text: Vec<u8>) {
        self.s = text;
        self.encoder = Some(MarkupEncoder::Packed(PackedEncode::new()));
    }

    fn get_output_stream(&mut self) -> &mut Vec<u8> {
        self.sync_output();
        &mut self.s
    }

    fn set_packed_output(&mut self, val: bool) {
        if self.encoder.is_none() {
            return;
        }
        self.sync_output();
        self.encoder = Some(if val {
            MarkupEncoder::Packed(PackedEncode::new())
        } else {
            MarkupEncoder::Xml(XmlEncode::new(true))
        });
    }

    fn emits_markup(&self) -> bool {
        true
    }
}

pub struct EmitNoMarkup {
    pub base: EmitBase,
    pub s: Vec<u8>,
}

impl EmitNoMarkup {
    pub fn new() -> EmitNoMarkup {
        EmitNoMarkup {
            base: EmitBase::new(),
            s: Vec::new(),
        }
    }
}

impl Default for EmitNoMarkup {
    fn default() -> EmitNoMarkup {
        EmitNoMarkup::new()
    }
}

impl Emit for EmitNoMarkup {
    fn base(&self) -> &EmitBase {
        &self.base
    }

    fn base_mut(&mut self) -> &mut EmitBase {
        &mut self.base
    }

    fn as_dyn(&mut self) -> &mut dyn Emit {
        self
    }

    fn begin_document(&mut self) -> Result<i32> {
        Ok(0)
    }

    fn end_document(&mut self, _id: i32) -> Result<()> {
        Ok(())
    }

    fn begin_function(&mut self, _fd: Option<&FuncMark>) -> Result<i32> {
        Ok(0)
    }

    fn end_function(&mut self, _id: i32) -> Result<()> {
        Ok(())
    }

    fn begin_block(&mut self, _bl: Option<BlockMark>) -> Result<i32> {
        Ok(0)
    }

    fn end_block(&mut self, _id: i32) -> Result<()> {
        Ok(())
    }

    fn tag_line(&mut self) -> Result<()> {
        self.s.push(b'\n');
        let mut count = self.base.indentlevel;
        while count > 0 {
            self.s.push(b' ');
            count -= 1;
        }
        Ok(())
    }

    fn tag_line_indent(&mut self, indent: i32) -> Result<()> {
        self.s.push(b'\n');
        let mut count = indent;
        while count > 0 {
            self.s.push(b' ');
            count -= 1;
        }
        Ok(())
    }

    fn begin_return_type(&mut self, _vn: Option<VarnodeMark>) -> Result<i32> {
        Ok(0)
    }

    fn end_return_type(&mut self, _id: i32) -> Result<()> {
        Ok(())
    }

    fn begin_var_decl(&mut self, _sym: Option<SymbolMark>) -> Result<i32> {
        Ok(0)
    }

    fn end_var_decl(&mut self, _id: i32) -> Result<()> {
        Ok(())
    }

    fn begin_statement(&mut self, _op: Option<OpMark>) -> Result<i32> {
        Ok(0)
    }

    fn end_statement(&mut self, _id: i32) -> Result<()> {
        Ok(())
    }

    fn begin_func_proto(&mut self) -> Result<i32> {
        Ok(0)
    }

    fn end_func_proto(&mut self, _id: i32) -> Result<()> {
        Ok(())
    }

    fn tag_variable(
        &mut self,
        name: &str,
        _hl: SyntaxHighlight,
        _vn: Option<VarnodeMark>,
        _op: Option<OpMark>,
    ) -> Result<()> {
        self.s.extend_from_slice(name.as_bytes());
        Ok(())
    }

    fn tag_op(&mut self, name: &str, _hl: SyntaxHighlight, _op: Option<OpMark>) -> Result<()> {
        self.s.extend_from_slice(name.as_bytes());
        Ok(())
    }

    fn tag_func_name(
        &mut self,
        name: &str,
        _hl: SyntaxHighlight,
        _fd: Option<&FuncMark>,
        _op: Option<OpMark>,
    ) -> Result<()> {
        self.s.extend_from_slice(name.as_bytes());
        Ok(())
    }

    fn tag_type(&mut self, name: &str, _hl: SyntaxHighlight, _ct: Option<&TypeMark>) -> Result<()> {
        self.s.extend_from_slice(name.as_bytes());
        Ok(())
    }

    fn tag_field(
        &mut self,
        name: &str,
        _hl: SyntaxHighlight,
        _ct: Option<&TypeMark>,
        _off: i32,
        _op: Option<OpMark>,
    ) -> Result<()> {
        self.s.extend_from_slice(name.as_bytes());
        Ok(())
    }

    fn tag_bit_field(
        &mut self,
        name: &str,
        _hl: SyntaxHighlight,
        _ct: Option<&TypeMark>,
        _id: i32,
        _op: Option<OpMark>,
    ) -> Result<()> {
        self.s.extend_from_slice(name.as_bytes());
        Ok(())
    }

    fn tag_comment(&mut self, name: &str, _hl: SyntaxHighlight, _spc: Option<&SpaceRef>, _off: u64) -> Result<()> {
        self.s.extend_from_slice(name.as_bytes());
        Ok(())
    }

    fn tag_label(&mut self, name: &str, _hl: SyntaxHighlight, _spc: Option<&SpaceRef>, _off: u64) -> Result<()> {
        self.s.extend_from_slice(name.as_bytes());
        Ok(())
    }

    fn tag_case_label(&mut self, name: &str, _hl: SyntaxHighlight, _op: Option<OpMark>, _value: u64) -> Result<()> {
        self.s.extend_from_slice(name.as_bytes());
        Ok(())
    }

    fn print(&mut self, data: &str, _hl: SyntaxHighlight) -> Result<()> {
        self.s.extend_from_slice(data.as_bytes());
        Ok(())
    }

    fn open_paren(&mut self, paren: &str, id: i32) -> Result<i32> {
        self.s.extend_from_slice(paren.as_bytes());
        self.base.parenlevel += 1;
        Ok(id)
    }

    fn close_paren(&mut self, paren: &str, _id: i32) -> Result<()> {
        self.s.extend_from_slice(paren.as_bytes());
        self.base.parenlevel -= 1;
        Ok(())
    }

    fn set_output_stream(&mut self, text: Vec<u8>) {
        self.s = text;
    }

    fn get_output_stream(&mut self) -> &mut Vec<u8> {
        &mut self.s
    }

    fn emits_markup(&self) -> bool {
        false
    }
}

#[repr(i32)]
#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Default)]
pub enum PrintClass {
    #[default]
    Begin = 0,
    End = 1,
    Tokenstring = 2,
    Tokenbreak = 3,
    BeginIndent = 4,
    EndIndent = 5,
    BeginComment = 6,
    EndComment = 7,
    Ignore = 8,
}

#[repr(i32)]
#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Default)]
pub enum TagType {
    #[default]
    DocuB = 0,
    DocuE = 1,
    FuncB = 2,
    FuncE = 3,
    BlocB = 4,
    BlocE = 5,
    RtypB = 6,
    RtypE = 7,
    VardB = 8,
    VardE = 9,
    StatB = 10,
    StatE = 11,
    ProtB = 12,
    ProtE = 13,
    VariT = 14,
    OpT = 15,
    FnamT = 16,
    TypeT = 17,
    FieldT = 18,
    BitfieldT = 19,
    CommT = 20,
    LabelT = 21,
    CaseT = 22,
    SyntT = 23,
    OparT = 24,
    CparT = 25,
    OinvT = 26,
    CinvT = 27,
    SpacT = 28,
    BumpT = 29,
    LineT = 30,
}

#[derive(Clone, Debug, Default)]
pub enum TokenRef {
    #[default]
    None,
    Varnode(VarnodeMark),
    Block(BlockMark),
    Func(FuncMark),
    Type(TypeMark),
    Space(SpaceRef),
    Symbol(SymbolMark),
}

pub static TOKEN_SPLIT_COUNTBASE: AtomicI32 = AtomicI32::new(0);

fn next_token_count() -> i32 {
    TOKEN_SPLIT_COUNTBASE.fetch_add(1, Ordering::Relaxed)
}

#[derive(Clone, Debug, Default)]
pub struct TokenSplit {
    pub tagtype: TagType,
    pub delimtype: PrintClass,
    pub tok: String,
    pub hl: SyntaxHighlight,
    pub op: Option<OpMark>,
    pub ptr_second: TokenRef,
    pub off: u64,
    pub indentbump: i32,
    pub numspaces: i32,
    pub size: i32,
    pub count: i32,
}

impl TokenSplit {
    pub fn new() -> TokenSplit {
        TokenSplit::default()
    }

    fn set_token(&mut self, name: &str) {
        self.tok = name.to_string();
        self.size = self.tok.len() as i32;
    }

    pub fn begin_document(&mut self) -> i32 {
        self.tagtype = TagType::DocuB;
        self.delimtype = PrintClass::Begin;
        self.size = 0;
        self.count = next_token_count();
        self.count
    }

    pub fn end_document(&mut self, id: i32) {
        self.tagtype = TagType::DocuE;
        self.delimtype = PrintClass::End;
        self.size = 0;
        self.count = id;
    }

    pub fn begin_function(&mut self, func_mark: Option<&FuncMark>) -> i32 {
        self.tagtype = TagType::FuncB;
        self.delimtype = PrintClass::Begin;
        self.size = 0;
        self.ptr_second = match func_mark {
            Some(mark) => TokenRef::Func(mark.clone()),
            None => TokenRef::None,
        };
        self.count = next_token_count();
        self.count
    }

    pub fn end_function(&mut self, id: i32) {
        self.tagtype = TagType::FuncE;
        self.delimtype = PrintClass::End;
        self.size = 0;
        self.count = id;
    }

    pub fn begin_block(&mut self, block_mark: Option<BlockMark>) -> i32 {
        self.tagtype = TagType::BlocB;
        self.delimtype = PrintClass::Ignore;
        self.ptr_second = match block_mark {
            Some(mark) => TokenRef::Block(mark),
            None => TokenRef::None,
        };
        self.count = next_token_count();
        self.count
    }

    pub fn end_block(&mut self, id: i32) {
        self.tagtype = TagType::BlocE;
        self.delimtype = PrintClass::Ignore;
        self.count = id;
    }

    pub fn begin_return_type(&mut self, varnode_mark: Option<VarnodeMark>) -> i32 {
        self.tagtype = TagType::RtypB;
        self.delimtype = PrintClass::Begin;
        self.ptr_second = match varnode_mark {
            Some(mark) => TokenRef::Varnode(mark),
            None => TokenRef::None,
        };
        self.count = next_token_count();
        self.count
    }

    pub fn end_return_type(&mut self, id: i32) {
        self.tagtype = TagType::RtypE;
        self.delimtype = PrintClass::End;
        self.count = id;
    }

    pub fn begin_var_decl(&mut self, sym: Option<SymbolMark>) -> i32 {
        self.tagtype = TagType::VardB;
        self.delimtype = PrintClass::Begin;
        self.ptr_second = match sym {
            Some(mark) => TokenRef::Symbol(mark),
            None => TokenRef::None,
        };
        self.count = next_token_count();
        self.count
    }

    pub fn end_var_decl(&mut self, id: i32) {
        self.tagtype = TagType::VardE;
        self.delimtype = PrintClass::End;
        self.count = id;
    }

    pub fn begin_statement(&mut self, op_mark: Option<OpMark>) -> i32 {
        self.tagtype = TagType::StatB;
        self.delimtype = PrintClass::Begin;
        self.op = op_mark;
        self.count = next_token_count();
        self.count
    }

    pub fn end_statement(&mut self, id: i32) {
        self.tagtype = TagType::StatE;
        self.delimtype = PrintClass::End;
        self.count = id;
    }

    pub fn begin_func_proto(&mut self) -> i32 {
        self.tagtype = TagType::ProtB;
        self.delimtype = PrintClass::Begin;
        self.count = next_token_count();
        self.count
    }

    pub fn end_func_proto(&mut self, id: i32) {
        self.tagtype = TagType::ProtE;
        self.delimtype = PrintClass::End;
        self.count = id;
    }

    pub fn tag_variable(
        &mut self,
        name: &str,
        highlight: SyntaxHighlight,
        varnode_mark: Option<VarnodeMark>,
        op_mark: Option<OpMark>,
    ) {
        self.set_token(name);
        self.tagtype = TagType::VariT;
        self.delimtype = PrintClass::Tokenstring;
        self.hl = highlight;
        self.ptr_second = match varnode_mark {
            Some(mark) => TokenRef::Varnode(mark),
            None => TokenRef::None,
        };
        self.op = op_mark;
    }

    pub fn tag_op(&mut self, name: &str, highlight: SyntaxHighlight, op_mark: Option<OpMark>) {
        self.set_token(name);
        self.tagtype = TagType::OpT;
        self.delimtype = PrintClass::Tokenstring;
        self.hl = highlight;
        self.op = op_mark;
    }

    pub fn tag_func_name(
        &mut self,
        name: &str,
        highlight: SyntaxHighlight,
        func_mark: Option<&FuncMark>,
        op_mark: Option<OpMark>,
    ) {
        self.set_token(name);
        self.tagtype = TagType::FnamT;
        self.delimtype = PrintClass::Tokenstring;
        self.hl = highlight;
        self.ptr_second = match func_mark {
            Some(mark) => TokenRef::Func(mark.clone()),
            None => TokenRef::None,
        };
        self.op = op_mark;
    }

    pub fn tag_type(&mut self, name: &str, highlight: SyntaxHighlight, ct: Option<&TypeMark>) {
        self.set_token(name);
        self.tagtype = TagType::TypeT;
        self.delimtype = PrintClass::Tokenstring;
        self.hl = highlight;
        self.ptr_second = match ct {
            Some(mark) => TokenRef::Type(mark.clone()),
            None => TokenRef::None,
        };
    }

    pub fn tag_field(
        &mut self,
        name: &str,
        highlight: SyntaxHighlight,
        ct: Option<&TypeMark>,
        offset: i32,
        in_op: Option<OpMark>,
    ) {
        self.set_token(name);
        self.tagtype = TagType::FieldT;
        self.delimtype = PrintClass::Tokenstring;
        self.hl = highlight;
        self.ptr_second = match ct {
            Some(mark) => TokenRef::Type(mark.clone()),
            None => TokenRef::None,
        };
        self.off = offset as i64 as u64;
        self.op = in_op;
    }

    pub fn tag_bit_field(
        &mut self,
        name: &str,
        highlight: SyntaxHighlight,
        ct: Option<&TypeMark>,
        id: i32,
        in_op: Option<OpMark>,
    ) {
        self.set_token(name);
        self.tagtype = TagType::BitfieldT;
        self.delimtype = PrintClass::Tokenstring;
        self.hl = highlight;
        self.ptr_second = match ct {
            Some(mark) => TokenRef::Type(mark.clone()),
            None => TokenRef::None,
        };
        self.off = id as i64 as u64;
        self.op = in_op;
    }

    pub fn tag_comment(&mut self, name: &str, highlight: SyntaxHighlight, spc: Option<&SpaceRef>, offset: u64) {
        self.set_token(name);
        self.ptr_second = match spc {
            Some(space) => TokenRef::Space(space.clone()),
            None => TokenRef::None,
        };
        self.off = offset;
        self.tagtype = TagType::CommT;
        self.delimtype = PrintClass::Tokenstring;
        self.hl = highlight;
    }

    pub fn tag_label(&mut self, name: &str, highlight: SyntaxHighlight, spc: Option<&SpaceRef>, offset: u64) {
        self.set_token(name);
        self.ptr_second = match spc {
            Some(space) => TokenRef::Space(space.clone()),
            None => TokenRef::None,
        };
        self.off = offset;
        self.tagtype = TagType::LabelT;
        self.delimtype = PrintClass::Tokenstring;
        self.hl = highlight;
    }

    pub fn tag_case_label(&mut self, name: &str, highlight: SyntaxHighlight, in_op: Option<OpMark>, int_value: u64) {
        self.set_token(name);
        self.op = in_op;
        self.off = int_value;
        self.tagtype = TagType::CaseT;
        self.delimtype = PrintClass::Tokenstring;
        self.hl = highlight;
    }

    pub fn print(&mut self, data: &str, highlight: SyntaxHighlight) {
        self.set_token(data);
        self.tagtype = TagType::SyntT;
        self.delimtype = PrintClass::Tokenstring;
        self.hl = highlight;
    }

    pub fn open_paren(&mut self, paren: &str, id: i32) {
        self.tok = paren.to_string();
        self.size = 1;
        self.tagtype = TagType::OparT;
        self.delimtype = PrintClass::Tokenstring;
        self.count = id;
    }

    pub fn close_paren(&mut self, paren: &str, id: i32) {
        self.tok = paren.to_string();
        self.size = 1;
        self.tagtype = TagType::CparT;
        self.delimtype = PrintClass::Tokenstring;
        self.count = id;
    }

    pub fn open_group(&mut self) -> i32 {
        self.tagtype = TagType::OinvT;
        self.delimtype = PrintClass::Begin;
        self.count = next_token_count();
        self.count
    }

    pub fn close_group(&mut self, id: i32) {
        self.tagtype = TagType::CinvT;
        self.delimtype = PrintClass::End;
        self.count = id;
    }

    pub fn start_indent(&mut self, bump: i32) -> i32 {
        self.tagtype = TagType::BumpT;
        self.delimtype = PrintClass::BeginIndent;
        self.indentbump = bump;
        self.size = 0;
        self.count = next_token_count();
        self.count
    }

    pub fn stop_indent(&mut self, id: i32) {
        self.tagtype = TagType::BumpT;
        self.delimtype = PrintClass::EndIndent;
        self.size = 0;
        self.count = id;
    }

    pub fn start_comment(&mut self) -> i32 {
        self.tagtype = TagType::OinvT;
        self.delimtype = PrintClass::BeginComment;
        self.count = next_token_count();
        self.count
    }

    pub fn stop_comment(&mut self, id: i32) {
        self.tagtype = TagType::CinvT;
        self.delimtype = PrintClass::EndComment;
        self.count = id;
    }

    pub fn spaces(&mut self, num: i32, bump: i32) {
        self.tagtype = TagType::SpacT;
        self.delimtype = PrintClass::Tokenbreak;
        self.numspaces = num;
        self.indentbump = bump;
    }

    pub fn tag_line(&mut self) {
        self.tagtype = TagType::BumpT;
        self.delimtype = PrintClass::Tokenbreak;
        self.numspaces = 999999;
        self.indentbump = 0;
    }

    pub fn tag_line_indent(&mut self, indent: i32) {
        self.tagtype = TagType::LineT;
        self.delimtype = PrintClass::Tokenbreak;
        self.numspaces = 999999;
        self.indentbump = indent;
    }

    fn func_ref(&self) -> Option<&FuncMark> {
        match &self.ptr_second {
            TokenRef::Func(mark) => Some(mark),
            _ => None,
        }
    }

    fn type_ref(&self) -> Option<&TypeMark> {
        match &self.ptr_second {
            TokenRef::Type(mark) => Some(mark),
            _ => None,
        }
    }

    fn space_ref(&self) -> Option<&SpaceRef> {
        match &self.ptr_second {
            TokenRef::Space(space) => Some(space),
            _ => None,
        }
    }

    fn varnode_ref(&self) -> Option<VarnodeMark> {
        match &self.ptr_second {
            TokenRef::Varnode(mark) => Some(*mark),
            _ => None,
        }
    }

    fn block_ref(&self) -> Option<BlockMark> {
        match &self.ptr_second {
            TokenRef::Block(mark) => Some(*mark),
            _ => None,
        }
    }

    fn symbol_ref(&self) -> Option<SymbolMark> {
        match &self.ptr_second {
            TokenRef::Symbol(mark) => Some(*mark),
            _ => None,
        }
    }

    pub fn print_emit(&self, emit: &mut dyn Emit) -> Result<()> {
        match self.tagtype {
            TagType::DocuB => {
                emit.begin_document()?;
            }
            TagType::DocuE => emit.end_document(self.count)?,
            TagType::FuncB => {
                emit.begin_function(self.func_ref())?;
            }
            TagType::FuncE => emit.end_function(self.count)?,
            TagType::BlocB => {
                emit.begin_block(self.block_ref())?;
            }
            TagType::BlocE => emit.end_block(self.count)?,
            TagType::RtypB => {
                emit.begin_return_type(self.varnode_ref())?;
            }
            TagType::RtypE => emit.end_return_type(self.count)?,
            TagType::VardB => {
                emit.begin_var_decl(self.symbol_ref())?;
            }
            TagType::VardE => emit.end_var_decl(self.count)?,
            TagType::StatB => {
                emit.begin_statement(self.op)?;
            }
            TagType::StatE => emit.end_statement(self.count)?,
            TagType::ProtB => {
                emit.begin_func_proto()?;
            }
            TagType::ProtE => emit.end_func_proto(self.count)?,
            TagType::VariT => emit.tag_variable(&self.tok, self.hl, self.varnode_ref(), self.op)?,
            TagType::OpT => emit.tag_op(&self.tok, self.hl, self.op)?,
            TagType::FnamT => emit.tag_func_name(&self.tok, self.hl, self.func_ref(), self.op)?,
            TagType::TypeT => emit.tag_type(&self.tok, self.hl, self.type_ref())?,
            TagType::FieldT => emit.tag_field(&self.tok, self.hl, self.type_ref(), self.off as i32, self.op)?,
            TagType::BitfieldT => emit.tag_bit_field(&self.tok, self.hl, self.type_ref(), self.off as i32, self.op)?,
            TagType::CommT => emit.tag_comment(&self.tok, self.hl, self.space_ref(), self.off)?,
            TagType::LabelT => emit.tag_label(&self.tok, self.hl, self.space_ref(), self.off)?,
            TagType::CaseT => emit.tag_case_label(&self.tok, self.hl, self.op, self.off)?,
            TagType::SyntT => emit.print(&self.tok, self.hl)?,
            TagType::OparT => {
                emit.open_paren(&self.tok, self.count)?;
            }
            TagType::CparT => emit.close_paren(&self.tok, self.count)?,
            TagType::OinvT | TagType::CinvT => {}
            TagType::SpacT => emit.spaces(self.numspaces, 0)?,
            TagType::LineT | TagType::BumpT => {
                return Err(Error::Lowlevel("Should never get called".to_string()));
            }
        }
        Ok(())
    }

    pub fn get_indent_bump(&self) -> i32 {
        self.indentbump
    }

    pub fn get_num_spaces(&self) -> i32 {
        self.numspaces
    }

    pub fn get_size(&self) -> i32 {
        self.size
    }

    pub fn set_size(&mut self, sz: i32) {
        self.size = sz;
    }

    pub fn get_class(&self) -> PrintClass {
        self.delimtype
    }

    pub fn get_tag(&self) -> TagType {
        self.tagtype
    }

    pub fn get_count(&self) -> i32 {
        self.count
    }

    pub fn print_debug(&self, out: &mut String) {
        let label = match self.tagtype {
            TagType::DocuB => "docu_b",
            TagType::DocuE => "docu_e",
            TagType::FuncB => "func_b",
            TagType::FuncE => "func_e",
            TagType::BlocB => "bloc_b",
            TagType::BlocE => "bloc_e",
            TagType::RtypB => "rtyp_b",
            TagType::RtypE => "rtyp_e",
            TagType::VardB => "vard_b",
            TagType::VardE => "vard_e",
            TagType::StatB => "stat_b",
            TagType::StatE => "stat_e",
            TagType::ProtB => "prot_b",
            TagType::ProtE => "prot_e",
            TagType::VariT => "vari_t",
            TagType::OpT => "op_t",
            TagType::FnamT => "fnam_t",
            TagType::TypeT => "type_t",
            TagType::FieldT => "field_t",
            TagType::BitfieldT => "bitfield_t",
            TagType::CommT => "comm_t",
            TagType::LabelT => "label_t",
            TagType::CaseT => "case_t",
            TagType::SyntT => "synt_t",
            TagType::OparT => "opar_t",
            TagType::CparT => "cpar_t",
            TagType::OinvT => "oinv_t",
            TagType::CinvT => "cinv_t",
            TagType::SpacT => "spac_t",
            TagType::LineT => "line_t",
            TagType::BumpT => "bump_t",
        };
        out.push_str(label);
    }
}

#[derive(Clone, Debug)]
pub struct CircularQueue<T> {
    cache: Vec<T>,
    left: i32,
    right: i32,
    max: i32,
}

impl<T: Default + Clone> CircularQueue<T> {
    pub fn new(sz: i32) -> CircularQueue<T> {
        CircularQueue {
            cache: vec![T::default(); sz as usize],
            left: 1,
            right: 0,
            max: sz,
        }
    }

    pub fn set_max(&mut self, sz: i32) {
        if self.max != sz {
            self.max = sz;
            self.cache = vec![T::default(); sz as usize];
        }
        self.left = 1;
        self.right = 0;
    }

    pub fn get_max(&self) -> i32 {
        self.max
    }

    pub fn expand(&mut self, amount: i32) {
        let mut newcache = vec![T::default(); (self.max + amount) as usize];
        let mut index = self.left;
        let mut slot = 0usize;
        while index != self.right {
            newcache[slot] = self.cache[index as usize].clone();
            slot += 1;
            index = (index + 1) % self.max;
        }
        newcache[slot] = self.cache[index as usize].clone();
        self.left = 0;
        self.right = slot as i32;
        self.cache = newcache;
        self.max += amount;
    }

    pub fn clear(&mut self) {
        self.left = 1;
        self.right = 0;
    }

    pub fn empty(&self) -> bool {
        self.left == (self.right + 1) % self.max
    }

    pub fn topref(&self) -> i32 {
        self.right
    }

    pub fn bottomref(&self) -> i32 {
        self.left
    }

    pub fn ref_at(&mut self, reference: i32) -> &mut T {
        &mut self.cache[reference as usize]
    }

    pub fn top(&mut self) -> &mut T {
        &mut self.cache[self.right as usize]
    }

    pub fn bottom(&mut self) -> &mut T {
        &mut self.cache[self.left as usize]
    }

    pub fn push(&mut self) -> &mut T {
        self.right = (self.right + 1) % self.max;
        &mut self.cache[self.right as usize]
    }

    pub fn pop(&mut self) -> &mut T {
        let tmp = self.right;
        self.right = (self.right + self.max - 1) % self.max;
        &mut self.cache[tmp as usize]
    }

    pub fn popbottom(&mut self) -> &mut T {
        let tmp = self.left;
        self.left = (self.left + 1) % self.max;
        &mut self.cache[tmp as usize]
    }
}

pub struct EmitPrettyPrint {
    pub base: EmitBase,
    pub checkid: Vec<i32>,
    pub lowlevel: Box<dyn Emit>,
    pub indentstack: Vec<i32>,
    pub spaceremain: i32,
    pub maxlinesize: i32,
    pub leftotal: i32,
    pub rightotal: i32,
    pub needbreak: bool,
    pub commentmode: bool,
    pub commentfill: String,
    pub scanqueue: CircularQueue<i32>,
    pub tokqueue: CircularQueue<TokenSplit>,
}

impl EmitPrettyPrint {
    pub fn new() -> EmitPrettyPrint {
        let mut printer = EmitPrettyPrint {
            base: EmitBase::new(),
            checkid: Vec::new(),
            lowlevel: Box::new(EmitNoMarkup::new()),
            indentstack: Vec::new(),
            spaceremain: 0,
            maxlinesize: 0,
            leftotal: 1,
            rightotal: 1,
            needbreak: false,
            commentmode: false,
            commentfill: String::new(),
            scanqueue: CircularQueue::new(3 * 100),
            tokqueue: CircularQueue::new(3 * 100),
        };
        printer.reset_defaults_pretty_print();
        printer
    }

    fn expand(&mut self) {
        let max = self.tokqueue.get_max();
        let left = self.tokqueue.bottomref();
        self.tokqueue.expand(200);
        for index in 0..max {
            let reference = self.scanqueue.ref_at(index);
            *reference = (*reference + max - left) % max;
        }
        self.scanqueue.expand(200);
    }

    fn checkstart(&mut self) -> Result<()> {
        if self.needbreak {
            self.tokqueue.push().spaces(0, 0);
            self.scan()?;
        }
        self.needbreak = false;
        Ok(())
    }

    fn checkend(&mut self) -> Result<()> {
        if !self.needbreak {
            self.tokqueue.push().print(EMPTY_STRING, SyntaxHighlight::NoColor);
            self.scan()?;
        }
        self.needbreak = true;
        Ok(())
    }

    fn checkstring(&mut self) -> Result<()> {
        if self.needbreak {
            self.tokqueue.push().spaces(0, 0);
            self.scan()?;
        }
        self.needbreak = true;
        Ok(())
    }

    fn checkbreak(&mut self) -> Result<()> {
        if !self.needbreak {
            self.tokqueue.push().print(EMPTY_STRING, SyntaxHighlight::NoColor);
            self.scan()?;
        }
        self.needbreak = false;
        Ok(())
    }

    fn overflow(&mut self) -> Result<()> {
        let half = self.maxlinesize / 2;
        for index in (0..self.indentstack.len()).rev() {
            if self.indentstack[index] < half {
                self.indentstack[index] = half;
            } else {
                break;
            }
        }
        let newspaceremain = match self.indentstack.last() {
            Some(last) => *last,
            None => self.maxlinesize,
        };
        if newspaceremain == self.spaceremain {
            return Ok(());
        }
        if self.commentmode && newspaceremain == self.spaceremain + self.commentfill.len() as i32 {
            return Ok(());
        }
        self.spaceremain = newspaceremain;
        self.lowlevel.tag_line_indent(self.maxlinesize - self.spaceremain)?;
        if self.commentmode && !self.commentfill.is_empty() {
            self.lowlevel.print(&self.commentfill, SyntaxHighlight::CommentColor)?;
            self.spaceremain -= self.commentfill.len() as i32;
        }
        Ok(())
    }

    fn indent_back(&self) -> Result<i32> {
        match self.indentstack.last() {
            Some(last) => Ok(*last),
            None => Err(Error::Lowlevel("indent error".to_string())),
        }
    }

    fn print_token(&mut self, tok: &TokenSplit) -> Result<()> {
        match tok.get_class() {
            PrintClass::Ignore => {
                tok.print_emit(self.lowlevel.as_mut())?;
            }
            PrintClass::BeginIndent => {
                let val = self.indent_back()? - tok.get_indent_bump();
                self.indentstack.push(val);
            }
            PrintClass::BeginComment | PrintClass::Begin => {
                if tok.get_class() == PrintClass::BeginComment {
                    self.commentmode = true;
                }
                tok.print_emit(self.lowlevel.as_mut())?;
                self.indentstack.push(self.spaceremain);
            }
            PrintClass::EndIndent => {
                if self.indentstack.is_empty() {
                    return Err(Error::Lowlevel("indent error".to_string()));
                }
                self.indentstack.pop();
            }
            PrintClass::EndComment | PrintClass::End => {
                if tok.get_class() == PrintClass::EndComment {
                    self.commentmode = false;
                }
                tok.print_emit(self.lowlevel.as_mut())?;
                self.indentstack.pop();
            }
            PrintClass::Tokenstring => {
                if tok.get_size() > self.spaceremain {
                    self.overflow()?;
                }
                tok.print_emit(self.lowlevel.as_mut())?;
                self.spaceremain -= tok.get_size();
            }
            PrintClass::Tokenbreak => {
                if tok.get_size() > self.spaceremain {
                    if tok.get_tag() == TagType::LineT {
                        self.spaceremain = self.maxlinesize - tok.get_indent_bump();
                    } else {
                        let val = self.indent_back()? - tok.get_indent_bump();
                        if tok.get_num_spaces() <= self.spaceremain && val - self.spaceremain < 10 {
                            self.lowlevel.spaces(tok.get_num_spaces(), 0)?;
                            self.spaceremain -= tok.get_num_spaces();
                            return Ok(());
                        }
                        if let Some(last) = self.indentstack.last_mut() {
                            *last = val;
                        }
                        self.spaceremain = val;
                    }
                    self.lowlevel.tag_line_indent(self.maxlinesize - self.spaceremain)?;
                    if self.commentmode && !self.commentfill.is_empty() {
                        self.lowlevel.print(&self.commentfill, SyntaxHighlight::CommentColor)?;
                        self.spaceremain -= self.commentfill.len() as i32;
                    }
                } else {
                    self.lowlevel.spaces(tok.get_num_spaces(), 0)?;
                    self.spaceremain -= tok.get_num_spaces();
                }
            }
        }
        Ok(())
    }

    fn advanceleft(&mut self) -> Result<()> {
        let mut size = self.tokqueue.bottom().get_size();
        while size >= 0 {
            let tok = self.tokqueue.bottom().clone();
            self.print_token(&tok)?;
            match tok.get_class() {
                PrintClass::Tokenbreak => self.leftotal += tok.get_num_spaces(),
                PrintClass::Tokenstring => self.leftotal += size,
                _ => {}
            }
            self.tokqueue.popbottom();
            if self.tokqueue.empty() {
                break;
            }
            size = self.tokqueue.bottom().get_size();
        }
        Ok(())
    }

    fn scan(&mut self) -> Result<()> {
        if self.tokqueue.empty() {
            self.expand();
        }
        let top = self.tokqueue.topref();
        match self.tokqueue.ref_at(top).get_class() {
            PrintClass::BeginComment | PrintClass::Begin => {
                if self.scanqueue.empty() {
                    self.leftotal = 1;
                    self.rightotal = 1;
                }
                let rightotal = self.rightotal;
                self.tokqueue.ref_at(top).set_size(-rightotal);
                *self.scanqueue.push() = top;
            }
            PrintClass::EndComment | PrintClass::End => {
                self.tokqueue.ref_at(top).set_size(0);
                if !self.scanqueue.empty() {
                    let rightotal = self.rightotal;
                    let reference = *self.scanqueue.pop();
                    let entry = self.tokqueue.ref_at(reference);
                    entry.set_size(entry.get_size() + rightotal);
                    if entry.get_class() == PrintClass::Tokenbreak && !self.scanqueue.empty() {
                        let reference2 = *self.scanqueue.pop();
                        let entry2 = self.tokqueue.ref_at(reference2);
                        entry2.set_size(entry2.get_size() + rightotal);
                    }
                    if self.scanqueue.empty() {
                        self.advanceleft()?;
                    }
                }
            }
            PrintClass::Tokenbreak => {
                if self.scanqueue.empty() {
                    self.leftotal = 1;
                    self.rightotal = 1;
                } else {
                    let rightotal = self.rightotal;
                    let reference = *self.scanqueue.top();
                    let entry = self.tokqueue.ref_at(reference);
                    if entry.get_class() == PrintClass::Tokenbreak {
                        entry.set_size(entry.get_size() + rightotal);
                        self.scanqueue.pop();
                    }
                }
                let rightotal = self.rightotal;
                let entry = self.tokqueue.ref_at(top);
                entry.set_size(-rightotal);
                let numspaces = entry.get_num_spaces();
                *self.scanqueue.push() = top;
                self.rightotal += numspaces;
            }
            PrintClass::BeginIndent | PrintClass::EndIndent | PrintClass::Ignore => {
                self.tokqueue.ref_at(top).set_size(0);
            }
            PrintClass::Tokenstring => {
                if !self.scanqueue.empty() {
                    self.rightotal += self.tokqueue.ref_at(top).get_size();
                    while self.rightotal - self.leftotal > self.spaceremain {
                        let reference = *self.scanqueue.popbottom();
                        self.tokqueue.ref_at(reference).set_size(999999);
                        self.advanceleft()?;
                        if self.scanqueue.empty() {
                            break;
                        }
                    }
                }
            }
        }
        Ok(())
    }

    fn apply_max_line_size(&mut self, val: i32) {
        self.maxlinesize = val;
        self.scanqueue.set_max(3 * val);
        self.tokqueue.set_max(3 * val);
        self.spaceremain = self.maxlinesize;
        self.clear();
    }

    fn reset_defaults_pretty_print(&mut self) {
        self.apply_max_line_size(100);
    }
}

impl Default for EmitPrettyPrint {
    fn default() -> EmitPrettyPrint {
        EmitPrettyPrint::new()
    }
}

impl Emit for EmitPrettyPrint {
    fn base(&self) -> &EmitBase {
        &self.base
    }

    fn base_mut(&mut self) -> &mut EmitBase {
        &mut self.base
    }

    fn as_dyn(&mut self) -> &mut dyn Emit {
        self
    }

    fn begin_document(&mut self) -> Result<i32> {
        self.checkstart()?;
        let id = self.tokqueue.push().begin_document();
        self.scan()?;
        Ok(id)
    }

    fn end_document(&mut self, id: i32) -> Result<()> {
        self.checkend()?;
        self.tokqueue.push().end_document(id);
        self.scan()
    }

    fn begin_function(&mut self, fd: Option<&FuncMark>) -> Result<i32> {
        self.checkstart()?;
        let id = self.tokqueue.push().begin_function(fd);
        self.scan()?;
        Ok(id)
    }

    fn end_function(&mut self, id: i32) -> Result<()> {
        self.checkend()?;
        self.tokqueue.push().end_function(id);
        self.scan()
    }

    fn begin_block(&mut self, bl: Option<BlockMark>) -> Result<i32> {
        let id = self.tokqueue.push().begin_block(bl);
        self.scan()?;
        Ok(id)
    }

    fn end_block(&mut self, id: i32) -> Result<()> {
        self.tokqueue.push().end_block(id);
        self.scan()
    }

    fn tag_line(&mut self) -> Result<()> {
        self.emit_pending()?;
        self.checkbreak()?;
        self.tokqueue.push().tag_line();
        self.scan()
    }

    fn tag_line_indent(&mut self, indent: i32) -> Result<()> {
        self.emit_pending()?;
        self.checkbreak()?;
        self.tokqueue.push().tag_line_indent(indent);
        self.scan()
    }

    fn begin_return_type(&mut self, vn: Option<VarnodeMark>) -> Result<i32> {
        self.checkstart()?;
        let id = self.tokqueue.push().begin_return_type(vn);
        self.scan()?;
        Ok(id)
    }

    fn end_return_type(&mut self, id: i32) -> Result<()> {
        self.checkend()?;
        self.tokqueue.push().end_return_type(id);
        self.scan()
    }

    fn begin_var_decl(&mut self, sym: Option<SymbolMark>) -> Result<i32> {
        self.checkstart()?;
        let id = self.tokqueue.push().begin_var_decl(sym);
        self.scan()?;
        Ok(id)
    }

    fn end_var_decl(&mut self, id: i32) -> Result<()> {
        self.checkend()?;
        self.tokqueue.push().end_var_decl(id);
        self.scan()
    }

    fn begin_statement(&mut self, op: Option<OpMark>) -> Result<i32> {
        self.checkstart()?;
        let id = self.tokqueue.push().begin_statement(op);
        self.scan()?;
        Ok(id)
    }

    fn end_statement(&mut self, id: i32) -> Result<()> {
        self.checkend()?;
        self.tokqueue.push().end_statement(id);
        self.scan()
    }

    fn begin_func_proto(&mut self) -> Result<i32> {
        self.checkstart()?;
        let id = self.tokqueue.push().begin_func_proto();
        self.scan()?;
        Ok(id)
    }

    fn end_func_proto(&mut self, id: i32) -> Result<()> {
        self.checkend()?;
        self.tokqueue.push().end_func_proto(id);
        self.scan()
    }

    fn tag_variable(
        &mut self,
        name: &str,
        hl: SyntaxHighlight,
        vn: Option<VarnodeMark>,
        op: Option<OpMark>,
    ) -> Result<()> {
        self.checkstring()?;
        self.tokqueue.push().tag_variable(name, hl, vn, op);
        self.scan()
    }

    fn tag_op(&mut self, name: &str, hl: SyntaxHighlight, op: Option<OpMark>) -> Result<()> {
        self.checkstring()?;
        self.tokqueue.push().tag_op(name, hl, op);
        self.scan()
    }

    fn tag_func_name(
        &mut self,
        name: &str,
        hl: SyntaxHighlight,
        fd: Option<&FuncMark>,
        op: Option<OpMark>,
    ) -> Result<()> {
        self.checkstring()?;
        self.tokqueue.push().tag_func_name(name, hl, fd, op);
        self.scan()
    }

    fn tag_type(&mut self, name: &str, hl: SyntaxHighlight, ct: Option<&TypeMark>) -> Result<()> {
        self.checkstring()?;
        self.tokqueue.push().tag_type(name, hl, ct);
        self.scan()
    }

    fn tag_field(
        &mut self,
        name: &str,
        hl: SyntaxHighlight,
        ct: Option<&TypeMark>,
        off: i32,
        op: Option<OpMark>,
    ) -> Result<()> {
        self.checkstring()?;
        self.tokqueue.push().tag_field(name, hl, ct, off, op);
        self.scan()
    }

    fn tag_bit_field(
        &mut self,
        name: &str,
        hl: SyntaxHighlight,
        ct: Option<&TypeMark>,
        id: i32,
        op: Option<OpMark>,
    ) -> Result<()> {
        self.checkstring()?;
        self.tokqueue.push().tag_bit_field(name, hl, ct, id, op);
        self.scan()
    }

    fn tag_comment(&mut self, name: &str, hl: SyntaxHighlight, spc: Option<&SpaceRef>, off: u64) -> Result<()> {
        self.checkstring()?;
        self.tokqueue.push().tag_comment(name, hl, spc, off);
        self.scan()
    }

    fn tag_label(&mut self, name: &str, hl: SyntaxHighlight, spc: Option<&SpaceRef>, off: u64) -> Result<()> {
        self.checkstring()?;
        self.tokqueue.push().tag_label(name, hl, spc, off);
        self.scan()
    }

    fn tag_case_label(&mut self, name: &str, hl: SyntaxHighlight, op: Option<OpMark>, value: u64) -> Result<()> {
        self.checkstring()?;
        self.tokqueue.push().tag_case_label(name, hl, op, value);
        self.scan()
    }

    fn print(&mut self, data: &str, hl: SyntaxHighlight) -> Result<()> {
        self.checkstring()?;
        self.tokqueue.push().print(data, hl);
        self.scan()
    }

    fn open_paren(&mut self, paren: &str, _id: i32) -> Result<i32> {
        let id = self.open_group()?;
        self.tokqueue.push().open_paren(paren, id);
        self.scan()?;
        self.needbreak = true;
        Ok(id)
    }

    fn close_paren(&mut self, paren: &str, id: i32) -> Result<()> {
        self.checkstring()?;
        self.tokqueue.push().close_paren(paren, id);
        self.scan()?;
        self.close_group(id)
    }

    fn open_group(&mut self) -> Result<i32> {
        self.checkstart()?;
        let id = self.tokqueue.push().open_group();
        self.scan()?;
        Ok(id)
    }

    fn close_group(&mut self, id: i32) -> Result<()> {
        self.checkend()?;
        self.tokqueue.push().close_group(id);
        self.scan()
    }

    fn clear(&mut self) {
        self.base.parenlevel = 0;
        self.base.indentlevel = 0;
        self.base.pend_print = None;
        self.lowlevel.clear();
        self.indentstack.clear();
        self.scanqueue.clear();
        self.tokqueue.clear();
        self.leftotal = 1;
        self.rightotal = 1;
        self.needbreak = false;
        self.commentmode = false;
        self.spaceremain = self.maxlinesize;
    }

    fn set_output_stream(&mut self, text: Vec<u8>) {
        self.lowlevel.set_output_stream(text);
    }

    fn get_output_stream(&mut self) -> &mut Vec<u8> {
        self.lowlevel.get_output_stream()
    }

    fn set_packed_output(&mut self, val: bool) {
        self.lowlevel.set_packed_output(val);
    }

    fn spaces(&mut self, num: i32, bump: i32) -> Result<()> {
        self.checkbreak()?;
        self.tokqueue.push().spaces(num, bump);
        self.scan()
    }

    fn start_indent(&mut self) -> Result<i32> {
        let increment = self.base.indentincrement;
        let id = self.tokqueue.push().start_indent(increment);
        self.scan()?;
        Ok(id)
    }

    fn stop_indent(&mut self, id: i32) -> Result<()> {
        self.tokqueue.push().stop_indent(id);
        self.scan()
    }

    fn start_comment(&mut self) -> Result<i32> {
        self.checkstart()?;
        let id = self.tokqueue.push().start_comment();
        self.scan()?;
        Ok(id)
    }

    fn stop_comment(&mut self, id: i32) -> Result<()> {
        self.checkend()?;
        self.tokqueue.push().stop_comment(id);
        self.scan()
    }

    fn flush(&mut self) -> Result<()> {
        while !self.tokqueue.empty() {
            let tok = self.tokqueue.popbottom().clone();
            if tok.get_size() < 0 {
                return Err(Error::Lowlevel(
                    "Cannot flush pretty printer. Missing group end".to_string(),
                ));
            }
            self.print_token(&tok)?;
        }
        self.needbreak = false;
        self.lowlevel.flush()
    }

    fn set_max_line_size(&mut self, val: i32) -> Result<()> {
        if !(20..=10000).contains(&val) {
            return Err(Error::Lowlevel("Bad maximum line size".to_string()));
        }
        self.apply_max_line_size(val);
        Ok(())
    }

    fn get_max_line_size(&self) -> i32 {
        self.maxlinesize
    }

    fn set_comment_fill(&mut self, fill: &str) {
        self.commentfill = fill.to_string();
    }

    fn emits_markup(&self) -> bool {
        self.lowlevel.emits_markup()
    }

    fn reset_defaults(&mut self) {
        self.lowlevel.reset_defaults();
        self.base.reset_defaults_internal();
        self.reset_defaults_pretty_print();
    }

    fn set_markup(&mut self, val: bool) {
        let stream = self.lowlevel.take_output_stream();
        self.lowlevel = if val {
            Box::new(EmitMarkup::new())
        } else {
            Box::new(EmitNoMarkup::new())
        };
        self.lowlevel.set_output_stream(stream);
    }
}

pub trait PendPrint: Send {
    fn callback(&mut self, emit: &mut dyn Emit) -> Result<()>;
}
