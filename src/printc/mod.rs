use std::sync::{Arc, Mutex};

use crate::address::{Address, calc_mask, sign_extend_size};
use crate::architecture::Architecture;
use crate::block::{BlockId, BlockType, FlowBlock};
use crate::cast::CastStrategyC;
use crate::comment::{Comment, CommentKey, CommentSorter};
use crate::database::{ScopeId, Symbol, SymbolId, SymbolKind};
use crate::error::{Error, Result};
use crate::expression::{InsertExpression, InsertStoreExpression, PullExpression};
use crate::float::FloatClass;
use crate::fspec::{CallSpecId, FuncCallSpecs, FuncProto};
use crate::funcdata::Funcdata;
use crate::op::{OpId, PcodeOp};
use crate::opcodes::{OpCode, get_booleanflip};
use crate::prettyprint::{BraceStyle, Emit, FuncMark, PendPrint, PendPrintRef, SymbolMark, SyntaxHighlight};
use crate::printlanguage::{
    Atom, COMMA_SEPARATE, FALSEBRANCH, FLAT, FORCE_DEC, FORCE_HEX, FORCE_POINTER, FORCE_SCINOTE, HIDE_THISPARAM,
    NEGATETOKEN, NO_BRANCH, NOFALLTHRU, NamespaceStrategy, ONLY_BRANCH, OpToken, OpTokenKey, OpTokenType,
    PENDING_BRACE, PRINT_LOAD_VALUE, PRINT_STORE_VALUE, PrintContext, PrintLanguage, PrintLanguageBase,
    PrintLanguageCapability, PrintTagType, ReversePolish, def_facing_type, format_binary, most_natural_base,
    push_opcode, read_facing_type, symboltab, symboltab_mut, translate, types, types_mut, unicode_needs_escape,
};
use crate::space::{AddrSpace, SpaceType};
use crate::stringmanage::StringManagerBase;
use crate::typeop::{TypeOpFloatInt2Float, TypeOpSubpiece};
use crate::types::{EnumRepresentation, TypeBitField, TypeField, TypeId, TypeKind, TypeMetatype};
use crate::userop::UserPcodeOp;
use crate::varnode::VarnodeId;

pub const EMPTY_STRING: &str = "";
pub const OPEN_CURLY: &str = "{";
pub const CLOSE_CURLY: &str = "}";
pub const SEMICOLON: &str = ";";
pub const COLON: &str = ":";
pub const EQUALSIGN: &str = "=";
pub const COMMA: &str = ",";
pub const DOTDOTDOT: &str = "...";
pub const KEYWORD_VOID: &str = "void";
pub const KEYWORD_TRUE: &str = "true";
pub const KEYWORD_FALSE: &str = "false";
pub const KEYWORD_IF: &str = "if";
pub const KEYWORD_ELSE: &str = "else";
pub const KEYWORD_DO: &str = "do";
pub const KEYWORD_WHILE: &str = "while";
pub const KEYWORD_FOR: &str = "for";
pub const KEYWORD_GOTO: &str = "goto";
pub const KEYWORD_BREAK: &str = "break";
pub const KEYWORD_CONTINUE: &str = "continue";
pub const KEYWORD_CASE: &str = "case";
pub const KEYWORD_SWITCH: &str = "switch";
pub const KEYWORD_DEFAULT: &str = "default";
pub const KEYWORD_RETURN: &str = "return";
pub const KEYWORD_NEW: &str = "new";
pub const TYPE_POINTER_REL_TOKEN: &str = "ADJ";

pub fn default_token_table() -> Vec<OpToken> {
    use OpTokenType::*;
    let token = OpToken::new;
    let mut table = vec![
        token("", "", 1, 70, false, Hiddenfunction, 0, 0, None),
        token("::", "", 2, 70, true, Binary, 0, 0, None),
        token(".", "", 2, 66, true, Binary, 0, 0, None),
        token("->", "", 2, 66, true, Binary, 0, 0, None),
        token("[", "]", 2, 66, false, Postsurround, 0, 0, None),
        token("(", ")", 2, 66, false, Postsurround, 0, 10, None),
        token("~", "", 1, 62, false, UnaryPrefix, 0, 0, None),
        token("!", "", 1, 62, false, UnaryPrefix, 0, 0, None),
        token("-", "", 1, 62, false, UnaryPrefix, 0, 0, None),
        token("+", "", 1, 62, false, UnaryPrefix, 0, 0, None),
        token("&", "", 1, 62, false, UnaryPrefix, 0, 0, None),
        token("*", "", 1, 62, false, UnaryPrefix, 0, 0, None),
        token("(", ")", 2, 62, false, Presurround, 0, 0, None),
        token("*", "", 2, 54, true, Binary, 1, 0, None),
        token("/", "", 2, 54, false, Binary, 1, 0, None),
        token("%", "", 2, 54, false, Binary, 1, 0, None),
        token("+", "", 2, 50, true, Binary, 1, 0, None),
        token("-", "", 2, 50, false, Binary, 1, 0, None),
        token("<<", "", 2, 46, false, Binary, 1, 0, None),
        token(">>", "", 2, 46, false, Binary, 1, 0, None),
        token(">>", "", 2, 46, false, Binary, 1, 0, None),
        token("<", "", 2, 42, false, Binary, 1, 0, None),
        token("<=", "", 2, 42, false, Binary, 1, 0, None),
        token(">", "", 2, 42, false, Binary, 1, 0, None),
        token(">=", "", 2, 42, false, Binary, 1, 0, None),
        token("==", "", 2, 38, false, Binary, 1, 0, None),
        token("!=", "", 2, 38, false, Binary, 1, 0, None),
        token("&", "", 2, 34, true, Binary, 1, 0, None),
        token("^", "", 2, 30, true, Binary, 1, 0, None),
        token("|", "", 2, 26, true, Binary, 1, 0, None),
        token("&&", "", 2, 22, false, Binary, 1, 0, None),
        token("||", "", 2, 18, false, Binary, 1, 0, None),
        token("^^", "", 2, 20, false, Binary, 1, 0, None),
        token("=", "", 2, 14, false, Binary, 1, 5, None),
        token(",", "", 2, 2, true, Binary, 0, 0, None),
        token("", "", 2, 62, false, Space, 1, 0, None),
        token("*=", "", 2, 14, false, Binary, 1, 5, None),
        token("/=", "", 2, 14, false, Binary, 1, 5, None),
        token("%=", "", 2, 14, false, Binary, 1, 5, None),
        token("+=", "", 2, 14, false, Binary, 1, 5, None),
        token("-=", "", 2, 14, false, Binary, 1, 5, None),
        token("<<=", "", 2, 14, false, Binary, 1, 5, None),
        token(">>=", "", 2, 14, false, Binary, 1, 5, None),
        token("&=", "", 2, 14, false, Binary, 1, 5, None),
        token("|=", "", 2, 14, false, Binary, 1, 5, None),
        token("^=", "", 2, 14, false, Binary, 1, 5, None),
        token("", "", 2, 10, false, Space, 1, 0, None),
        token("", "", 2, 10, false, Space, 0, 0, None),
        token("*", "", 1, 62, false, UnaryPrefix, 0, 0, None),
        token("[", "]", 2, 66, false, Postsurround, 1, 0, None),
        token("|", "", 2, 26, true, Binary, 0, 0, None),
        token("instanceof", "", 2, 60, true, Binary, 1, 0, None),
    ];
    table[OpTokenKey::LessThan.index()].negate = Some(OpTokenKey::GreaterEqual);
    table[OpTokenKey::LessEqual.index()].negate = Some(OpTokenKey::GreaterThan);
    table[OpTokenKey::GreaterThan.index()].negate = Some(OpTokenKey::LessEqual);
    table[OpTokenKey::GreaterEqual.index()].negate = Some(OpTokenKey::LessThan);
    table[OpTokenKey::Equal.index()].negate = Some(OpTokenKey::NotEqual);
    table[OpTokenKey::NotEqual.index()].negate = Some(OpTokenKey::Equal);
    table
}

pub struct PrintCCapability {
    pub name: &'static str,
    pub isdefault: bool,
}

pub static PRINT_C_CAPABILITY: PrintCCapability = PrintCCapability {
    name: "c-language",
    isdefault: true,
};

impl PrintLanguageCapability for PrintCCapability {
    fn get_name(&self) -> &str {
        self.name
    }

    fn is_default(&self) -> bool {
        self.isdefault
    }

    fn build_language(&self, glb: &mut Architecture) -> Box<dyn PrintLanguage> {
        Box::new(PrintC::new(glb, self.name))
    }
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum ProtoRef {
    Function,
    CallSpec(CallSpecId),
    Code(TypeId),
}

pub struct ParamSummary {
    pub tp: TypeId,
    pub is_this: bool,
    pub symbol: Result<SymbolId>,
}

pub struct ProtoSummary {
    pub num_params: i32,
    pub params: Vec<Option<ParamSummary>>,
    pub dotdotdot: bool,
    pub output_type: TypeId,
    pub has_this: bool,
}

impl ProtoSummary {
    fn build(proto: &mut FuncProto, glb: &Architecture) -> ProtoSummary {
        let num_params = proto.num_params(glb);
        let mut params = Vec::new();
        for index in 0..num_params {
            let param = proto.get_param(index, glb).map(|param| ParamSummary {
                tp: param.get_type(glb),
                is_this: param.is_this_pointer(glb),
                symbol: param.get_symbol(),
            });
            params.push(param);
        }
        ProtoSummary {
            num_params,
            params,
            dotdotdot: proto.is_dotdotdot(),
            output_type: proto.get_output_type(glb),
            has_this: proto.has_this_pointer(),
        }
    }

    fn param(&self, index: i32) -> Option<&ParamSummary> {
        if index < 0 {
            return None;
        }
        self.params.get(index as usize).and_then(|param| param.as_ref())
    }
}

#[derive(Clone, Debug)]
pub struct PartialSymbolEntry {
    pub token: OpTokenKey,
    pub field: Option<TypeField>,
    pub parent: Option<TypeId>,
    pub offset: i64,
    pub size: i32,
    pub hilite: SyntaxHighlight,
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum PrintFlavor {
    C,
    Java,
}

pub struct PrintC {
    pub base: PrintLanguageBase,
    pub flavor: PrintFlavor,
    pub option_null: bool,
    pub option_inplace_ops: bool,
    pub option_convention: bool,
    pub option_nocasts: bool,
    pub option_unplaced: bool,
    pub option_hide_exts: bool,
    pub option_brace_func: BraceStyle,
    pub option_brace_ifelse: BraceStyle,
    pub option_brace_loop: BraceStyle,
    pub option_brace_switch: BraceStyle,
    pub null_token: String,
    pub size_suffix: String,
    pub commsorter: CommentSorter,
}

pub struct PendingBrace {
    pub indent_id: i32,
    pub style: BraceStyle,
}

impl PendingBrace {
    pub fn new(style_2: BraceStyle) -> PendingBrace {
        PendingBrace {
            indent_id: -1,
            style: style_2,
        }
    }

    pub fn get_indent_id(&self) -> i32 {
        self.indent_id
    }
}

impl PendPrint for PendingBrace {
    fn callback(&mut self, emit: &mut dyn Emit) -> Result<()> {
        self.indent_id = emit.open_brace_indent(OPEN_CURLY, self.style)?;
        Ok(())
    }
}

pub(crate) fn is_value_flexible(data: &Funcdata, vn: VarnodeId) -> bool {
    let varnode = data.vn(vn);
    if varnode.is_implied() && varnode.is_written() {
        let def = varnode.get_def().expect("written varnode has no defining op");
        let mut opc = data.op(def).code();
        if opc == OpCode::Copy {
            let invn = data.vn(data.op(def).get_in(0));
            if !invn.is_implied() || !invn.is_written() {
                return false;
            }
            opc = data
                .op(invn.get_def().expect("written varnode has no defining op"))
                .code();
        }
        if opc == OpCode::Ptrsub {
            return true;
        }
        if opc == OpCode::Ptradd {
            return true;
        }
    }
    false
}

pub fn print_char_hex_escape(out: &mut String, val: i32) {
    let value = val as u32;
    if val < 256 {
        out.push_str(&format!("\\x{:02x}", value));
    } else if val < 65536 {
        out.push_str(&format!("\\x{:04x}", value));
    } else {
        out.push_str(&format!("\\x{:08x}", value));
    }
}

pub fn write_utf8_char(out: &mut String, onechar: i32) {
    let mut bytes: Vec<u8> = Vec::new();
    if StringManagerBase::write_utf8(&mut bytes, onechar).is_ok() {
        out.push_str(&String::from_utf8_lossy(&bytes));
    }
}

pub fn print_unicode_c_style(out: &mut String, onechar: i32) {
    if unicode_needs_escape(onechar) {
        match onechar {
            0 => out.push_str("\\0"),
            7 => out.push_str("\\a"),
            8 => out.push_str("\\b"),
            9 => out.push_str("\\t"),
            10 => out.push_str("\\n"),
            11 => out.push_str("\\v"),
            12 => out.push_str("\\f"),
            13 => out.push_str("\\r"),
            92 => out.push_str("\\\\"),
            0x22 => out.push_str("\\\""),
            0x27 => out.push_str("\\'"),
            _ => print_char_hex_escape(out, onechar),
        }
        return;
    }
    write_utf8_char(out, onechar);
}

pub(crate) fn metatype(ctx: &PrintContext<'_>, ct: TypeId) -> TypeMetatype {
    types(ctx.glb).get(ct).get_metatype()
}

pub(crate) fn ptr_to(ctx: &PrintContext<'_>, ct: TypeId) -> TypeId {
    types(ctx.glb).get(ct).get_ptr_to()
}

pub(crate) fn display_name(ctx: &PrintContext<'_>, ct: TypeId) -> String {
    types(ctx.glb).get(ct).get_display_name().to_string()
}

pub(crate) fn symbol_display_name(ctx: &PrintContext<'_>, sym: SymbolId) -> String {
    symboltab(ctx.glb).symbol(sym).get_display_name().to_string()
}

pub(crate) fn global_scope(ctx: &PrintContext<'_>) -> Result<ScopeId> {
    match symboltab(ctx.glb).get_global_scope() {
        Some(scope) => Ok(scope),
        None => Err(Error::Lowlevel("No global scope".to_string())),
    }
}

pub(crate) fn function_display_name(ctx: &PrintContext<'_>, sym: SymbolId) -> (String, Address) {
    let symbol = symboltab(ctx.glb).symbol(sym);
    if let SymbolKind::Function { fd: Some(fd), .. } = &symbol.kind {
        return (fd.get_display_name().to_string(), fd.get_address().clone());
    }
    if let Some(data) = ctx.data.as_deref()
        && data.get_symbol() == Some(sym)
    {
        return (data.get_display_name().to_string(), data.get_address().clone());
    }
    let addr = match symbol.mapentry.first() {
        Some(entry) => symboltab(ctx.glb).entry(*entry).get_addr().clone(),
        None => Address::default(),
    };
    (symbol.get_display_name().to_string(), addr)
}

pub(crate) fn op_in(ctx: &PrintContext<'_>, op: OpId, slot: i32) -> VarnodeId {
    ctx.data_ref().op(op).get_in(slot)
}

pub(crate) fn op_out(ctx: &PrintContext<'_>, op: OpId) -> Option<VarnodeId> {
    ctx.data_ref().op(op).get_out()
}

pub(crate) fn num_input(ctx: &PrintContext<'_>, op: OpId) -> i32 {
    ctx.data_ref().op(op).num_input()
}

pub(crate) fn op_code(ctx: &PrintContext<'_>, op: OpId) -> OpCode {
    ctx.data_ref().op(op).code()
}

pub(crate) fn def_op(ctx: &PrintContext<'_>, vn: VarnodeId) -> Result<OpId> {
    match ctx.data_ref().vn(vn).get_def() {
        Some(op) => Ok(op),
        None => Err(Error::Lowlevel("varnode has no defining op".to_string())),
    }
}

pub(crate) fn operator_name(ctx: &PrintContext<'_>, op: OpId) -> String {
    let data = ctx.data_ref();
    let opc = data.op(op).code();
    match ctx.glb.inst.get(opc.index()).and_then(|top| top.as_ref()) {
        Some(top) => top.get_operator_name(op, data, ctx.glb),
        None => String::new(),
    }
}

impl PrintC {
    pub fn new(_glb: &mut Architecture, nm: &str) -> PrintC {
        let mut base = PrintLanguageBase::new(nm);
        base.cast_strategy = Some(Box::new(CastStrategyC::new()));
        let mut printer = PrintC {
            base,
            flavor: PrintFlavor::C,
            option_null: false,
            option_inplace_ops: false,
            option_convention: false,
            option_nocasts: false,
            option_unplaced: false,
            option_hide_exts: false,
            option_brace_func: BraceStyle::SkipLine,
            option_brace_ifelse: BraceStyle::SameLine,
            option_brace_loop: BraceStyle::SameLine,
            option_brace_switch: BraceStyle::SameLine,
            null_token: "NULL".to_string(),
            size_suffix: String::new(),
            commsorter: CommentSorter::new(),
        };
        printer.reset_defaults_print_c();
        printer
    }

    pub fn is_java(&self) -> bool {
        self.flavor == PrintFlavor::Java
    }

    pub(crate) fn mods(&self) -> u32 {
        self.base.mods
    }

    pub(crate) fn emit(&mut self) -> &mut dyn Emit {
        self.base.emit.as_mut()
    }

    pub fn proto_summary(&self, ctx: &mut PrintContext<'_>, proto: ProtoRef) -> ProtoSummary {
        match proto {
            ProtoRef::Function => {
                let (glb, data) = ctx.parts();
                ProtoSummary::build(&mut data.funcp, glb)
            }
            ProtoRef::CallSpec(fc) => {
                let (glb, data) = ctx.parts();
                ProtoSummary::build(&mut data.call_spec_mut(fc).proto, glb)
            }
            ProtoRef::Code(ct) => {
                let taken = match &mut types_mut(ctx.glb).get_mut(ct).kind {
                    TypeKind::Code(code) => code.proto.take(),
                    _ => None,
                };
                let mut proto = taken.expect("code data-type has no prototype");
                let summary = ProtoSummary::build(&mut proto, ctx.glb);
                if let TypeKind::Code(code) = &mut types_mut(ctx.glb).get_mut(ct).kind {
                    code.proto = Some(proto);
                }
                summary
            }
        }
    }

    pub fn build_type_stack(&self, ctx: &mut PrintContext<'_>, ct: TypeId, typestack: &mut Vec<TypeId>) -> Result<()> {
        let mut ct = ct;
        loop {
            typestack.push(ct);
            let datatype = types(ctx.glb).get(ct);
            if !datatype.get_name().is_empty() {
                break;
            }
            match datatype.get_metatype() {
                TypeMetatype::Ptr => ct = datatype.get_ptr_to(),
                TypeMetatype::Array => ct = datatype.get_base(),
                TypeMetatype::Code => {
                    let output = datatype.get_prototype().map(|proto| proto.get_output_type(ctx.glb));
                    ct = match output {
                        Some(output) => output,
                        None => types_mut(ctx.glb).get_type_void()?,
                    };
                }
                _ => break,
            }
        }
        Ok(())
    }

    pub fn push_prototype_inputs(&mut self, ctx: &mut PrintContext<'_>, proto: ProtoRef) -> Result<()> {
        let summary = self.proto_summary(ctx, proto);
        let sz = summary.num_params;
        if sz == 0 && !summary.dotdotdot {
            self.push_atom(
                ctx,
                &Atom::new(KEYWORD_VOID, PrintTagType::Syntax, SyntaxHighlight::KeywordColor),
            )?;
        } else {
            for _ in 0..sz - 1 {
                self.push_op(ctx, OpTokenKey::Comma, None)?;
            }
            if summary.dotdotdot && sz != 0 {
                self.push_op(ctx, OpTokenKey::Comma, None)?;
            }
            for index in 0..sz {
                let tp = match summary.param(index) {
                    Some(param) => param.tp,
                    None => return Err(Error::Lowlevel("missing prototype parameter".to_string())),
                };
                self.push_type_start(ctx, tp, true)?;
                self.push_atom(
                    ctx,
                    &Atom::new(EMPTY_STRING, PrintTagType::Blanktoken, SyntaxHighlight::NoColor),
                )?;
                self.push_type_end(ctx, tp)?;
            }
            if summary.dotdotdot {
                if sz != 0 {
                    self.push_atom(
                        ctx,
                        &Atom::new(DOTDOTDOT, PrintTagType::Syntax, SyntaxHighlight::NoColor),
                    )?;
                } else {
                    self.push_atom(
                        ctx,
                        &Atom::new(EMPTY_STRING, PrintTagType::Blanktoken, SyntaxHighlight::NoColor),
                    )?;
                }
            }
        }
        Ok(())
    }

    pub(crate) fn scope_depth(&self, ctx: &mut PrintContext<'_>, symbol: SymbolId) -> i32 {
        let curscope = self.base.curscope;
        match self.base.namespc_strategy {
            NamespaceStrategy::MinimalNamespaces => {
                symboltab_mut(ctx.glb).symbol_get_resolution_depth(symbol, curscope)
            }
            NamespaceStrategy::AllNamespaces => {
                if Some(symboltab(ctx.glb).symbol(symbol).get_scope()) == curscope {
                    0
                } else {
                    symboltab_mut(ctx.glb).symbol_get_resolution_depth(symbol, None)
                }
            }
            NamespaceStrategy::NoNamespaces => 0,
        }
    }

    pub(crate) fn scope_list(&self, ctx: &PrintContext<'_>, symbol: SymbolId, scopedepth: i32) -> Vec<Option<ScopeId>> {
        let db = symboltab(ctx.glb);
        let mut scope_list = Vec::new();
        let mut point = Some(db.symbol(symbol).get_scope());
        for _ in 0..scopedepth {
            scope_list.push(point);
            point = point.and_then(|scope| db.scope(scope).get_parent());
        }
        scope_list
    }

    pub fn push_symbol_scope(&mut self, ctx: &mut PrintContext<'_>, symbol: SymbolId) -> Result<()> {
        let scopedepth = self.scope_depth(ctx, symbol);
        if scopedepth != 0 {
            let scope_list = self.scope_list(ctx, symbol, scopedepth);
            for _ in 0..scopedepth {
                self.push_op(ctx, OpTokenKey::Scope, None)?;
            }
            for scope in scope_list.iter().rev() {
                let name = match scope {
                    Some(scope) => symboltab(ctx.glb).scope(*scope).get_display_name().to_string(),
                    None => return Err(Error::Lowlevel("symbol scope path is too short".to_string())),
                };
                self.push_atom(
                    ctx,
                    &Atom::with_varnode(&name, PrintTagType::Syntax, SyntaxHighlight::GlobalColor, None, None),
                )?;
            }
        }
        Ok(())
    }

    pub fn emit_symbol_scope(&mut self, ctx: &mut PrintContext<'_>, symbol: SymbolId) -> Result<()> {
        let scopedepth = self.scope_depth(ctx, symbol);
        if scopedepth != 0 {
            let scope_list = self.scope_list(ctx, symbol, scopedepth);
            let delimiter = self.get_token(OpTokenKey::Scope).print1;
            for scope in scope_list.iter().rev() {
                let name = match scope {
                    Some(scope) => symboltab(ctx.glb).scope(*scope).get_display_name().to_string(),
                    None => return Err(Error::Lowlevel("symbol scope path is too short".to_string())),
                };
                self.emit().print(&name, SyntaxHighlight::GlobalColor)?;
                self.emit().print(delimiter, SyntaxHighlight::NoColor)?;
            }
        }
        Ok(())
    }

    pub fn push_type_start(&mut self, ctx: &mut PrintContext<'_>, ct: TypeId, noident: bool) -> Result<()> {
        if self.is_java() {
            self.push_type_start_java(ctx, ct, noident)
        } else {
            self.push_type_start_c(ctx, ct, noident)
        }
    }

    pub fn push_type_end(&mut self, ctx: &mut PrintContext<'_>, ct: TypeId) -> Result<()> {
        if self.is_java() {
            self.push_type_end_java(ctx, ct)
        } else {
            self.push_type_end_c(ctx, ct)
        }
    }

    pub fn push_type_start_c(&mut self, ctx: &mut PrintContext<'_>, ct: TypeId, noident: bool) -> Result<()> {
        let mut typestack = Vec::new();
        self.build_type_stack(ctx, ct, &mut typestack)?;
        let base_type = *typestack.last().expect("type stack is empty");
        let tok = if noident && typestack.len() == 1 {
            OpTokenKey::TypeExprNospace
        } else {
            OpTokenKey::TypeExprSpace
        };
        if types(ctx.glb).get(base_type).get_name().is_empty() {
            let nm = self.generic_type_name(ctx, base_type);
            self.push_op(ctx, tok, None)?;
            self.push_atom(
                ctx,
                &Atom::with_type(&nm, PrintTagType::Typetoken, SyntaxHighlight::TypeColor, base_type),
            )?;
        } else {
            self.push_op(ctx, tok, None)?;
            let nm = display_name(ctx, base_type);
            self.push_atom(
                ctx,
                &Atom::with_type(&nm, PrintTagType::Typetoken, SyntaxHighlight::TypeColor, base_type),
            )?;
        }
        for index in (0..typestack.len().saturating_sub(1)).rev() {
            let current = typestack[index];
            match metatype(ctx, current) {
                TypeMetatype::Ptr => self.push_op(ctx, OpTokenKey::PtrExpr, None)?,
                TypeMetatype::Array => self.push_op(ctx, OpTokenKey::ArrayExpr, None)?,
                TypeMetatype::Code => self.push_op(ctx, OpTokenKey::FunctionCall, None)?,
                _ => {
                    self.clear();
                    return Err(Error::Lowlevel("Bad type expression".to_string()));
                }
            }
        }
        Ok(())
    }

    pub fn push_type_end_c(&mut self, ctx: &mut PrintContext<'_>, ct: TypeId) -> Result<()> {
        self.push_mod();
        self.set_mod(FORCE_DEC);
        let mut ct = ct;
        loop {
            let (has_name, meta) = {
                let datatype = types(ctx.glb).get(ct);
                (!datatype.get_name().is_empty(), datatype.get_metatype())
            };
            if has_name {
                break;
            }
            match meta {
                TypeMetatype::Ptr => ct = ptr_to(ctx, ct),
                TypeMetatype::Array => {
                    let (base, count) = {
                        let datatype = types(ctx.glb).get(ct);
                        (datatype.get_base(), datatype.num_elements())
                    };
                    ct = base;
                    self.push_integer(ctx, count as i64 as u64, 4, false, PrintTagType::Syntax, None, None, 0)?;
                }
                TypeMetatype::Code => {
                    let output = types(ctx.glb)
                        .get(ct)
                        .get_prototype()
                        .map(|proto| proto.get_output_type(ctx.glb));
                    match output {
                        Some(output) => {
                            self.push_prototype_inputs(ctx, ProtoRef::Code(ct))?;
                            ct = output;
                        }
                        None => {
                            self.push_atom(
                                ctx,
                                &Atom::new(EMPTY_STRING, PrintTagType::Blanktoken, SyntaxHighlight::NoColor),
                            )?;
                            break;
                        }
                    }
                }
                _ => break,
            }
        }
        self.pop_mod();
        Ok(())
    }

    pub fn check_array_deref(&self, ctx: &mut PrintContext<'_>, vn: VarnodeId) -> bool {
        let data = ctx.data_ref();
        let mut vn = vn;
        if !data.vn(vn).is_implied() {
            return false;
        }
        if !data.vn(vn).is_written() {
            return false;
        }
        let mut op = data.vn(vn).get_def().expect("written varnode has no defining op");
        if data.op(op).code() == OpCode::Segmentop {
            vn = data.op(op).get_in(2);
            if !data.vn(vn).is_implied() {
                return false;
            }
            if !data.vn(vn).is_written() {
                return false;
            }
            op = data.vn(vn).get_def().expect("written varnode has no defining op");
        }
        let opc = data.op(op).code();
        if opc != OpCode::Ptrsub && opc != OpCode::Ptradd {
            return false;
        }
        true
    }

    pub fn check_bit_field_member(&self, ctx: &mut PrintContext<'_>, vn: VarnodeId, field: &TypeBitField) -> bool {
        let mut vn = vn;
        if field.bits.byte_offset != 0 {
            let data = ctx.data_ref();
            if !data.vn(vn).is_written() {
                return false;
            }
            let op = data.vn(vn).get_def().expect("written varnode has no defining op");
            if data.op(op).code() != OpCode::Ptrsub {
                return false;
            }
            vn = data.op(op).get_in(0);
        }
        self.check_array_deref(ctx, vn)
    }

    pub fn check_address_of_cast(&self, ctx: &mut PrintContext<'_>, op: OpId) -> Result<bool> {
        let outvn = op_out(ctx, op).expect("cast op has no output");
        let dt0 = def_facing_type(ctx, outvn)?;
        let vnin = op_in(ctx, op, 0);
        let dt1 = read_facing_type(ctx, vnin, Some(op))?;
        if metatype(ctx, dt0) != TypeMetatype::Ptr || metatype(ctx, dt1) != TypeMetatype::Ptr {
            return Ok(false);
        }
        let mut base0 = ptr_to(ctx, dt0);
        let mut base1 = ptr_to(ctx, dt1);
        if metatype(ctx, base0) != TypeMetatype::Array {
            return Ok(false);
        }
        let array_size = types(ctx.glb).get(base0).get_size();
        base0 = types(ctx.glb).get(base0).get_base();
        while let Some(typedef) = types(ctx.glb).get(base0).get_typedef() {
            base0 = typedef;
        }
        while let Some(typedef) = types(ctx.glb).get(base1).get_typedef() {
            base1 = typedef;
        }
        if base0 != base1 {
            return Ok(false);
        }
        let mut symbol_type: Option<TypeId> = None;
        let entry = match ctx.data_ref().vn(vnin).get_symbol_entry() {
            Some(entry) => {
                let high = ctx.data_ref().vn(vnin).get_high()?;
                if ctx.data_ref().high(high).get_symbol_offset() == -1 {
                    Some(entry)
                } else {
                    None
                }
            }
            None => None,
        };
        if let Some(entry) = entry {
            let db = symboltab(ctx.glb);
            let sym = db.entry(entry).get_symbol();
            symbol_type = db.symbol(sym).get_type();
        } else if ctx.data_ref().vn(vnin).is_written() {
            let ptrsub = def_op(ctx, vnin)?;
            if op_code(ctx, ptrsub) == OpCode::Ptrsub {
                let root = op_in(ctx, ptrsub, 0);
                let mut root_type = read_facing_type(ctx, root, Some(ptrsub))?;
                if metatype(ctx, root_type) == TypeMetatype::Ptr {
                    root_type = ptr_to(ctx, root_type);
                    let mut off = ctx.data_ref().vn(op_in(ctx, ptrsub, 1)).get_offset() as i64;
                    let start = off;
                    symbol_type = types(ctx.glb).get(root_type).get_sub_type(start, &mut off, ctx.glb);
                    if off != 0 {
                        return Ok(false);
                    }
                }
            }
        }
        let symbol_type = match symbol_type {
            Some(symbol_type) => symbol_type,
            None => return Ok(false),
        };
        let datatype = types(ctx.glb).get(symbol_type);
        if datatype.get_metatype() != TypeMetatype::Array || datatype.get_size() != array_size {
            return Ok(false);
        }
        Ok(true)
    }

    pub fn op_func(&mut self, ctx: &mut PrintContext<'_>, op: OpId) -> Result<()> {
        self.push_op(ctx, OpTokenKey::FunctionCall, Some(op))?;
        let nm = operator_name(ctx, op);
        self.push_atom(
            ctx,
            &Atom::with_op(&nm, PrintTagType::Optoken, SyntaxHighlight::NoColor, Some(op)),
        )?;
        let count = num_input(ctx, op);
        if count > 0 {
            for _ in 0..count - 1 {
                self.push_op(ctx, OpTokenKey::Comma, Some(op))?;
            }
            for index in (0..count).rev() {
                let mods = self.mods();
                self.push_vn(ctx, op_in(ctx, op, index), Some(op), mods)?;
            }
        } else {
            self.push_atom(
                ctx,
                &Atom::new(EMPTY_STRING, PrintTagType::Blanktoken, SyntaxHighlight::NoColor),
            )?;
        }
        Ok(())
    }

    pub fn op_type_cast(&mut self, ctx: &mut PrintContext<'_>, op: OpId) -> Result<()> {
        let outvn = op_out(ctx, op).expect("cast op has no output");
        let dt = def_facing_type(ctx, outvn)?;
        if types(ctx.glb).get(dt).is_pointer_to_array() && self.check_address_of_cast(ctx, op)? {
            self.push_op(ctx, OpTokenKey::Addressof, Some(op))?;
            let mods = self.mods();
            return self.push_vn(ctx, op_in(ctx, op, 0), Some(op), mods);
        }
        if !self.option_nocasts {
            self.push_op(ctx, OpTokenKey::Typecast, Some(op))?;
            self.push_type(ctx, dt)?;
        }
        let mods = self.mods();
        self.push_vn(ctx, op_in(ctx, op, 0), Some(op), mods)
    }

    pub fn op_hidden_func(&mut self, ctx: &mut PrintContext<'_>, op: OpId) -> Result<()> {
        self.push_op(ctx, OpTokenKey::Hidden, Some(op))?;
        let mods = self.mods();
        self.push_vn(ctx, op_in(ctx, op, 0), Some(op), mods)
    }

    pub fn op_load_c(&mut self, ctx: &mut PrintContext<'_>, op: OpId) -> Result<()> {
        let in1 = op_in(ctx, op, 1);
        let usearray = self.check_array_deref(ctx, in1);
        let mut mods = self.mods();
        if usearray && !self.is_set(FORCE_POINTER) {
            mods |= PRINT_LOAD_VALUE;
        } else {
            self.push_op(ctx, OpTokenKey::Dereference, Some(op))?;
        }
        self.push_vn(ctx, in1, Some(op), mods)
    }

    pub fn op_store_c(&mut self, ctx: &mut PrintContext<'_>, op: OpId) -> Result<()> {
        let mut store_mods = self.mods();
        self.push_op(ctx, OpTokenKey::Assignment, Some(op))?;
        let in1 = op_in(ctx, op, 1);
        let usearray = self.check_array_deref(ctx, in1);
        if usearray && !self.is_set(FORCE_POINTER) {
            store_mods |= PRINT_STORE_VALUE;
        } else {
            self.push_op(ctx, OpTokenKey::Dereference, Some(op))?;
        }
        let mods = self.mods();
        self.push_vn(ctx, op_in(ctx, op, 2), Some(op), mods)?;
        self.push_vn(ctx, in1, Some(op), store_mods)
    }

    pub fn op_callind_c(&mut self, ctx: &mut PrintContext<'_>, op: OpId) -> Result<()> {
        self.push_op(ctx, OpTokenKey::FunctionCall, Some(op))?;
        self.push_op(ctx, OpTokenKey::Dereference, Some(op))?;
        self.push_callind_arguments(ctx, op)
    }

    pub fn push_callind_arguments(&mut self, ctx: &mut PrintContext<'_>, op: OpId) -> Result<()> {
        let fc = match ctx.data_ref().get_call_specs_op(op) {
            Some(fc) => fc,
            None => return Err(Error::Lowlevel("Missing indirect function callspec".to_string())),
        };
        let skip = self.get_hidden_this_slot(ctx, op, ProtoRef::CallSpec(fc));
        let total = num_input(ctx, op);
        let mut count = total - 1;
        count -= if skip < 0 { 0 } else { 1 };
        let mods = self.mods();
        if count > 1 {
            self.push_vn(ctx, op_in(ctx, op, 0), Some(op), mods)?;
            for _ in 0..count - 1 {
                self.push_op(ctx, OpTokenKey::Comma, Some(op))?;
            }
            for index in (1..total).rev() {
                if index == skip {
                    continue;
                }
                self.push_vn(ctx, op_in(ctx, op, index), Some(op), mods)?;
            }
        } else if count == 1 {
            if skip == 1 {
                self.push_vn(ctx, op_in(ctx, op, 2), Some(op), mods)?;
            } else {
                self.push_vn(ctx, op_in(ctx, op, 1), Some(op), mods)?;
            }
            self.push_vn(ctx, op_in(ctx, op, 0), Some(op), mods)?;
        } else {
            self.push_vn(ctx, op_in(ctx, op, 0), Some(op), mods)?;
            self.push_atom(
                ctx,
                &Atom::new(EMPTY_STRING, PrintTagType::Blanktoken, SyntaxHighlight::NoColor),
            )?;
        }
        Ok(())
    }
}

mod constants;
mod emission;
mod language;
mod operators;
