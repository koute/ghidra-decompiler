use crate::architecture::Architecture;
use crate::cast::CastStrategyJava;
use crate::cpool::CPoolRecord;
use crate::error::{Error, Result};
use crate::op::OpId;
use crate::opcodes::OpCode;
use crate::prettyprint::SyntaxHighlight;
use crate::printc::{EMPTY_STRING, PrintC, PrintFlavor, display_name, metatype, ptr_to, write_utf8_char};
use crate::printlanguage::{
    Atom, HIDE_THISPARAM, OpTokenKey, PRINT_LOAD_VALUE, PRINT_STORE_VALUE, PrintContext, PrintLanguage,
    PrintLanguageCapability, PrintTagType, types, types_mut, unicode_needs_escape,
};
use crate::types::{TypeId, TypeMetatype};
use crate::varnode::VarnodeId;

pub struct PrintJavaCapability {
    pub name: &'static str,
    pub isdefault: bool,
}

pub static PRINT_JAVA_CAPABILITY: PrintJavaCapability = PrintJavaCapability {
    name: "java-language",
    isdefault: false,
};

impl PrintLanguageCapability for PrintJavaCapability {
    fn get_name(&self) -> &str {
        self.name
    }

    fn is_default(&self) -> bool {
        self.isdefault
    }

    fn build_language(&self, glb: &mut Architecture) -> Box<dyn PrintLanguage> {
        Box::new(PrintC::new_java(glb, self.name))
    }
}

pub fn is_array_type(ctx: &mut PrintContext<'_>, ct: TypeId) -> bool {
    if metatype(ctx, ct) != TypeMetatype::Ptr {
        return false;
    }
    let ct = ptr_to(ctx, ct);
    let datatype = types(ctx.glb).get(ct);
    match datatype.get_metatype() {
        TypeMetatype::Uint => datatype.is_char_print(),
        TypeMetatype::Int | TypeMetatype::Bool | TypeMetatype::Float | TypeMetatype::Ptr => true,
        _ => false,
    }
}

pub fn need_zero_array(ctx: &mut PrintContext<'_>, vn: VarnodeId) -> bool {
    let tp = ctx.data_ref().vn(vn).get_type();
    if !is_array_type(ctx, tp) {
        return false;
    }
    let varnode = ctx.data_ref().vn(vn);
    if varnode.is_explicit() {
        return true;
    }
    if !varnode.is_written() {
        return true;
    }
    let def = varnode.get_def().expect("written varnode has no defining op");
    let opc = ctx.data_ref().op(def).code();
    if opc == OpCode::Ptradd || opc == OpCode::Ptrsub || opc == OpCode::Cpoolref {
        return false;
    }
    true
}

pub fn print_unicode_java_style(out: &mut String, onechar: i32) {
    if unicode_needs_escape(onechar) {
        match onechar {
            0 => out.push_str("\\0"),
            8 => out.push_str("\\b"),
            9 => out.push_str("\\t"),
            10 => out.push_str("\\n"),
            12 => out.push_str("\\f"),
            13 => out.push_str("\\r"),
            92 => out.push_str("\\\\"),
            0x22 => out.push_str("\\\""),
            0x27 => out.push_str("\\'"),
            _ => {
                if onechar < 65536 {
                    out.push_str(&format!("\\ux{:04x}", onechar as u32));
                } else {
                    out.push_str(&format!("\\ux{:08x}", onechar as u32));
                }
            }
        }
        return;
    }
    write_utf8_char(out, onechar);
}

impl PrintC {
    pub fn new_java(glb: &mut Architecture, nm: &str) -> PrintC {
        let mut printer = PrintC::new(glb, nm);
        printer.flavor = PrintFlavor::Java;
        printer.reset_defaults_print_java();
        printer.null_token = "null".to_string();
        printer.base.cast_strategy = Some(Box::new(CastStrategyJava::new()));
        printer
    }

    pub fn reset_defaults_print_java(&mut self) {
        self.option_null = true;
        self.option_convention = false;
        self.base.mods |= HIDE_THISPARAM;
    }

    pub fn print_unicode_java(&self, out: &mut String, onechar: i32) {
        print_unicode_java_style(out, onechar);
    }

    pub fn reset_defaults_java(&mut self) {
        self.reset_defaults_c();
        self.reset_defaults_print_java();
    }

    pub fn doc_function_java(&mut self, ctx: &mut PrintContext<'_>) -> Result<()> {
        let mut singleton_function = false;
        if self.base.curscope.is_none() {
            singleton_function = true;
            let local = ctx.data_ref().get_scope_local();
            let parent = local.and_then(|scope| crate::printlanguage::symboltab(ctx.glb).scope(scope).get_parent());
            self.push_scope(parent);
        }
        self.doc_function_c(ctx)?;
        if singleton_function {
            self.pop_scope();
        }
        Ok(())
    }

    pub fn push_type_start_java(&mut self, ctx: &mut PrintContext<'_>, ct: TypeId, noident: bool) -> Result<()> {
        let mut ct = ct;
        let mut array_count = 0;
        loop {
            if metatype(ctx, ct) == TypeMetatype::Ptr {
                if is_array_type(ctx, ct) {
                    array_count += 1;
                }
                ct = ptr_to(ctx, ct);
            } else if !types(ctx.glb).get(ct).get_name().is_empty() {
                break;
            } else {
                ct = types_mut(ctx.glb).get_type_void()?;
                break;
            }
        }
        let tok = if noident {
            OpTokenKey::TypeExprNospace
        } else {
            OpTokenKey::TypeExprSpace
        };
        self.push_op(ctx, tok, None)?;
        for _ in 0..array_count {
            self.push_op(ctx, OpTokenKey::Subscript, None)?;
        }
        if types(ctx.glb).get(ct).get_name().is_empty() {
            let nm = self.generic_type_name(ctx, ct);
            self.push_atom(
                ctx,
                &Atom::with_type(&nm, PrintTagType::Typetoken, SyntaxHighlight::TypeColor, ct),
            )?;
        } else {
            let nm = display_name(ctx, ct);
            self.push_atom(
                ctx,
                &Atom::with_type(&nm, PrintTagType::Typetoken, SyntaxHighlight::TypeColor, ct),
            )?;
        }
        for _ in 0..array_count {
            self.push_atom(
                ctx,
                &Atom::new(EMPTY_STRING, PrintTagType::Blanktoken, SyntaxHighlight::NoColor),
            )?;
        }
        Ok(())
    }

    pub fn push_type_end_java(&mut self, _ctx: &mut PrintContext<'_>, _ct: TypeId) -> Result<()> {
        Ok(())
    }

    pub fn adjust_type_operators_java(&mut self, glb: &mut Architecture) {
        self.base.tokens[OpTokenKey::Scope.index()].print1 = ".";
        self.base.tokens[OpTokenKey::ShiftRight.index()].print1 = ">>>";
        crate::typeop::select_java_operators(&mut glb.inst, true);
    }

    pub fn op_load_java(&mut self, ctx: &mut PrintContext<'_>, op: OpId) -> Result<()> {
        let load_mods = self.base.mods | PRINT_LOAD_VALUE;
        let in1 = ctx.data_ref().op(op).get_in(1);
        let print_array_ref = need_zero_array(ctx, in1);
        if print_array_ref {
            self.push_op(ctx, OpTokenKey::Subscript, Some(op))?;
        }
        self.push_vn(ctx, in1, Some(op), load_mods)?;
        if print_array_ref {
            self.push_integer(ctx, 0, 4, false, PrintTagType::Syntax, None, Some(op), 0)?;
        }
        Ok(())
    }

    pub fn op_store_java(&mut self, ctx: &mut PrintContext<'_>, op: OpId) -> Result<()> {
        let store_mods = self.base.mods | PRINT_STORE_VALUE;
        self.push_op(ctx, OpTokenKey::Assignment, Some(op))?;
        let in1 = ctx.data_ref().op(op).get_in(1);
        let in2 = ctx.data_ref().op(op).get_in(2);
        let mods = self.base.mods;
        if need_zero_array(ctx, in1) {
            self.push_op(ctx, OpTokenKey::Subscript, Some(op))?;
            self.push_vn(ctx, in1, Some(op), store_mods)?;
            self.push_integer(ctx, 0, 4, false, PrintTagType::Syntax, None, Some(op), 0)?;
            self.push_vn(ctx, in2, Some(op), mods)?;
        } else {
            self.push_vn(ctx, in2, Some(op), mods)?;
            self.push_vn(ctx, in1, Some(op), store_mods)?;
        }
        Ok(())
    }

    pub fn op_callind_java(&mut self, ctx: &mut PrintContext<'_>, op: OpId) -> Result<()> {
        self.push_op(ctx, OpTokenKey::FunctionCall, Some(op))?;
        self.push_callind_arguments(ctx, op)
    }

    pub fn op_cpool_ref_op_java(&mut self, ctx: &mut PrintContext<'_>, op: OpId) -> Result<()> {
        let outvn = ctx.data_ref().op(op).get_out();
        let vn0 = ctx.data_ref().op(op).get_in(0);
        let mut refs: Vec<u64> = Vec::new();
        let total = ctx.data_ref().op(op).num_input();
        for index in 1..total {
            let input = ctx.data_ref().op(op).get_in(index);
            refs.push(ctx.data_ref().vn(input).get_offset());
        }
        let record = ctx
            .glb
            .cpool
            .as_deref()
            .expect("constant pool is not initialized")
            .get_record(&refs)
            .cloned();
        let record = match record {
            None => {
                return self.push_atom(
                    ctx,
                    &Atom::with_varnode(
                        "UNKNOWNREF",
                        PrintTagType::Syntax,
                        SyntaxHighlight::ConstColor,
                        Some(op),
                        outvn,
                    ),
                );
            }
            Some(record) => record,
        };
        let mods = self.base.mods;
        match record.get_tag() {
            CPoolRecord::STRING_LITERAL => {
                let mut text = String::new();
                let full_length = record.get_byte_data_length();
                let len = full_length.min(2048);
                text.push('"');
                let bytes = record.get_byte_data().unwrap_or(&[]);
                self.escape_character_data(&mut text, bytes, len, 1, false);
                if len == full_length {
                    text.push('"');
                } else {
                    text.push_str("...\"");
                }
                self.push_atom(
                    ctx,
                    &Atom::with_varnode(
                        &text,
                        PrintTagType::Vartoken,
                        SyntaxHighlight::ConstColor,
                        Some(op),
                        outvn,
                    ),
                )
            }
            CPoolRecord::CLASS_REFERENCE => self.push_atom(
                ctx,
                &Atom::with_varnode(
                    record.get_token(),
                    PrintTagType::Vartoken,
                    SyntaxHighlight::TypeColor,
                    Some(op),
                    outvn,
                ),
            ),
            CPoolRecord::INSTANCE_OF => {
                let mut dt = match record.get_type() {
                    Some(dt) => dt,
                    None => return Err(Error::Lowlevel("constant pool record has no data-type".to_string())),
                };
                while metatype(ctx, dt) == TypeMetatype::Ptr {
                    dt = ptr_to(ctx, dt);
                }
                self.push_op(ctx, OpTokenKey::Instanceof, Some(op))?;
                self.push_vn(ctx, vn0, Some(op), mods)?;
                let nm = display_name(ctx, dt);
                self.push_atom(
                    ctx,
                    &Atom::with_varnode(&nm, PrintTagType::Syntax, SyntaxHighlight::TypeColor, Some(op), outvn),
                )
            }
            _ => {
                let mut ct = match record.get_type() {
                    Some(ct) => ct,
                    None => return Err(Error::Lowlevel("constant pool record has no data-type".to_string())),
                };
                let mut color = SyntaxHighlight::VarColor;
                if metatype(ctx, ct) == TypeMetatype::Ptr {
                    ct = ptr_to(ctx, ct);
                    if metatype(ctx, ct) == TypeMetatype::Code {
                        color = SyntaxHighlight::FuncnameColor;
                    }
                }
                if ctx.data_ref().vn(vn0).is_constant() {
                    self.push_atom(
                        ctx,
                        &Atom::with_varnode(record.get_token(), PrintTagType::Vartoken, color, Some(op), outvn),
                    )
                } else {
                    self.push_op(ctx, OpTokenKey::ObjectMember, Some(op))?;
                    self.push_vn(ctx, vn0, Some(op), mods)?;
                    self.push_atom(
                        ctx,
                        &Atom::with_varnode(record.get_token(), PrintTagType::Syntax, color, Some(op), outvn),
                    )
                }
            }
        }
    }
}
