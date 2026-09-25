use super::*;

impl PrintC {
    pub(crate) fn op_branch_c(&mut self, ctx: &mut PrintContext<'_>, op: OpId) -> Result<()> {
        if self.is_set(FLAT) {
            let mark = ctx.op_mark(Some(op));
            self.emit().tag_op(KEYWORD_GOTO, SyntaxHighlight::KeywordColor, mark)?;
            self.emit().spaces(1, 0)?;
            let mods = self.mods();
            self.push_vn(ctx, op_in(ctx, op, 0), Some(op), mods)?;
        }
        Ok(())
    }

    pub(crate) fn op_cbranch_c(&mut self, ctx: &mut PrintContext<'_>, op: OpId) -> Result<()> {
        let yesif = self.is_set(FLAT);
        let yesparen = !self.is_set(COMMA_SEPARATE);
        let mut booleanflip = ctx.data_ref().op(op).is_boolean_flip();
        let mut branch_mods = self.mods();
        if yesif {
            let mark = ctx.op_mark(Some(op));
            self.emit().tag_op(KEYWORD_IF, SyntaxHighlight::KeywordColor, mark)?;
            self.emit().spaces(1, 0)?;
            if ctx.data_ref().op(op).is_fallthru_true() {
                booleanflip = !booleanflip;
                branch_mods |= FALSEBRANCH;
            }
        }
        let id = if yesparen {
            self.emit().open_paren(crate::printlanguage::OPEN_PAREN, 0)?
        } else {
            self.emit().open_group()?
        };
        let in1 = op_in(ctx, op, 1);
        if booleanflip && self.check_print_negation(ctx, in1) {
            branch_mods |= NEGATETOKEN;
            booleanflip = false;
        }
        if booleanflip {
            self.push_op(ctx, OpTokenKey::BooleanNot, Some(op))?;
        }
        self.push_vn(ctx, in1, Some(op), branch_mods)?;
        self.recurse(ctx)?;
        if yesparen {
            self.emit().close_paren(crate::printlanguage::CLOSE_PAREN, id)?;
        } else {
            self.emit().close_group(id)?;
        }
        if yesif {
            self.emit().spaces(1, 0)?;
            self.emit().print(KEYWORD_GOTO, SyntaxHighlight::KeywordColor)?;
            self.emit().spaces(1, 0)?;
            let mods = self.mods();
            self.push_vn(ctx, op_in(ctx, op, 0), Some(op), mods)?;
        }
        Ok(())
    }

    pub(crate) fn op_branchind_c(&mut self, ctx: &mut PrintContext<'_>, op: OpId) -> Result<()> {
        let mark = ctx.op_mark(Some(op));
        self.emit()
            .tag_op(KEYWORD_SWITCH, SyntaxHighlight::KeywordColor, mark)?;
        let id = self.emit().open_paren(crate::printlanguage::OPEN_PAREN, 0)?;
        let mods = self.mods();
        self.push_vn(ctx, op_in(ctx, op, 0), Some(op), mods)?;
        self.recurse(ctx)?;
        self.emit().close_paren(crate::printlanguage::CLOSE_PAREN, id)
    }

    pub(crate) fn op_call_c(&mut self, ctx: &mut PrintContext<'_>, op: OpId) -> Result<()> {
        self.push_op(ctx, OpTokenKey::FunctionCall, Some(op))?;
        let callpoint = op_in(ctx, op, 0);
        let is_fspec = match ctx.data_ref().vn(callpoint).get_space() {
            Some(space) => space.get_type() == SpaceType::Fspec,
            None => false,
        };
        if is_fspec {
            let addr = ctx.data_ref().vn(callpoint).get_addr().clone();
            let fc = FuncCallSpecs::get_fspec_from_const(&addr);
            let (name, entry, function) = {
                let spec = ctx.data_ref().call_spec(fc);
                (
                    spec.get_name().to_string(),
                    spec.get_entry_address().clone(),
                    spec.get_funcdata(),
                )
            };
            if name.is_empty() {
                let nm = self.generic_function_name(&entry);
                self.push_atom(
                    ctx,
                    &Atom::with_func(
                        &nm,
                        PrintTagType::Functoken,
                        SyntaxHighlight::FuncnameColor,
                        Some(op),
                        None,
                    ),
                )?;
            } else {
                if let Some(function) = function {
                    self.push_symbol_scope(ctx, function)?;
                }
                self.push_atom(
                    ctx,
                    &Atom::with_func(
                        &name,
                        PrintTagType::Functoken,
                        SyntaxHighlight::FuncnameColor,
                        Some(op),
                        None,
                    ),
                )?;
            }
        } else {
            self.clear();
            return Err(Error::Lowlevel("Missing function callspec".to_string()));
        }
        let skip = -1;
        let total = num_input(ctx, op);
        let mut count = total - 1;
        count -= if skip < 0 { 0 } else { 1 };
        if count > 0 {
            for _ in 0..count - 1 {
                self.push_op(ctx, OpTokenKey::Comma, Some(op))?;
            }
            for index in (1..total).rev() {
                if index == skip {
                    continue;
                }
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

    pub(crate) fn op_callother_c(&mut self, ctx: &mut PrintContext<'_>, op: OpId) -> Result<()> {
        let index = ctx.data_ref().vn(op_in(ctx, op, 0)).get_offset() as u32;
        let userop: std::sync::Arc<UserPcodeOp> = match ctx.glb.userops.get_op(index) {
            Some(userop) => userop.clone(),
            None => return Err(Error::Lowlevel("Unknown user-defined p-code op".to_string())),
        };
        let display = userop.get_display();
        let mods = self.mods();
        if display == 0 {
            let nm = operator_name(ctx, op);
            self.push_op(ctx, OpTokenKey::FunctionCall, Some(op))?;
            self.push_atom(
                ctx,
                &Atom::with_op(&nm, PrintTagType::Optoken, SyntaxHighlight::FuncnameColor, Some(op)),
            )?;
            let total = num_input(ctx, op);
            if total > 1 {
                for _ in 1..total - 1 {
                    self.push_op(ctx, OpTokenKey::Comma, Some(op))?;
                }
                for index in (1..total).rev() {
                    self.push_vn(ctx, op_in(ctx, op, index), Some(op), mods)?;
                }
            } else {
                self.push_atom(
                    ctx,
                    &Atom::new(EMPTY_STRING, PrintTagType::Blanktoken, SyntaxHighlight::NoColor),
                )?;
            }
        } else if display == UserPcodeOp::ANNOTATION_ASSIGNMENT {
            self.push_op(ctx, OpTokenKey::Assignment, Some(op))?;
            self.push_vn(ctx, op_in(ctx, op, 2), Some(op), mods)?;
            self.push_vn(ctx, op_in(ctx, op, 1), Some(op), mods)?;
        } else if display == UserPcodeOp::NO_OPERATOR {
            self.push_vn(ctx, op_in(ctx, op, 1), Some(op), mods)?;
        } else if display == UserPcodeOp::DISPLAY_STRING {
            let vn = op_out(ctx, op).expect("display string op has no output");
            let mut ct = ctx.data_ref().vn(vn).get_type();
            let mut text = String::new();
            if metatype(ctx, ct) == TypeMetatype::Ptr {
                ct = ptr_to(ctx, ct);
                let addr = ctx.data_ref().vn(op_in(ctx, op, 1)).get_addr().clone();
                if !self.print_character_constant(ctx, &mut text, &addr, ct)? {
                    text.push_str("\"badstring\"");
                }
            } else {
                text.push_str("\"badstring\"");
            }
            self.push_atom(
                ctx,
                &Atom::with_varnode(
                    &text,
                    PrintTagType::Vartoken,
                    SyntaxHighlight::ConstColor,
                    Some(op),
                    Some(vn),
                ),
            )?;
        }
        Ok(())
    }

    pub(crate) fn op_constructor_c(&mut self, ctx: &mut PrintContext<'_>, op: OpId, with_new: bool) -> Result<()> {
        let mut dt;
        if with_new {
            let newop = def_op(ctx, op_in(ctx, op, 1))?;
            let outvn = op_out(ctx, newop);
            self.push_op(ctx, OpTokenKey::NewOp, Some(newop))?;
            self.push_atom(
                ctx,
                &Atom::with_varnode(
                    KEYWORD_NEW,
                    PrintTagType::Optoken,
                    SyntaxHighlight::KeywordColor,
                    Some(newop),
                    outvn,
                ),
            )?;
            let outvn = outvn.expect("new op has no output");
            dt = ctx.data_ref().vn_get_type_def_facing(outvn, ctx.glb);
        } else {
            let thisvn = op_in(ctx, op, 1);
            dt = ctx.data_ref().vn(thisvn).get_type();
        }
        if metatype(ctx, dt) == TypeMetatype::Ptr {
            dt = ptr_to(ctx, dt);
        }
        let nm = display_name(ctx, dt);
        self.push_op(ctx, OpTokenKey::FunctionCall, Some(op))?;
        self.push_atom(
            ctx,
            &Atom::with_op(&nm, PrintTagType::Optoken, SyntaxHighlight::FuncnameColor, Some(op)),
        )?;
        let total = num_input(ctx, op);
        let mods = self.mods();
        if total > 3 {
            for _ in 2..total - 1 {
                self.push_op(ctx, OpTokenKey::Comma, Some(op))?;
            }
            for index in (2..total).rev() {
                self.push_vn(ctx, op_in(ctx, op, index), Some(op), mods)?;
            }
        } else if total == 3 {
            self.push_vn(ctx, op_in(ctx, op, 2), Some(op), mods)?;
        } else {
            self.push_atom(
                ctx,
                &Atom::new(EMPTY_STRING, PrintTagType::Blanktoken, SyntaxHighlight::NoColor),
            )?;
        }
        Ok(())
    }

    pub(crate) fn op_return_c(&mut self, ctx: &mut PrintContext<'_>, op: OpId) -> Result<()> {
        let halt = ctx.data_ref().op(op).get_halt_type();
        let nm = if halt == PcodeOp::NORETURN || halt == PcodeOp::HALT {
            "halt"
        } else if halt == PcodeOp::BADINSTRUCTION {
            "halt_baddata"
        } else if halt == PcodeOp::UNIMPLEMENTED {
            "halt_unimplemented"
        } else if halt == PcodeOp::MISSING {
            "halt_missing"
        } else {
            let mark = ctx.op_mark(Some(op));
            self.emit()
                .tag_op(KEYWORD_RETURN, SyntaxHighlight::KeywordColor, mark)?;
            if num_input(ctx, op) > 1 {
                self.emit().spaces(1, 0)?;
                let mods = self.mods();
                self.push_vn(ctx, op_in(ctx, op, 1), Some(op), mods)?;
            }
            return Ok(());
        };
        self.push_op(ctx, OpTokenKey::FunctionCall, Some(op))?;
        self.push_atom(
            ctx,
            &Atom::with_op(nm, PrintTagType::Optoken, SyntaxHighlight::FuncnameColor, Some(op)),
        )?;
        self.push_atom(
            ctx,
            &Atom::new(EMPTY_STRING, PrintTagType::Blanktoken, SyntaxHighlight::NoColor),
        )
    }

    pub(crate) fn op_extension(
        &mut self,
        ctx: &mut PrintContext<'_>,
        op: OpId,
        read_op: Option<OpId>,
        zext: bool,
    ) -> Result<()> {
        let outvn = op_out(ctx, op).expect("extension op has no output");
        let outtype = def_facing_type(ctx, outvn)?;
        let intype = read_facing_type(ctx, op_in(ctx, op, 0), Some(op))?;
        let is_cast = {
            let cast = self.base.cast_strategy.as_deref().expect("no cast strategy");
            if zext {
                cast.is_zext_cast(outtype, intype, types(ctx.glb))
            } else {
                cast.is_sext_cast(outtype, intype, types(ctx.glb))
            }
        };
        if is_cast {
            let implied = self.option_hide_exts && {
                let cast = self.base.cast_strategy.as_deref().expect("no cast strategy");
                let (glb, data) = ctx.parts();
                cast.is_extension_cast_implied(op, read_op, data, glb)?
            };
            if implied {
                self.op_hidden_func(ctx, op)
            } else {
                self.op_type_cast(ctx, op)
            }
        } else {
            self.op_func(ctx, op)
        }
    }

    pub(crate) fn op_bool_negate_c(&mut self, ctx: &mut PrintContext<'_>, op: OpId) -> Result<()> {
        let in0 = op_in(ctx, op, 0);
        if self.is_set(NEGATETOKEN) {
            self.unset_mod(NEGATETOKEN);
            let mods = self.mods();
            self.push_vn(ctx, in0, Some(op), mods)
        } else if self.check_print_negation(ctx, in0) {
            let mods = self.mods();
            self.push_vn(ctx, in0, Some(op), mods | NEGATETOKEN)
        } else {
            self.push_op(ctx, OpTokenKey::BooleanNot, Some(op))?;
            let mods = self.mods();
            self.push_vn(ctx, in0, Some(op), mods)
        }
    }

    pub(crate) fn op_float_int2float_c(&mut self, ctx: &mut PrintContext<'_>, op: OpId) -> Result<()> {
        let zext_op = TypeOpFloatInt2Float::absorb_zext(op, ctx.data_ref());
        let vn0 = match zext_op {
            Some(zext) => op_in(ctx, zext, 0),
            None => op_in(ctx, op, 0),
        };
        let outvn = op_out(ctx, op).expect("conversion op has no output");
        let dt = def_facing_type(ctx, outvn)?;
        if !self.option_nocasts {
            self.push_op(ctx, OpTokenKey::Typecast, Some(op))?;
            self.push_type(ctx, dt)?;
        }
        let mods = self.mods();
        self.push_vn(ctx, vn0, Some(op), mods)
    }

    pub(crate) fn op_subpiece_c(&mut self, ctx: &mut PrintContext<'_>, op: OpId) -> Result<()> {
        let outvn = op_out(ctx, op).expect("subpiece op has no output");
        if ctx.data_ref().op(op).does_special_printing() {
            let vn = op_in(ctx, op, 0);
            let ct = read_facing_type(ctx, vn, Some(op))?;
            if types(ctx.glb).get(ct).is_piece_structured() {
                let mut byte_off = TypeOpSubpiece::compute_byte_offset_for_composite(op, ctx.data_ref()) as i64;
                let high = ctx.data_ref().vn(vn).get_high()?;
                let sym = {
                    let (glb, data) = ctx.parts();
                    data.high_get_symbol(high, glb)
                };
                if let Some(sym) = sym
                    && ctx.data_ref().vn(vn).is_explicit()
                {
                    let sz = ctx.data_ref().vn(outvn).get_size();
                    let suboff = ctx.data_ref().high(high).get_symbol_offset();
                    if suboff > 0 {
                        byte_off += suboff as i64;
                    }
                    let slot = if types(ctx.glb).get(ct).needs_resolution() {
                        1
                    } else {
                        0
                    };
                    return self.push_partial_symbol(ctx, sym, byte_off as i32, sz, Some(outvn), Some(op), slot, true);
                }
                let mut offset: i64 = 0;
                let out_size = ctx.data_ref().vn(outvn).get_size();
                let field = crate::types::Datatype::find_truncation(
                    ct,
                    byte_off,
                    out_size,
                    op,
                    1,
                    &mut offset,
                    ctx.data_ref(),
                    ctx.glb,
                );
                if let Some(field) = field
                    && offset == 0
                {
                    self.push_op(ctx, OpTokenKey::ObjectMember, Some(op))?;
                    let mods = self.mods();
                    self.push_vn(ctx, vn, Some(op), mods)?;
                    return self.push_atom(
                        ctx,
                        &Atom::with_field(
                            &field.name,
                            PrintTagType::Fieldtoken,
                            SyntaxHighlight::NoColor,
                            ct,
                            field.ident,
                            Some(op),
                        ),
                    );
                }
            }
        }
        let outtype = def_facing_type(ctx, outvn)?;
        let intype = read_facing_type(ctx, op_in(ctx, op, 0), Some(op))?;
        let offset = ctx.data_ref().vn(op_in(ctx, op, 1)).get_offset() as u32;
        let is_cast = self
            .base
            .cast_strategy
            .as_deref()
            .expect("no cast strategy")
            .is_subpiece_cast(outtype, intype, offset, types(ctx.glb));
        if is_cast {
            self.op_type_cast(ctx, op)
        } else {
            self.op_func(ctx, op)
        }
    }

    pub(crate) fn op_ptradd_c(&mut self, ctx: &mut PrintContext<'_>, op: OpId) -> Result<()> {
        let printval = self.is_set(PRINT_LOAD_VALUE | PRINT_STORE_VALUE);
        let mods = self.mods() & !(PRINT_LOAD_VALUE | PRINT_STORE_VALUE);
        if printval {
            self.push_op(ctx, OpTokenKey::Subscript, Some(op))?;
        } else {
            self.push_op(ctx, OpTokenKey::BinaryPlus, Some(op))?;
        }
        self.push_vn(ctx, op_in(ctx, op, 1), Some(op), mods)?;
        self.push_vn(ctx, op_in(ctx, op, 0), Some(op), mods)
    }

    pub(crate) fn push_field_atom(
        &mut self,
        ctx: &mut PrintContext<'_>,
        fieldname: &str,
        ct: TypeId,
        fieldid: i32,
        op: OpId,
    ) -> Result<()> {
        self.push_atom(
            ctx,
            &Atom::with_field(
                fieldname,
                PrintTagType::Fieldtoken,
                SyntaxHighlight::NoColor,
                ct,
                fieldid,
                Some(op),
            ),
        )
    }

    pub(crate) fn op_ptrsub_c(&mut self, ctx: &mut PrintContext<'_>, op: OpId) -> Result<()> {
        let in0 = op_in(ctx, op, 0);
        let in1const = ctx.data_ref().vn(op_in(ctx, op, 1)).get_offset();
        let ptype = read_facing_type(ctx, in0, Some(op))?;
        if metatype(ctx, ptype) != TypeMetatype::Ptr {
            self.clear();
            return Err(Error::Lowlevel("PTRSUB off of non-pointer type".to_string()));
        }
        let ptrel;
        let mut ct;
        {
            let datatype = types(ctx.glb).get(ptype);
            if datatype.is_formal_pointer_rel() && datatype.evaluate_thru_parent(in1const, types(ctx.glb)) {
                ptrel = Some(ptype);
                ct = datatype.get_parent();
            } else {
                ptrel = None;
                ct = datatype.get_ptr_to();
            }
        }
        let mods = self.mods() & !(PRINT_LOAD_VALUE | PRINT_STORE_VALUE);
        let mut valueon = (self.mods() & (PRINT_LOAD_VALUE | PRINT_STORE_VALUE)) != 0;
        let flex = is_value_flexible(ctx.data_ref(), in0);
        let meta = metatype(ctx, ct);
        if meta == TypeMetatype::Struct || meta == TypeMetatype::Union {
            let mut suboff: i64 = in1const as i32 as i64;
            if let Some(rel) = ptrel {
                suboff += types(ctx.glb).get(rel).get_address_offset() as i64;
                suboff &= calc_mask(types(ctx.glb).get(ptype).get_size()) as i64;
                if suboff == 0 {
                    self.push_type_pointer_rel(ctx, op)?;
                    if flex {
                        return self.push_vn(ctx, in0, Some(op), mods | PRINT_LOAD_VALUE);
                    } else {
                        return self.push_vn(ctx, in0, Some(op), mods);
                    }
                }
            }
            suboff = AddrSpace::address_to_byte_int(suboff, types(ctx.glb).get(ptype).get_word_size());
            let fieldname: String;
            let fieldtype: Option<TypeId>;
            let fieldid: i32;
            if meta == TypeMetatype::Union {
                if suboff != 0 {
                    return Err(Error::Lowlevel(
                        "PTRSUB accesses union with non-zero offset".to_string(),
                    ));
                }
                let field_num = ctx
                    .data_ref()
                    .get_union_field(ptype, op, -1, ctx.glb)
                    .map(|resolved| resolved.get_field_num());
                let field_num = match field_num {
                    Some(num) if num >= 0 => num,
                    _ => {
                        return Err(Error::Lowlevel(
                            "PTRSUB for union that does not resolve to a field".to_string(),
                        ));
                    }
                };
                let fld = types(ctx.glb).get(ct).get_field(field_num).clone();
                fieldid = fld.ident;
                fieldname = fld.name;
                fieldtype = Some(fld.tp);
            } else {
                let mut newoff: i64 = 0;
                let fld =
                    crate::types::Datatype::find_truncation(ct, suboff, 0, op, 0, &mut newoff, ctx.data_ref(), ctx.glb);
                match fld {
                    None => {
                        if types(ctx.glb).get(ct).get_size() as i64 <= suboff || suboff < 0 {
                            self.clear();
                            return Err(Error::Lowlevel("PTRSUB out of bounds into struct".to_string()));
                        }
                        fieldname = format!("field_0x{:x}", suboff);
                        fieldtype = None;
                        fieldid = suboff as i32;
                    }
                    Some(fld) => {
                        fieldname = fld.name;
                        fieldtype = Some(fld.tp);
                        fieldid = fld.ident;
                    }
                }
            }
            let mut arrayvalue = false;
            if let Some(fieldtype) = fieldtype
                && metatype(ctx, fieldtype) == TypeMetatype::Array
            {
                arrayvalue = valueon;
                valueon = true;
            }
            if !valueon {
                if flex {
                    self.push_op(ctx, OpTokenKey::Addressof, Some(op))?;
                    self.push_op(ctx, OpTokenKey::ObjectMember, Some(op))?;
                    if ptrel.is_some() {
                        self.push_type_pointer_rel(ctx, op)?;
                    }
                    self.push_vn(ctx, in0, Some(op), mods | PRINT_LOAD_VALUE)?;
                    self.push_field_atom(ctx, &fieldname, ct, fieldid, op)?;
                } else {
                    self.push_op(ctx, OpTokenKey::Addressof, Some(op))?;
                    self.push_op(ctx, OpTokenKey::PointerMember, Some(op))?;
                    if ptrel.is_some() {
                        self.push_type_pointer_rel(ctx, op)?;
                    }
                    self.push_vn(ctx, in0, Some(op), mods)?;
                    self.push_field_atom(ctx, &fieldname, ct, fieldid, op)?;
                }
            } else {
                if arrayvalue {
                    self.push_op(ctx, OpTokenKey::Subscript, Some(op))?;
                }
                if flex {
                    self.push_op(ctx, OpTokenKey::ObjectMember, Some(op))?;
                    if ptrel.is_some() {
                        self.push_type_pointer_rel(ctx, op)?;
                    }
                    self.push_vn(ctx, in0, Some(op), mods | PRINT_LOAD_VALUE)?;
                    self.push_field_atom(ctx, &fieldname, ct, fieldid, op)?;
                } else {
                    self.push_op(ctx, OpTokenKey::PointerMember, Some(op))?;
                    if ptrel.is_some() {
                        self.push_type_pointer_rel(ctx, op)?;
                    }
                    self.push_vn(ctx, in0, Some(op), mods)?;
                    self.push_field_atom(ctx, &fieldname, ct, fieldid, op)?;
                }
                if arrayvalue {
                    self.push_integer(ctx, 0, 4, false, PrintTagType::Syntax, None, Some(op), 0)?;
                }
            }
        } else if meta == TypeMetatype::Spacebase {
            let high = ctx.data_ref().vn(op_in(ctx, op, 1)).get_high()?;
            let symbol = {
                let (glb, data) = ctx.parts();
                data.high_get_symbol(high, glb)
            };
            let mut arrayvalue = false;
            if let Some(symbol) = symbol {
                ct = symboltab(ctx.glb)
                    .symbol(symbol)
                    .get_type()
                    .expect("symbol has no data-type");
                let symmeta = metatype(ctx, ct);
                if symmeta == TypeMetatype::Array {
                    arrayvalue = valueon;
                    valueon = true;
                } else if symmeta == TypeMetatype::Code {
                    valueon = true;
                }
            }
            if !valueon {
                self.push_op(ctx, OpTokenKey::Addressof, Some(op))?;
            } else if arrayvalue {
                self.push_op(ctx, OpTokenKey::Subscript, Some(op))?;
            }
            match symbol {
                None => {
                    let size = ctx.data_ref().vn(in0).get_size();
                    let point = ctx.data_ref().op(op).get_addr().clone();
                    let addr = types(ctx.glb).get(ct).get_address(in1const, size, &point, ctx.glb);
                    self.push_unnamed_location(ctx, &addr, None, Some(op))?;
                }
                Some(symbol) => {
                    let off = ctx.data_ref().high(high).get_symbol_offset();
                    if off == 0 {
                        self.push_symbol(ctx, symbol, None, Some(op))?;
                    } else {
                        self.push_partial_symbol(ctx, symbol, off, 0, None, Some(op), -1, false)?;
                    }
                }
            }
            if arrayvalue {
                self.push_integer(ctx, 0, 4, false, PrintTagType::Syntax, None, Some(op), 0)?;
            }
        } else if meta == TypeMetatype::Array {
            if in1const != 0 {
                self.clear();
                return Err(Error::Lowlevel(
                    "PTRSUB with non-zero offset into array type".to_string(),
                ));
            }
            if !valueon {
                if flex {
                    if ptrel.is_some() {
                        self.push_type_pointer_rel(ctx, op)?;
                    }
                    self.push_vn(ctx, in0, Some(op), mods | PRINT_LOAD_VALUE)?;
                } else {
                    self.push_op(ctx, OpTokenKey::Dereference, Some(op))?;
                    if ptrel.is_some() {
                        self.push_type_pointer_rel(ctx, op)?;
                    }
                    self.push_vn(ctx, in0, Some(op), mods)?;
                }
            } else if flex {
                self.push_op(ctx, OpTokenKey::Subscript, Some(op))?;
                if ptrel.is_some() {
                    self.push_type_pointer_rel(ctx, op)?;
                }
                self.push_vn(ctx, in0, Some(op), mods | PRINT_LOAD_VALUE)?;
                self.push_integer(ctx, 0, 4, false, PrintTagType::Syntax, None, Some(op), 0)?;
            } else {
                self.push_op(ctx, OpTokenKey::Subscript, Some(op))?;
                self.push_op(ctx, OpTokenKey::Dereference, Some(op))?;
                if ptrel.is_some() {
                    self.push_type_pointer_rel(ctx, op)?;
                }
                self.push_vn(ctx, in0, Some(op), mods)?;
                self.push_integer(ctx, 0, 4, false, PrintTagType::Syntax, None, Some(op), 0)?;
            }
        } else {
            self.clear();
            return Err(Error::Lowlevel("PTRSUB off of non structured pointer type".to_string()));
        }
        Ok(())
    }

    pub(crate) fn op_segment_op_c(&mut self, ctx: &mut PrintContext<'_>, op: OpId) -> Result<()> {
        let mods = self.mods();
        self.push_vn(ctx, op_in(ctx, op, 2), Some(op), mods)
    }

    pub fn op_cpool_ref_op_c(&mut self, ctx: &mut PrintContext<'_>, op: OpId) -> Result<()> {
        let outvn = op_out(ctx, op);
        let vn0 = op_in(ctx, op, 0);
        let mut refs: Vec<u64> = Vec::new();
        for index in 1..num_input(ctx, op) {
            refs.push(ctx.data_ref().vn(op_in(ctx, op, index)).get_offset());
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
        let mods = self.mods();
        match record.get_tag() {
            crate::cpool::CPoolRecord::STRING_LITERAL => {
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
                )?;
            }
            crate::cpool::CPoolRecord::CLASS_REFERENCE => {
                self.push_atom(
                    ctx,
                    &Atom::with_varnode(
                        record.get_token(),
                        PrintTagType::Vartoken,
                        SyntaxHighlight::TypeColor,
                        Some(op),
                        outvn,
                    ),
                )?;
            }
            crate::cpool::CPoolRecord::INSTANCE_OF => {
                let mut dt = record.get_type().expect("constant pool record has no data-type");
                while metatype(ctx, dt) == TypeMetatype::Ptr {
                    dt = ptr_to(ctx, dt);
                }
                self.push_op(ctx, OpTokenKey::FunctionCall, Some(op))?;
                self.push_atom(
                    ctx,
                    &Atom::with_varnode(
                        record.get_token(),
                        PrintTagType::Functoken,
                        SyntaxHighlight::FuncnameColor,
                        Some(op),
                        outvn,
                    ),
                )?;
                self.push_op(ctx, OpTokenKey::Comma, None)?;
                self.push_vn(ctx, vn0, Some(op), mods)?;
                let nm = display_name(ctx, dt);
                self.push_atom(
                    ctx,
                    &Atom::with_varnode(&nm, PrintTagType::Syntax, SyntaxHighlight::TypeColor, Some(op), outvn),
                )?;
            }
            _ => {
                let mut ct = record.get_type().expect("constant pool record has no data-type");
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
                    )?;
                } else {
                    self.push_op(ctx, OpTokenKey::PointerMember, Some(op))?;
                    self.push_vn(ctx, vn0, Some(op), mods)?;
                    self.push_atom(
                        ctx,
                        &Atom::with_varnode(record.get_token(), PrintTagType::Syntax, color, Some(op), outvn),
                    )?;
                }
            }
        }
        Ok(())
    }

    pub(crate) fn op_new_op_c(&mut self, ctx: &mut PrintContext<'_>, op: OpId) -> Result<()> {
        let outvn = op_out(ctx, op);
        let vn0 = op_in(ctx, op, 0);
        let mods = self.mods();
        if num_input(ctx, op) == 2 {
            let vn1 = op_in(ctx, op, 1);
            if !ctx.data_ref().vn(vn0).is_constant() {
                self.push_op(ctx, OpTokenKey::NewOp, Some(op))?;
                self.push_atom(
                    ctx,
                    &Atom::with_varnode(
                        KEYWORD_NEW,
                        PrintTagType::Optoken,
                        SyntaxHighlight::KeywordColor,
                        Some(op),
                        outvn,
                    ),
                )?;
                let nm = match outvn {
                    None => "<unused>".to_string(),
                    Some(outvn) => {
                        let mut dt = ctx.data_ref().vn_get_type_def_facing(outvn, ctx.glb);
                        while metatype(ctx, dt) == TypeMetatype::Ptr {
                            dt = ptr_to(ctx, dt);
                        }
                        display_name(ctx, dt)
                    }
                };
                self.push_op(ctx, OpTokenKey::Subscript, Some(op))?;
                self.push_atom(
                    ctx,
                    &Atom::with_op(&nm, PrintTagType::Optoken, SyntaxHighlight::TypeColor, Some(op)),
                )?;
                return self.push_vn(ctx, vn1, Some(op), mods);
            }
        }
        self.push_op(ctx, OpTokenKey::FunctionCall, Some(op))?;
        self.push_atom(
            ctx,
            &Atom::with_varnode(
                KEYWORD_NEW,
                PrintTagType::Optoken,
                SyntaxHighlight::KeywordColor,
                Some(op),
                outvn,
            ),
        )?;
        self.push_vn(ctx, vn0, Some(op), mods)
    }

    pub(crate) fn op_pull_c(&mut self, ctx: &mut PrintContext<'_>, op: OpId) -> Result<()> {
        let expr = {
            let (glb, data) = ctx.parts();
            PullExpression::new(op, data, glb)?
        };
        if !expr.expr.is_valid() {
            return self.op_func(ctx, op);
        }
        let the_struct = expr.expr.the_struct.expect("bitfield expression has no structure");
        let bitfield = types(ctx.glb)
            .get(the_struct)
            .get_bit_field(expr.expr.bitfield.expect("bitfield expression has no field") as i32)
            .clone();
        if let Some(load_op) = expr.load_op {
            let mut mods = self.mods();
            let load_ptr = op_in(ctx, load_op, 1);
            if self.check_bit_field_member(ctx, load_ptr, &bitfield) {
                mods |= PRINT_LOAD_VALUE;
                self.push_op(ctx, OpTokenKey::ObjectMember, Some(op))?;
            } else {
                self.push_op(ctx, OpTokenKey::PointerMember, Some(op))?;
            }
            let struct_ptr = expr.struct_ptr.expect("bitfield expression has no structure pointer");
            self.push_vn(ctx, struct_ptr, Some(load_op), mods)?;
        } else {
            self.push_op(ctx, OpTokenKey::ObjectMember, Some(op))?;
            self.push_symbol_detail(ctx, op_in(ctx, op, 0), Some(op), true)?;
        }
        self.push_atom(
            ctx,
            &Atom::with_field(
                &bitfield.name,
                PrintTagType::Bitfieldtoken,
                SyntaxHighlight::NoColor,
                the_struct,
                bitfield.ident,
                Some(op),
            ),
        )
    }
}
