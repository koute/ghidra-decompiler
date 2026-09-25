use super::*;

impl PrintC {
    pub fn push_integer(
        &mut self,
        ctx: &mut PrintContext<'_>,
        val: u64,
        sz: i32,
        sign: bool,
        tag: PrintTagType,
        vn: Option<VarnodeId>,
        op: Option<OpId>,
        display_format: u32,
    ) -> Result<()> {
        let mut val = val;
        let mut display_format = display_format;
        let mut force_unsigned_token = false;
        let mut force_sized_token = false;
        if let Some(varnode) = vn
            && !ctx.data_ref().vn(varnode).is_annotation()
        {
            let high = ctx.data_ref().vn(varnode).get_high()?;
            let sym = {
                let (glb, data) = ctx.parts();
                data.high_get_symbol(high, glb)
            };
            if let Some(sym) = sym {
                let (name_locked, category, format) = {
                    let symbol = symboltab(ctx.glb).symbol(sym);
                    (
                        symbol.is_name_locked(),
                        symbol.get_category(),
                        symbol.get_display_format(),
                    )
                };
                if name_locked && category == Symbol::EQUATE && self.push_equate_c(ctx, val, sz, sym, vn, op)? {
                    return Ok(());
                }
                display_format = format;
            }
            force_unsigned_token = ctx.data_ref().vn(varnode).is_unsigned_print();
            force_sized_token = ctx.data_ref().vn(varnode).is_long_print();
        }
        let print_negsign;
        if sign && display_format != Symbol::FORCE_CHAR {
            let mask = calc_mask(sz);
            let flip = val ^ mask;
            print_negsign = flip < val;
            if print_negsign {
                val = flip.wrapping_add(1);
            }
            force_unsigned_token = false;
        } else {
            print_negsign = false;
        }
        if display_format != 0 {
        } else if (self.mods() & FORCE_HEX) != 0 {
            display_format = Symbol::FORCE_HEX;
        } else if val <= 10 || (self.mods() & FORCE_DEC) != 0 {
            display_format = Symbol::FORCE_DEC;
        } else {
            display_format = if most_natural_base(val) == 16 {
                Symbol::FORCE_HEX
            } else {
                Symbol::FORCE_DEC
            };
        }
        let mut text = String::new();
        if print_negsign {
            text.push('-');
        }
        if display_format == Symbol::FORCE_HEX {
            text.push_str(&format!("0x{:x}", val));
        } else if display_format == Symbol::FORCE_DEC {
            text.push_str(&format!("{}", val));
        } else if display_format == Symbol::FORCE_OCT {
            text.push_str(&format!("0{:o}", val));
        } else if display_format == Symbol::FORCE_CHAR {
            if self.do_emit_wide_char_prefix() && sz > 1 {
                text.push('L');
            }
            text.push('\'');
            if sz == 1 && val >= 0x80 {
                print_char_hex_escape(&mut text, val as i32);
            } else {
                self.print_unicode(&mut text, val as i32);
            }
            text.push('\'');
        } else {
            text.push_str("0b");
            format_binary(&mut text, val);
        }
        if force_unsigned_token {
            text.push('U');
        }
        if force_sized_token {
            text.push_str(&self.size_suffix);
        }
        self.push_atom(
            ctx,
            &Atom::with_value(&text, tag, SyntaxHighlight::ConstColor, op, vn, val),
        )
    }

    pub fn push_float(
        &mut self,
        ctx: &mut PrintContext<'_>,
        val: u64,
        sz: i32,
        tag: PrintTagType,
        vn: Option<VarnodeId>,
        op: Option<OpId>,
    ) -> Result<()> {
        let token = match translate(ctx.glb).get_float_format(sz) {
            None => "FLOAT_UNKNOWN".to_string(),
            Some(format) => {
                let (floatval, class) = format.get_host_float(val);
                if class == FloatClass::Infinity {
                    if format.extract_sign(val) {
                        "-INFINITY".to_string()
                    } else {
                        "INFINITY".to_string()
                    }
                } else if class == FloatClass::Nan {
                    if format.extract_sign(val) {
                        "-NAN".to_string()
                    } else {
                        "NAN".to_string()
                    }
                } else if (self.mods() & FORCE_SCINOTE) != 0 {
                    format.print_decimal(floatval, true)
                } else {
                    let mut token = format.print_decimal(floatval, false);
                    let looks_like_float = token.bytes().any(|byte| byte == b'.' || byte == b'e');
                    if !looks_like_float {
                        token.push_str(".0");
                    }
                    token
                }
            }
        };
        self.push_atom(
            ctx,
            &Atom::with_value(&token, tag, SyntaxHighlight::ConstColor, op, vn, val),
        )
    }

    pub fn push_bool_constant(
        &mut self,
        ctx: &mut PrintContext<'_>,
        val: u64,
        _ct: TypeId,
        tag: PrintTagType,
        vn: Option<VarnodeId>,
        op: Option<OpId>,
    ) -> Result<()> {
        let keyword = if val != 0 { KEYWORD_TRUE } else { KEYWORD_FALSE };
        self.push_atom(
            ctx,
            &Atom::with_value(keyword, tag, SyntaxHighlight::ConstColor, op, vn, val),
        )
    }

    pub fn do_emit_wide_char_prefix(&self) -> bool {
        !self.is_java()
    }

    pub fn print_char_hex_escape(out: &mut String, val: i32) {
        print_char_hex_escape(out, val);
    }

    pub fn print_character_constant(
        &self,
        ctx: &mut PrintContext<'_>,
        out: &mut String,
        addr: &Address,
        char_type: TypeId,
    ) -> Result<bool> {
        let glb = &mut *ctx.glb;
        let big_endian = glb
            .translate
            .as_deref()
            .expect("translator is not initialized")
            .is_big_endian();
        let types_ref = glb.types.as_deref().expect("type factory is not initialized");
        let loader = glb.loader.as_deref().expect("load image is not initialized");
        let manager = glb
            .string_manager
            .as_deref_mut()
            .expect("string manager is not initialized");
        let (buffer, is_trunc) = manager.get_string_data(addr, char_type, types_ref, loader)?;
        if buffer.is_empty() {
            return Ok(false);
        }
        let buffer = buffer.clone();
        let datatype = types_ref.get(char_type);
        if self.do_emit_wide_char_prefix() && datatype.get_size() > 1 && !datatype.is_opaque_string() {
            out.push('L');
        }
        out.push('"');
        self.escape_character_data(out, &buffer, buffer.len() as i32, 1, big_endian);
        if is_trunc {
            out.push_str("...\" /* TRUNCATED STRING LITERAL */");
        } else {
            out.push('"');
        }
        Ok(true)
    }

    pub fn get_hidden_this_slot(&self, ctx: &mut PrintContext<'_>, op: OpId, fc: ProtoRef) -> i32 {
        let total = num_input(ctx, op);
        if self.is_set(HIDE_THISPARAM) {
            let summary = self.proto_summary(ctx, fc);
            if summary.has_this {
                for index in 1..total - 1 {
                    if let Some(param) = summary.param(index - 1)
                        && param.is_this
                    {
                        return index;
                    }
                }
                if total >= 2
                    && let Some(param) = summary.param(total - 2)
                    && param.is_this
                {
                    return total - 1;
                }
            }
        }
        -1
    }

    pub fn reset_defaults_print_c(&mut self) {
        self.option_convention = true;
        self.option_hide_exts = true;
        self.option_inplace_ops = false;
        self.option_nocasts = false;
        self.option_null = false;
        self.option_unplaced = false;
        self.option_brace_func = BraceStyle::SkipLine;
        self.option_brace_ifelse = BraceStyle::SameLine;
        self.option_brace_loop = BraceStyle::SameLine;
        self.option_brace_switch = BraceStyle::SameLine;
        self.set_c_style_comments();
    }

    pub fn push_char_constant(
        &mut self,
        ctx: &mut PrintContext<'_>,
        val: u64,
        ct: TypeId,
        tag: PrintTagType,
        vn: Option<VarnodeId>,
        op: Option<OpId>,
    ) -> Result<()> {
        let mut display_format: u32 = 0;
        let is_signed = metatype(ctx, ct) == TypeMetatype::Int;
        let ct_size = types(ctx.glb).get(ct).get_size();
        if let Some(varnode) = vn
            && !ctx.data_ref().vn(varnode).is_annotation()
        {
            let high = ctx.data_ref().vn(varnode).get_high()?;
            let sym = {
                let (glb, data) = ctx.parts();
                data.high_get_symbol(high, glb)
            };
            if let Some(sym) = sym {
                let (name_locked, category, format) = {
                    let symbol = symboltab(ctx.glb).symbol(sym);
                    (
                        symbol.is_name_locked(),
                        symbol.get_category(),
                        symbol.get_display_format(),
                    )
                };
                if name_locked && category == Symbol::EQUATE {
                    let size = ctx.data_ref().vn(varnode).get_size();
                    if self.push_equate_c(ctx, val, size, sym, vn, op)? {
                        return Ok(());
                    }
                }
                display_format = format;
            }
            if display_format == 0 {
                let high_type = {
                    let (glb, data) = ctx.parts();
                    data.high_get_type(high, glb)
                };
                display_format = types(ctx.glb).get(high_type).get_display_format();
            }
        }
        if display_format != 0 && display_format != Symbol::FORCE_CHAR {
            let cares = match vn {
                Some(varnode) => self
                    .base
                    .cast_strategy
                    .as_deref()
                    .expect("no cast strategy")
                    .cares_about_char_representation(varnode, op),
                None => false,
            };
            if !cares {
                return self.push_integer(ctx, val, ct_size, is_signed, tag, vn, op, display_format);
            }
        }
        if ct_size == 1 && val >= 0x80 {
            if display_format != Symbol::FORCE_HEX && display_format != Symbol::FORCE_CHAR {
                return self.push_integer(ctx, val, 1, is_signed, tag, vn, op, display_format);
            }
            display_format = Symbol::FORCE_HEX;
        }
        let mut text = String::new();
        if self.do_emit_wide_char_prefix() && ct_size > 1 {
            text.push('L');
        }
        text.push('\'');
        if display_format == Symbol::FORCE_HEX {
            print_char_hex_escape(&mut text, val as i32);
        } else {
            self.print_unicode(&mut text, val as i32);
        }
        text.push('\'');
        self.push_atom(
            ctx,
            &Atom::with_value(&text, tag, SyntaxHighlight::ConstColor, op, vn, val),
        )
    }

    pub fn push_enum_constant(
        &mut self,
        ctx: &mut PrintContext<'_>,
        val: u64,
        ct: TypeId,
        tag: PrintTagType,
        vn: Option<VarnodeId>,
        op: Option<OpId>,
    ) -> Result<()> {
        let mut rep = EnumRepresentation::new();
        types(ctx.glb).get(ct).get_matches(val, &mut rep, types(ctx.glb));
        if !rep.matchname.is_empty() {
            if rep.shift_amount != 0 {
                self.push_op(ctx, OpTokenKey::ShiftRight, op)?;
            }
            if rep.complement {
                self.push_op(ctx, OpTokenKey::BitwiseNot, op)?;
            }
            for _ in (1..rep.matchname.len()).rev() {
                self.push_op(ctx, OpTokenKey::EnumCat, op)?;
            }
            for name in rep.matchname.iter() {
                self.push_atom(
                    ctx,
                    &Atom::with_value(name, tag, SyntaxHighlight::ConstColor, op, vn, val),
                )?;
            }
            if rep.shift_amount != 0 {
                self.push_integer(ctx, rep.shift_amount as i64 as u64, 4, false, tag, vn, op, 0)?;
            }
            Ok(())
        } else {
            let (size, format) = {
                let datatype = types(ctx.glb).get(ct);
                (datatype.get_size(), datatype.get_display_format())
            };
            self.push_integer(ctx, val, size, false, tag, vn, op, format)
        }
    }

    pub fn push_ptr_char_constant(
        &mut self,
        ctx: &mut PrintContext<'_>,
        val: u64,
        ct: TypeId,
        vn: Option<VarnodeId>,
        op: Option<OpId>,
    ) -> Result<bool> {
        if val == 0 {
            return Ok(false);
        }
        let spc = match ctx.glb.manager.get_default_data_space() {
            Some(spc) => spc,
            None => return Ok(false),
        };
        let mut full_encoding: u64 = 0;
        let point = match op {
            Some(op) => ctx.data_ref().op(op).get_addr().clone(),
            None => Address::default(),
        };
        let size = types(ctx.glb).get(ct).get_size();
        let stringaddr = ctx
            .glb
            .manager
            .resolve_constant(&spc, val, size, &point, &mut full_encoding);
        if stringaddr.is_invalid() {
            return Ok(false);
        }
        let global = global_scope(ctx)?;
        if !symboltab(ctx.glb).scope_is_read_only(global, &stringaddr, 1, &Address::default()) {
            return Ok(false);
        }
        let mut text = String::new();
        let subct = ptr_to(ctx, ct);
        if !self.print_character_constant(ctx, &mut text, &stringaddr, subct)? {
            return Ok(false);
        }
        self.push_atom(
            ctx,
            &Atom::with_varnode(&text, PrintTagType::Vartoken, SyntaxHighlight::ConstColor, op, vn),
        )?;
        Ok(true)
    }

    pub fn push_ptr_code_constant(
        &mut self,
        ctx: &mut PrintContext<'_>,
        val: u64,
        _ct: TypeId,
        _vn: Option<VarnodeId>,
        op: Option<OpId>,
    ) -> Result<bool> {
        let spc = match ctx.glb.manager.get_default_code_space() {
            Some(spc) => spc,
            None => return Ok(false),
        };
        let val = AddrSpace::address_to_byte(val, spc.get_word_size());
        let global = global_scope(ctx)?;
        let function = symboltab(ctx.glb).scope_query_function(global, &Address::new(spc, val));
        if let Some(function) = function {
            let (name, entry) = function_display_name(ctx, function);
            self.push_atom(
                ctx,
                &Atom::with_func(
                    &name,
                    PrintTagType::Functoken,
                    SyntaxHighlight::FuncnameColor,
                    op,
                    Some(FuncMark { entry }),
                ),
            )?;
            return Ok(true);
        }
        Ok(false)
    }

    pub(crate) fn push_constant_c(
        &mut self,
        ctx: &mut PrintContext<'_>,
        val: u64,
        ct: TypeId,
        tag: PrintTagType,
        vn: Option<VarnodeId>,
        op: Option<OpId>,
        display_format: u32,
    ) -> Result<()> {
        let (meta, size, is_char_print, is_enum) = {
            let datatype = types(ctx.glb).get(ct);
            (
                datatype.get_metatype(),
                datatype.get_size(),
                datatype.is_char_print(),
                datatype.is_enum_type(),
            )
        };
        match meta {
            TypeMetatype::Uint => {
                if is_char_print {
                    return self.push_char_constant(ctx, val, ct, tag, vn, op);
                } else if is_enum {
                    return self.push_enum_constant(ctx, val, ct, tag, vn, op);
                } else {
                    return self.push_integer(ctx, val, size, false, tag, vn, op, display_format);
                }
            }
            TypeMetatype::Int => {
                if is_char_print {
                    return self.push_char_constant(ctx, val, ct, tag, vn, op);
                } else if is_enum {
                    return self.push_enum_constant(ctx, val, ct, tag, vn, op);
                } else {
                    return self.push_integer(ctx, val, size, true, tag, vn, op, display_format);
                }
            }
            TypeMetatype::Unknown => {
                return self.push_integer(ctx, val, size, false, tag, vn, op, display_format);
            }
            TypeMetatype::Bool => {
                return self.push_bool_constant(ctx, val, ct, tag, vn, op);
            }
            TypeMetatype::Void => {
                self.clear();
                return Err(Error::Lowlevel("Cannot have a constant of type void".to_string()));
            }
            TypeMetatype::Ptr | TypeMetatype::PtrRel => {
                if self.option_null && val == 0 {
                    let token = self.null_token.clone();
                    return self.push_atom(
                        ctx,
                        &Atom::with_varnode(&token, PrintTagType::Vartoken, SyntaxHighlight::VarColor, op, vn),
                    );
                }
                let subtype = ptr_to(ctx, ct);
                if types(ctx.glb).get(subtype).is_char_print() {
                    if self.push_ptr_char_constant(ctx, val, ct, vn, op)? {
                        return Ok(());
                    }
                } else if metatype(ctx, subtype) == TypeMetatype::Code
                    && self.push_ptr_code_constant(ctx, val, ct, vn, op)?
                {
                    return Ok(());
                }
            }
            TypeMetatype::Float => {
                return self.push_float(ctx, val, size, tag, vn, op);
            }
            _ => {}
        }
        if !self.option_nocasts {
            self.push_op(ctx, OpTokenKey::Typecast, op)?;
            self.push_type(ctx, ct)?;
        }
        self.push_mod();
        if !self.is_set(FORCE_DEC) {
            self.set_mod(FORCE_HEX);
        }
        self.push_integer(ctx, val, size, false, tag, vn, op, display_format)?;
        self.pop_mod();
        Ok(())
    }

    pub(crate) fn push_equate_c(
        &mut self,
        ctx: &mut PrintContext<'_>,
        val: u64,
        sz: i32,
        sym: SymbolId,
        vn: Option<VarnodeId>,
        op: Option<OpId>,
    ) -> Result<bool> {
        let mask = calc_mask(sz);
        let baseval = symboltab(ctx.glb).symbol(sym).get_value();
        let mut modval = baseval & mask;
        if modval != baseval && sign_extend_size(modval, sz, 8) != baseval {
            return Ok(false);
        }
        if modval == val {
            self.push_symbol_c(ctx, sym, vn, op)?;
            return Ok(true);
        }
        modval = (!baseval) & mask;
        if modval == val {
            self.push_op(ctx, OpTokenKey::BitwiseNot, None)?;
            self.push_symbol_c(ctx, sym, vn, op)?;
            return Ok(true);
        }
        modval = baseval.wrapping_neg() & mask;
        if modval == val {
            self.push_op(ctx, OpTokenKey::UnaryMinus, None)?;
            self.push_symbol_c(ctx, sym, vn, op)?;
            return Ok(true);
        }
        modval = baseval.wrapping_add(1) & mask;
        if modval == val {
            self.push_op(ctx, OpTokenKey::BinaryPlus, None)?;
            self.push_symbol_c(ctx, sym, vn, op)?;
            self.push_integer(ctx, 1, sz, false, PrintTagType::Syntax, None, None, 0)?;
            return Ok(true);
        }
        modval = baseval.wrapping_sub(1) & mask;
        if modval == val {
            self.push_op(ctx, OpTokenKey::BinaryMinus, None)?;
            self.push_symbol_c(ctx, sym, vn, op)?;
            self.push_integer(ctx, 1, sz, false, PrintTagType::Syntax, None, None, 0)?;
            return Ok(true);
        }
        Ok(false)
    }

    pub(crate) fn push_annotation_c(
        &mut self,
        ctx: &mut PrintContext<'_>,
        vn: VarnodeId,
        op: Option<OpId>,
    ) -> Result<()> {
        let op = match op {
            Some(op) => op,
            None => return Err(Error::Lowlevel("annotation printed without an op".to_string())),
        };
        let sym_scope = match ctx.data_ref().get_scope_local() {
            Some(scope) => scope,
            None => return Err(Error::Lowlevel("function has no local scope".to_string())),
        };
        let mut size = 0;
        if op_code(ctx, op) == OpCode::Callother {
            let userind = ctx.data_ref().vn(op_in(ctx, op, 0)).get_offset() as i32;
            let userop = match ctx.glb.userops.get_op(userind as u32) {
                Some(userop) => userop.clone(),
                None => return Err(Error::Lowlevel("Unknown user-defined p-code op".to_string())),
            };
            size = userop.extract_annotation_size(vn, op, ctx.data_ref())?;
        }
        let vn_addr = ctx.data_ref().vn(vn).get_addr().clone();
        let op_addr = ctx.data_ref().op(op).get_addr().clone();
        let entry;
        if size != 0 {
            entry = symboltab(ctx.glb).scope_query_container(sym_scope, &vn_addr, size, &op_addr);
        } else {
            entry = symboltab(ctx.glb).scope_query_container(sym_scope, &vn_addr, 1, &op_addr);
            size = match entry {
                Some(entry) => symboltab(ctx.glb).entry(entry).get_size(),
                None => ctx.data_ref().vn(vn).get_size(),
            };
        }
        if let Some(entry) = entry {
            let (entry_size, entry_first, sym) = {
                let record = symboltab(ctx.glb).entry(entry);
                (record.get_size(), record.get_first(), record.get_symbol())
            };
            if entry_size == size {
                self.push_symbol_c(ctx, sym, Some(vn), Some(op))
            } else {
                let symboloff = ctx.data_ref().vn(vn).get_offset().wrapping_sub(entry_first) as i32;
                self.push_partial_symbol_c(ctx, sym, symboloff, size, Some(vn), Some(op), -1, false)
            }
        } else {
            let spc = vn_addr.get_space().cloned().expect("annotation has no address space");
            let offset = vn_addr.get_offset();
            let mut regname = translate(ctx.glb).get_register_name(&spc, offset, size);
            if regname.is_empty() {
                let mut spacename = spc.get_name().to_string();
                if let Some(first) = spacename.get_mut(0..1) {
                    first.make_ascii_uppercase();
                }
                let width = (2 * spc.get_addr_size()) as usize;
                regname = format!(
                    "{}{:0width$x}",
                    spacename,
                    AddrSpace::byte_to_address(offset, spc.get_word_size()),
                    width = width
                );
            }
            self.push_atom(
                ctx,
                &Atom::with_varnode(
                    &regname,
                    PrintTagType::Vartoken,
                    SyntaxHighlight::SpecialColor,
                    Some(op),
                    Some(vn),
                ),
            )
        }
    }

    pub(crate) fn push_symbol_c(
        &mut self,
        ctx: &mut PrintContext<'_>,
        sym: SymbolId,
        vn: Option<VarnodeId>,
        op: Option<OpId>,
    ) -> Result<()> {
        let (token_color, merge_problems, name) = {
            let db = symboltab(ctx.glb);
            let symbol = db.symbol(sym);
            let color = if symbol.is_volatile() {
                SyntaxHighlight::SpecialColor
            } else if db.scope(symbol.get_scope()).is_global() {
                SyntaxHighlight::GlobalColor
            } else if symbol.get_category() == Symbol::FUNCTION_PARAMETER {
                SyntaxHighlight::ParamColor
            } else if symbol.get_category() == Symbol::EQUATE {
                SyntaxHighlight::ConstColor
            } else {
                SyntaxHighlight::VarColor
            };
            (
                color,
                symbol.has_merge_problems(),
                symbol.get_display_name().to_string(),
            )
        };
        self.push_symbol_scope(ctx, sym)?;
        if merge_problems && let Some(varnode) = vn {
            let high = ctx.data_ref().vn(varnode).get_high()?;
            if ctx.data_ref().high(high).is_unmerged() {
                let mut text = name.clone();
                let entry = ctx.data_ref().high_get_symbol_entry(high, ctx.glb);
                match entry {
                    Some(entry) => {
                        let db = symboltab(ctx.glb);
                        let owner = db.entry(entry).get_symbol();
                        let position = db.symbol(owner).get_map_entry_position(entry, db, types(ctx.glb));
                        text.push_str(&format!("${}", position));
                    }
                    None => text.push_str("$$"),
                }
                return self.push_atom(
                    ctx,
                    &Atom::with_varnode(&text, PrintTagType::Vartoken, token_color, op, vn),
                );
            }
        }
        self.push_atom(
            ctx,
            &Atom::with_varnode(&name, PrintTagType::Vartoken, token_color, op, vn),
        )
    }

    pub(crate) fn push_unnamed_location_c(
        &mut self,
        ctx: &mut PrintContext<'_>,
        addr: &Address,
        vn: Option<VarnodeId>,
        op: Option<OpId>,
    ) -> Result<()> {
        let mut text = String::new();
        if let Some(space) = addr.get_space() {
            text.push_str(space.get_name());
        }
        addr.print_raw(&mut text);
        self.push_atom(
            ctx,
            &Atom::with_varnode(&text, PrintTagType::Vartoken, SyntaxHighlight::VarColor, op, vn),
        )
    }

    pub(crate) fn push_partial_symbol_c(
        &mut self,
        ctx: &mut PrintContext<'_>,
        sym: SymbolId,
        off: i32,
        sz: i32,
        vn: Option<VarnodeId>,
        op: Option<OpId>,
        slot: i32,
        allow_cast: bool,
    ) -> Result<()> {
        let mut off = off;
        let mut sz = sz;
        let mut stack: Vec<PartialSymbolEntry> = Vec::new();
        let mut finalcast: Option<TypeId> = None;
        let mut ct = symboltab(ctx.glb).symbol(sym).get_type();
        while let Some(current) = ct {
            let (meta, size, needs_resolution) = {
                let datatype = types(ctx.glb).get(current);
                (
                    datatype.get_metatype(),
                    datatype.get_size(),
                    datatype.needs_resolution(),
                )
            };
            if off == 0 && (sz == 0 || (sz == size && (!needs_resolution || meta == TypeMetatype::Ptr))) {
                break;
            }
            let mut succeeded = false;
            if meta == TypeMetatype::Struct {
                let op_id = op.ok_or_else(|| Error::Lowlevel("partial symbol printed without an op".to_string()))?;
                if needs_resolution && size == sz {
                    let outtype = crate::types::Datatype::find_resolve(current, op_id, slot, ctx.data_ref(), ctx.glb);
                    if outtype == current {
                        break;
                    }
                }
                let mut newoff: i64 = 0;
                let field = crate::types::Datatype::find_truncation(
                    current,
                    off as i64,
                    sz,
                    op_id,
                    slot,
                    &mut newoff,
                    ctx.data_ref(),
                    ctx.glb,
                );
                if let Some(field) = field {
                    off = newoff as i32;
                    let next = field.tp;
                    stack.push(PartialSymbolEntry {
                        token: OpTokenKey::ObjectMember,
                        field: Some(field),
                        parent: Some(current),
                        offset: 0,
                        size: 0,
                        hilite: SyntaxHighlight::NoColor,
                    });
                    ct = Some(next);
                    succeeded = true;
                } else {
                    let opc = op_code(ctx, op_id);
                    if opc == OpCode::Zpull || opc == OpCode::Spull {
                        break;
                    }
                }
            } else if meta == TypeMetatype::Array {
                let mut el: i32 = 0;
                let mut newoff = off;
                let arrayof = types(ctx.glb)
                    .get(current)
                    .get_sub_entry(off, sz, &mut newoff, &mut el, types(ctx.glb));
                if let Some(arrayof) = arrayof {
                    off = newoff;
                    stack.push(PartialSymbolEntry {
                        token: OpTokenKey::Subscript,
                        field: None,
                        parent: None,
                        offset: el as i64,
                        size: 0,
                        hilite: SyntaxHighlight::ConstColor,
                    });
                    ct = Some(arrayof);
                    succeeded = true;
                }
            } else if meta == TypeMetatype::Union {
                let op_id = op.ok_or_else(|| Error::Lowlevel("partial symbol printed without an op".to_string()))?;
                let mut newoff: i64 = 0;
                let field = crate::types::Datatype::find_truncation(
                    current,
                    off as i64,
                    sz,
                    op_id,
                    slot,
                    &mut newoff,
                    ctx.data_ref(),
                    ctx.glb,
                );
                if let Some(field) = field {
                    off = newoff as i32;
                    let next = field.tp;
                    stack.push(PartialSymbolEntry {
                        token: OpTokenKey::ObjectMember,
                        field: Some(field),
                        parent: Some(current),
                        offset: 0,
                        size: 0,
                        hilite: SyntaxHighlight::NoColor,
                    });
                    ct = Some(next);
                    succeeded = true;
                } else if size == sz {
                    break;
                }
            } else if allow_cast && let Some(varnode) = vn {
                let high = ctx.data_ref().vn(varnode).get_high()?;
                let outtype = {
                    let (glb, data) = ctx.parts();
                    data.high_get_type(high, glb)
                };
                let rep = ctx.data().high_get_name_representative(high);
                let big_endian = match ctx.data_ref().vn(rep).get_space() {
                    Some(space) => space.is_big_endian(),
                    None => false,
                };
                let is_cast = self
                    .base
                    .cast_strategy
                    .as_deref()
                    .expect("no cast strategy")
                    .is_subpiece_cast_endian(outtype, current, off as u32, big_endian, types(ctx.glb));
                if is_cast {
                    finalcast = Some(outtype);
                    ct = None;
                    succeeded = true;
                }
            }
            if !succeeded {
                if sz == 0 {
                    sz = size - off;
                }
                stack.push(PartialSymbolEntry {
                    token: OpTokenKey::ObjectMember,
                    field: None,
                    parent: None,
                    offset: off as i64,
                    size: sz,
                    hilite: SyntaxHighlight::NoColor,
                });
                ct = None;
            }
        }
        if let Some(finalcast) = finalcast
            && !self.option_nocasts
        {
            self.push_op(ctx, OpTokenKey::Typecast, op)?;
            self.push_type(ctx, finalcast)?;
        }
        for entry in stack.iter().rev() {
            self.push_op(ctx, entry.token, op)?;
        }
        self.push_symbol_c(ctx, sym, vn, op)?;
        for entry in stack.iter() {
            match &entry.field {
                None => {
                    if entry.size <= 0 {
                        self.push_integer(
                            ctx,
                            entry.offset as u64,
                            entry.size,
                            entry.offset < 0,
                            PrintTagType::Syntax,
                            None,
                            op,
                            0,
                        )?;
                    } else {
                        let field = self.unnamed_field(entry.offset as i32, entry.size);
                        self.push_atom(ctx, &Atom::with_op(&field, PrintTagType::Syntax, entry.hilite, op))?;
                    }
                }
                Some(field) => {
                    let parent = entry.parent.expect("field entry has no parent data-type");
                    self.push_atom(
                        ctx,
                        &Atom::with_field(
                            &field.name,
                            PrintTagType::Fieldtoken,
                            entry.hilite,
                            parent,
                            field.ident,
                            op,
                        ),
                    )?;
                }
            }
        }
        Ok(())
    }

    pub(crate) fn push_mismatch_symbol_c(
        &mut self,
        ctx: &mut PrintContext<'_>,
        sym: SymbolId,
        off: i32,
        _sz: i32,
        vn: Option<VarnodeId>,
        op: Option<OpId>,
    ) -> Result<()> {
        if off == 0 {
            let nm = format!("_{}", symbol_display_name(ctx, sym));
            self.push_atom(
                ctx,
                &Atom::with_varnode(&nm, PrintTagType::Vartoken, SyntaxHighlight::VarColor, op, vn),
            )
        } else {
            let varnode = vn.expect("mismatched symbol has no varnode");
            let addr = ctx.data_ref().vn(varnode).get_addr().clone();
            self.push_unnamed_location_c(ctx, &addr, vn, op)
        }
    }

    pub(crate) fn push_implied_field_c(
        &mut self,
        ctx: &mut PrintContext<'_>,
        vn: VarnodeId,
        op: Option<OpId>,
    ) -> Result<()> {
        let mut proceed = false;
        let high = ctx.data_ref().vn(vn).get_high()?;
        let parent = {
            let (glb, data) = ctx.parts();
            data.high_get_type(high, glb)
        };
        let mut field: Option<TypeField> = None;
        let (needs_resolution, meta) = {
            let datatype = types(ctx.glb).get(parent);
            (datatype.needs_resolution(), datatype.get_metatype())
        };
        if needs_resolution
            && meta != TypeMetatype::Ptr
            && let Some(read_op) = op
        {
            let slot = ctx.data_ref().op(read_op).get_slot(vn);
            let field_num = ctx
                .data_ref()
                .get_union_field(parent, read_op, slot, ctx.glb)
                .map(|resolved| resolved.get_field_num());
            if let Some(field_num) = field_num
                && field_num >= 0
            {
                if meta == TypeMetatype::Struct && field_num == 0 {
                    field = types(ctx.glb).get(parent).get_fields().first().cloned();
                    proceed = true;
                } else if meta == TypeMetatype::Union {
                    field = Some(types(ctx.glb).get(parent).get_field(field_num).clone());
                    proceed = true;
                }
            }
        }
        let def = def_op(ctx, vn)?;
        if !proceed {
            return push_opcode(self, ctx, def, op);
        }
        let field = field.expect("resolved field is missing");
        self.push_op(ctx, OpTokenKey::ObjectMember, op)?;
        push_opcode(self, ctx, def, op)?;
        self.push_atom(
            ctx,
            &Atom::with_field(
                &field.name,
                PrintTagType::Fieldtoken,
                SyntaxHighlight::NoColor,
                parent,
                field.ident,
                op,
            ),
        )
    }
}
