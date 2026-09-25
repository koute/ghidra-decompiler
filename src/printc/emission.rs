use super::*;

impl PrintC {
    pub fn emit_struct_definition(&mut self, ctx: &mut PrintContext<'_>, ct: TypeId) -> Result<()> {
        if types(ctx.glb).get(ct).get_name().is_empty() {
            self.clear();
            return Err(Error::Lowlevel("Trying to save unnamed structure".to_string()));
        }
        self.emit().tag_line()?;
        self.emit().print("typedef struct", SyntaxHighlight::KeywordColor)?;
        let id = self.emit().open_brace_indent(OPEN_CURLY, BraceStyle::SameLine)?;
        self.emit().tag_line()?;
        let fields: Vec<TypeField> = types(ctx.glb).get(ct).get_fields().to_vec();
        for (index, field) in fields.iter().enumerate() {
            self.push_type_start(ctx, field.tp, false)?;
            self.push_atom(
                ctx,
                &Atom::new(&field.name, PrintTagType::Syntax, SyntaxHighlight::VarColor),
            )?;
            self.push_type_end(ctx, field.tp)?;
            if index + 1 != fields.len() {
                self.emit().print(COMMA, SyntaxHighlight::NoColor)?;
                self.emit().tag_line()?;
            }
        }
        self.emit().close_brace_indent(CLOSE_CURLY, id)?;
        self.emit().spaces(1, 0)?;
        let name = display_name(ctx, ct);
        self.emit().print(&name, SyntaxHighlight::NoColor)?;
        self.emit().print(SEMICOLON, SyntaxHighlight::NoColor)
    }

    pub fn emit_enum_definition(&mut self, ctx: &mut PrintContext<'_>, ct: TypeId) -> Result<()> {
        if types(ctx.glb).get(ct).get_name().is_empty() {
            self.clear();
            return Err(Error::Lowlevel("Trying to save unnamed enumeration".to_string()));
        }
        self.push_mod();
        let (sign, size, entries) = {
            let datatype = types(ctx.glb).get(ct);
            let entries: Vec<(u64, String)> = datatype
                .get_enum_map()
                .iter()
                .map(|(value, name)| (*value, name.clone()))
                .collect();
            (
                datatype.get_metatype() == TypeMetatype::Int,
                datatype.get_size(),
                entries,
            )
        };
        self.emit().tag_line()?;
        self.emit().print("typedef enum", SyntaxHighlight::KeywordColor)?;
        let id = self.emit().open_brace_indent(OPEN_CURLY, BraceStyle::SameLine)?;
        self.emit().tag_line()?;
        for (index, (value, name)) in entries.iter().enumerate() {
            self.emit().print(name, SyntaxHighlight::ConstColor)?;
            self.emit().spaces(1, 0)?;
            self.emit().print(EQUALSIGN, SyntaxHighlight::NoColor)?;
            self.emit().spaces(1, 0)?;
            self.push_integer(ctx, *value, size, sign, PrintTagType::Syntax, None, None, 0)?;
            self.recurse(ctx)?;
            self.emit().print(SEMICOLON, SyntaxHighlight::NoColor)?;
            if index + 1 != entries.len() {
                self.emit().tag_line()?;
            }
        }
        self.pop_mod();
        self.emit().close_brace_indent(CLOSE_CURLY, id)?;
        self.emit().spaces(1, 0)?;
        let name = display_name(ctx, ct);
        self.emit().print(&name, SyntaxHighlight::NoColor)?;
        self.emit().print(SEMICOLON, SyntaxHighlight::NoColor)
    }

    pub fn emit_prototype_output(&mut self, ctx: &mut PrintContext<'_>, proto: ProtoRef) -> Result<()> {
        let mut op = None;
        if proto == ProtoRef::Function {
            op = ctx.data_ref().get_first_return_op();
            if let Some(ret) = op
                && num_input(ctx, ret) < 2
            {
                op = None;
            }
        }
        let outtype = self.proto_summary(ctx, proto).output_type;
        let vn = match op {
            Some(ret) if metatype(ctx, outtype) != TypeMetatype::Void => Some(op_in(ctx, ret, 1)),
            _ => None,
        };
        let mark = ctx.varnode_mark(vn);
        let id = self.emit().begin_return_type(mark)?;
        self.push_type(ctx, outtype)?;
        self.recurse(ctx)?;
        self.emit().end_return_type(id)
    }

    pub fn emit_prototype_inputs(&mut self, ctx: &mut PrintContext<'_>, proto: ProtoRef) -> Result<()> {
        let summary = self.proto_summary(ctx, proto);
        let sz = summary.num_params;
        if sz == 0 {
            self.emit().print(KEYWORD_VOID, SyntaxHighlight::KeywordColor)?;
        } else {
            let mut print_comma = false;
            for index in 0..sz {
                if print_comma {
                    self.emit().print(COMMA, SyntaxHighlight::NoColor)?;
                }
                let param = match summary.param(index) {
                    Some(param) => param,
                    None => return Err(Error::Lowlevel("missing prototype parameter".to_string())),
                };
                if self.is_set(HIDE_THISPARAM) && param.is_this {
                    continue;
                }
                let sym = match &param.symbol {
                    Ok(sym) => Some(*sym),
                    Err(err) => return Err(err.clone()),
                };
                print_comma = true;
                match sym {
                    Some(sym) => self.emit_var_decl_c(ctx, sym)?,
                    None => {
                        self.push_type_start(ctx, param.tp, true)?;
                        self.push_atom(
                            ctx,
                            &Atom::new(EMPTY_STRING, PrintTagType::Blanktoken, SyntaxHighlight::NoColor),
                        )?;
                        self.push_type_end(ctx, param.tp)?;
                        self.recurse(ctx)?;
                    }
                }
            }
        }
        if summary.dotdotdot {
            if sz != 0 {
                self.emit().print(COMMA, SyntaxHighlight::NoColor)?;
            }
            self.emit().print(DOTDOTDOT, SyntaxHighlight::NoColor)?;
        }
        Ok(())
    }

    pub fn emit_global_var_decls_recursive(&mut self, ctx: &mut PrintContext<'_>, sym_scope: ScopeId) -> Result<()> {
        if !symboltab(ctx.glb).scope(sym_scope).is_global() {
            return Ok(());
        }
        self.emit_scope_var_decls_c(ctx, sym_scope, Symbol::NO_CATEGORY as i32)?;
        let children: Vec<ScopeId> = symboltab(ctx.glb)
            .scope(sym_scope)
            .children()
            .values()
            .copied()
            .collect();
        for child in children {
            self.emit_global_var_decls_recursive(ctx, child)?;
        }
        Ok(())
    }

    pub fn emit_local_var_decls(&mut self, ctx: &mut PrintContext<'_>) -> Result<()> {
        let mut notempty = false;
        let local = match ctx.data_ref().get_scope_local() {
            Some(local) => local,
            None => return Err(Error::Lowlevel("function has no local scope".to_string())),
        };
        if self.emit_scope_var_decls_c(ctx, local, Symbol::NO_CATEGORY as i32)? {
            notempty = true;
        }
        let children: Vec<ScopeId> = symboltab(ctx.glb).scope(local).children().values().copied().collect();
        for child in children {
            if self.emit_scope_var_decls_c(ctx, child, Symbol::NO_CATEGORY as i32)? {
                notempty = true;
            }
        }
        if notempty {
            self.emit().tag_line()?;
        }
        Ok(())
    }

    pub fn emit_statement(&mut self, ctx: &mut PrintContext<'_>, inst: OpId) -> Result<()> {
        let mark = ctx.op_mark(Some(inst));
        let id = self.emit().begin_statement(mark)?;
        self.emit_expression_c(ctx, inst)?;
        self.emit().end_statement(id)?;
        if !self.is_set(COMMA_SEPARATE) {
            self.emit().print(SEMICOLON, SyntaxHighlight::NoColor)?;
        }
        Ok(())
    }

    pub fn emit_inplace_op(&mut self, ctx: &mut PrintContext<'_>, op: OpId) -> Result<bool> {
        let tok = match op_code(ctx, op) {
            OpCode::IntMult => OpTokenKey::Multequal,
            OpCode::IntDiv | OpCode::IntSdiv => OpTokenKey::Divequal,
            OpCode::IntRem | OpCode::IntSrem => OpTokenKey::Remequal,
            OpCode::IntAdd => OpTokenKey::Plusequal,
            OpCode::IntSub => OpTokenKey::Minusequal,
            OpCode::IntLeft => OpTokenKey::Leftequal,
            OpCode::IntRight | OpCode::IntSright => OpTokenKey::Rightequal,
            OpCode::IntAnd => OpTokenKey::Andequal,
            OpCode::IntOr => OpTokenKey::Orequal,
            OpCode::IntXor => OpTokenKey::Xorequal,
            _ => return Ok(false),
        };
        let vn = op_in(ctx, op, 0);
        let outvn = op_out(ctx, op).expect("inplace op has no output");
        if ctx.data_ref().vn(outvn).get_high_option() != ctx.data_ref().vn(vn).get_high_option() {
            return Ok(false);
        }
        self.push_op(ctx, tok, Some(op))?;
        self.push_vn_explicit(ctx, vn, Some(op))?;
        let mods = self.mods();
        self.push_vn(ctx, op_in(ctx, op, 1), Some(op), mods)?;
        self.recurse(ctx)?;
        Ok(true)
    }

    pub fn emit_goto_statement(
        &mut self,
        ctx: &mut PrintContext<'_>,
        bl: BlockId,
        exp_bl: Option<BlockId>,
        tp: u32,
    ) -> Result<()> {
        let last = ctx.data_ref().block_last_op(bl);
        let mark = ctx.op_mark(last);
        let id = self.emit().begin_statement(mark)?;
        if tp == FlowBlock::F_BREAK_GOTO {
            self.emit().print(KEYWORD_BREAK, SyntaxHighlight::KeywordColor)?;
        } else if tp == FlowBlock::F_CONTINUE_GOTO {
            self.emit().print(KEYWORD_CONTINUE, SyntaxHighlight::KeywordColor)?;
        } else if tp == FlowBlock::F_GOTO_GOTO {
            self.emit().print(KEYWORD_GOTO, SyntaxHighlight::KeywordColor)?;
            self.emit().spaces(1, 0)?;
            if let Some(target) = exp_bl {
                self.emit_label(ctx, target)?;
            }
        }
        self.emit().print(SEMICOLON, SyntaxHighlight::NoColor)?;
        self.emit().end_statement(id)
    }

    pub fn emit_switch_case(&mut self, ctx: &mut PrintContext<'_>, casenum: i32, switchbl: BlockId) -> Result<()> {
        let ct = {
            let (glb, data) = ctx.parts();
            data.block_get_switch_type(switchbl, glb)?
        };
        let case_block = ctx.data_ref().block(switchbl).get_case_block(casenum);
        let op = ctx.data_ref().block_first_op(case_block);
        let op_mark = ctx.op_mark(op);
        if ctx.data_ref().block(switchbl).is_default_case(casenum) {
            let val = ctx.data_ref().block_get_label(switchbl, casenum, 0)?;
            self.emit().tag_line()?;
            self.emit()
                .tag_case_label(KEYWORD_DEFAULT, SyntaxHighlight::KeywordColor, op_mark, val)?;
            self.emit().print(COLON, SyntaxHighlight::NoColor)?;
        } else {
            let num = ctx.data_ref().block_get_num_labels(switchbl, casenum);
            let mut display_format = ctx.data_ref().block_get_display_format(switchbl);
            if display_format == 0 {
                display_format = types(ctx.glb).get(ct).get_display_format();
            }
            for index in 0..num {
                let val = ctx.data_ref().block_get_label(switchbl, casenum, index)?;
                self.emit().tag_line()?;
                self.emit().print(KEYWORD_CASE, SyntaxHighlight::KeywordColor)?;
                self.emit().spaces(1, 0)?;
                self.push_constant(ctx, val, ct, PrintTagType::Casetoken, None, op, display_format)?;
                self.recurse(ctx)?;
                self.emit().print(COLON, SyntaxHighlight::NoColor)?;
            }
        }
        Ok(())
    }

    pub fn emit_label(&mut self, ctx: &mut PrintContext<'_>, bl: BlockId) -> Result<()> {
        let leaf = match ctx.data_ref().block_get_front_leaf(bl) {
            Some(leaf) => leaf,
            None => return Ok(()),
        };
        let bb = ctx
            .data_ref()
            .block(leaf)
            .sub_block(0)
            .expect("leaf block has no basic block");
        let addr = ctx.data_ref().block_get_entry_addr(bb);
        let spc = addr.get_space().cloned();
        let off = addr.get_offset();
        let (special, block_type, joined, duplicated) = {
            let block = ctx.data_ref().block(bb);
            (
                block.has_special_label(),
                block.get_type(),
                block.is_joined(),
                block.is_duplicated(),
            )
        };
        if !special
            && block_type == BlockType::Basic
            && let Some(sym_scope) = ctx.data_ref().get_scope_local()
        {
            let sym = symboltab(ctx.glb).scope_query_code_label(sym_scope, &addr);
            if let Some(sym) = sym {
                let name = symbol_display_name(ctx, sym);
                return self
                    .emit()
                    .tag_label(&name, SyntaxHighlight::NoColor, spc.as_ref(), off);
            }
        }
        let mut label = String::new();
        if joined {
            label.push_str("joined_");
        } else if duplicated {
            label.push_str("dup_");
        } else {
            label.push_str("code_");
        }
        label.push(addr.get_shortcut());
        addr.print_raw(&mut label);
        self.emit()
            .tag_label(&label, SyntaxHighlight::NoColor, spc.as_ref(), off)
    }

    pub fn emit_label_statement(&mut self, ctx: &mut PrintContext<'_>, bl: BlockId) -> Result<()> {
        if self.is_set(ONLY_BRANCH) {
            return Ok(());
        }
        if self.is_set(FLAT) {
            if !ctx.data_ref().block_is_jump_target(bl) {
                return Ok(());
            }
        } else {
            let block = ctx.data_ref().block(bl);
            if !block.is_unstructured_target() {
                return Ok(());
            }
            if block.get_type() != BlockType::Copy {
                return Ok(());
            }
        }
        self.emit().tag_line_indent(0)?;
        self.emit_label(ctx, bl)?;
        self.emit().print(COLON, SyntaxHighlight::NoColor)
    }

    pub fn emit_any_label_statement(&mut self, ctx: &mut PrintContext<'_>, bl: BlockId) -> Result<()> {
        if ctx.data_ref().block(bl).is_label_bump_up() {
            return Ok(());
        }
        let leaf = match ctx.data_ref().block_get_front_leaf(bl) {
            Some(leaf) => leaf,
            None => return Ok(()),
        };
        self.emit_label_statement(ctx, leaf)
    }

    pub(crate) fn comment_from_key(ctx: &PrintContext<'_>, key: &CommentKey) -> Option<Comment> {
        ctx.glb.commentdb.as_deref().and_then(|db| db.get_comment(key)).cloned()
    }

    pub(crate) fn mark_comment_emitted(ctx: &PrintContext<'_>, key: &CommentKey) {
        if let Some(comm) = ctx.glb.commentdb.as_deref().and_then(|db| db.get_comment(key)) {
            comm.set_emitted(true);
        }
    }

    pub fn emit_comment_group(&mut self, ctx: &mut PrintContext<'_>, inst: Option<OpId>) -> Result<()> {
        self.commsorter.setup_op_list(ctx.data_ref(), inst);
        while self.commsorter.has_next() {
            let key = self.commsorter.get_next();
            let comm = match PrintC::comment_from_key(ctx, &key) {
                Some(comm) => comm,
                None => continue,
            };
            if comm.is_emitted() {
                continue;
            }
            if (self.base.instr_comment_type & comm.get_type()) == 0 {
                continue;
            }
            self.emit_line_comment(ctx, -1, &comm)?;
            PrintC::mark_comment_emitted(ctx, &key);
        }
        Ok(())
    }

    pub fn emit_comment_block_tree(&mut self, ctx: &mut PrintContext<'_>, bl: Option<BlockId>) -> Result<()> {
        let mut bl = match bl {
            Some(bl) => bl,
            None => return Ok(()),
        };
        let mut btype = ctx.data_ref().block(bl).get_type();
        if btype == BlockType::Copy {
            bl = ctx
                .data_ref()
                .block(bl)
                .sub_block(0)
                .expect("copy block has no component");
            btype = ctx.data_ref().block(bl).get_type();
        }
        if btype == BlockType::Plain {
            return Ok(());
        }
        if btype != BlockType::Basic {
            let size = ctx.data_ref().block(bl).get_size();
            for index in 0..size {
                let sub = ctx.data_ref().block(bl).sub_block(index);
                self.emit_comment_block_tree(ctx, sub)?;
            }
            return Ok(());
        }
        self.commsorter.setup_block_list(ctx.data_ref(), bl);
        self.emit_comment_group(ctx, None)
    }

    pub fn emit_comment_func_header(&mut self, ctx: &mut PrintContext<'_>) -> Result<()> {
        let mut extralinebreak = false;
        self.commsorter.setup_header(CommentSorter::HEADER_BASIC);
        while self.commsorter.has_next() {
            let key = self.commsorter.get_next();
            let comm = match PrintC::comment_from_key(ctx, &key) {
                Some(comm) => comm,
                None => continue,
            };
            if comm.is_emitted() {
                continue;
            }
            if (self.base.head_comment_type & comm.get_type()) == 0 {
                continue;
            }
            self.emit_line_comment(ctx, 0, &comm)?;
            PrintC::mark_comment_emitted(ctx, &key);
            extralinebreak = true;
        }
        let func_addr = ctx.data_ref().get_address().clone();
        if self.option_unplaced {
            if extralinebreak {
                self.emit().tag_line()?;
            }
            extralinebreak = false;
            self.commsorter.setup_header(CommentSorter::HEADER_UNPLACED);
            while self.commsorter.has_next() {
                let key = self.commsorter.get_next();
                let comm = match PrintC::comment_from_key(ctx, &key) {
                    Some(comm) => comm,
                    None => continue,
                };
                if comm.is_emitted() {
                    continue;
                }
                if !extralinebreak {
                    let label = Comment::new(
                        Comment::WARNINGHEADER,
                        &func_addr,
                        &func_addr,
                        0,
                        "Comments that could not be placed in the function body:",
                    );
                    self.emit_line_comment(ctx, 0, &label)?;
                    extralinebreak = true;
                }
                self.emit_line_comment(ctx, 1, &comm)?;
                PrintC::mark_comment_emitted(ctx, &key);
            }
        }
        if self.option_nocasts {
            if extralinebreak {
                self.emit().tag_line()?;
            }
            let comm = Comment::new(
                Comment::WARNINGHEADER,
                &func_addr,
                &func_addr,
                0,
                "DISPLAY WARNING: Type casts are NOT being printed",
            );
            self.emit_line_comment(ctx, 0, &comm)?;
            extralinebreak = true;
        }
        if extralinebreak {
            self.emit().tag_line()?;
        }
        Ok(())
    }

    pub fn emit_for_loop(&mut self, ctx: &mut PrintContext<'_>, bl: BlockId) -> Result<()> {
        self.push_mod();
        self.unset_mod(NO_BRANCH | ONLY_BRANCH);
        self.emit_any_label_statement(ctx, bl)?;
        let cond_block = ctx.data_ref().block(bl).get_block(0);
        self.emit_comment_block_tree(ctx, Some(cond_block))?;
        self.emit().tag_line()?;
        let op = ctx.data_ref().block_last_op(cond_block);
        let mark = ctx.op_mark(op);
        self.emit().tag_op(KEYWORD_FOR, SyntaxHighlight::KeywordColor, mark)?;
        self.emit().spaces(1, 0)?;
        let id1 = self.emit().open_paren(crate::printlanguage::OPEN_PAREN, 0)?;
        self.push_mod();
        self.set_mod(COMMA_SEPARATE);
        let init = ctx.data_ref().block(bl).get_initialize_op();
        if let Some(init) = init {
            let mark = ctx.op_mark(Some(init));
            let id3 = self.emit().begin_statement(mark)?;
            self.emit_expression_c(ctx, init)?;
            self.emit().end_statement(id3)?;
        }
        self.emit().print(SEMICOLON, SyntaxHighlight::NoColor)?;
        self.emit().spaces(1, 0)?;
        Funcdata::block_emit(cond_block, self, ctx)?;
        self.emit().print(SEMICOLON, SyntaxHighlight::NoColor)?;
        self.emit().spaces(1, 0)?;
        let iterate = ctx
            .data_ref()
            .block(bl)
            .get_iterate_op()
            .expect("for loop has no iterate op");
        let mark = ctx.op_mark(Some(iterate));
        let id4 = self.emit().begin_statement(mark)?;
        self.emit_expression_c(ctx, iterate)?;
        self.emit().end_statement(id4)?;
        self.pop_mod();
        self.emit().close_paren(crate::printlanguage::CLOSE_PAREN, id1)?;
        let brace = self.option_brace_loop;
        let indent = self.emit().open_brace_indent(OPEN_CURLY, brace)?;
        self.set_mod(NO_BRANCH);
        let body = ctx.data_ref().block(bl).get_block(1);
        let body_mark = self.block_mark(ctx, body);
        let id2 = self.emit().begin_block(body_mark)?;
        Funcdata::block_emit(body, self, ctx)?;
        self.emit().end_block(id2)?;
        self.emit().close_brace_indent(CLOSE_CURLY, indent)?;
        self.pop_mod();
        Ok(())
    }

    pub(crate) fn block_mark(&self, ctx: &PrintContext<'_>, bl: BlockId) -> Option<crate::prettyprint::BlockMark> {
        Some(crate::prettyprint::BlockMark {
            id: bl,
            index: ctx.data_ref().block(bl).get_index(),
        })
    }

    pub(crate) fn emit_sub_block(&mut self, ctx: &mut PrintContext<'_>, bl: BlockId) -> Result<()> {
        let mark = self.block_mark(ctx, bl);
        let id = self.emit().begin_block(mark)?;
        Funcdata::block_emit(bl, self, ctx)?;
        self.emit().end_block(id)
    }

    pub fn generic_function_name(&self, addr: &Address) -> String {
        let mut text = String::from("func_");
        addr.print_raw(&mut text);
        text
    }

    pub fn generic_type_name(&self, ctx: &mut PrintContext<'_>, ct: TypeId) -> String {
        let datatype = types(ctx.glb).get(ct);
        let prefix = match datatype.get_metatype() {
            TypeMetatype::Int => "unkint",
            TypeMetatype::Uint => "unkuint",
            TypeMetatype::Unknown => "unkbyte",
            TypeMetatype::Spacebase => return "BADSPACEBASE".to_string(),
            TypeMetatype::Float => "unkfloat",
            _ => return "BADTYPE".to_string(),
        };
        format!("{}{}", prefix, datatype.get_size())
    }

    pub fn emit_type_definition(&mut self, ctx: &mut PrintContext<'_>, ct: TypeId) -> Result<()> {
        let (meta, is_enum) = {
            let datatype = types(ctx.glb).get(ct);
            (datatype.get_metatype(), datatype.is_enum_type())
        };
        if meta == TypeMetatype::Struct {
            self.emit_struct_definition(ctx, ct)
        } else if is_enum {
            self.emit_enum_definition(ctx, ct)
        } else {
            self.clear();
            Err(Error::Lowlevel("Unsupported typedef".to_string()))
        }
    }

    pub fn push_type_pointer_rel(&mut self, ctx: &mut PrintContext<'_>, op: OpId) -> Result<()> {
        self.push_op(ctx, OpTokenKey::FunctionCall, Some(op))?;
        self.push_atom(
            ctx,
            &Atom::with_op(
                TYPE_POINTER_REL_TOKEN,
                PrintTagType::Optoken,
                SyntaxHighlight::FuncnameColor,
                Some(op),
            ),
        )
    }

    pub fn print_unicode_c(&self, out: &mut String, onechar: i32) {
        print_unicode_c_style(out, onechar);
    }

    pub fn adjust_type_operators_c(&mut self, glb: &mut Architecture) {
        self.base.tokens[OpTokenKey::Scope.index()].print1 = "::";
        self.base.tokens[OpTokenKey::ShiftRight.index()].print1 = ">>";
        crate::typeop::select_java_operators(&mut glb.inst, false);
    }

    pub fn reset_defaults_c(&mut self) {
        self.reset_defaults_language();
        self.reset_defaults_print_c();
    }

    pub fn set_null_printing(&mut self, val: bool) {
        self.option_null = val;
    }

    pub fn set_inplace_ops(&mut self, val: bool) {
        self.option_inplace_ops = val;
    }

    pub fn set_convention(&mut self, val: bool) {
        self.option_convention = val;
    }

    pub fn set_no_cast_printing(&mut self, val: bool) {
        self.option_nocasts = val;
    }

    pub fn set_c_style_comments(&mut self) {
        self.set_comment_delimeter("/* ", " */", false);
    }

    pub fn set_c_plus_plus_style_comments(&mut self) {
        self.set_comment_delimeter("// ", "", true);
    }

    pub fn set_display_unplaced(&mut self, val: bool) {
        self.option_unplaced = val;
    }

    pub fn set_hide_implied_exts(&mut self, val: bool) {
        self.option_hide_exts = val;
    }

    pub fn set_brace_format_function(&mut self, style: BraceStyle) {
        self.option_brace_func = style;
    }

    pub fn set_brace_format_if_else(&mut self, style: BraceStyle) {
        self.option_brace_ifelse = style;
    }

    pub fn set_brace_format_loop(&mut self, style: BraceStyle) {
        self.option_brace_loop = style;
    }

    pub fn set_brace_format_switch(&mut self, style: BraceStyle) {
        self.option_brace_switch = style;
    }

    pub(crate) fn emit_expression_c(&mut self, ctx: &mut PrintContext<'_>, op: OpId) -> Result<()> {
        if ctx.data_ref().op(op).does_special_printing() {
            if ctx.data_ref().op(op).is_call() {
                return self.emit_constructor_c(ctx, op);
            }
            let opc = op_code(ctx, op);
            if opc == OpCode::Store {
                return self.emit_bit_field_store_c(ctx, op);
            } else if opc == OpCode::Insert {
                return self.emit_bit_field_expression_c(ctx, op);
            } else if opc == OpCode::Subpiece {
            } else {
                return Err(Error::Lowlevel("Unsupported special printing".to_string()));
            }
        }
        if let Some(outvn) = op_out(ctx, op) {
            if self.option_inplace_ops && self.emit_inplace_op(ctx, op)? {
                return Ok(());
            }
            self.push_op(ctx, OpTokenKey::Assignment, Some(op))?;
            self.push_symbol_detail(ctx, outvn, Some(op), false)?;
        }
        push_opcode(self, ctx, op, None)?;
        self.recurse(ctx)
    }

    pub(crate) fn emit_constructor_c(&mut self, ctx: &mut PrintContext<'_>, op: OpId) -> Result<()> {
        let newop = def_op(ctx, op_in(ctx, op, 1))?;
        let outvn = op_out(ctx, newop).expect("new op has no output");
        self.push_op(ctx, OpTokenKey::Assignment, Some(newop))?;
        self.push_symbol_detail(ctx, outvn, Some(newop), false)?;
        self.op_constructor(ctx, op, true)?;
        self.recurse(ctx)
    }

    pub(crate) fn emit_bit_field_store_c(&mut self, ctx: &mut PrintContext<'_>, op: OpId) -> Result<()> {
        let expr = {
            let (glb, data) = ctx.parts();
            InsertStoreExpression::new(op, data, glb)
        };
        if !expr.expr.is_valid() {
            push_opcode(self, ctx, op, None)?;
            return self.recurse(ctx);
        }
        self.push_op(ctx, OpTokenKey::Assignment, Some(op))?;
        let the_struct = expr.expr.the_struct.expect("bitfield expression has no structure");
        let bitfield = types(ctx.glb)
            .get(the_struct)
            .get_bit_field(expr.expr.bitfield.expect("bitfield expression has no field") as i32)
            .clone();
        let insert_op = expr.insert_op.expect("bitfield store has no insert op");
        let mut store_mods = self.mods();
        let in1 = op_in(ctx, op, 1);
        if self.check_bit_field_member(ctx, in1, &bitfield) {
            store_mods |= PRINT_STORE_VALUE;
            self.push_op(ctx, OpTokenKey::ObjectMember, Some(insert_op))?;
        } else {
            self.push_op(ctx, OpTokenKey::PointerMember, Some(insert_op))?;
        }
        let struct_ptr = expr.struct_ptr.expect("bitfield store has no structure pointer");
        self.push_vn(ctx, struct_ptr, Some(op), store_mods)?;
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
        )?;
        let mods = self.mods();
        self.push_vn(ctx, op_in(ctx, insert_op, 1), Some(op), mods)?;
        self.recurse(ctx)
    }

    pub(crate) fn emit_bit_field_expression_c(&mut self, ctx: &mut PrintContext<'_>, op: OpId) -> Result<()> {
        let expr = {
            let (glb, data) = ctx.parts();
            InsertExpression::new(op, data, glb)?
        };
        if !expr.expr.is_valid() {
            self.op_func(ctx, op)?;
            return self.recurse(ctx);
        }
        self.push_op(ctx, OpTokenKey::Assignment, Some(op))?;
        self.push_op(ctx, OpTokenKey::ObjectMember, Some(expr.insert_op))?;
        let the_struct = expr.expr.the_struct.expect("bitfield expression has no structure");
        let struct_size = types(ctx.glb).get(the_struct).get_size();
        let symbol = expr.symbol.expect("bitfield expression has no symbol");
        let outvn = op_out(ctx, op);
        self.push_partial_symbol(
            ctx,
            symbol,
            expr.expr.offset_to_bit_struct,
            struct_size,
            outvn,
            Some(op),
            -1,
            false,
        )?;
        let bitfield = types(ctx.glb)
            .get(the_struct)
            .get_bit_field(expr.expr.bitfield.expect("bitfield expression has no field") as i32)
            .clone();
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
        )?;
        let mods = self.mods();
        self.push_vn(ctx, op_in(ctx, op, 1), Some(op), mods)?;
        self.recurse(ctx)
    }

    pub(crate) fn emit_var_decl_c(&mut self, ctx: &mut PrintContext<'_>, sym: SymbolId) -> Result<()> {
        let (symbol_id, tp) = {
            let symbol = symboltab(ctx.glb).symbol(sym);
            (symbol.get_id(), symbol.get_type().expect("symbol has no data-type"))
        };
        let id = self.emit().begin_var_decl(Some(SymbolMark { id: sym, symbol_id }))?;
        self.push_type_start(ctx, tp, false)?;
        self.push_symbol_c(ctx, sym, None, None)?;
        self.push_type_end(ctx, tp)?;
        self.recurse(ctx)?;
        self.emit().end_var_decl(id)
    }

    pub(crate) fn emit_var_decl_statement_c(&mut self, ctx: &mut PrintContext<'_>, sym: SymbolId) -> Result<()> {
        self.emit().tag_line()?;
        self.emit_var_decl_c(ctx, sym)?;
        self.emit().print(SEMICOLON, SyntaxHighlight::NoColor)
    }

    pub(crate) fn emit_scope_var_decls_c(
        &mut self,
        ctx: &mut PrintContext<'_>,
        sym_scope: ScopeId,
        cat: i32,
    ) -> Result<bool> {
        let mut notempty = false;
        if cat >= 0 {
            let sz = symboltab(ctx.glb).scope_get_category_size(sym_scope, cat);
            for index in 0..sz {
                let sym = match symboltab(ctx.glb).scope_get_category_symbol(sym_scope, cat, index) {
                    Some(sym) => sym,
                    None => continue,
                };
                {
                    let symbol = symboltab(ctx.glb).symbol(sym);
                    if symbol.get_name().is_empty() {
                        continue;
                    }
                    if symbol.is_name_undefined() {
                        continue;
                    }
                }
                notempty = true;
                self.emit_var_decl_statement_c(ctx, sym)?;
            }
            return Ok(notempty);
        }
        let mut entries: Vec<crate::database::EntryId> = Vec::new();
        {
            let db = symboltab(ctx.glb);
            let scope = db.scope(sym_scope);
            let mut iter = db.scope_begin(sym_scope);
            let enditer = db.scope_end(sym_scope);
            while !iter.equals(&enditer, scope) {
                entries.push(iter.get(scope));
                iter.advance(scope);
            }
        }
        for entry in entries {
            let sym = {
                let db = symboltab(ctx.glb);
                let record = db.entry(entry);
                if record.is_piece() {
                    continue;
                }
                let sym = record.get_symbol();
                let symbol = db.symbol(sym);
                if symbol.get_category() as i32 != cat {
                    continue;
                }
                if symbol.get_name().is_empty() {
                    continue;
                }
                if matches!(symbol.kind, SymbolKind::Function { .. }) {
                    continue;
                }
                if matches!(symbol.kind, SymbolKind::Label) {
                    continue;
                }
                if symbol.is_multi_entry() && db.symbol_get_first_whole_map(sym)? != entry {
                    continue;
                }
                sym
            };
            notempty = true;
            self.emit_var_decl_statement_c(ctx, sym)?;
        }
        let dynamic: Vec<crate::database::EntryId> = symboltab(ctx.glb).scope_dynamic_entries(sym_scope).to_vec();
        for entry in dynamic {
            let sym = {
                let db = symboltab(ctx.glb);
                let record = db.entry(entry);
                if record.is_piece() {
                    continue;
                }
                let sym = record.get_symbol();
                let symbol = db.symbol(sym);
                if symbol.get_category() as i32 != cat {
                    continue;
                }
                if symbol.get_name().is_empty() {
                    continue;
                }
                if symbol.is_multi_entry() && db.symbol_get_first_whole_map(sym)? != entry {
                    continue;
                }
                sym
            };
            notempty = true;
            self.emit_var_decl_statement_c(ctx, sym)?;
        }
        Ok(notempty)
    }

    pub(crate) fn emit_function_declaration_c(&mut self, ctx: &mut PrintContext<'_>) -> Result<()> {
        let id = self.emit().begin_func_proto()?;
        self.emit_prototype_output(ctx, ProtoRef::Function)?;
        self.emit().spaces(1, 0)?;
        if self.option_convention {
            let model = {
                let proto = &ctx.data_ref().funcp;
                if proto.print_model_in_decl(ctx.glb) {
                    let highlight = if proto.is_model_unknown(ctx.glb) {
                        SyntaxHighlight::ErrorColor
                    } else {
                        SyntaxHighlight::KeywordColor
                    };
                    Some((proto.get_model_name(ctx.glb).to_string(), highlight))
                } else {
                    None
                }
            };
            if let Some((name, highlight)) = model {
                self.emit().print(&name, highlight)?;
                self.emit().spaces(1, 0)?;
            }
        }
        let id1 = self.emit().open_group()?;
        if let Some(symbol) = ctx.data_ref().get_symbol() {
            self.emit_symbol_scope(ctx, symbol)?;
        }
        let name = ctx.data_ref().get_display_name().to_string();
        let func_mark = FuncMark {
            entry: ctx.data_ref().get_address().clone(),
        };
        self.emit()
            .tag_func_name(&name, SyntaxHighlight::FuncnameColor, Some(&func_mark), None)?;
        let call_token = *self.get_token(OpTokenKey::FunctionCall);
        self.emit().spaces(call_token.spacing, call_token.bump)?;
        let id2 = self.emit().open_paren(crate::printlanguage::OPEN_PAREN, 0)?;
        self.emit().spaces(0, call_token.bump)?;
        let local = ctx.data_ref().get_scope_local();
        self.push_scope(local);
        self.emit_prototype_inputs(ctx, ProtoRef::Function)?;
        self.emit().close_paren(crate::printlanguage::CLOSE_PAREN, id2)?;
        self.emit().close_group(id1)?;
        self.emit().end_func_proto(id)
    }

    pub(crate) fn doc_all_globals_c(&mut self, ctx: &mut PrintContext<'_>) -> Result<()> {
        let id = self.emit().begin_document()?;
        let global = global_scope(ctx)?;
        self.emit_global_var_decls_recursive(ctx, global)?;
        self.emit().tag_line()?;
        self.emit().end_document(id)?;
        self.emit().flush()
    }

    pub(crate) fn doc_single_global_c(&mut self, ctx: &mut PrintContext<'_>, sym: SymbolId) -> Result<()> {
        let id = self.emit().begin_document()?;
        self.emit_var_decl_statement_c(ctx, sym)?;
        self.emit().tag_line()?;
        self.emit().end_document(id)?;
        self.emit().flush()
    }

    pub fn doc_function_c(&mut self, ctx: &mut PrintContext<'_>) -> Result<()> {
        let modsave = self.mods();
        if !ctx.data_ref().is_proc_started() {
            return Err(Error::Recov("Function not decompiled".to_string()));
        }
        if !self.is_set(FLAT) && ctx.data_ref().has_no_struct_blocks() {
            return Err(Error::Recov(
                "Function not fully decompiled. No structure present.".to_string(),
            ));
        }
        let result = self.doc_function_body(ctx, modsave);
        if let Err(err) = &result
            && err.is_lowlevel()
        {
            self.clear();
        }
        result
    }

    pub(crate) fn doc_function_body(&mut self, ctx: &mut PrintContext<'_>, modsave: u32) -> Result<()> {
        let comment_types = self.base.instr_comment_type | self.base.head_comment_type;
        {
            let data = ctx.data.as_deref().expect("printing context has no function");
            let db = ctx
                .glb
                .commentdb
                .as_deref()
                .expect("comment database is not initialized");
            self.commsorter
                .setup_function_list(comment_types, data, db, self.option_unplaced)?;
        }
        let func_mark = FuncMark {
            entry: ctx.data_ref().get_address().clone(),
        };
        let id1 = self.emit().begin_function(Some(&func_mark))?;
        self.emit_comment_func_header(ctx)?;
        self.emit().tag_line()?;
        self.emit_function_declaration_c(ctx)?;
        let brace = self.option_brace_func;
        let id = self.emit().open_brace_indent(OPEN_CURLY, brace)?;
        self.emit_local_var_decls(ctx)?;
        let root = if self.is_set(FLAT) {
            ctx.data_ref().get_basic_blocks()
        } else {
            ctx.data_ref().get_structure()
        };
        self.emit_block_graph_c(ctx, root)?;
        self.pop_scope();
        self.emit().close_brace_indent(CLOSE_CURLY, id)?;
        self.emit().tag_line()?;
        self.emit().end_function(id1)?;
        self.emit().flush()?;
        self.base.mods = modsave;
        Ok(())
    }

    pub(crate) fn emit_block_basic_c(&mut self, ctx: &mut PrintContext<'_>, bb: BlockId) -> Result<()> {
        self.commsorter.setup_block_list(ctx.data_ref(), bb);
        self.emit_label_statement(ctx, bb)?;
        if self.is_set(ONLY_BRANCH) {
            if let Some(inst) = ctx.data_ref().block_last_op(bb)
                && ctx.data_ref().op(inst).is_branch()
            {
                self.emit_expression_c(ctx, inst)?;
            }
        } else {
            let mut separator = false;
            let mut ops: Vec<OpId> = Vec::new();
            {
                let data = ctx.data_ref();
                let mut current = data.block(bb).get_op_list().front();
                while let Some(op) = current {
                    ops.push(op);
                    current = data.op(op).links[PcodeOp::BASIC_LIST].next;
                }
            }
            for inst in ops {
                {
                    let data = ctx.data_ref();
                    let pcode = data.op(inst);
                    if pcode.not_printed() {
                        continue;
                    }
                    if pcode.is_branch() {
                        if self.is_set(NO_BRANCH) {
                            continue;
                        }
                        if pcode.code() == OpCode::Branch {
                            continue;
                        }
                    }
                    if let Some(vn) = pcode.get_out()
                        && data.vn(vn).is_implied()
                    {
                        continue;
                    }
                }
                if separator {
                    if self.is_set(COMMA_SEPARATE) {
                        self.emit().print(COMMA, SyntaxHighlight::NoColor)?;
                        self.emit().spaces(1, 0)?;
                    } else {
                        self.emit_comment_group(ctx, Some(inst))?;
                        self.emit().tag_line()?;
                    }
                } else if !self.is_set(COMMA_SEPARATE) {
                    self.emit_comment_group(ctx, Some(inst))?;
                    self.emit().tag_line()?;
                }
                self.emit_statement(ctx, inst)?;
                separator = true;
            }
            if self.is_set(FLAT) && self.is_set(NOFALLTHRU) {
                let inst = ctx.data_ref().block_last_op(bb);
                self.emit().tag_line()?;
                let mark = ctx.op_mark(inst);
                let id = self.emit().begin_statement(mark)?;
                self.emit().print(KEYWORD_GOTO, SyntaxHighlight::KeywordColor)?;
                self.emit().spaces(1, 0)?;
                let target = {
                    let data = ctx.data_ref();
                    let block = data.block(bb);
                    if block.size_out() == 2 {
                        let fallthru_true = inst.map(|inst| data.op(inst).is_fallthru_true()).unwrap_or(false);
                        if fallthru_true {
                            block.get_out(1)
                        } else {
                            block.get_out(0)
                        }
                    } else {
                        block.get_out(0)
                    }
                };
                self.emit_label(ctx, target)?;
                self.emit().print(SEMICOLON, SyntaxHighlight::NoColor)?;
                self.emit().end_statement(id)?;
            }
            self.emit_comment_group(ctx, None)?;
        }
        Ok(())
    }

    pub(crate) fn emit_block_graph_c(&mut self, ctx: &mut PrintContext<'_>, bl: BlockId) -> Result<()> {
        let list: Vec<BlockId> = ctx.data_ref().block(bl).get_list().to_vec();
        for sub in list {
            self.emit_sub_block(ctx, sub)?;
        }
        Ok(())
    }

    pub(crate) fn emit_block_copy_c(&mut self, ctx: &mut PrintContext<'_>, bl: BlockId) -> Result<()> {
        self.emit_any_label_statement(ctx, bl)?;
        let sub = ctx
            .data_ref()
            .block(bl)
            .sub_block(0)
            .expect("copy block has no component");
        Funcdata::block_emit(sub, self, ctx)
    }

    pub(crate) fn emit_block_goto_c(&mut self, ctx: &mut PrintContext<'_>, bl: BlockId) -> Result<()> {
        self.push_mod();
        self.set_mod(NO_BRANCH);
        let first = ctx.data_ref().block(bl).get_block(0);
        Funcdata::block_emit(first, self, ctx)?;
        self.pop_mod();
        if ctx.data_ref().block_goto_prints(bl) {
            self.emit().tag_line()?;
            let (target, gototype) = {
                let block = ctx.data_ref().block(bl);
                (block.get_goto_target(), block.get_goto_type())
            };
            self.emit_goto_statement(ctx, first, Some(target), gototype)?;
        }
        Ok(())
    }

    pub(crate) fn emit_block_ls_c(&mut self, ctx: &mut PrintContext<'_>, bl: BlockId) -> Result<()> {
        let size = ctx.data_ref().block(bl).get_size();
        if self.is_set(ONLY_BRANCH) {
            let last = ctx.data_ref().block(bl).get_block(size - 1);
            return Funcdata::block_emit(last, self, ctx);
        }
        if size == 0 {
            return Ok(());
        }
        let mut index = 0;
        let mut subbl = ctx.data_ref().block(bl).get_block(index);
        index += 1;
        let mark = self.block_mark(ctx, subbl);
        let id1 = self.emit().begin_block(mark)?;
        if index == size {
            Funcdata::block_emit(subbl, self, ctx)?;
            return self.emit().end_block(id1);
        }
        self.push_mod();
        if !self.is_set(FLAT) {
            self.set_mod(NO_BRANCH);
        }
        if Some(ctx.data_ref().block(bl).get_block(index)) != ctx.data_ref().block_next_in_flow(subbl) {
            self.push_mod();
            self.set_mod(NOFALLTHRU);
            Funcdata::block_emit(subbl, self, ctx)?;
            self.pop_mod();
        } else {
            Funcdata::block_emit(subbl, self, ctx)?;
        }
        self.emit().end_block(id1)?;
        while index < size - 1 {
            subbl = ctx.data_ref().block(bl).get_block(index);
            index += 1;
            let mark = self.block_mark(ctx, subbl);
            let id2 = self.emit().begin_block(mark)?;
            if Some(ctx.data_ref().block(bl).get_block(index)) != ctx.data_ref().block_next_in_flow(subbl) {
                self.push_mod();
                self.set_mod(NOFALLTHRU);
                Funcdata::block_emit(subbl, self, ctx)?;
                self.pop_mod();
            } else {
                Funcdata::block_emit(subbl, self, ctx)?;
            }
            self.emit().end_block(id2)?;
        }
        self.pop_mod();
        subbl = ctx.data_ref().block(bl).get_block(index);
        self.emit_sub_block(ctx, subbl)
    }

    pub(crate) fn emit_block_condition_c(&mut self, ctx: &mut PrintContext<'_>, bl: BlockId) -> Result<()> {
        let first = ctx.data_ref().block(bl).get_block(0);
        if self.is_set(NO_BRANCH) {
            return self.emit_sub_block(ctx, first);
        }
        if self.is_set(ONLY_BRANCH) || self.is_set(COMMA_SEPARATE) {
            let id = self.emit().open_paren(crate::printlanguage::OPEN_PAREN, 0)?;
            Funcdata::block_emit(first, self, ctx)?;
            self.push_mod();
            self.unset_mod(ONLY_BRANCH);
            self.set_mod(COMMA_SEPARATE);
            let tok = if ctx.data_ref().block(bl).get_opcode() == OpCode::BoolAnd {
                OpTokenKey::BooleanAnd
            } else {
                OpTokenKey::BooleanOr
            };
            let mut pol = ReversePolish {
                tok,
                visited: 1,
                paren: false,
                op: None,
                id: 0,
                id2: 0,
            };
            self.emit_op(ctx, &mut pol)?;
            let id2 = self.emit().open_paren(crate::printlanguage::OPEN_PAREN, 0)?;
            let second = ctx.data_ref().block(bl).get_block(1);
            Funcdata::block_emit(second, self, ctx)?;
            self.emit().close_paren(crate::printlanguage::CLOSE_PAREN, id2)?;
            self.pop_mod();
            self.emit().close_paren(crate::printlanguage::CLOSE_PAREN, id)?;
        }
        Ok(())
    }

    pub(crate) fn emit_block_if_c(&mut self, ctx: &mut PrintContext<'_>, bl: BlockId) -> Result<()> {
        let pending_brace = Arc::new(Mutex::new(PendingBrace::new(self.option_brace_ifelse)));
        let pending_ref: PendPrintRef = pending_brace.clone();
        if self.is_set(PENDING_BRACE) {
            self.emit().set_pending_print(pending_ref.clone());
        }
        self.push_mod();
        self.unset_mod(NO_BRANCH | ONLY_BRANCH | PENDING_BRACE);
        self.push_mod();
        self.set_mod(NO_BRANCH);
        let cond_block = ctx.data_ref().block(bl).get_block(0);
        Funcdata::block_emit(cond_block, self, ctx)?;
        self.pop_mod();
        self.emit_comment_block_tree(ctx, Some(cond_block))?;
        if self.emit().has_pending_print(&pending_ref) {
            self.emit().cancel_pending_print();
            self.emit().spaces(1, 0)?;
        } else {
            self.emit().tag_line()?;
        }
        let op = ctx.data_ref().block_last_op(cond_block);
        let mark = ctx.op_mark(op);
        self.emit().tag_op(KEYWORD_IF, SyntaxHighlight::KeywordColor, mark)?;
        self.emit().spaces(1, 0)?;
        self.push_mod();
        self.set_mod(ONLY_BRANCH);
        Funcdata::block_emit(cond_block, self, ctx)?;
        self.pop_mod();
        let main_type = ctx.data_ref().block(bl).get_type();
        if main_type == BlockType::IfGoto {
            self.emit().spaces(1, 0)?;
            let (target, gototype) = {
                let block = ctx.data_ref().block(bl);
                (block.get_goto_target(), block.get_goto_type())
            };
            self.emit_goto_statement(ctx, cond_block, Some(target), gototype)?;
        } else {
            self.set_mod(NO_BRANCH);
            let brace = self.option_brace_ifelse;
            let id = self.emit().open_brace_indent(OPEN_CURLY, brace)?;
            let body = ctx.data_ref().block(bl).get_block(1);
            self.emit_sub_block(ctx, body)?;
            self.emit().close_brace_indent(CLOSE_CURLY, id)?;
            if main_type == BlockType::IfElse {
                self.emit().tag_line()?;
                self.emit().print(KEYWORD_ELSE, SyntaxHighlight::KeywordColor)?;
                let else_block = ctx.data_ref().block(bl).get_block(2);
                let else_type = ctx.data_ref().block(else_block).get_type();
                if else_type == BlockType::If || else_type == BlockType::IfElse || else_type == BlockType::IfGoto {
                    self.set_mod(PENDING_BRACE);
                    self.emit_sub_block(ctx, else_block)?;
                } else {
                    let id2 = self.emit().open_brace_indent(OPEN_CURLY, brace)?;
                    self.emit_sub_block(ctx, else_block)?;
                    self.emit().close_brace_indent(CLOSE_CURLY, id2)?;
                }
            } else if main_type == BlockType::IfNoExit {
                let follow_block = ctx.data_ref().block(bl).get_block(2);
                self.emit_sub_block(ctx, follow_block)?;
            }
        }
        self.pop_mod();
        let indent_id = pending_brace
            .lock()
            .expect("poisoned pending brace lock")
            .get_indent_id();
        if indent_id >= 0 {
            self.emit().close_brace_indent(CLOSE_CURLY, indent_id)?;
        }
        Ok(())
    }

    pub(crate) fn emit_block_while_do_c(&mut self, ctx: &mut PrintContext<'_>, bl: BlockId) -> Result<()> {
        if ctx.data_ref().block(bl).get_iterate_op().is_some() {
            return self.emit_for_loop(ctx, bl);
        }
        self.push_mod();
        self.unset_mod(NO_BRANCH | ONLY_BRANCH);
        self.emit_any_label_statement(ctx, bl)?;
        let cond_block = ctx.data_ref().block(bl).get_block(0);
        let op = ctx.data_ref().block_last_op(cond_block);
        let mark = ctx.op_mark(op);
        let brace = self.option_brace_loop;
        let indent;
        if ctx.data_ref().block(bl).has_overflow_syntax() {
            self.emit().tag_line()?;
            self.emit().tag_op(KEYWORD_WHILE, SyntaxHighlight::KeywordColor, mark)?;
            let id1 = self.emit().open_paren(crate::printlanguage::OPEN_PAREN, 0)?;
            self.emit().spaces(1, 0)?;
            self.emit().print(KEYWORD_TRUE, SyntaxHighlight::ConstColor)?;
            self.emit().spaces(1, 0)?;
            self.emit().close_paren(crate::printlanguage::CLOSE_PAREN, id1)?;
            indent = self.emit().open_brace_indent(OPEN_CURLY, brace)?;
            self.push_mod();
            self.set_mod(NO_BRANCH);
            Funcdata::block_emit(cond_block, self, ctx)?;
            self.pop_mod();
            self.emit_comment_block_tree(ctx, Some(cond_block))?;
            self.emit().tag_line()?;
            self.emit().tag_op(KEYWORD_IF, SyntaxHighlight::KeywordColor, mark)?;
            self.emit().spaces(1, 0)?;
            self.push_mod();
            self.set_mod(ONLY_BRANCH);
            Funcdata::block_emit(cond_block, self, ctx)?;
            self.pop_mod();
            self.emit().spaces(1, 0)?;
            self.emit_goto_statement(ctx, cond_block, None, FlowBlock::F_BREAK_GOTO)?;
        } else {
            self.emit_comment_block_tree(ctx, Some(cond_block))?;
            self.emit().tag_line()?;
            self.emit().tag_op(KEYWORD_WHILE, SyntaxHighlight::KeywordColor, mark)?;
            self.emit().spaces(1, 0)?;
            let id1 = self.emit().open_paren(crate::printlanguage::OPEN_PAREN, 0)?;
            self.push_mod();
            self.set_mod(COMMA_SEPARATE);
            Funcdata::block_emit(cond_block, self, ctx)?;
            self.pop_mod();
            self.emit().close_paren(crate::printlanguage::CLOSE_PAREN, id1)?;
            indent = self.emit().open_brace_indent(OPEN_CURLY, brace)?;
        }
        self.set_mod(NO_BRANCH);
        let body = ctx.data_ref().block(bl).get_block(1);
        self.emit_sub_block(ctx, body)?;
        self.emit().close_brace_indent(CLOSE_CURLY, indent)?;
        self.pop_mod();
        Ok(())
    }

    pub(crate) fn emit_block_do_while_c(&mut self, ctx: &mut PrintContext<'_>, bl: BlockId) -> Result<()> {
        self.push_mod();
        self.unset_mod(NO_BRANCH | ONLY_BRANCH);
        self.emit_any_label_statement(ctx, bl)?;
        self.emit().tag_line()?;
        self.emit().print(KEYWORD_DO, SyntaxHighlight::KeywordColor)?;
        let brace = self.option_brace_loop;
        let id = self.emit().open_brace_indent(OPEN_CURLY, brace)?;
        self.push_mod();
        let body = ctx.data_ref().block(bl).get_block(0);
        let mark = self.block_mark(ctx, body);
        let id2 = self.emit().begin_block(mark)?;
        self.set_mod(NO_BRANCH);
        Funcdata::block_emit(body, self, ctx)?;
        self.emit().end_block(id2)?;
        self.pop_mod();
        self.emit().close_brace_indent(CLOSE_CURLY, id)?;
        self.emit().spaces(1, 0)?;
        let op = ctx.data_ref().block_last_op(body);
        let op_mark = ctx.op_mark(op);
        self.emit()
            .tag_op(KEYWORD_WHILE, SyntaxHighlight::KeywordColor, op_mark)?;
        self.emit().spaces(1, 0)?;
        self.set_mod(ONLY_BRANCH);
        Funcdata::block_emit(body, self, ctx)?;
        self.emit().print(SEMICOLON, SyntaxHighlight::NoColor)?;
        self.pop_mod();
        Ok(())
    }

    pub(crate) fn emit_block_inf_loop_c(&mut self, ctx: &mut PrintContext<'_>, bl: BlockId) -> Result<()> {
        self.push_mod();
        self.unset_mod(NO_BRANCH | ONLY_BRANCH);
        self.emit_any_label_statement(ctx, bl)?;
        self.emit().tag_line()?;
        self.emit().print(KEYWORD_DO, SyntaxHighlight::KeywordColor)?;
        let brace = self.option_brace_loop;
        let id = self.emit().open_brace_indent(OPEN_CURLY, brace)?;
        let body = ctx.data_ref().block(bl).get_block(0);
        self.emit_sub_block(ctx, body)?;
        self.emit().close_brace_indent(CLOSE_CURLY, id)?;
        self.emit().spaces(1, 0)?;
        let op = ctx.data_ref().block_last_op(body);
        let op_mark = ctx.op_mark(op);
        self.emit()
            .tag_op(KEYWORD_WHILE, SyntaxHighlight::KeywordColor, op_mark)?;
        let id2 = self.emit().open_paren(crate::printlanguage::OPEN_PAREN, 0)?;
        self.emit().spaces(1, 0)?;
        self.emit().print(KEYWORD_TRUE, SyntaxHighlight::ConstColor)?;
        self.emit().spaces(1, 0)?;
        self.emit().close_paren(crate::printlanguage::CLOSE_PAREN, id2)?;
        self.emit().print(SEMICOLON, SyntaxHighlight::NoColor)?;
        self.pop_mod();
        Ok(())
    }

    pub(crate) fn emit_block_switch_c(&mut self, ctx: &mut PrintContext<'_>, bl: BlockId) -> Result<()> {
        self.push_mod();
        self.unset_mod(NO_BRANCH | ONLY_BRANCH);
        self.push_mod();
        self.set_mod(NO_BRANCH);
        let switch_block = ctx.data_ref().block(bl).get_switch_block();
        Funcdata::block_emit(switch_block, self, ctx)?;
        self.pop_mod();
        self.emit().tag_line()?;
        self.push_mod();
        self.set_mod(ONLY_BRANCH | COMMA_SEPARATE);
        Funcdata::block_emit(switch_block, self, ctx)?;
        self.pop_mod();
        let brace = self.option_brace_switch;
        self.emit().open_brace(OPEN_CURLY, brace)?;
        let num_cases = ctx.data_ref().block(bl).get_num_case_blocks();
        for index in 0..num_cases {
            self.emit_switch_case(ctx, index, bl)?;
            let id = self.emit().start_indent()?;
            let (gototype, case_block, first, is_exit) = {
                let block = ctx.data_ref().block(bl);
                (
                    block.get_case_goto_type(index),
                    block.get_case_block(index),
                    block.get_block(0),
                    block.is_exit(index),
                )
            };
            if gototype != 0 {
                self.emit().tag_line()?;
                self.emit_goto_statement(ctx, first, Some(case_block), gototype)?;
            } else {
                let mark = self.block_mark(ctx, case_block);
                let id2 = self.emit().begin_block(mark)?;
                Funcdata::block_emit(case_block, self, ctx)?;
                if is_exit && index != num_cases - 1 {
                    self.emit().tag_line()?;
                    self.emit_goto_statement(ctx, case_block, None, FlowBlock::F_BREAK_GOTO)?;
                }
                self.emit().end_block(id2)?;
            }
            self.emit().stop_indent(id)?;
        }
        self.emit().tag_line()?;
        self.emit().print(CLOSE_CURLY, SyntaxHighlight::NoColor)?;
        self.pop_mod();
        Ok(())
    }

    pub(crate) fn initialize_from_architecture_c(&mut self, glb: &mut Architecture) -> Result<()> {
        let types_ref = glb.types.as_deref().expect("type factory is not initialized");
        if let Some(cast) = self.base.cast_strategy.as_deref_mut() {
            cast.set_type_factory(types_ref);
        }
        if types_ref.get_size_of_long() == types_ref.get_size_of_int() {
            self.size_suffix = "LL".to_string();
        } else {
            self.size_suffix = "L".to_string();
        }
        Ok(())
    }

    pub(crate) fn set_comment_style_c(&mut self, nm: &str) -> Result<()> {
        if nm == "c" || nm.starts_with("/*") {
            self.set_c_style_comments();
        } else if nm == "cplusplus" || nm.starts_with("//") {
            self.set_c_plus_plus_style_comments();
        } else {
            return Err(Error::Lowlevel(
                "Unknown comment style. Use \"c\" or \"cplusplus\"".to_string(),
            ));
        }
        Ok(())
    }

    pub(crate) fn doc_type_definitions_c(&mut self, ctx: &mut PrintContext<'_>) -> Result<()> {
        let mut deporder: Vec<TypeId> = Vec::new();
        types(ctx.glb).dependent_order(&mut deporder);
        for ct in deporder {
            if types(ctx.glb).get(ct).is_core_type() {
                continue;
            }
            self.emit_type_definition(ctx, ct)?;
        }
        Ok(())
    }

    pub(crate) fn check_print_negation_c(&self, ctx: &PrintContext<'_>, vn: VarnodeId) -> bool {
        let data = ctx.data_ref();
        let varnode = data.vn(vn);
        if !varnode.is_implied() {
            return false;
        }
        if !varnode.is_written() {
            return false;
        }
        let op = varnode.get_def().expect("written varnode has no defining op");
        get_booleanflip(data.op(op).code()).is_some()
    }
}
