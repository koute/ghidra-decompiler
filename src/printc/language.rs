use super::*;

impl PrintLanguage for PrintC {
    fn base(&self) -> &PrintLanguageBase {
        &self.base
    }

    fn base_mut(&mut self) -> &mut PrintLanguageBase {
        &mut self.base
    }

    fn as_dyn_language(&mut self) -> &mut dyn PrintLanguage {
        self
    }

    fn print_unicode(&self, out: &mut String, onechar: i32) {
        if self.is_java() {
            self.print_unicode_java(out, onechar)
        } else {
            self.print_unicode_c(out, onechar)
        }
    }

    fn push_type(&mut self, ctx: &mut PrintContext<'_>, ct: TypeId) -> Result<()> {
        self.push_type_start(ctx, ct, true)?;
        self.push_atom(
            ctx,
            &Atom::new(EMPTY_STRING, PrintTagType::Blanktoken, SyntaxHighlight::NoColor),
        )?;
        self.push_type_end(ctx, ct)
    }

    fn push_constant(
        &mut self,
        ctx: &mut PrintContext<'_>,
        val: u64,
        ct: TypeId,
        tag: PrintTagType,
        vn: Option<VarnodeId>,
        op: Option<OpId>,
        display_format: u32,
    ) -> Result<()> {
        self.push_constant_c(ctx, val, ct, tag, vn, op, display_format)
    }

    fn push_equate(
        &mut self,
        ctx: &mut PrintContext<'_>,
        val: u64,
        sz: i32,
        sym: SymbolId,
        vn: Option<VarnodeId>,
        op: Option<OpId>,
    ) -> Result<bool> {
        self.push_equate_c(ctx, val, sz, sym, vn, op)
    }

    fn push_annotation(&mut self, ctx: &mut PrintContext<'_>, vn: VarnodeId, op: Option<OpId>) -> Result<()> {
        self.push_annotation_c(ctx, vn, op)
    }

    fn push_symbol(
        &mut self,
        ctx: &mut PrintContext<'_>,
        sym: SymbolId,
        vn: Option<VarnodeId>,
        op: Option<OpId>,
    ) -> Result<()> {
        self.push_symbol_c(ctx, sym, vn, op)
    }

    fn push_unnamed_location(
        &mut self,
        ctx: &mut PrintContext<'_>,
        addr: &Address,
        vn: Option<VarnodeId>,
        op: Option<OpId>,
    ) -> Result<()> {
        self.push_unnamed_location_c(ctx, addr, vn, op)
    }

    fn push_partial_symbol(
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
        self.push_partial_symbol_c(ctx, sym, off, sz, vn, op, slot, allow_cast)
    }

    fn push_mismatch_symbol(
        &mut self,
        ctx: &mut PrintContext<'_>,
        sym: SymbolId,
        off: i32,
        sz: i32,
        vn: Option<VarnodeId>,
        op: Option<OpId>,
    ) -> Result<()> {
        self.push_mismatch_symbol_c(ctx, sym, off, sz, vn, op)
    }

    fn push_implied_field(&mut self, ctx: &mut PrintContext<'_>, vn: VarnodeId, op: Option<OpId>) -> Result<()> {
        self.push_implied_field_c(ctx, vn, op)
    }

    fn emit_var_decl(&mut self, ctx: &mut PrintContext<'_>, sym: SymbolId) -> Result<()> {
        self.emit_var_decl_c(ctx, sym)
    }

    fn emit_var_decl_statement(&mut self, ctx: &mut PrintContext<'_>, sym: SymbolId) -> Result<()> {
        self.emit_var_decl_statement_c(ctx, sym)
    }

    fn emit_scope_var_decls(&mut self, ctx: &mut PrintContext<'_>, sym_scope: ScopeId, cat: i32) -> Result<bool> {
        self.emit_scope_var_decls_c(ctx, sym_scope, cat)
    }

    fn emit_expression(&mut self, ctx: &mut PrintContext<'_>, op: OpId) -> Result<()> {
        self.emit_expression_c(ctx, op)
    }

    fn emit_constructor(&mut self, ctx: &mut PrintContext<'_>, op: OpId) -> Result<()> {
        self.emit_constructor_c(ctx, op)
    }

    fn emit_bit_field_store(&mut self, ctx: &mut PrintContext<'_>, op: OpId) -> Result<()> {
        self.emit_bit_field_store_c(ctx, op)
    }

    fn emit_bit_field_expression(&mut self, ctx: &mut PrintContext<'_>, op: OpId) -> Result<()> {
        self.emit_bit_field_expression_c(ctx, op)
    }

    fn emit_function_declaration(&mut self, ctx: &mut PrintContext<'_>) -> Result<()> {
        self.emit_function_declaration_c(ctx)
    }

    fn check_print_negation(&mut self, ctx: &mut PrintContext<'_>, vn: VarnodeId) -> bool {
        self.check_print_negation_c(ctx, vn)
    }

    fn initialize_from_architecture(&mut self, glb: &mut Architecture) -> Result<()> {
        self.initialize_from_architecture_c(glb)
    }

    fn adjust_type_operators(&mut self, glb: &mut Architecture) {
        if self.is_java() {
            self.adjust_type_operators_java(glb)
        } else {
            self.adjust_type_operators_c(glb)
        }
    }

    fn reset_defaults(&mut self) {
        if self.is_java() {
            self.reset_defaults_java()
        } else {
            self.reset_defaults_c()
        }
    }

    fn set_comment_style(&mut self, nm: &str) -> Result<()> {
        self.set_comment_style_c(nm)
    }

    fn doc_type_definitions(&mut self, ctx: &mut PrintContext<'_>) -> Result<()> {
        self.doc_type_definitions_c(ctx)
    }

    fn doc_all_globals(&mut self, ctx: &mut PrintContext<'_>) -> Result<()> {
        self.doc_all_globals_c(ctx)
    }

    fn doc_single_global(&mut self, ctx: &mut PrintContext<'_>, sym: SymbolId) -> Result<()> {
        self.doc_single_global_c(ctx, sym)
    }

    fn doc_function(&mut self, ctx: &mut PrintContext<'_>) -> Result<()> {
        if self.is_java() {
            self.doc_function_java(ctx)
        } else {
            self.doc_function_c(ctx)
        }
    }

    fn emit_block_basic(&mut self, ctx: &mut PrintContext<'_>, bb: BlockId) -> Result<()> {
        self.emit_block_basic_c(ctx, bb)
    }

    fn emit_block_graph(&mut self, ctx: &mut PrintContext<'_>, bl: BlockId) -> Result<()> {
        self.emit_block_graph_c(ctx, bl)
    }

    fn emit_block_copy(&mut self, ctx: &mut PrintContext<'_>, bl: BlockId) -> Result<()> {
        self.emit_block_copy_c(ctx, bl)
    }

    fn emit_block_goto(&mut self, ctx: &mut PrintContext<'_>, bl: BlockId) -> Result<()> {
        self.emit_block_goto_c(ctx, bl)
    }

    fn emit_block_ls(&mut self, ctx: &mut PrintContext<'_>, bl: BlockId) -> Result<()> {
        self.emit_block_ls_c(ctx, bl)
    }

    fn emit_block_condition(&mut self, ctx: &mut PrintContext<'_>, bl: BlockId) -> Result<()> {
        self.emit_block_condition_c(ctx, bl)
    }

    fn emit_block_if(&mut self, ctx: &mut PrintContext<'_>, bl: BlockId) -> Result<()> {
        self.emit_block_if_c(ctx, bl)
    }

    fn emit_block_while_do(&mut self, ctx: &mut PrintContext<'_>, bl: BlockId) -> Result<()> {
        self.emit_block_while_do_c(ctx, bl)
    }

    fn emit_block_do_while(&mut self, ctx: &mut PrintContext<'_>, bl: BlockId) -> Result<()> {
        self.emit_block_do_while_c(ctx, bl)
    }

    fn emit_block_inf_loop(&mut self, ctx: &mut PrintContext<'_>, bl: BlockId) -> Result<()> {
        self.emit_block_inf_loop_c(ctx, bl)
    }

    fn emit_block_switch(&mut self, ctx: &mut PrintContext<'_>, bl: BlockId) -> Result<()> {
        self.emit_block_switch_c(ctx, bl)
    }

    fn op_copy(&mut self, ctx: &mut PrintContext<'_>, op: OpId) -> Result<()> {
        let mods = self.mods();
        self.push_vn(ctx, op_in(ctx, op, 0), Some(op), mods)
    }

    fn op_load(&mut self, ctx: &mut PrintContext<'_>, op: OpId) -> Result<()> {
        if self.is_java() {
            self.op_load_java(ctx, op)
        } else {
            self.op_load_c(ctx, op)
        }
    }

    fn op_store(&mut self, ctx: &mut PrintContext<'_>, op: OpId) -> Result<()> {
        if self.is_java() {
            self.op_store_java(ctx, op)
        } else {
            self.op_store_c(ctx, op)
        }
    }

    fn op_branch(&mut self, ctx: &mut PrintContext<'_>, op: OpId) -> Result<()> {
        self.op_branch_c(ctx, op)
    }

    fn op_cbranch(&mut self, ctx: &mut PrintContext<'_>, op: OpId) -> Result<()> {
        self.op_cbranch_c(ctx, op)
    }

    fn op_branchind(&mut self, ctx: &mut PrintContext<'_>, op: OpId) -> Result<()> {
        self.op_branchind_c(ctx, op)
    }

    fn op_call(&mut self, ctx: &mut PrintContext<'_>, op: OpId) -> Result<()> {
        self.op_call_c(ctx, op)
    }

    fn op_callind(&mut self, ctx: &mut PrintContext<'_>, op: OpId) -> Result<()> {
        if self.is_java() {
            self.op_callind_java(ctx, op)
        } else {
            self.op_callind_c(ctx, op)
        }
    }

    fn op_callother(&mut self, ctx: &mut PrintContext<'_>, op: OpId) -> Result<()> {
        self.op_callother_c(ctx, op)
    }

    fn op_constructor(&mut self, ctx: &mut PrintContext<'_>, op: OpId, with_new: bool) -> Result<()> {
        self.op_constructor_c(ctx, op, with_new)
    }

    fn op_return(&mut self, ctx: &mut PrintContext<'_>, op: OpId) -> Result<()> {
        self.op_return_c(ctx, op)
    }

    fn op_int_equal(&mut self, ctx: &mut PrintContext<'_>, op: OpId) -> Result<()> {
        self.op_binary(ctx, OpTokenKey::Equal, op)
    }

    fn op_int_not_equal(&mut self, ctx: &mut PrintContext<'_>, op: OpId) -> Result<()> {
        self.op_binary(ctx, OpTokenKey::NotEqual, op)
    }

    fn op_int_sless(&mut self, ctx: &mut PrintContext<'_>, op: OpId) -> Result<()> {
        self.op_binary(ctx, OpTokenKey::LessThan, op)
    }

    fn op_int_sless_equal(&mut self, ctx: &mut PrintContext<'_>, op: OpId) -> Result<()> {
        self.op_binary(ctx, OpTokenKey::LessEqual, op)
    }

    fn op_int_less(&mut self, ctx: &mut PrintContext<'_>, op: OpId) -> Result<()> {
        self.op_binary(ctx, OpTokenKey::LessThan, op)
    }

    fn op_int_less_equal(&mut self, ctx: &mut PrintContext<'_>, op: OpId) -> Result<()> {
        self.op_binary(ctx, OpTokenKey::LessEqual, op)
    }

    fn op_int_zext(&mut self, ctx: &mut PrintContext<'_>, op: OpId, read_op: Option<OpId>) -> Result<()> {
        self.op_extension(ctx, op, read_op, true)
    }

    fn op_int_sext(&mut self, ctx: &mut PrintContext<'_>, op: OpId, read_op: Option<OpId>) -> Result<()> {
        self.op_extension(ctx, op, read_op, false)
    }

    fn op_int_add(&mut self, ctx: &mut PrintContext<'_>, op: OpId) -> Result<()> {
        self.op_binary(ctx, OpTokenKey::BinaryPlus, op)
    }

    fn op_int_sub(&mut self, ctx: &mut PrintContext<'_>, op: OpId) -> Result<()> {
        self.op_binary(ctx, OpTokenKey::BinaryMinus, op)
    }

    fn op_int_carry(&mut self, ctx: &mut PrintContext<'_>, op: OpId) -> Result<()> {
        self.op_func(ctx, op)
    }

    fn op_int_scarry(&mut self, ctx: &mut PrintContext<'_>, op: OpId) -> Result<()> {
        self.op_func(ctx, op)
    }

    fn op_int_sborrow(&mut self, ctx: &mut PrintContext<'_>, op: OpId) -> Result<()> {
        self.op_func(ctx, op)
    }

    fn op_int_2comp(&mut self, ctx: &mut PrintContext<'_>, op: OpId) -> Result<()> {
        self.op_unary(ctx, OpTokenKey::UnaryMinus, op)
    }

    fn op_int_negate(&mut self, ctx: &mut PrintContext<'_>, op: OpId) -> Result<()> {
        self.op_unary(ctx, OpTokenKey::BitwiseNot, op)
    }

    fn op_int_xor(&mut self, ctx: &mut PrintContext<'_>, op: OpId) -> Result<()> {
        self.op_binary(ctx, OpTokenKey::BitwiseXor, op)
    }

    fn op_int_and(&mut self, ctx: &mut PrintContext<'_>, op: OpId) -> Result<()> {
        self.op_binary(ctx, OpTokenKey::BitwiseAnd, op)
    }

    fn op_int_or(&mut self, ctx: &mut PrintContext<'_>, op: OpId) -> Result<()> {
        self.op_binary(ctx, OpTokenKey::BitwiseOr, op)
    }

    fn op_int_left(&mut self, ctx: &mut PrintContext<'_>, op: OpId) -> Result<()> {
        self.op_binary(ctx, OpTokenKey::ShiftLeft, op)
    }

    fn op_int_right(&mut self, ctx: &mut PrintContext<'_>, op: OpId) -> Result<()> {
        self.op_binary(ctx, OpTokenKey::ShiftRight, op)
    }

    fn op_int_sright(&mut self, ctx: &mut PrintContext<'_>, op: OpId) -> Result<()> {
        self.op_binary(ctx, OpTokenKey::ShiftSright, op)
    }

    fn op_int_mult(&mut self, ctx: &mut PrintContext<'_>, op: OpId) -> Result<()> {
        self.op_binary(ctx, OpTokenKey::Multiply, op)
    }

    fn op_int_div(&mut self, ctx: &mut PrintContext<'_>, op: OpId) -> Result<()> {
        self.op_binary(ctx, OpTokenKey::Divide, op)
    }

    fn op_int_sdiv(&mut self, ctx: &mut PrintContext<'_>, op: OpId) -> Result<()> {
        self.op_binary(ctx, OpTokenKey::Divide, op)
    }

    fn op_int_rem(&mut self, ctx: &mut PrintContext<'_>, op: OpId) -> Result<()> {
        self.op_binary(ctx, OpTokenKey::Modulo, op)
    }

    fn op_int_srem(&mut self, ctx: &mut PrintContext<'_>, op: OpId) -> Result<()> {
        self.op_binary(ctx, OpTokenKey::Modulo, op)
    }

    fn op_bool_negate(&mut self, ctx: &mut PrintContext<'_>, op: OpId) -> Result<()> {
        self.op_bool_negate_c(ctx, op)
    }

    fn op_bool_xor(&mut self, ctx: &mut PrintContext<'_>, op: OpId) -> Result<()> {
        self.op_binary(ctx, OpTokenKey::BooleanXor, op)
    }

    fn op_bool_and(&mut self, ctx: &mut PrintContext<'_>, op: OpId) -> Result<()> {
        self.op_binary(ctx, OpTokenKey::BooleanAnd, op)
    }

    fn op_bool_or(&mut self, ctx: &mut PrintContext<'_>, op: OpId) -> Result<()> {
        self.op_binary(ctx, OpTokenKey::BooleanOr, op)
    }

    fn op_float_equal(&mut self, ctx: &mut PrintContext<'_>, op: OpId) -> Result<()> {
        self.op_binary(ctx, OpTokenKey::Equal, op)
    }

    fn op_float_not_equal(&mut self, ctx: &mut PrintContext<'_>, op: OpId) -> Result<()> {
        self.op_binary(ctx, OpTokenKey::NotEqual, op)
    }

    fn op_float_less(&mut self, ctx: &mut PrintContext<'_>, op: OpId) -> Result<()> {
        self.op_binary(ctx, OpTokenKey::LessThan, op)
    }

    fn op_float_less_equal(&mut self, ctx: &mut PrintContext<'_>, op: OpId) -> Result<()> {
        self.op_binary(ctx, OpTokenKey::LessEqual, op)
    }

    fn op_float_nan(&mut self, ctx: &mut PrintContext<'_>, op: OpId) -> Result<()> {
        self.op_func(ctx, op)
    }

    fn op_float_add(&mut self, ctx: &mut PrintContext<'_>, op: OpId) -> Result<()> {
        self.op_binary(ctx, OpTokenKey::BinaryPlus, op)
    }

    fn op_float_div(&mut self, ctx: &mut PrintContext<'_>, op: OpId) -> Result<()> {
        self.op_binary(ctx, OpTokenKey::Divide, op)
    }

    fn op_float_mult(&mut self, ctx: &mut PrintContext<'_>, op: OpId) -> Result<()> {
        self.op_binary(ctx, OpTokenKey::Multiply, op)
    }

    fn op_float_sub(&mut self, ctx: &mut PrintContext<'_>, op: OpId) -> Result<()> {
        self.op_binary(ctx, OpTokenKey::BinaryMinus, op)
    }

    fn op_float_neg(&mut self, ctx: &mut PrintContext<'_>, op: OpId) -> Result<()> {
        self.op_unary(ctx, OpTokenKey::UnaryMinus, op)
    }

    fn op_float_abs(&mut self, ctx: &mut PrintContext<'_>, op: OpId) -> Result<()> {
        self.op_func(ctx, op)
    }

    fn op_float_sqrt(&mut self, ctx: &mut PrintContext<'_>, op: OpId) -> Result<()> {
        self.op_func(ctx, op)
    }

    fn op_float_int2float(&mut self, ctx: &mut PrintContext<'_>, op: OpId) -> Result<()> {
        self.op_float_int2float_c(ctx, op)
    }

    fn op_float_float2float(&mut self, ctx: &mut PrintContext<'_>, op: OpId) -> Result<()> {
        self.op_type_cast(ctx, op)
    }

    fn op_float_trunc(&mut self, ctx: &mut PrintContext<'_>, op: OpId) -> Result<()> {
        self.op_type_cast(ctx, op)
    }

    fn op_float_ceil(&mut self, ctx: &mut PrintContext<'_>, op: OpId) -> Result<()> {
        self.op_func(ctx, op)
    }

    fn op_float_floor(&mut self, ctx: &mut PrintContext<'_>, op: OpId) -> Result<()> {
        self.op_func(ctx, op)
    }

    fn op_float_round(&mut self, ctx: &mut PrintContext<'_>, op: OpId) -> Result<()> {
        self.op_func(ctx, op)
    }

    fn op_multiequal(&mut self, _ctx: &mut PrintContext<'_>, _op: OpId) -> Result<()> {
        Ok(())
    }

    fn op_indirect(&mut self, _ctx: &mut PrintContext<'_>, _op: OpId) -> Result<()> {
        Ok(())
    }

    fn op_piece(&mut self, ctx: &mut PrintContext<'_>, op: OpId) -> Result<()> {
        self.op_func(ctx, op)
    }

    fn op_subpiece(&mut self, ctx: &mut PrintContext<'_>, op: OpId) -> Result<()> {
        self.op_subpiece_c(ctx, op)
    }

    fn op_cast(&mut self, ctx: &mut PrintContext<'_>, op: OpId) -> Result<()> {
        self.op_type_cast(ctx, op)
    }

    fn op_ptradd(&mut self, ctx: &mut PrintContext<'_>, op: OpId) -> Result<()> {
        self.op_ptradd_c(ctx, op)
    }

    fn op_ptrsub(&mut self, ctx: &mut PrintContext<'_>, op: OpId) -> Result<()> {
        self.op_ptrsub_c(ctx, op)
    }

    fn op_segment_op(&mut self, ctx: &mut PrintContext<'_>, op: OpId) -> Result<()> {
        self.op_segment_op_c(ctx, op)
    }

    fn op_cpool_ref_op(&mut self, ctx: &mut PrintContext<'_>, op: OpId) -> Result<()> {
        if self.is_java() {
            self.op_cpool_ref_op_java(ctx, op)
        } else {
            self.op_cpool_ref_op_c(ctx, op)
        }
    }

    fn op_new_op(&mut self, ctx: &mut PrintContext<'_>, op: OpId) -> Result<()> {
        self.op_new_op_c(ctx, op)
    }

    fn op_insert_op(&mut self, ctx: &mut PrintContext<'_>, op: OpId) -> Result<()> {
        self.op_func(ctx, op)
    }

    fn op_zpull_op(&mut self, ctx: &mut PrintContext<'_>, op: OpId) -> Result<()> {
        self.op_pull_c(ctx, op)
    }

    fn op_popcount_op(&mut self, ctx: &mut PrintContext<'_>, op: OpId) -> Result<()> {
        self.op_func(ctx, op)
    }

    fn op_lzcount_op(&mut self, ctx: &mut PrintContext<'_>, op: OpId) -> Result<()> {
        self.op_func(ctx, op)
    }

    fn op_spull_op(&mut self, ctx: &mut PrintContext<'_>, op: OpId) -> Result<()> {
        self.op_pull_c(ctx, op)
    }

    fn get_scope_delimiter(&self) -> String {
        self.get_token(OpTokenKey::Scope).print1.to_string()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn token_table_matches_keys() {
        let table = default_token_table();
        assert_eq!(table.len(), OpTokenKey::COUNT);
        assert_eq!(table[OpTokenKey::Scope.index()].print1, "::");
        assert_eq!(table[OpTokenKey::BooleanOr.index()].print1, "||");
        assert_eq!(table[OpTokenKey::BooleanXor.index()].precedence, 20);
        assert_eq!(table[OpTokenKey::Xorequal.index()].print1, "^=");
        assert_eq!(table[OpTokenKey::EnumCat.index()].spacing, 0);
        assert_eq!(table[OpTokenKey::Instanceof.index()].print1, "instanceof");
        assert_eq!(
            table[OpTokenKey::LessThan.index()].negate,
            Some(OpTokenKey::GreaterEqual)
        );
        assert_eq!(table[OpTokenKey::NotEqual.index()].negate, Some(OpTokenKey::Equal));
    }
}
