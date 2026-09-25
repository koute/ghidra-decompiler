use crate::address::{Address, calc_mask};
use crate::architecture::Architecture;
use crate::database::{Database, EntryId, ScopeId, Symbol, SymbolId};
use crate::dynamic::DynamicHash;
use crate::error::{Error, Result};
use crate::expression::TraverseNode;
use crate::fspec::{CallSpecId, EffectRecord, ParamActive, ParamTrial};
use crate::funcdata::Funcdata;
use crate::op::{OpId, PcodeOp, PieceNode};
use crate::opcodes::OpCode;
use crate::pcoderaw::VarnodeData;
use crate::space::{SpaceRef, SpaceType};
use crate::types::{TypeFactory, TypeId, TypeMetatype};
use crate::unionresolve::ResolvedUnion;
use crate::userop::{UserOpManage, UserPcodeOp};
use crate::variable::HighId;
use crate::varnode::{LocIter, Varnode, VarnodeId};

const POINTER_SIZE: i32 = 8;

fn type_factory(glb: &Architecture) -> &TypeFactory {
    glb.types.as_deref().expect("architecture has no type factory")
}

fn type_factory_mut(glb: &mut Architecture) -> &mut TypeFactory {
    glb.types.as_deref_mut().expect("architecture has no type factory")
}

fn symbol_table(glb: &Architecture) -> &Database {
    glb.symboltab.as_deref().expect("architecture has no symbol table")
}

fn symbol_table_mut(glb: &mut Architecture) -> &mut Database {
    glb.symboltab.as_deref_mut().expect("architecture has no symbol table")
}

fn base_type(glb: &mut Architecture, size: i32, meta: TypeMetatype) -> TypeId {
    type_factory_mut(glb)
        .get_base(size, meta)
        .expect("base data-type creation failed")
}

impl Funcdata {
    fn local_scope(&self) -> ScopeId {
        self.localmap.expect("function has no local scope")
    }

    fn first_basic_block(&self) -> crate::block::BlockId {
        self.block(self.bblocks).get_block(0)
    }

    fn apply_entry_properties(
        &mut self,
        vn: VarnodeId,
        entry: Option<EntryId>,
        vflags: u32,
        glb: &mut Architecture,
    ) -> Result<()> {
        match entry {
            Some(entry) => {
                self.vn_set_symbol_properties(vn, entry, glb)?;
            }
            None => self.vn_set_flags(vn, vflags & !Varnode::TYPELOCK),
        }
        Ok(())
    }

    pub fn set_varnode_properties(&mut self, vn: VarnodeId, glb: &mut Architecture) -> Result<()> {
        if !self.vn(vn).is_mapped() {
            let mut vflags = 0;
            let usepoint = self.vn_get_use_point(vn);
            let (addr, size) = (self.vn(vn).get_addr().clone(), self.vn(vn).get_size());
            let entry =
                symbol_table(glb).scope_query_properties(self.local_scope(), &addr, size, &usepoint, &mut vflags);
            self.apply_entry_properties(vn, entry, vflags, glb)?;
        }
        if self.vn(vn).cover.is_none() && self.is_high_on() {
            self.vbank.varnodes.get_mut(vn).calc_cover(&mut self.highs);
        }
        Ok(())
    }

    pub fn assign_high(&mut self, vn: VarnodeId, glb: &mut Architecture) -> Result<Option<HighId>> {
        if (self.flags & Funcdata::HIGHLEVEL_ON) != 0 {
            if self.vn(vn).has_cover() {
                self.vbank.varnodes.get_mut(vn).calc_cover(&mut self.highs);
            }
            let tp = self.vn(vn).get_type();
            if type_factory(glb).get(tp).has_warning() {
                self.issue_datatype_warning(tp, glb);
            }
            if !self.vn(vn).is_annotation() {
                return Ok(Some(self.high_create(vn, glb)?));
            }
        }
        Ok(None)
    }

    fn assign_high_fresh(&mut self, vn: VarnodeId, glb: &mut Architecture) {
        self.assign_high(vn, glb)
            .expect("high variable creation failed for a fresh varnode");
    }

    pub fn new_constant(&mut self, size: i32, constant_val: u64, glb: &mut Architecture) -> VarnodeId {
        let ct = base_type(glb, size, TypeMetatype::Unknown);
        let addr = glb.manager.get_constant(constant_val);
        let vn = self.vbank.create(size, &addr, ct);
        self.assign_high_fresh(vn, glb);
        vn
    }

    pub fn new_unique(&mut self, size: i32, ct: Option<TypeId>, glb: &mut Architecture) -> VarnodeId {
        let ct = match ct {
            Some(ct) => ct,
            None => base_type(glb, size, TypeMetatype::Unknown),
        };
        let vn = self.vbank.create_unique(size, ct);
        self.assign_high_fresh(vn, glb);
        if size as u32 >= self.min_laned_size {
            let addr = self.vn(vn).get_addr().clone();
            self.check_for_laned_register(size, &addr, glb);
        }
        vn
    }

    pub fn new_varnode_out(
        &mut self,
        size: i32,
        addr: &Address,
        op: OpId,
        glb: &mut Architecture,
    ) -> Result<VarnodeId> {
        let ct = base_type(glb, size, TypeMetatype::Unknown);
        let loc = if addr.is_valid_range(size as u64) {
            addr.clone()
        } else {
            glb.manager.construct_wrapping_address(addr, size)?
        };
        let vn = self
            .vbank
            .create_def(size, &loc, ct, op, &mut self.obank.ops, &mut self.highs)?;
        self.op_mut(op).set_output(Some(vn));
        self.assign_high(vn, glb)?;
        if size as u32 >= self.min_laned_size {
            self.check_for_laned_register(size, addr, glb);
        }
        let mut vflags = 0;
        let op_addr = self.op(op).get_addr().clone();
        let entry = symbol_table(glb).scope_query_properties(self.local_scope(), addr, size, &op_addr, &mut vflags);
        self.apply_entry_properties(vn, entry, vflags, glb)?;
        Ok(vn)
    }

    pub fn new_unique_out(&mut self, size: i32, op: OpId, glb: &mut Architecture) -> Result<VarnodeId> {
        let ct = base_type(glb, size, TypeMetatype::Unknown);
        let vn = self
            .vbank
            .create_def_unique(size, ct, op, &mut self.obank.ops, &mut self.highs)?;
        self.op_mut(op).set_output(Some(vn));
        self.assign_high(vn, glb)?;
        if size as u32 >= self.min_laned_size {
            let addr = self.vn(vn).get_addr().clone();
            self.check_for_laned_register(size, &addr, glb);
        }
        Ok(vn)
    }

    pub fn new_varnode(
        &mut self,
        size: i32,
        addr: &Address,
        ct: Option<TypeId>,
        glb: &mut Architecture,
    ) -> Result<VarnodeId> {
        let ct = match ct {
            Some(ct) => ct,
            None => base_type(glb, size, TypeMetatype::Unknown),
        };
        let vn = if addr.is_valid_range(size as u64) {
            self.vbank.create(size, addr, ct)
        } else {
            let loc = glb.manager.construct_wrapping_address(addr, size)?;
            self.vbank.create(size, &loc, ct)
        };
        self.assign_high(vn, glb)?;
        if size as u32 >= self.min_laned_size {
            self.check_for_laned_register(size, addr, glb);
        }
        let mut vflags = 0;
        let (loc, vn_size) = (self.vn(vn).get_addr().clone(), self.vn(vn).get_size());
        let entry = symbol_table(glb).scope_query_properties(
            self.local_scope(),
            &loc,
            vn_size,
            &Address::invalid(),
            &mut vflags,
        );
        self.apply_entry_properties(vn, entry, vflags, glb)?;
        Ok(vn)
    }

    pub fn new_varnode_space_offset(
        &mut self,
        size: i32,
        base: &SpaceRef,
        off: u64,
        glb: &mut Architecture,
    ) -> Result<VarnodeId> {
        self.new_varnode(size, &Address::new(base.clone(), off), None, glb)
    }

    pub fn new_varnode_iop(&mut self, op: OpId, glb: &mut Architecture) -> VarnodeId {
        let ct = base_type(glb, POINTER_SIZE, TypeMetatype::Unknown);
        let cspc = glb.manager.get_iop_space().expect("architecture has no iop space");
        let vn = self.vbank.create(POINTER_SIZE, &Address::new(cspc, op.0 as u64), ct);
        self.assign_high_fresh(vn, glb);
        vn
    }

    pub fn new_varnode_space(&mut self, spc: &SpaceRef, glb: &mut Architecture) -> VarnodeId {
        let ct = base_type(glb, POINTER_SIZE, TypeMetatype::Unknown);
        let addr = glb.manager.create_const_from_space(spc);
        let vn = self.vbank.create(POINTER_SIZE, &addr, ct);
        self.assign_high_fresh(vn, glb);
        vn
    }

    pub fn new_varnode_call_specs(&mut self, fc: CallSpecId, glb: &mut Architecture) -> VarnodeId {
        let ct = base_type(glb, POINTER_SIZE, TypeMetatype::Unknown);
        let cspc = glb.manager.get_fspec_space().expect("architecture has no fspec space");
        let vn = self.vbank.create(POINTER_SIZE, &Address::new(cspc, fc.0 as u64), ct);
        self.assign_high_fresh(vn, glb);
        vn
    }

    pub fn new_code_ref(&mut self, addr: &Address, glb: &mut Architecture) -> VarnodeId {
        let ct = type_factory_mut(glb)
            .get_type_code()
            .expect("code data-type creation failed");
        let vn = self.vbank.create(1, addr, ct);
        self.vn_set_flags(vn, Varnode::ANNOTATION);
        self.assign_high_fresh(vn, glb);
        vn
    }

    pub fn clone_varnode(&mut self, vn: VarnodeId) -> VarnodeId {
        let (size, addr, tp, flags) = {
            let varnode = self.vn(vn);
            (
                varnode.get_size(),
                varnode.get_addr().clone(),
                varnode.get_type(),
                varnode.get_flags(),
            )
        };
        self.clone_varnode_parts(size, &addr, tp, flags)
    }

    pub fn destroy_varnode(&mut self, vn: VarnodeId) -> Result<()> {
        let descend = self.vn(vn).descend().to_vec();
        for op in descend {
            let slot = self.op(op).get_slot(vn);
            self.op_mut(op).clear_input(slot);
        }
        if let Some(def) = self.vn(vn).get_def() {
            self.op_mut(def).set_output(None);
            self.vn_mut(vn).def = None;
        }
        self.vn_mut(vn).destroy_descend();
        self.delete_varnode(vn)
    }

    pub fn check_for_laned_register(&mut self, sz: i32, addr: &Address, glb: &Architecture) {
        let Some(laned_register) = glb.get_laned_register(addr, sz) else {
            return;
        };
        let storage = VarnodeData {
            space: addr.get_space().cloned(),
            offset: addr.get_offset(),
            size: sz as u32,
        };
        self.laned_map.insert(storage, laned_register);
    }

    pub fn find_high(&mut self, nm: &str, glb: &Architecture) -> Result<Option<HighId>> {
        let mut sym_list = Vec::new();
        let symtab = symbol_table(glb);
        symtab.scope_query_by_name(self.local_scope(), nm, &mut sym_list);
        let Some(sym) = sym_list.first().copied() else {
            return Ok(None);
        };
        let entry = symtab.symbol_get_first_whole_map(sym)?;
        if let Some(vn) = self.find_linked_varnode(entry, glb) {
            return Ok(Some(self.vn(vn).get_high()?));
        }
        Ok(None)
    }

    pub fn set_input_varnode(&mut self, vn: VarnodeId, glb: &mut Architecture) -> Result<VarnodeId> {
        if self.vn(vn).is_input() {
            return Ok(vn);
        }
        let after = self.vn(vn).get_addr().add(self.vn(vn).get_size() as i64);
        let iter = self.vbank.begin_def_addr(Varnode::INPUT, &after)?;
        if iter != self.vbank.begin_def() {
            let previous = match iter.as_ref() {
                Some(key) => self.vbank.def_tree.range(..key).next_back().map(|(_, id)| *id),
                None => self.vbank.def_tree.values().next_back().copied(),
            };
            if let Some(invn) = previous
                && self.vn(invn).is_input()
                && (self.vn(vn).overlap(self.vn(invn)) != -1 || self.vn(invn).overlap(self.vn(vn)) != -1)
            {
                if self.vn(vn).get_size() == self.vn(invn).get_size()
                    && self.vn(vn).get_addr() == self.vn(invn).get_addr()
                {
                    return Ok(invn);
                }
                return Err(Error::Lowlevel("Overlapping input varnodes".to_string()));
            }
        }
        let vn = self.vbank.set_input(vn, &mut self.obank.ops, &mut self.highs)?;
        self.set_varnode_properties(vn, glb)?;
        let (addr, size) = (self.vn(vn).get_addr().clone(), self.vn(vn).get_size());
        let effecttype = self.funcp.has_effect(&addr, size, glb);
        if effecttype == EffectRecord::UNAFFECTED {
            self.vn_set_flags(vn, Varnode::UNAFFECTED);
        }
        if effecttype == EffectRecord::RETURN_ADDRESS {
            self.vn_set_flags(vn, Varnode::UNAFFECTED);
            self.vn_mut(vn).set_return_address();
        }
        Ok(vn)
    }

    pub fn combine_input_varnodes(&mut self, vn_hi: VarnodeId, vn_lo: VarnodeId, glb: &mut Architecture) -> Result<()> {
        if !self.vn(vn_hi).is_input() || !self.vn(vn_lo).is_input() {
            return Err(Error::Lowlevel("Varnodes being combined are not inputs".to_string()));
        }
        let mut addr = self.vn(vn_lo).get_addr().clone();
        let is_contiguous = if addr.is_big_endian() {
            addr = self.vn(vn_hi).get_addr().clone();
            let otheraddr = addr.add(self.vn(vn_hi).get_size() as i64);
            otheraddr == *self.vn(vn_lo).get_addr()
        } else {
            let otheraddr = addr.add(self.vn(vn_lo).get_size() as i64);
            otheraddr == *self.vn(vn_hi).get_addr()
        };
        if !is_contiguous {
            return Err(Error::Lowlevel(
                "Input varnodes being combined are not contiguous".to_string(),
            ));
        }
        let mut piece_list = Vec::new();
        let mut other_ops_hi = false;
        let mut other_ops_lo = false;
        for op in self.vn(vn_hi).descend().iter() {
            let pcode_op = self.op(*op);
            if pcode_op.code() == OpCode::Piece && pcode_op.get_in(0) == vn_hi && pcode_op.get_in(1) == vn_lo {
                piece_list.push(*op);
            } else {
                other_ops_hi = true;
            }
        }
        for op in self.vn(vn_lo).descend().iter() {
            let pcode_op = self.op(*op);
            if pcode_op.code() != OpCode::Piece || pcode_op.get_in(0) != vn_hi || pcode_op.get_in(1) != vn_lo {
                other_ops_lo = true;
            }
        }
        for op in piece_list.iter() {
            self.op_remove_input(*op, 1);
            self.op_unset_input(*op, 0);
        }
        let mut sub_hi = None;
        let mut sub_lo = None;
        if other_ops_hi {
            let bb = self.first_basic_block();
            let start = self.block(bb).get_start();
            let op = self.new_op(2, &start);
            self.op_set_opcode(op, OpCode::Subpiece, glb);
            let cvn = self.new_constant(4, self.vn(vn_lo).get_size() as u64, glb);
            self.op_set_input(op, cvn, 1)?;
            let (hi_size, hi_addr) = (self.vn(vn_hi).get_size(), self.vn(vn_hi).get_addr().clone());
            let new_hi = self.new_varnode_out(hi_size, &hi_addr, op, glb)?;
            self.op_insert_begin(op, bb);
            self.total_replace(vn_hi, new_hi)?;
            sub_hi = Some(op);
        }
        if other_ops_lo {
            let bb = self.first_basic_block();
            let start = self.block(bb).get_start();
            let op = self.new_op(2, &start);
            self.op_set_opcode(op, OpCode::Subpiece, glb);
            let cvn = self.new_constant(4, 0, glb);
            self.op_set_input(op, cvn, 1)?;
            let (lo_size, lo_addr) = (self.vn(vn_lo).get_size(), self.vn(vn_lo).get_addr().clone());
            let new_lo = self.new_varnode_out(lo_size, &lo_addr, op, glb)?;
            self.op_insert_begin(op, bb);
            self.total_replace(vn_lo, new_lo)?;
            sub_lo = Some(op);
        }
        let out_size = self.vn(vn_hi).get_size() + self.vn(vn_lo).get_size();
        self.delete_varnode(vn_hi)?;
        self.delete_varnode(vn_lo)?;
        let in_vn = self.new_varnode(out_size, &addr, None, glb)?;
        let in_vn = self.set_input_varnode(in_vn, glb)?;
        for op in piece_list.iter() {
            self.op_set_input(*op, in_vn, 0)?;
            self.op_set_opcode(*op, OpCode::Copy, glb);
        }
        if let Some(op) = sub_hi {
            self.op_set_input(op, in_vn, 0)?;
        }
        if let Some(op) = sub_lo {
            self.op_set_input(op, in_vn, 0)?;
        }
        Ok(())
    }

    pub fn new_extended_constant(
        &mut self,
        size: i32,
        val: &[u64; 2],
        op: OpId,
        glb: &mut Architecture,
    ) -> Result<VarnodeId> {
        if size <= 8 {
            return Ok(self.new_constant(size, val[0], glb));
        }
        let op_addr = self.op(op).get_addr().clone();
        let new_const_vn;
        if val[1] == 0 {
            let ext_op = self.new_op(1, &op_addr);
            self.op_set_opcode(ext_op, OpCode::IntZext, glb);
            new_const_vn = self.new_unique_out(size, ext_op, glb)?;
            let cvn = self.new_constant(8, val[0], glb);
            self.op_set_input(ext_op, cvn, 0)?;
            self.op_insert_before(ext_op, op);
        } else {
            let piece_op = self.new_op(2, &op_addr);
            self.op_set_opcode(piece_op, OpCode::Piece, glb);
            new_const_vn = self.new_unique_out(size, piece_op, glb)?;
            let hivn = self.new_constant(8, val[1], glb);
            self.op_set_input(piece_op, hivn, 0)?;
            let lovn = self.new_constant(8, val[0], glb);
            self.op_set_input(piece_op, lovn, 1)?;
            self.op_insert_before(piece_op, op);
        }
        Ok(new_const_vn)
    }

    pub fn adjust_input_varnodes(&mut self, addr: &Address, sz: i32, glb: &mut Architecture) -> Result<()> {
        let endaddr = addr.add((sz - 1) as i64);
        let iter = self.vbank.begin_def_addr(Varnode::INPUT, addr)?;
        let enditer = self.vbank.end_def_addr(Varnode::INPUT, &endaddr)?;
        let mut inlist = Vec::new();
        for vn in self.vbank.def_range(&iter, &enditer) {
            let varnode = self.vn(vn);
            if varnode.get_offset().wrapping_add((varnode.get_size() - 1) as u64) > endaddr.get_offset() {
                return Err(Error::Lowlevel("Cannot properly adjust input varnodes".to_string()));
            }
            inlist.push(vn);
        }
        for index in 0..inlist.len() {
            let vn = inlist[index];
            let (vn_addr, vn_size) = (self.vn(vn).get_addr().clone(), self.vn(vn).get_size());
            let sa = addr.justified_contain(sz, &vn_addr, vn_size, false);
            if !self.vn(vn).is_input() || sa < 0 || sz <= vn_size {
                return Err(Error::Lowlevel("Bad adjustment to input varnode".to_string()));
            }
            let func_addr = self.get_address().clone();
            let subop = self.new_op(2, &func_addr);
            self.op_set_opcode(subop, OpCode::Subpiece, glb);
            let cvn = self.new_constant(4, sa as u64, glb);
            self.op_set_input(subop, cvn, 1)?;
            let newvn = self.new_varnode_out(vn_size, &vn_addr, subop, glb)?;
            let bb = self.first_basic_block();
            self.op_insert_begin(subop, bb);
            self.total_replace(vn, newvn)?;
            self.delete_varnode(vn)?;
            inlist[index] = newvn;
        }
        let invn = self.new_varnode(sz, addr, None, glb)?;
        let invn = self.set_input_varnode(invn, glb)?;
        let (in_addr, in_size) = (self.vn(invn).get_addr().clone(), self.vn(invn).get_size());
        self.heritage.mark_range_heritaged(&in_addr, in_size);
        for vn in inlist {
            let op = self.vn(vn).get_def().expect("adjusted input has no defining SUBPIECE");
            self.op_set_input(op, invn, 0)?;
        }
        Ok(())
    }

    pub fn destroy_varnode_recursive(&mut self, vn: VarnodeId) -> Result<()> {
        if self.vn(vn).is_auto_live() || !self.vn(vn).has_no_descend() {
            return Ok(());
        }
        if !self.vn(vn).is_written() {
            return self.delete_varnode(vn);
        }
        let mut scratch = Vec::new();
        let def = self.vn(vn).get_def().expect("written varnode has no def");
        self.op_destroy_recursive(def, &mut scratch)
    }

    pub fn descend2_undef(&mut self, vn: VarnodeId, glb: &mut Architecture) -> Result<bool> {
        let mut res = false;
        let sz = self.vn(vn).get_size();
        let descend = self.vn(vn).descend().to_vec();
        for op in descend {
            let parent = self.op(op).get_parent().expect("p-code op has no parent block");
            if self.block(parent).is_dead() {
                continue;
            }
            if self.block(parent).size_in() != 0 {
                res = true;
            }
            let slot = self.op(op).get_slot(vn);
            let badconst = self.new_constant(sz, 0xBADDEF, glb);
            if self.op(op).code() == OpCode::Multiequal {
                let inbl = self.block(parent).get_in(slot);
                let start = self.block(inbl).get_start();
                let copyop = self.new_op(1, &start);
                let inputvn = self.new_unique_out(sz, copyop, glb)?;
                self.op_set_opcode(copyop, OpCode::Copy, glb);
                self.op_set_input(copyop, badconst, 0)?;
                self.op_insert_end(copyop, inbl);
                self.op_set_input(op, inputvn, slot)?;
            } else if self.op(op).code() == OpCode::Indirect {
                let op_addr = self.op(op).get_addr().clone();
                let copyop = self.new_op(1, &op_addr);
                let inputvn = self.new_unique_out(sz, copyop, glb)?;
                self.op_set_opcode(copyop, OpCode::Copy, glb);
                self.op_set_input(copyop, badconst, 0)?;
                self.op_insert_before(copyop, op);
                self.op_set_input(op, inputvn, slot)?;
            } else {
                self.op_set_input(op, badconst, slot)?;
            }
        }
        Ok(res)
    }

    pub fn init_active_output(&mut self, glb: &Architecture) {
        let mut activeoutput = ParamActive::new(false);
        let mut maxdelay = self.funcp.get_max_output_delay(glb);
        if maxdelay > 0 {
            maxdelay = 3;
        }
        activeoutput.set_max_pass(maxdelay);
        self.activeoutput = Some(Box::new(activeoutput));
    }

    pub fn set_high_level(&mut self, glb: &mut Architecture) -> Result<()> {
        if (self.flags & Funcdata::HIGHLEVEL_ON) != 0 {
            return Ok(());
        }
        self.flags |= Funcdata::HIGHLEVEL_ON;
        self.high_level_index = self.vbank.get_create_index();
        let all = self.vbank.loc_range(&self.vbank.begin_loc(), &self.vbank.end_loc());
        for vn in all {
            self.assign_high(vn, glb)?;
        }
        Ok(())
    }

    pub fn transfer_varnode_properties(
        &mut self,
        vn: VarnodeId,
        new_vn: VarnodeId,
        lsb_offset: i32,
        _glb: &Architecture,
    ) {
        let mut new_consume = u64::MAX;
        if (lsb_offset as u32) < 8 {
            let mut fill_bits = 0;
            if lsb_offset != 0 {
                fill_bits = new_consume << (8 * (8 - lsb_offset));
            }
            new_consume =
                ((self.vn(vn).get_consume() >> (8 * lsb_offset)) | fill_bits) & calc_mask(self.vn(new_vn).get_size());
        }
        let vn_flags = self.vn(vn).get_flags() & (Varnode::DIRECTWRITE | Varnode::ADDRFORCE);
        self.vn_set_flags(new_vn, vn_flags);
        self.vn_mut(new_vn).set_consume(new_consume);
    }

    pub fn fillin_read_only(&mut self, vn: VarnodeId, glb: &mut Architecture) -> Result<bool> {
        if self.vn(vn).is_written() {
            let defop = self.vn(vn).get_def().expect("written varnode has no def");
            if self.op(defop).is_marker() {
                self.op_mut(defop).set_additional_flag(PcodeOp::WARNING);
            } else if !self.op(defop).is_warning() {
                self.op_mut(defop).set_additional_flag(PcodeOp::WARNING);
                let varnode = self.vn(vn);
                if !varnode.is_addr_force() || !varnode.has_no_descend() {
                    let mut msg = String::from("Read-only address (");
                    msg.push_str(varnode.get_space().expect("varnode has no space").get_name());
                    msg.push(',');
                    varnode.get_addr().print_raw(&mut msg);
                    msg.push_str(") is written");
                    let def_addr = self.op(defop).get_addr().clone();
                    self.warning(&msg, &def_addr, glb);
                }
            }
            return Ok(false);
        }
        if self.vn(vn).get_size() > 8 {
            return Ok(false);
        }
        let size = self.vn(vn).get_size() as usize;
        let mut bytes = [0u8; 32];
        let loader = glb.loader.clone().expect("architecture has no load image");
        match loader.load_fill(&mut bytes[..size], self.vn(vn).get_addr()) {
            Ok(()) => {}
            Err(Error::DataUnavail(_)) => {
                self.vn_clear_flags(vn, Varnode::READONLY);
                return Ok(true);
            }
            Err(err) => return Err(err),
        }
        let mut res: u64 = 0;
        if self.vn(vn).get_addr().is_big_endian() {
            for byte in bytes[..size].iter() {
                res <<= 8;
                res |= *byte as u64;
            }
        } else {
            for byte in bytes[..size].iter().rev() {
                res <<= 8;
                res |= *byte as u64;
            }
        }
        let mut changemade = false;
        let locktype = if self.vn(vn).is_type_lock() {
            Some(self.vn(vn).get_type())
        } else {
            None
        };
        let descend = self.vn(vn).descend().to_vec();
        for op in descend {
            let slot = self.op(op).get_slot(vn);
            if self.op(op).is_marker() {
                if self.op(op).code() != OpCode::Indirect || slot != 0 {
                    continue;
                }
                let outvn = self.op(op).get_out().expect("INDIRECT has no output");
                if self.vn(outvn).get_addr() == self.vn(vn).get_addr() {
                    continue;
                }
                self.op_remove_input(op, 1);
                self.op_set_opcode(op, OpCode::Copy, glb);
            }
            let cvn = self.new_constant(size as i32, res, glb);
            if let Some(locktype) = locktype {
                self.vn_update_type_locked(cvn, locktype, true, true, glb);
            }
            self.op_set_input(op, cvn, slot)?;
            changemade = true;
        }
        Ok(changemade)
    }

    pub fn replace_volatile(&mut self, vn: VarnodeId, glb: &mut Architecture) -> Result<bool> {
        let newop;
        if self.vn(vn).is_written() {
            let vw_op = UserOpManage::register_builtin(glb, UserPcodeOp::BUILTIN_VOLATILE_WRITE)?;
            if !self.vn(vn).has_no_descend() {
                return Err(Error::Lowlevel("Volatile memory was propagated".to_string()));
            }
            let defop = self.vn(vn).get_def().expect("written varnode has no def");
            let def_addr = self.op(defop).get_addr().clone();
            newop = self.new_op(3, &def_addr);
            self.op_set_opcode(newop, OpCode::Callother, glb);
            let idvn = self.new_constant(4, vw_op.get_index() as u64, glb);
            self.op_set_input(newop, idvn, 0)?;
            let vn_addr = self.vn(vn).get_addr().clone();
            let annote_vn = self.new_code_ref(&vn_addr, glb);
            self.vn_set_flags(annote_vn, Varnode::VOLATIL);
            self.op_set_input(newop, annote_vn, 1)?;
            let tmp = self.new_unique(self.vn(vn).get_size(), None, glb);
            self.op_set_output(defop, tmp, glb)?;
            self.op_set_input(newop, tmp, 2)?;
            self.op_insert_after(newop, defop);
        } else {
            let vr_op = UserOpManage::register_builtin(glb, UserPcodeOp::BUILTIN_VOLATILE_READ)?;
            if self.vn(vn).has_no_descend() {
                return Ok(false);
            }
            let Some(readop) = self.vn(vn).lone_descend() else {
                return Err(Error::Lowlevel("Volatile memory value used more than once".to_string()));
            };
            let read_addr = self.op(readop).get_addr().clone();
            newop = self.new_op(2, &read_addr);
            self.op_set_opcode(newop, OpCode::Callother, glb);
            let tmp = self.new_unique_out(self.vn(vn).get_size(), newop, glb)?;
            let idvn = self.new_constant(4, vr_op.get_index() as u64, glb);
            self.op_set_input(newop, idvn, 0)?;
            let vn_addr = self.vn(vn).get_addr().clone();
            let annote_vn = self.new_code_ref(&vn_addr, glb);
            self.vn_set_flags(annote_vn, Varnode::VOLATIL);
            self.op_set_input(newop, annote_vn, 1)?;
            let slot = self.op(readop).get_slot(vn);
            self.op_set_input(readop, tmp, slot)?;
            self.op_insert_before(newop, readop);
            if vr_op.get_display() != 0 {
                self.op_mut(newop).set_hold_output();
            }
        }
        if self.vn(vn).is_type_lock() {
            self.op_mut(newop).set_additional_flag(PcodeOp::SPECIAL_PROP);
        }
        Ok(true)
    }

    pub fn check_indirect_use(&mut self, vn: VarnodeId) -> bool {
        let mut vlist = vec![vn];
        self.vn_mut(vn).set_mark();
        let mut result = true;
        let mut index = 0;
        while index < vlist.len() && result {
            let cur = vlist[index];
            index += 1;
            for op in self.vn(cur).descend().to_vec() {
                let opc = self.op(op).code();
                if opc == OpCode::Indirect {
                    if self.op(op).is_indirect_store() {
                        let outvn = self.op(op).get_out().expect("INDIRECT has no output");
                        if !self.vn(outvn).is_mark() {
                            vlist.push(outvn);
                            self.vn_mut(outvn).set_mark();
                        }
                    }
                } else if opc == OpCode::Multiequal {
                    let outvn = self.op(op).get_out().expect("MULTIEQUAL has no output");
                    if !self.vn(outvn).is_mark() {
                        vlist.push(outvn);
                        self.vn_mut(outvn).set_mark();
                    }
                } else {
                    result = false;
                    break;
                }
            }
        }
        for vn in vlist {
            self.vn_mut(vn).clear_mark();
        }
        result
    }

    pub fn mark_indirect_only(&mut self) {
        let begin = self
            .vbank
            .begin_def_flags(Varnode::INPUT)
            .expect("input iteration failed");
        let end = self
            .vbank
            .end_def_flags(Varnode::INPUT)
            .expect("input iteration failed");
        for vn in self.vbank.def_range(&begin, &end) {
            if !self.vn(vn).is_illegal_input() {
                continue;
            }
            if self.check_indirect_use(vn) {
                self.vn_set_flags(vn, Varnode::INDIRECTONLY);
            }
        }
    }

    pub fn clear_dead_varnodes(&mut self) -> Result<()> {
        let all = self.vbank.loc_range(&self.vbank.begin_loc(), &self.vbank.end_loc());
        for vn in all {
            if !self.vbank.varnodes.contains(vn) {
                continue;
            }
            if self.vn(vn).has_no_descend() {
                if self.vn(vn).is_input() && !self.vn(vn).is_locked_input() {
                    self.vbank.make_free(vn, &self.obank.ops, &mut self.highs);
                    self.vn_mut(vn).clear_cover();
                }
                if self.vn(vn).is_free() {
                    self.delete_varnode(vn)?;
                }
            }
        }
        Ok(())
    }

    pub fn calc_nz_mask(&mut self, glb: &Architecture) {
        let types = type_factory(glb);
        let alive = self.obank.alive_ops();
        for op in alive.iter().copied() {
            if self.op(op).is_mark() {
                continue;
            }
            let mut opstack: Vec<(OpId, i32)> = vec![(op, 0)];
            self.op_mut(op).set_mark();
            while let Some(node) = opstack.last_mut() {
                let (node_op, node_slot) = *node;
                if node_slot >= self.op(node_op).num_input() {
                    if let Some(outvn) = self.op(node_op).get_out() {
                        let mask = self.op_get_nz_mask_local(node_op, true);
                        self.vn_mut(outvn).nzm = mask;
                    }
                    opstack.pop();
                    continue;
                }
                node.1 += 1;
                if self.op(node_op).code() == OpCode::Multiequal {
                    let parent = self.op(node_op).get_parent().expect("MULTIEQUAL has no parent block");
                    if self.block(parent).is_loop_in(node_slot) {
                        continue;
                    }
                }
                let vn = self.op(node_op).get_in(node_slot);
                if !self.vn(vn).is_written() {
                    let varnode = self.vn(vn);
                    let mask = if varnode.is_constant() {
                        varnode.get_offset()
                    } else if varnode.is_type_lock()
                        && types.get(varnode.get_type()).get_metatype() == TypeMetatype::Bool
                    {
                        1
                    } else {
                        let mut mask = calc_mask(varnode.get_size());
                        if varnode.is_spacebase() {
                            mask &= !0xff;
                        }
                        mask
                    };
                    self.vn_mut(vn).nzm = mask;
                } else {
                    let def = self.vn(vn).get_def().expect("written varnode has no def");
                    if !self.op(def).is_mark() {
                        opstack.push((def, 0));
                        self.op_mut(def).set_mark();
                    }
                }
            }
        }
        let mut worklist = Vec::new();
        for op in alive {
            self.op_mut(op).clear_mark();
            if self.op(op).code() == OpCode::Multiequal {
                worklist.push(op);
            }
        }
        while let Some(op) = worklist.pop() {
            let Some(vn) = self.op(op).get_out() else {
                continue;
            };
            let nzmask = self.op_get_nz_mask_local(op, false);
            if nzmask != self.vn(vn).nzm {
                self.vn_mut(vn).nzm = nzmask;
                worklist.extend_from_slice(self.vn(vn).descend());
            }
        }
    }

    pub fn sync_varnodes_with_symbols(
        &mut self,
        lm: ScopeId,
        update_datatypes: bool,
        unmapped_alias_check: bool,
        glb: &mut Architecture,
    ) -> Result<bool> {
        let mut updateoccurred = false;
        let spaceid = symbol_table(glb).scope(lm).local_data().get_space_id().clone();
        let mut iter = self.vbank.begin_loc_space(&spaceid);
        let enditer = self.vbank.end_loc_space(&spaceid, &glb.manager);
        while iter != enditer {
            let vnexemplar = self.vbank.loc_at(&iter).expect("location iterator is past the end");
            let (addr, size) = (self.vn(vnexemplar).get_addr().clone(), self.vn(vnexemplar).get_size());
            let entry = symbol_table(glb).scope_find_overlap(lm, &addr, size);
            let mut ct = None;
            let fl;
            match entry {
                Some(entry) => {
                    let mut entry_flags = symbol_table(glb).entry_get_all_flags(entry);
                    if symbol_table(glb).entry(entry).get_size() >= size {
                        if update_datatypes {
                            ct = Database::entry_get_sized_type(glb, entry, &addr, size)?;
                            if let Some(tp) = ct
                                && type_factory(glb).get(tp).get_metatype() == TypeMetatype::Unknown
                            {
                                ct = None;
                            }
                        }
                    } else {
                        entry_flags &= !(Varnode::TYPELOCK | Varnode::NAMELOCK);
                    }
                    fl = entry_flags;
                }
                None => {
                    let usepoint = self.vn_get_use_point(vnexemplar);
                    if symbol_table(glb).scope(lm).in_scope(&addr, size, &usepoint) {
                        fl = Varnode::MAPPED | Varnode::ADDRTIED;
                    } else if unmapped_alias_check {
                        fl = if symbol_table(glb).local_is_unmapped_unaliased(self, lm, vnexemplar) {
                            Varnode::NOLOCALALIAS
                        } else {
                            0
                        };
                    } else {
                        fl = 0;
                    }
                }
            }
            if self.sync_varnodes_with_symbol(&mut iter, fl, ct, glb)? {
                updateoccurred = true;
            }
        }
        Ok(updateoccurred)
    }

    pub fn mark_indirect_alias_update(&mut self, vn: VarnodeId) {
        let Some(indop) = self.vn(vn).get_def() else {
            return;
        };
        if self.op(indop).code() != OpCode::Indirect {
            return;
        }
        let in1 = self.vn(self.op(indop).get_in(1));
        if in1.get_space().map(|spc| spc.get_type()) != Some(SpaceType::Iop) {
            return;
        }
        let effect_op = PcodeOp::get_op_from_const(in1.get_addr());
        self.op_mut(effect_op).set_alias_update();
    }

    pub fn sync_varnodes_with_symbol(
        &mut self,
        iter: &mut LocIter,
        fl: u32,
        ct: Option<TypeId>,
        _glb: &mut Architecture,
    ) -> Result<bool> {
        let mut updateoccurred = false;
        let mut mask = Varnode::MAPPED;
        if (fl & Varnode::ADDRTIED) == 0 {
            mask |= Varnode::ADDRTIED | Varnode::ADDRFORCE;
        }
        if (fl & Varnode::NOLOCALALIAS) != 0 {
            mask |= Varnode::NOLOCALALIAS | Varnode::ADDRFORCE;
        }
        let fl = fl & mask;
        let first = self.vbank.loc_at(iter).expect("location iterator is past the end");
        let enditer = self
            .vbank
            .end_loc_size(self.vn(first).get_size(), &self.vn(first).get_addr().clone());
        loop {
            let vn = self.vbank.loc_at(iter).expect("location iterator is past the end");
            *iter = self.vbank.loc_next(iter);
            if !self.vn(vn).is_free() {
                let vnflags = self.vn(vn).get_flags();
                if self.vn(vn).mapentry.is_some() {
                    let local_mask = mask & !Varnode::MAPPED;
                    let local_flags = fl & local_mask;
                    if (vnflags & local_mask) != local_flags {
                        updateoccurred = true;
                        self.vn_set_flags(vn, local_flags);
                        self.vn_clear_flags(vn, (!local_flags) & local_mask);
                        self.mark_indirect_alias_update(vn);
                    }
                } else if (vnflags & mask) != fl {
                    updateoccurred = true;
                    self.vn_set_flags(vn, fl);
                    self.vn_clear_flags(vn, (!fl) & mask);
                    self.mark_indirect_alias_update(vn);
                }
                if let Some(ct) = ct
                    && self.vn_update_type(vn, ct)
                {
                    updateoccurred = true;
                }
            }
            if *iter == enditer {
                break;
            }
        }
        Ok(updateoccurred)
    }

    pub fn remap_varnode(
        &mut self,
        vn: VarnodeId,
        sym: SymbolId,
        usepoint: &Address,
        glb: &mut Architecture,
    ) -> Result<()> {
        self.vn_clear_symbol_links(vn);
        let addr = self.vn(vn).get_addr().clone();
        let scope = self.local_scope();
        let types = glb.types.as_deref().expect("architecture has no type factory");
        let symtab = glb.symboltab.as_deref_mut().expect("architecture has no symbol table");
        let entry = symtab.local_remap_symbol(scope, sym, &addr, usepoint, types)?;
        self.vn_set_symbol_entry(vn, entry, glb)
    }

    pub fn remap_dynamic_varnode(
        &mut self,
        vn: VarnodeId,
        sym: SymbolId,
        usepoint: &Address,
        hash: u64,
        glb: &mut Architecture,
    ) -> Result<()> {
        self.vn_clear_symbol_links(vn);
        let scope = self.local_scope();
        let types = glb.types.as_deref().expect("architecture has no type factory");
        let symtab = glb.symboltab.as_deref_mut().expect("architecture has no symbol table");
        let entry = symtab.local_remap_symbol_dynamic(scope, sym, hash, usepoint, types)?;
        self.vn_set_symbol_entry(vn, entry, glb)
    }

    pub fn remap_conflict_symbol(&mut self, sym: SymbolId, glb: &mut Architecture) -> Result<()> {
        let symtab = symbol_table(glb);
        let entry_id = symtab.symbol_get_first_whole_map(sym)?;
        let entry = symtab.entry(entry_id);
        if !entry.is_conflict() {
            return Ok(());
        }
        let (size, addr, first_use, unique) = (
            entry.get_size(),
            entry.get_addr().clone(),
            entry.get_first_use_address(),
            entry.get_unique(),
        );
        let name = symtab.symbol(sym).get_name().to_string();
        let Some(vn) = self.find_varnode_written(size, &addr, &first_use, unique) else {
            return Err(Error::Lowlevel(format!(
                "Cannot resolve SymbolEntry conflict on {}: no varnode",
                name
            )));
        };
        let mut dhash = DynamicHash::new();
        dhash.unique_hash_varnode(vn, self);
        if dhash.get_hash() == 0 {
            return Err(Error::Lowlevel(format!(
                "Cannot resolve SymbolEntry conflict on {}: cannot generate hash",
                name
            )));
        }
        let usepoint = self.vn_get_use_point(vn);
        self.remap_dynamic_varnode(vn, sym, &usepoint, dhash.get_hash(), glb)
    }

    fn conflict_with(&self, vn: VarnodeId, other_vn: VarnodeId) -> Option<bool> {
        let other = self.vn(other_vn);
        if !other.is_written() {
            return None;
        }
        let varnode = self.vn(vn);
        let vn_addr = self
            .op(varnode.get_def().expect("written varnode has no def"))
            .get_seq_num()
            .get_addr();
        let other_addr = self
            .op(other.get_def().expect("written varnode has no def"))
            .get_seq_num()
            .get_addr();
        if vn_addr != other_addr {
            return None;
        }
        if varnode.intersects(other) {
            let high = varnode.get_high_option();
            let other_high = other.get_high_option();
            if high != other_high {
                let same_group = match (high, other_high) {
                    (Some(first), Some(second)) => self.high(first).is_same_group(self.high(second)),
                    _ => false,
                };
                if !same_group {
                    return Some(true);
                }
            }
        }
        Some(false)
    }

    pub fn detect_symbol_conflicts(&mut self, vn: VarnodeId, _glb: &mut Architecture) -> Result<bool> {
        if self.vn(vn).is_addr_tied() {
            return Ok(false);
        }
        if !self.vn(vn).is_written() {
            return Ok(false);
        }
        if self.vn(vn).get_space().map(|spc| spc.get_type()) == Some(SpaceType::Internal) {
            return Ok(true);
        }
        let key = self.vn(vn).defiter.expect("varnode is not in the def tree");
        for (_, other_vn) in self
            .vbank
            .def_tree
            .range((std::ops::Bound::Excluded(&key), std::ops::Bound::Unbounded))
        {
            match self.conflict_with(vn, *other_vn) {
                None => break,
                Some(true) => return Ok(true),
                Some(false) => {}
            }
        }
        for (_, other_vn) in self.vbank.def_tree.range(..&key).rev() {
            match self.conflict_with(vn, *other_vn) {
                None => break,
                Some(true) => return Ok(true),
                Some(false) => {}
            }
        }
        Ok(false)
    }

    pub fn link_proto_partial(&mut self, vn: VarnodeId, glb: &mut Architecture) -> Result<()> {
        let high = self.vn(vn).get_high()?;
        if self.high_get_symbol(high, glb).is_some() {
            return Ok(());
        }
        let root_vn = PieceNode::find_root(self, vn)?;
        if root_vn == vn {
            return Ok(());
        }
        let root_high = self.vn(root_vn).get_high()?;
        if !self.high(root_high).is_same_group(self.high(high)) {
            return Ok(());
        }
        let name_rep = self.high_get_name_representative(root_high);
        let Some(sym) = self.link_symbol(name_rep, glb)? else {
            return Ok(());
        };
        self.high_establish_group_symbol_offset(root_high, glb)?;
        let entry = symbol_table(glb).symbol_get_first_whole_map(sym)?;
        self.vn_set_symbol_entry(vn, entry, glb)
    }

    pub fn link_symbol(&mut self, vn: VarnodeId, glb: &mut Architecture) -> Result<Option<SymbolId>> {
        if self.vn(vn).is_proto_partial() {
            self.link_proto_partial(vn, glb)?;
        }
        let high = self.vn(vn).get_high()?;
        if let Some(sym) = self.high_get_symbol(high, glb) {
            return Ok(Some(sym));
        }
        let mut fl = 0;
        let usepoint = self.vn_get_use_point(vn);
        let addr = self.vn(vn).get_addr().clone();
        let scope = self.local_scope();
        let entry = symbol_table(glb).scope_query_properties(scope, &addr, 1, &usepoint, &mut fl);
        if let Some(entry) = entry
            && !symbol_table(glb).entry(entry).is_conflict()
        {
            self.vn_set_symbol_entry(vn, entry, glb)?;
            return Ok(Some(symbol_table(glb).entry(entry).get_symbol()));
        }
        let mut sym = None;
        if !self.vn(vn).is_persist() {
            let entry = if self.detect_symbol_conflicts(vn, glb)? {
                let tp = self.high_get_type(high, glb);
                Database::scope_add_symbol_with_conflict(glb, self, scope, "", Some(tp), vn)?
            } else {
                let mut usepoint = self.vn_get_use_point(vn);
                if self.vn(vn).is_addr_tied() {
                    usepoint = Address::invalid();
                }
                let tp = self.high_get_type(high, glb);
                Database::scope_add_symbol_at(glb, scope, "", Some(tp), &addr, &usepoint)?
            };
            sym = Some(symbol_table(glb).entry(entry).get_symbol());
            self.vn_set_symbol_entry(vn, entry, glb)?;
        }
        Ok(sym)
    }

    pub fn link_symbol_reference(&mut self, vn: VarnodeId, glb: &mut Architecture) -> Result<Option<SymbolId>> {
        let op = self
            .vn(vn)
            .lone_descend()
            .expect("symbol reference has no lone descendant");
        let in0 = self.op(op).get_in(0);
        let in0_high = self.vn(in0).get_high()?;
        let ptype = self.high_get_type(in0_high, glb);
        let types = type_factory(glb);
        if types.get(ptype).get_metatype() != TypeMetatype::Ptr {
            return Ok(None);
        }
        let sb = types.get(ptype).get_ptr_to();
        if types.get(sb).get_metatype() != TypeMetatype::Spacebase {
            return Ok(None);
        }
        let scope = types.get(sb).get_map(glb)?;
        let op_addr = self.op(op).get_addr().clone();
        let addr = types
            .get(sb)
            .get_address(self.vn(vn).get_offset(), self.vn(in0).get_size(), &op_addr, glb);
        if addr.is_invalid() {
            return Err(Error::Lowlevel(
                "Unable to generate proper address from spacebase".to_string(),
            ));
        }
        let symtab = symbol_table(glb);
        let Some(entry) = symtab.scope_query_container(scope, &addr, 1, &Address::invalid()) else {
            return Ok(None);
        };
        let entry_data = symtab.entry(entry);
        let off = addr.get_offset().wrapping_sub(entry_data.get_addr().get_offset()) as i32 + entry_data.get_offset();
        let sym = entry_data.get_symbol();
        self.vn_set_symbol_reference(vn, entry, off, glb);
        Ok(Some(sym))
    }

    pub fn find_linked_varnode(&mut self, entry: EntryId, glb: &Architecture) -> Option<VarnodeId> {
        let entry_data = symbol_table(glb).entry(entry);
        if entry_data.is_dynamic() {
            let (first_use, hash) = (entry_data.get_first_use_address(), entry_data.get_hash());
            let mut dhash = DynamicHash::new();
            let vn = dhash.find_varnode(self, &first_use, hash)?;
            if self.vn(vn).is_annotation() {
                return None;
            }
            return Some(vn);
        }
        let usestart = entry_data.get_first_use_address();
        let (size, addr) = (entry_data.get_size(), entry_data.get_addr().clone());
        let enditer = self.vbank.end_loc_size(size, &addr);
        if usestart.is_invalid() {
            let iter = self.vbank.begin_loc_size(size, &addr);
            if iter == enditer {
                return None;
            }
            let vn = self.vbank.loc_at(&iter)?;
            if !self.vn(vn).is_addr_tied() {
                return None;
            }
            return Some(vn);
        }
        let iter = self.vbank.begin_loc_pc(size, &addr, &usestart, u32::MAX);
        for vn in self.vbank.loc_range(&iter, &enditer) {
            let usepoint = self.vn_get_use_point(vn);
            if entry_data.in_use(symbol_table(glb), &usepoint) {
                return Some(vn);
            }
        }
        None
    }

    pub fn find_linked_varnodes(&mut self, entry: EntryId, res: &mut Vec<VarnodeId>, glb: &Architecture) {
        let entry_data = symbol_table(glb).entry(entry);
        if entry_data.is_dynamic() {
            let (first_use, hash) = (entry_data.get_first_use_address(), entry_data.get_hash());
            let mut dhash = DynamicHash::new();
            if let Some(vn) = dhash.find_varnode(self, &first_use, hash) {
                res.push(vn);
            }
        } else {
            let (size, addr) = (entry_data.get_size(), entry_data.get_addr().clone());
            let iter = self.vbank.begin_loc_size(size, &addr);
            let enditer = self.vbank.end_loc_size(size, &addr);
            for vn in self.vbank.loc_range(&iter, &enditer) {
                let usepoint = self.vn_get_use_point(vn);
                if entry_data.in_use(symbol_table(glb), &usepoint) {
                    res.push(vn);
                }
            }
        }
    }

    pub fn build_dynamic_symbol(&mut self, vn: VarnodeId, glb: &mut Architecture) -> Result<()> {
        if !self.is_high_on() {
            return Err(Error::Recov(
                "Cannot create dynamic symbols until decompile has completed".to_string(),
            ));
        }
        let high = self.vn(vn).get_high()?;
        if self.high_get_symbol(high, glb).is_some() {
            return Ok(());
        }
        let mut dhash = DynamicHash::new();
        dhash.unique_hash_varnode(vn, self);
        if dhash.get_hash() == 0 {
            return Err(Error::Recov("Unable to find unique hash for varnode".to_string()));
        }
        let scope = self.local_scope();
        let hash_addr = dhash.get_address().clone();
        let sym = if self.vn(vn).is_constant() {
            let offset = self.vn(vn).get_offset();
            Database::scope_add_equate_symbol(glb, scope, "", Symbol::FORCE_HEX, offset, &hash_addr, dhash.get_hash())?
        } else {
            let tp = self.high_get_type(high, glb);
            {
                let types = glb.types.as_deref().expect("architecture has no type factory");
                let symtab = glb.symboltab.as_deref_mut().expect("architecture has no symbol table");
                symtab.scope_add_dynamic_symbol(scope, "", Some(tp), &hash_addr, dhash.get_hash(), types)?
            }
        };
        let entry = symbol_table(glb).symbol_get_first_whole_map(sym)?;
        self.vn_set_symbol_entry(vn, entry, glb)
    }

    pub fn attempt_dynamic_mapping(
        &mut self,
        entry: EntryId,
        dhash: &mut DynamicHash,
        glb: &mut Architecture,
    ) -> Result<bool> {
        let symtab = symbol_table(glb);
        let entry_data = symtab.entry(entry);
        let sym = entry_data.get_symbol();
        if Some(symtab.symbol(sym).get_scope()) != self.localmap {
            return Err(Error::Lowlevel(
                "Cannot currently have a dynamic symbol outside the local scope".to_string(),
            ));
        }
        dhash.clear();
        let category = symtab.symbol(sym).get_category();
        if category == Symbol::UNION_FACET {
            return self.apply_union_facet(entry, dhash, glb);
        }
        let (first_use, hash, entry_size) = (
            entry_data.get_first_use_address(),
            entry_data.get_hash(),
            entry_data.get_size(),
        );
        let Some(vn) = dhash.find_varnode(self, &first_use, hash) else {
            return Ok(false);
        };
        if self.vn(vn).get_symbol_entry().is_some() {
            return Ok(false);
        }
        if category == Symbol::EQUATE {
            self.vn_set_symbol_entry(vn, entry, glb)?;
            return Ok(true);
        } else if entry_size == self.vn(vn).get_size() && self.vn_set_symbol_properties(vn, entry, glb)? {
            return Ok(true);
        }
        Ok(false)
    }

    pub fn attempt_dynamic_mapping_late(
        &mut self,
        entry: EntryId,
        dhash: &mut DynamicHash,
        glb: &mut Architecture,
    ) -> Result<bool> {
        dhash.clear();
        let symtab = symbol_table(glb);
        let entry_data = symtab.entry(entry);
        let sym = entry_data.get_symbol();
        if symtab.symbol(sym).get_category() == Symbol::UNION_FACET {
            return self.apply_union_facet(entry, dhash, glb);
        }
        let (first_use, hash, entry_size) = (
            entry_data.get_first_use_address(),
            entry_data.get_hash(),
            entry_data.get_size(),
        );
        let Some(mut vn) = dhash.find_varnode(self, &first_use, hash) else {
            return Ok(false);
        };
        if self.vn(vn).get_symbol_entry().is_some() {
            return Ok(false);
        }
        let symtab = symbol_table(glb);
        let symbol = symtab.symbol(sym);
        if symbol.get_category() == Symbol::EQUATE {
            self.vn_set_symbol_entry(vn, entry, glb)?;
            return Ok(true);
        }
        if self.vn(vn).get_size() != entry_size {
            let mut msg = String::from("Unable to use symbol ");
            if !symbol.is_name_undefined() {
                msg.push_str(symbol.get_name());
                msg.push(' ');
            }
            msg.push_str(": Size does not match variable it labels");
            self.warning_header(&msg, glb);
            return Ok(false);
        }
        if self.vn(vn).is_implied() {
            let mut newvn = None;
            let varnode = self.vn(vn);
            if varnode.is_written()
                && self.op(varnode.get_def().expect("written varnode has no def")).code() == OpCode::Cast
            {
                newvn = Some(
                    self.op(varnode.get_def().expect("written varnode has no def"))
                        .get_in(0),
                );
            } else if let Some(castop) = varnode.lone_descend()
                && self.op(castop).code() == OpCode::Cast
            {
                newvn = self.op(castop).get_out();
            }
            if let Some(newvn) = newvn
                && self.vn(newvn).is_explicit()
            {
                vn = newvn;
            }
        }
        self.vn_set_symbol_entry(vn, entry, glb)?;
        let symtab = symbol_table(glb);
        let symbol = symtab.symbol(sym);
        let vn_type = self.vn(vn).get_type();
        let scope = symbol.get_scope();
        if !symbol.is_type_locked() {
            Database::scope_retype_symbol(glb, scope, sym, vn_type)?;
        } else if symbol.get_type() != Some(vn_type) {
            let msg = format!("Unable to use type for symbol {}", symbol.get_name());
            self.warning_header(&msg, glb);
            Database::scope_retype_symbol(glb, scope, sym, vn_type)?;
        }
        Ok(true)
    }

    pub fn get_internal_string(
        &mut self,
        buf: &[u8],
        size: i32,
        ptr_type: TypeId,
        read_op: OpId,
        glb: &mut Architecture,
    ) -> Result<Option<VarnodeId>> {
        let types = type_factory(glb);
        if types.get(ptr_type).get_metatype() != TypeMetatype::Ptr {
            return Ok(None);
        }
        let char_type = types.get(ptr_type).get_ptr_to();
        let ptr_size = types.get(ptr_type).get_size();
        let addr = self.op(read_op).get_addr().clone();
        let hash = {
            let types = glb.types.as_deref().expect("architecture has no type factory");
            let space_manager = &glb.manager;
            let manager = glb
                .string_manager
                .as_deref_mut()
                .expect("architecture has no string manager");
            manager.register_internal_string_data(&addr, buf, size, char_type, types, space_manager)?
        };
        if hash == 0 {
            return Ok(None);
        }
        UserOpManage::register_builtin(glb, UserPcodeOp::BUILTIN_STRINGDATA)?;
        let string_op = self.new_op(2, &addr);
        self.op_set_opcode(string_op, OpCode::Callother, glb);
        self.op_mut(string_op).clear_flag(PcodeOp::CALL);
        let idvn = self.new_constant(4, UserPcodeOp::BUILTIN_STRINGDATA as u64, glb);
        self.op_set_input(string_op, idvn, 0)?;
        let hashvn = self.new_constant(8, hash, glb);
        self.op_set_input(string_op, hashvn, 1)?;
        let res_vn = self.new_unique_out(ptr_size, string_op, glb)?;
        self.vn_update_type_locked(res_vn, ptr_type, true, false, glb);
        self.op_insert_before(string_op, read_op);
        Ok(Some(res_vn))
    }

    pub fn test_for_return_address(&mut self, vn: VarnodeId, glb: &Architecture) -> bool {
        let retaddr = &glb.default_return_addr;
        let Some(retspace) = retaddr.space.as_ref() else {
            return false;
        };
        let mut vn = vn;
        while self.vn(vn).is_written() {
            let op = self.op(self.vn(vn).get_def().expect("written varnode has no def"));
            let opc = op.code();
            if opc == OpCode::Indirect || opc == OpCode::Copy {
                vn = op.get_in(0);
            } else if opc == OpCode::IntAnd {
                if !self.vn(op.get_in(1)).is_constant() {
                    return false;
                }
                vn = op.get_in(0);
            } else {
                return false;
            }
        }
        let varnode = self.vn(vn);
        if varnode.get_space().map(|spc| spc.get_index()) != Some(retspace.get_index())
            || varnode.get_offset() != retaddr.offset
            || varnode.get_size() as u32 != retaddr.size
        {
            return false;
        }
        varnode.is_input()
    }

    pub fn total_replace(&mut self, vn: VarnodeId, newvn: VarnodeId) -> Result<()> {
        let descend = self.vn(vn).descend().to_vec();
        for op in descend {
            let slot = self.op(op).get_slot(vn);
            self.op_set_input(op, newvn, slot)?;
        }
        Ok(())
    }

    pub fn total_replace_constant(&mut self, vn: VarnodeId, val: u64, glb: &mut Architecture) -> Result<()> {
        let mut copyop: Option<OpId> = None;
        let size = self.vn(vn).get_size();
        let descend = self.vn(vn).descend().to_vec();
        for op in descend {
            let slot = self.op(op).get_slot(vn);
            let newrep = if self.op(op).is_marker() {
                match copyop {
                    Some(copy) => self.op(copy).get_out().expect("COPY has no output"),
                    None => {
                        let (copy, newrep) = if let Some(def) = self.vn(vn).get_def() {
                            let def_addr = self.op(def).get_addr().clone();
                            let copy = self.new_op(1, &def_addr);
                            self.op_set_opcode(copy, OpCode::Copy, glb);
                            let newrep = self.new_unique_out(size, copy, glb)?;
                            let cvn = self.new_constant(size, val, glb);
                            self.op_set_input(copy, cvn, 0)?;
                            self.op_insert_after(copy, def);
                            (copy, newrep)
                        } else {
                            let bb = self.first_basic_block();
                            let start = self.block(bb).get_start();
                            let copy = self.new_op(1, &start);
                            self.op_set_opcode(copy, OpCode::Copy, glb);
                            let newrep = self.new_unique_out(size, copy, glb)?;
                            let cvn = self.new_constant(size, val, glb);
                            self.op_set_input(copy, cvn, 0)?;
                            self.op_insert_begin(copy, bb);
                            (copy, newrep)
                        };
                        copyop = Some(copy);
                        newrep
                    }
                }
            } else {
                self.new_constant(size, val, glb)
            };
            self.op_set_input(op, newrep, slot)?;
        }
        Ok(())
    }

    pub fn split_uses(&mut self, vn: VarnodeId, glb: &mut Architecture) -> Result<()> {
        let op = self.vn(vn).get_def().expect("split varnode has no def");
        let descend = self.vn(vn).descend().to_vec();
        if descend.len() < 2 {
            return Ok(());
        }
        for useop in descend {
            let slot = self.op(useop).get_slot(vn);
            let op_addr = self.op(op).get_addr().clone();
            let newop = self.new_op(self.op(op).num_input(), &op_addr);
            let (size, addr, tp) = (
                self.vn(vn).get_size(),
                self.vn(vn).get_addr().clone(),
                self.vn(vn).get_type(),
            );
            let newvn = self.new_varnode(size, &addr, Some(tp), glb)?;
            self.op_set_output(newop, newvn, glb)?;
            self.op_set_opcode(newop, self.op(op).code(), glb);
            for index in 0..self.op(op).num_input() {
                let input = self.op(op).get_in(index);
                self.op_set_input(newop, input, index)?;
            }
            self.op_set_input(useop, newvn, slot)?;
            self.op_insert_before(newop, op);
        }
        Ok(())
    }

    pub fn find_disjoint_cover(&self, vn: VarnodeId, sz: &mut i32) -> Address {
        let mut addr = self.vn(vn).get_addr().clone();
        let mut endaddr = addr.add(self.vn(vn).get_size() as i64);
        let key = self.vn(vn).lociter.expect("varnode is not in the location tree");
        for (_, curvn) in self.vbank.loc_tree.range(..&key).rev() {
            let cur = self.vn(*curvn);
            let cur_end = cur.get_addr().add(cur.get_size() as i64);
            if cur_end <= addr {
                break;
            }
            addr = cur.get_addr().clone();
        }
        for (_, curvn) in self.vbank.loc_tree.range(&key..) {
            let cur = self.vn(*curvn);
            if endaddr <= *cur.get_addr() {
                break;
            }
            endaddr = cur.get_addr().add(cur.get_size() as i64);
        }
        *sz = endaddr.get_offset().wrapping_sub(addr.get_offset()) as i32;
        addr
    }

    pub fn cover_varnodes(&mut self, entry: EntryId, list: &mut [VarnodeId], glb: &mut Architecture) -> Result<()> {
        let symtab = symbol_table(glb);
        let entry_data = symtab.entry(entry);
        let sym = entry_data.get_symbol();
        let scope = symtab.symbol(sym).get_scope();
        let sym_name = symtab.symbol(sym).get_name().to_string();
        let entry_offset = entry_data.get_addr().get_offset();
        for index in 0..list.len() {
            let vn = list[index];
            if index + 1 < list.len() && self.vn(list[index + 1]).get_addr() == self.vn(vn).get_addr() {
                continue;
            }
            let mut usepoint = self.vn_get_use_point(vn);
            let (addr, size) = (self.vn(vn).get_addr().clone(), self.vn(vn).get_size());
            let overlap_entry = symbol_table(glb).scope_find_container(scope, &addr, size, &usepoint);
            if overlap_entry.is_none() {
                let diff = self.vn(vn).get_offset().wrapping_sub(entry_offset) as i32;
                let name = format!("{}_{}", sym_name, diff);
                if self.vn(vn).is_addr_tied() {
                    usepoint = Address::invalid();
                }
                let high = self.vn(vn).get_high()?;
                let tp = self.high_get_type(high, glb);
                Database::scope_add_symbol_at(glb, scope, &name, Some(tp), &addr, &usepoint)?;
            }
        }
        Ok(())
    }

    pub fn apply_union_facet(
        &mut self,
        entry: EntryId,
        dhash: &mut DynamicHash,
        glb: &mut Architecture,
    ) -> Result<bool> {
        let symtab = symbol_table(glb);
        let entry_data = symtab.entry(entry);
        let sym = entry_data.get_symbol();
        let symbol = symtab.symbol(sym);
        let sym_type = symbol.get_type().expect("union facet symbol has no data-type");
        let field_number = symbol.get_field_number();
        let (first_use, hash) = (entry_data.get_first_use_address(), entry_data.get_hash());
        if symbol.is_addr_based() {
            let mut resolve = ResolvedUnion::new_field(sym_type, field_number, type_factory_mut(glb))?;
            resolve.set_lock(true);
            let slot = DynamicHash::get_slot_from_hash(hash);
            return Ok(self.set_address_based_union_field(sym_type, &first_use, slot, &resolve, glb));
        }
        let Some(op) = dhash.find_op(self, &first_use, hash) else {
            return Ok(false);
        };
        let slot = DynamicHash::get_slot_from_hash(hash);
        if let Some(res) = self.get_union_resolution(sym_type, op, slot, glb)
            && res.get_field_num() == field_number
        {
            return Ok(false);
        }
        let vn = if slot < 0 {
            self.op(op).get_out().expect("union facet op has no output")
        } else {
            self.op(op).get_in(slot)
        };
        let mut unres_type = sym_type;
        let dt = self.vn(vn).get_type();
        let types = type_factory(glb);
        let datatype = types.get(dt);
        match datatype.get_metatype() {
            TypeMetatype::Ptr if datatype.get_ptr_to() == unres_type => {
                unres_type = dt;
            }
            TypeMetatype::PartialStruct if datatype.get_parent() == unres_type => {
                unres_type = dt;
            }
            TypeMetatype::PartialUnion if datatype.get_parent_union() == unres_type => {
                unres_type = dt;
            }
            _ => {}
        }
        let mut resolve = ResolvedUnion::new_field(unres_type, field_number, type_factory_mut(glb))?;
        resolve.set_lock(true);
        self.set_union_field(unres_type, op, slot, &resolve, glb);
        Ok(true)
    }

    pub fn map_globals(&mut self, glb: &mut Architecture) -> Result<()> {
        let mut inconsistentuse = false;
        let all = self.vbank.loc_range(&self.vbank.begin_loc(), &self.vbank.end_loc());
        let mut uncovered_varnodes = Vec::new();
        let mut index = 0;
        while index < all.len() {
            let vn = all[index];
            index += 1;
            if self.vn(vn).is_free() {
                continue;
            }
            if !self.vn(vn).is_persist() {
                continue;
            }
            if self.vn(vn).get_symbol_entry().is_some() {
                continue;
            }
            let mut maxvn = vn;
            let addr = self.vn(vn).get_addr().clone();
            let mut endaddr = addr.add(self.vn(vn).get_size() as i64);
            uncovered_varnodes.clear();
            while index < all.len() {
                let cur = all[index];
                if !self.vn(cur).is_persist() {
                    break;
                }
                if *self.vn(cur).get_addr() < endaddr {
                    if *self.vn(cur).get_addr() != addr && self.vn(cur).get_symbol_entry().is_none() {
                        uncovered_varnodes.push(cur);
                    }
                    endaddr = self.vn(cur).get_addr().add(self.vn(cur).get_size() as i64);
                    if self.vn(cur).get_size() > self.vn(maxvn).get_size() {
                        maxvn = cur;
                    }
                    index += 1;
                } else {
                    break;
                }
            }
            let ct = if *self.vn(maxvn).get_addr() == addr && addr.add(self.vn(maxvn).get_size() as i64) == endaddr {
                let high = self.vn(maxvn).get_high()?;
                self.high_get_type(high, glb)
            } else {
                base_type(
                    glb,
                    endaddr.get_offset().wrapping_sub(addr.get_offset()) as i32,
                    TypeMetatype::Unknown,
                )
            };
            let ct_size = type_factory(glb).get(ct).get_size();
            let mut fl = 0;
            let usepoint = Address::invalid();
            let scope = self.local_scope();
            let entry = symbol_table(glb).scope_query_properties(scope, &addr, 1, &usepoint, &mut fl);
            match entry {
                None => {
                    let Some(discover) = symbol_table(glb).scope_discover_scope(scope, &addr, ct_size, &usepoint)
                    else {
                        return Err(Error::Lowlevel("Could not discover scope".to_string()));
                    };
                    let mut name_index = 0;
                    let symbolname = Database::scope_build_variable_name(
                        glb,
                        Some(self),
                        discover,
                        &addr,
                        &usepoint,
                        Some(ct),
                        &mut name_index,
                        Varnode::ADDRTIED | Varnode::PERSIST,
                    )?;
                    Database::scope_add_symbol_at(glb, discover, &symbolname, Some(ct), &addr, &usepoint)?;
                }
                Some(entry) => {
                    let entry_data = symbol_table(glb).entry(entry);
                    let entry_last = entry_data
                        .get_addr()
                        .get_offset()
                        .wrapping_add(entry_data.get_size() as u64)
                        .wrapping_sub(1);
                    if addr.get_offset().wrapping_add(ct_size as u64).wrapping_sub(1) > entry_last {
                        inconsistentuse = true;
                        if !uncovered_varnodes.is_empty() {
                            self.cover_varnodes(entry, &mut uncovered_varnodes, glb)?;
                        }
                    }
                }
            }
        }
        if inconsistentuse {
            self.warning_header(
                "Globals starting with '_' overlap smaller symbols at the same address",
                glb,
            );
        }
        Ok(())
    }

    pub fn prepare_this_pointer(&mut self, glb: &mut Architecture) -> Result<()> {
        let num_inputs = self.funcp.num_params(glb);
        for index in 0..num_inputs {
            if let Some(param) = self.funcp.get_param(index, glb)
                && param.is_this_pointer(glb)
                && param.is_type_locked(glb)
            {
                return Ok(());
            }
        }
        let scope = self.local_scope();
        if symbol_table(glb).scope(scope).local_data().has_type_recommendations() {
            return Ok(());
        }
        let spc = glb
            .manager
            .get_default_data_space()
            .expect("architecture has no default data space");
        let types = type_factory_mut(glb);
        let void_type = types.get_type_void()?;
        let dt = types.get_type_pointer(spc.get_addr_size() as i32, void_type, spc.get_word_size())?;
        let addr = self.funcp.get_this_pointer_storage(dt, glb)?;
        symbol_table_mut(glb)
            .scope_mut(scope)
            .local_data_mut()
            .add_type_recommendation(&addr, dt);
        Ok(())
    }

    pub fn check_call_double_use(&self, opmatch: OpId, op: OpId, vn: VarnodeId, fl: u32, trial: &ParamTrial) -> bool {
        let slot = self.op(op).get_slot(vn);
        if slot <= 0 {
            return false;
        }
        let fc = self.call_spec(self.get_call_specs_op(op).expect("call op has no call specification"));
        if self.op(op).code() == self.op(opmatch).code() {
            let isdirect = self.op(opmatch).code() == OpCode::Call;
            let matchfc = self.call_spec(
                self.get_call_specs_op(opmatch)
                    .expect("call op has no call specification"),
            );
            if (isdirect && matchfc.get_entry_address() == fc.get_entry_address())
                || (!isdirect && self.op(op).get_in(0) == self.op(opmatch).get_in(0))
            {
                let curtrial = fc.get_active_input_ref().get_trial_for_input_varnode(slot);
                if curtrial.get_address() == trial.get_address() {
                    if self.op(op).get_parent() == self.op(opmatch).get_parent() {
                        if self.op(opmatch).get_seq_num().get_order() < self.op(op).get_seq_num().get_order() {
                            return true;
                        }
                    } else {
                        return true;
                    }
                }
            }
        }
        if fc.is_input_active() {
            let curtrial = fc.get_active_input_ref().get_trial_for_input_varnode(slot);
            if curtrial.is_checked() {
                if curtrial.is_active() {
                    return false;
                }
            } else if TraverseNode::is_alternate_path_valid(vn, fl, self) {
                return false;
            }
            return true;
        }
        false
    }

    pub fn only_op_use(&mut self, invn: VarnodeId, opmatch: OpId, trial: &ParamTrial, main_flags: u32) -> bool {
        let mut varlist: Vec<TraverseNode> = Vec::with_capacity(64);
        self.vn_mut(invn).set_mark();
        varlist.push(TraverseNode::new(invn, main_flags));
        let mut res = true;
        let mut index = 0;
        while index < varlist.len() {
            let vn = varlist[index].vn;
            let base_flags = varlist[index].flags;
            index += 1;
            for op in self.vn(vn).descend().to_vec() {
                if op == opmatch && self.op(op).get_in(trial.get_slot()) == vn {
                    continue;
                }
                let mut cur_flags = base_flags;
                match self.op(op).code() {
                    OpCode::Branch | OpCode::Cbranch | OpCode::Branchind | OpCode::Load | OpCode::Store => {
                        res = false;
                    }
                    OpCode::Call | OpCode::Callind => {
                        if self.check_call_double_use(opmatch, op, vn, cur_flags, trial) {
                            continue;
                        }
                        res = false;
                    }
                    OpCode::Indirect => {
                        cur_flags |= TraverseNode::INDIRECTALT;
                    }
                    OpCode::Copy => {
                        let out = self.op(op).get_out().expect("COPY has no output");
                        if self.vn(out).get_space().map(|spc| spc.get_type()) != Some(SpaceType::Internal)
                            && !self.op(op).is_incidental_copy()
                            && !self.vn(vn).is_incidental_copy()
                        {
                            cur_flags |= TraverseNode::ACTIONALT;
                        }
                    }
                    OpCode::Return => {
                        if self.op(opmatch).code() == OpCode::Return {
                            if self.op(op).get_in(trial.get_slot()) == vn {
                                continue;
                            }
                        } else if self.activeoutput.is_some()
                            && self.op(op).get_in(0) != vn
                            && !TraverseNode::is_alternate_path_valid(vn, cur_flags, self)
                        {
                            continue;
                        }
                        res = false;
                    }
                    OpCode::Multiequal | OpCode::IntSext | OpCode::IntZext | OpCode::Cast => {}
                    OpCode::Piece => {
                        if self.op(op).get_in(0) == vn {
                            if (cur_flags & TraverseNode::LSB_TRUNCATED) != 0 {
                                continue;
                            }
                            cur_flags |= TraverseNode::CONCAT_HIGH;
                        }
                    }
                    OpCode::Subpiece => {
                        if self.vn(self.op(op).get_in(1)).get_offset() != 0
                            && (cur_flags & TraverseNode::CONCAT_HIGH) == 0
                        {
                            cur_flags |= TraverseNode::LSB_TRUNCATED;
                        }
                    }
                    _ => {
                        cur_flags |= TraverseNode::ACTIONALT;
                    }
                }
                if !res {
                    break;
                }
                if let Some(subvn) = self.op(op).get_out() {
                    if self.vn(subvn).is_persist() {
                        res = false;
                        break;
                    }
                    if !self.vn(subvn).is_mark() {
                        varlist.push(TraverseNode::new(subvn, cur_flags));
                        self.vn_mut(subvn).set_mark();
                    }
                }
            }
            if !res {
                break;
            }
        }
        for node in varlist {
            self.vn_mut(node.vn).clear_mark();
        }
        res
    }

    pub fn ancestor_op_use(
        &mut self,
        maxlevel: i32,
        invn: VarnodeId,
        op: OpId,
        trial: &mut ParamTrial,
        offset: i32,
        main_flags: u32,
    ) -> bool {
        if maxlevel == 0 {
            return false;
        }
        if !self.vn(invn).is_written() {
            if !self.vn(invn).is_input() {
                return false;
            }
            if !self.vn(invn).is_type_lock() {
                return false;
            }
            return self.only_op_use(invn, op, trial, main_flags);
        }
        let def = self.vn(invn).get_def().expect("written varnode has no def");
        match self.op(def).code() {
            OpCode::Indirect => {
                if self.op(def).is_indirect_creation() {
                    return false;
                }
                let input = self.op(def).get_in(0);
                return self.ancestor_op_use(
                    maxlevel - 1,
                    input,
                    op,
                    trial,
                    offset,
                    main_flags | TraverseNode::INDIRECT,
                );
            }
            OpCode::Multiequal => {
                if self.op(def).is_mark() {
                    return false;
                }
                self.op_mut(def).set_mark();
                for slot in 0..self.op(def).num_input() {
                    let input = self.op(def).get_in(slot);
                    if self.ancestor_op_use(maxlevel - 1, input, op, trial, offset, main_flags) {
                        self.op_mut(def).clear_mark();
                        return true;
                    }
                }
                self.op_mut(def).clear_mark();
                return false;
            }
            OpCode::Copy => {
                let input = self.op(def).get_in(0);
                if self.vn(invn).get_space().map(|spc| spc.get_type()) == Some(SpaceType::Internal)
                    || self.op(def).is_incidental_copy()
                    || self.vn(input).is_incidental_copy()
                {
                    return self.ancestor_op_use(maxlevel - 1, input, op, trial, offset, main_flags);
                }
            }
            OpCode::Piece => {
                let lo = self.op(def).get_in(1);
                if offset == 0 {
                    return self.ancestor_op_use(maxlevel - 1, lo, op, trial, 0, main_flags);
                }
                if offset == self.vn(lo).get_size() {
                    let hi = self.op(def).get_in(0);
                    return self.ancestor_op_use(maxlevel - 1, hi, op, trial, 0, main_flags);
                }
                return false;
            }
            OpCode::Subpiece => {
                let new_off = self.vn(self.op(def).get_in(1)).get_offset() as i32;
                let input = self.op(def).get_in(0);
                if new_off == 0 && self.vn(input).is_written() {
                    let remop = self.vn(input).get_def().expect("written varnode has no def");
                    let remopc = self.op(remop).code();
                    if remopc == OpCode::IntRem || remopc == OpCode::IntSrem {
                        trial.set_rem_formed();
                    }
                }
                if self.vn(invn).get_space().map(|spc| spc.get_type()) == Some(SpaceType::Internal)
                    || self.op(def).is_incidental_copy()
                    || self.vn(input).is_incidental_copy()
                    || self.vn(invn).overlap(self.vn(input)) == new_off
                {
                    return self.ancestor_op_use(maxlevel - 1, input, op, trial, offset + new_off, main_flags);
                }
            }
            OpCode::Call | OpCode::Callind => return false,
            _ => {}
        }
        self.only_op_use(invn, op, trial, main_flags)
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct AncestorState {
    pub op: OpId,
    pub slot: i32,
    pub flags: u32,
    pub offset: i32,
}

impl AncestorState {
    pub const SEEN_SOLID0: u32 = 1;
    pub const SEEN_SOLID1: u32 = 2;
    pub const SEEN_KILL: u32 = 4;

    pub fn new(op: OpId, slot: i32) -> AncestorState {
        AncestorState {
            op,
            slot,
            flags: 0,
            offset: 0,
        }
    }

    pub fn new_from_state(data: &Funcdata, op: OpId, old_state: &AncestorState) -> AncestorState {
        let input = data.op(op).get_in(1);
        AncestorState {
            op,
            slot: 0,
            flags: 0,
            offset: old_state.offset + data.vn(input).get_offset() as i32,
        }
    }

    pub fn get_solid_slot(&self) -> i32 {
        if (self.flags & AncestorState::SEEN_SOLID0) != 0 {
            0
        } else {
            1
        }
    }

    pub fn mark_solid(&mut self, slot: i32) {
        self.flags |= if slot == 0 {
            AncestorState::SEEN_SOLID0
        } else {
            AncestorState::SEEN_SOLID1
        };
    }

    pub fn mark_kill(&mut self) {
        self.flags |= AncestorState::SEEN_KILL;
    }

    pub fn seen_solid(&self) -> bool {
        (self.flags & (AncestorState::SEEN_SOLID0 | AncestorState::SEEN_SOLID1)) != 0
    }

    pub fn seen_kill(&self) -> bool {
        (self.flags & AncestorState::SEEN_KILL) != 0
    }
}

#[derive(Clone, Debug, Default)]
pub struct AncestorRealistic {
    pub(crate) state_stack: Vec<AncestorState>,
    pub(crate) marked_vn: Vec<VarnodeId>,
    pub(crate) multi_depth: i32,
    pub(crate) allow_failing_path: bool,
}

impl AncestorRealistic {
    pub const ENTER_NODE: i32 = 0;
    pub const POP_SUCCESS: i32 = 1;
    pub const POP_SOLID: i32 = 2;
    pub const POP_FAIL: i32 = 3;
    pub const POP_FAILKILL: i32 = 4;

    pub fn new() -> AncestorRealistic {
        AncestorRealistic {
            state_stack: Vec::new(),
            marked_vn: Vec::new(),
            multi_depth: 0,
            allow_failing_path: false,
        }
    }

    pub fn mark(&mut self, data: &mut Funcdata, vn: VarnodeId) {
        self.marked_vn.push(vn);
        data.vn_mut(vn).set_mark();
    }

    fn is_internal(data: &Funcdata, vn: VarnodeId) -> bool {
        data.vn(vn).get_space().map(|spc| spc.get_type()) == Some(SpaceType::Internal)
    }

    pub fn enter_node(&mut self, data: &mut Funcdata, trial: &mut ParamTrial) -> i32 {
        let state = *self.state_stack.last().expect("ancestor state stack is empty");
        let state_vn = data.op(state.op).get_in(state.slot);
        if data.vn(state_vn).is_mark() {
            return AncestorRealistic::POP_SUCCESS;
        }
        if !data.vn(state_vn).is_written() {
            let varnode = data.vn(state_vn);
            if varnode.is_input() {
                if varnode.is_unaffected() {
                    return AncestorRealistic::POP_FAIL;
                }
                if varnode.is_persist() {
                    return AncestorRealistic::POP_SUCCESS;
                }
                if !varnode.is_direct_write() {
                    return AncestorRealistic::POP_FAIL;
                }
            }
            return AncestorRealistic::POP_SUCCESS;
        }
        self.mark(data, state_vn);
        let mut op = data.vn(state_vn).get_def().expect("written varnode has no def");
        match data.op(op).code() {
            OpCode::Indirect => {
                if data.op(op).is_indirect_creation() {
                    trial.set_ind_create_formed();
                    if data.vn(data.op(op).get_in(0)).is_indirect_zero() {
                        return AncestorRealistic::POP_FAILKILL;
                    }
                    return AncestorRealistic::POP_SUCCESS;
                }
                if !data.op(op).is_indirect_store() {
                    let out = data.op(op).get_out().expect("INDIRECT has no output");
                    if data.vn(out).is_return_address() {
                        return AncestorRealistic::POP_FAIL;
                    }
                    if trial.is_killed_by_call() {
                        return AncestorRealistic::POP_FAIL;
                    }
                }
                self.state_stack.push(AncestorState::new(op, 0));
                AncestorRealistic::ENTER_NODE
            }
            OpCode::Subpiece => {
                let out = data.op(op).get_out().expect("SUBPIECE has no output");
                let input = data.op(op).get_in(0);
                if AncestorRealistic::is_internal(data, out)
                    || data.op(op).is_incidental_copy()
                    || data.vn(input).is_incidental_copy()
                    || data.vn(out).overlap(data.vn(input)) == data.vn(data.op(op).get_in(1)).get_offset() as i32
                {
                    self.state_stack.push(AncestorState::new_from_state(data, op, &state));
                    return AncestorRealistic::ENTER_NODE;
                }
                loop {
                    let vn = data.op(op).get_in(0);
                    let varnode = data.vn(vn);
                    if !varnode.is_mark()
                        && varnode.is_input()
                        && (varnode.is_unaffected() || !varnode.is_direct_write())
                    {
                        return AncestorRealistic::POP_FAIL;
                    }
                    match varnode.get_def() {
                        Some(def) if matches!(data.op(def).code(), OpCode::Copy | OpCode::Subpiece) => op = def,
                        _ => break,
                    }
                }
                AncestorRealistic::POP_SOLID
            }
            OpCode::Copy => {
                let out = data.op(op).get_out().expect("COPY has no output");
                let input = data.op(op).get_in(0);
                if AncestorRealistic::is_internal(data, out)
                    || data.op(op).is_incidental_copy()
                    || data.vn(input).is_incidental_copy()
                    || data.vn(out).get_addr() == data.vn(input).get_addr()
                {
                    self.state_stack.push(AncestorState::new(op, 0));
                    return AncestorRealistic::ENTER_NODE;
                }
                let mut vn = input;
                loop {
                    let varnode = data.vn(vn);
                    if !varnode.is_mark() && varnode.is_input() && !varnode.is_direct_write() {
                        return AncestorRealistic::POP_FAIL;
                    }
                    if data.op(op).is_store_unmapped() {
                        return AncestorRealistic::POP_FAIL;
                    }
                    let Some(def) = varnode.get_def() else {
                        break;
                    };
                    op = def;
                    let opc = data.op(op).code();
                    if opc == OpCode::Copy || opc == OpCode::Subpiece {
                        vn = data.op(op).get_in(0);
                    } else if opc == OpCode::Piece {
                        vn = data.op(op).get_in(1);
                    } else {
                        break;
                    }
                }
                AncestorRealistic::POP_SOLID
            }
            OpCode::Multiequal => {
                self.multi_depth += 1;
                self.state_stack.push(AncestorState::new(op, 0));
                AncestorRealistic::ENTER_NODE
            }
            OpCode::Piece => {
                if data.vn(state_vn).get_size() > trial.get_size() {
                    let lo_size = data.vn(data.op(op).get_in(1)).get_size();
                    let hi_size = data.vn(data.op(op).get_in(0)).get_size();
                    if state.offset == 0 && lo_size <= trial.get_size() {
                        self.state_stack.push(AncestorState::new(op, 1));
                        return AncestorRealistic::ENTER_NODE;
                    } else if state.offset == lo_size && hi_size <= trial.get_size() {
                        self.state_stack.push(AncestorState::new(op, 0));
                        return AncestorRealistic::ENTER_NODE;
                    }
                    if data.vn(state_vn).get_space().map(|spc| spc.get_type()) != Some(SpaceType::Spacebase) {
                        return AncestorRealistic::POP_FAIL;
                    }
                }
                AncestorRealistic::POP_SOLID
            }
            _ => AncestorRealistic::POP_SOLID,
        }
    }

    pub fn upon_pop(&mut self, data: &mut Funcdata, trial: &mut ParamTrial, command: i32) -> i32 {
        let mut pop_command = command;
        let depth = self.state_stack.len();
        let state = self.state_stack[depth - 1];
        if data.op(state.op).code() == OpCode::Multiequal {
            if pop_command == AncestorRealistic::POP_FAIL {
                self.multi_depth -= 1;
                self.state_stack.pop();
                return pop_command;
            } else if pop_command == AncestorRealistic::POP_SOLID
                && self.multi_depth == 1
                && data.op(state.op).num_input() == 2
            {
                self.state_stack[depth - 2].mark_solid(state.slot);
            } else if pop_command == AncestorRealistic::POP_FAILKILL {
                self.state_stack[depth - 2].mark_kill();
            }
            self.state_stack[depth - 1].slot += 1;
            let state = self.state_stack[depth - 1];
            if state.slot == data.op(state.op).num_input() {
                let prevstate = self.state_stack[depth - 2];
                if prevstate.seen_solid() {
                    pop_command = AncestorRealistic::POP_SUCCESS;
                    if prevstate.seen_kill() {
                        if self.allow_failing_path {
                            if !self.check_conditional_exe(data, &state) {
                                pop_command = AncestorRealistic::POP_FAIL;
                            } else {
                                trial.set_cond_exe_effect();
                            }
                        } else {
                            pop_command = AncestorRealistic::POP_FAIL;
                        }
                    }
                } else if prevstate.seen_kill() {
                    pop_command = AncestorRealistic::POP_FAILKILL;
                } else {
                    pop_command = AncestorRealistic::POP_SUCCESS;
                }
                self.multi_depth -= 1;
                self.state_stack.pop();
                return pop_command;
            }
            return AncestorRealistic::ENTER_NODE;
        }
        self.state_stack.pop();
        pop_command
    }

    pub fn check_conditional_exe(&mut self, data: &Funcdata, state: &AncestorState) -> bool {
        let bl = data.block(data.op(state.op).get_parent().expect("p-code op has no parent block"));
        if bl.size_in() != 2 {
            return false;
        }
        let solid_block = data.block(bl.get_in(state.get_solid_slot()));
        if solid_block.size_out() != 1 {
            return false;
        }
        true
    }

    pub fn execute(
        &mut self,
        data: &mut Funcdata,
        op: OpId,
        slot: i32,
        trial: &mut ParamTrial,
        allow_fail: bool,
    ) -> bool {
        self.allow_failing_path = allow_fail;
        self.marked_vn.clear();
        self.state_stack.clear();
        self.multi_depth = 0;
        if data.vn(data.op(op).get_in(slot)).is_input() && !trial.has_cond_exe_effect() {
            return false;
        }
        let mut command = AncestorRealistic::ENTER_NODE;
        self.state_stack.push(AncestorState::new(op, slot));
        while !self.state_stack.is_empty() {
            command = match command {
                AncestorRealistic::ENTER_NODE => self.enter_node(data, trial),
                _ => self.upon_pop(data, trial, command),
            };
        }
        for vn in self.marked_vn.iter() {
            data.vn_mut(*vn).clear_mark();
        }
        if command == AncestorRealistic::POP_SUCCESS {
            trial.set_ancestor_realistic();
            return true;
        } else if command == AncestorRealistic::POP_SOLID {
            trial.set_ancestor_realistic();
            trial.set_ancestor_solid();
            return true;
        }
        false
    }
}
