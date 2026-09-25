pub mod funcdata_block;
pub mod funcdata_op;
pub mod funcdata_varnode;

use crate::stdsort::std_sort;
use std::collections::BTreeMap;
use std::collections::btree_map::Entry;
use std::fmt::Write;

use crate::address::Address;
use crate::architecture::Architecture;
use crate::arena::Arena;
use crate::block::{BlockId, BlockKind, ELEM_BLOCK, ELEM_BLOCKEDGE, FlowBlock};
use crate::comment::Comment;
use crate::database::{Database, EntryId, Scope, ScopeId, SymbolId};
use crate::error::{Error, Result};
use crate::fspec::{CallSpecId, ELEM_PROTOTYPE, FuncCallSpecs, FuncProto, ParamActive, ProtoModel};
use crate::heritage::{Heritage, LoadGuard};
use crate::jumptable::{ATTRIB_LABEL, JumpTable, JumpTableId};
use crate::marshal::{ATTRIB_ID, ATTRIB_INDEX, ATTRIB_NAME, ATTRIB_SIZE, AttributeId, Decoder, ElementId, Encoder};
use crate::merge::Merge;
use crate::op::{OpId, OpTreeIter, PcodeOp, PcodeOpBank};
use crate::opcodes::OpCode;
use crate::overrides::{ELEM_OVERRIDE, Override};
use crate::pcoderaw::VarnodeData;
use crate::space::{SpaceRef, SpaceType};
use crate::translate::PcodeEmit;
use crate::types::{TypeFactory, TypeId, TypeMetatype};
use crate::unionresolve::{ResolveEdge, ResolvedUnion};
use crate::variable::{GroupId, HighId, HighVariable, VariableGroup};
use crate::varmap::ELEM_LOCALDB;
use crate::varnode::{DefIter, LocIter, Varnode, VarnodeBank, VarnodeId};

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

pub use funcdata_block::CloneBlockOps;
pub use funcdata_varnode::AncestorRealistic;

pub const ATTRIB_NOCODE: AttributeId = AttributeId::new("nocode", 84);
pub const ELEM_AST: ElementId = ElementId::new("ast", 115);
pub const ELEM_FUNCTION: ElementId = ElementId::new("function", 116);
pub const ELEM_HIGHLIST: ElementId = ElementId::new("highlist", 117);
pub const ELEM_JUMPTABLELIST: ElementId = ElementId::new("jumptablelist", 118);
pub const ELEM_VARNODES: ElementId = ElementId::new("varnodes", 119);

pub type JumpTableCallback = fn(&mut Funcdata, &mut Funcdata);

pub struct Funcdata {
    pub flags: u32,
    pub clean_up_index: u32,
    pub high_level_index: u32,
    pub cast_phase_index: u32,
    pub min_laned_size: u32,
    pub size: i32,
    pub function_symbol: Option<SymbolId>,
    pub name: String,
    pub display_name: String,
    pub baseaddr: Address,
    pub funcp: FuncProto,
    pub localmap: Option<ScopeId>,
    pub callspecs: Arena<CallSpecId, FuncCallSpecs>,
    pub qlst: Vec<CallSpecId>,
    pub jumptables: Arena<JumpTableId, JumpTable>,
    pub jumpvec: Vec<JumpTableId>,
    pub vbank: VarnodeBank,
    pub obank: PcodeOpBank,
    pub blocks: Arena<BlockId, FlowBlock>,
    pub bblocks: BlockId,
    pub sblocks: BlockId,
    pub highs: Arena<HighId, HighVariable>,
    pub groups: Arena<GroupId, VariableGroup>,
    pub heritage: Heritage,
    pub covermerge: Merge,
    pub activeoutput: Option<Box<ParamActive>>,
    pub localoverride: Override,
    pub laned_map: BTreeMap<VarnodeData, usize>,
    pub union_map: BTreeMap<ResolveEdge, ResolvedUnion>,
    pub jtcallback: Option<JumpTableCallback>,
    pub modify_list: Vec<OpId>,
    pub modify_before: Vec<String>,
    pub opactdbg_count: i32,
    pub opactdbg_breakcount: i32,
    pub opactdbg_on: bool,
    pub opactdbg_active: bool,
    pub opactdbg_breakon: bool,
    pub opactdbg_pclow: Vec<Address>,
    pub opactdbg_pchigh: Vec<Address>,
    pub opactdbg_uqlow: Vec<u32>,
    pub opactdbg_uqhigh: Vec<u32>,
}

impl Funcdata {
    pub const HIGHLEVEL_ON: u32 = 1;
    pub const BLOCKS_GENERATED: u32 = 2;
    pub const BLOCKS_UNREACHABLE: u32 = 4;
    pub const PROCESSING_STARTED: u32 = 8;
    pub const PROCESSING_COMPLETE: u32 = 0x10;
    pub const TYPERECOVERY_ON: u32 = 0x20;
    pub const TYPERECOVERY_START: u32 = 0x40;
    pub const NO_CODE: u32 = 0x80;
    pub const JUMPTABLERECOVERY_ON: u32 = 0x100;
    pub const JUMPTABLERECOVERY_DONT: u32 = 0x200;
    pub const RESTART_PENDING: u32 = 0x400;
    pub const UNIMPLEMENTED_PRESENT: u32 = 0x800;
    pub const BADDATA_PRESENT: u32 = 0x1000;
    pub const DOUBLE_PRECIS_ON: u32 = 0x2000;
    pub const TYPERECOVERY_EXCEEDED: u32 = 0x4000;
    pub const NORMALIZATION_ON: u32 = 0x8000;

    pub fn new(
        nm: &str,
        disp: &str,
        conf: Option<ScopeId>,
        addr: &Address,
        sym: Option<SymbolId>,
        sz: i32,
        glb: &mut Architecture,
    ) -> Result<Funcdata> {
        let trans = glb.translate.as_deref().expect("architecture has no translator");
        let vbank = VarnodeBank::new(&glb.manager, trans);
        let mut blocks = Arena::new();
        let bblocks = blocks.alloc(FlowBlock::new_graph_kind(BlockKind::Graph));
        let sblocks = blocks.alloc(FlowBlock::new_graph_kind(BlockKind::Graph));
        let mut fd = Funcdata {
            flags: 0,
            clean_up_index: 0,
            high_level_index: 0,
            cast_phase_index: 0,
            min_laned_size: glb.get_minimum_laned_register_size() as u32,
            size: sz,
            function_symbol: sym,
            name: nm.to_string(),
            display_name: disp.to_string(),
            baseaddr: addr.clone(),
            funcp: FuncProto::new(),
            localmap: None,
            callspecs: Arena::new(),
            qlst: Vec::new(),
            jumptables: Arena::new(),
            jumpvec: Vec::new(),
            vbank,
            obank: PcodeOpBank::new(),
            blocks,
            bblocks,
            sblocks,
            highs: Arena::new(),
            groups: Arena::new(),
            heritage: Heritage::new(),
            covermerge: Merge::new(),
            activeoutput: None,
            localoverride: Override::new(),
            laned_map: BTreeMap::new(),
            union_map: BTreeMap::new(),
            jtcallback: None,
            modify_list: Vec::new(),
            modify_before: Vec::new(),
            opactdbg_count: 0,
            opactdbg_breakcount: -1,
            opactdbg_on: false,
            opactdbg_active: false,
            opactdbg_breakon: false,
            opactdbg_pclow: Vec::new(),
            opactdbg_pchigh: Vec::new(),
            opactdbg_uqlow: Vec::new(),
            opactdbg_uqhigh: Vec::new(),
        };
        if !nm.is_empty() {
            let id = match sym {
                Some(sym) => symbol_table(glb).symbol(sym).get_id(),
                None => {
                    let id: u64 = 0x57AB12CD;
                    (id << 32) | (addr.get_offset() & 0xffffffff)
                }
            };
            let scope = fd.build_local_scope(id, glb)?;
            symbol_table_mut(glb).attach_scope(scope, conf)?;
            fd.localmap = Some(scope);
            let startpoint = fd.baseaddr.add(-1);
            fd.funcp.set_scope(scope, &startpoint, glb)?;
            Database::local_reset_local_window(glb, &mut fd, scope);
        }
        Ok(fd)
    }

    fn build_local_scope(&self, id: u64, glb: &mut Architecture) -> Result<ScopeId> {
        let stackid = glb
            .manager
            .get_stack_space()
            .ok_or_else(|| Error::Lowlevel("architecture has no stack space".to_string()))?;
        let scope = Scope::new_local(glb, id, &stackid, &self.baseaddr, &self.name);
        Ok(symbol_table_mut(glb).scopes.alloc(scope))
    }

    pub fn destroy(&mut self, glb: &mut Architecture) {
        if let Some(localmap) = self.localmap {
            symbol_table_mut(glb)
                .delete_scope(localmap)
                .expect("local scope could not be deleted");
        }
        self.clear_call_specs();
        for jt in self.jumpvec.drain(..) {
            self.jumptables.remove(jt);
        }
    }

    pub fn vn(&self, id: VarnodeId) -> &Varnode {
        self.vbank.varnodes.get(id)
    }

    pub fn vn_mut(&mut self, id: VarnodeId) -> &mut Varnode {
        self.vbank.varnodes.get_mut(id)
    }

    pub fn op(&self, id: OpId) -> &PcodeOp {
        self.obank.ops.get(id)
    }

    pub fn op_mut(&mut self, id: OpId) -> &mut PcodeOp {
        self.obank.ops.get_mut(id)
    }

    pub fn block(&self, id: BlockId) -> &FlowBlock {
        self.blocks.get(id)
    }

    pub fn block_mut(&mut self, id: BlockId) -> &mut FlowBlock {
        self.blocks.get_mut(id)
    }

    pub fn high(&self, id: HighId) -> &HighVariable {
        self.highs.get(id)
    }

    pub fn high_mut(&mut self, id: HighId) -> &mut HighVariable {
        self.highs.get_mut(id)
    }

    pub fn call_spec(&self, id: CallSpecId) -> &FuncCallSpecs {
        self.callspecs.get(id)
    }

    pub fn call_spec_mut(&mut self, id: CallSpecId) -> &mut FuncCallSpecs {
        self.callspecs.get_mut(id)
    }

    pub fn jump_table(&self, id: JumpTableId) -> &JumpTable {
        self.jumptables.get(id)
    }

    pub fn jump_table_mut(&mut self, id: JumpTableId) -> &mut JumpTable {
        self.jumptables.get_mut(id)
    }

    pub fn get_name(&self) -> &str {
        &self.name
    }

    pub fn get_display_name(&self) -> &str {
        &self.display_name
    }

    pub fn get_address(&self) -> &Address {
        &self.baseaddr
    }

    pub fn get_size(&self) -> i32 {
        self.size
    }

    pub fn get_symbol(&self) -> Option<SymbolId> {
        self.function_symbol
    }

    pub fn is_high_on(&self) -> bool {
        (self.flags & Funcdata::HIGHLEVEL_ON) != 0
    }

    pub fn is_proc_started(&self) -> bool {
        (self.flags & Funcdata::PROCESSING_STARTED) != 0
    }

    pub fn is_proc_complete(&self) -> bool {
        (self.flags & Funcdata::PROCESSING_COMPLETE) != 0
    }

    pub fn has_unreachable_blocks(&self) -> bool {
        (self.flags & Funcdata::BLOCKS_UNREACHABLE) != 0
    }

    pub fn is_type_recovery_on(&self) -> bool {
        (self.flags & Funcdata::TYPERECOVERY_ON) != 0
    }

    pub fn has_type_recovery_started(&self) -> bool {
        (self.flags & Funcdata::TYPERECOVERY_START) != 0
    }

    pub fn is_type_recovery_exceeded(&self) -> bool {
        (self.flags & Funcdata::TYPERECOVERY_EXCEEDED) != 0
    }

    pub fn is_normalization_on(&self) -> bool {
        (self.flags & Funcdata::NORMALIZATION_ON) != 0
    }

    pub fn has_no_code(&self) -> bool {
        (self.flags & Funcdata::NO_CODE) != 0
    }

    pub fn set_no_code(&mut self, val: bool) {
        if val {
            self.flags |= Funcdata::NO_CODE;
        } else {
            self.flags &= !Funcdata::NO_CODE;
        }
    }

    pub fn set_laned_reg_generated(&mut self) {
        self.min_laned_size = 1000000;
    }

    pub fn set_jumptable_recovery(&mut self, val: bool) {
        if val {
            self.flags &= !Funcdata::JUMPTABLERECOVERY_DONT;
        } else {
            self.flags |= Funcdata::JUMPTABLERECOVERY_DONT;
        }
    }

    pub fn is_jumptable_recovery_on(&self) -> bool {
        (self.flags & Funcdata::JUMPTABLERECOVERY_ON) != 0
    }

    pub fn set_double_precis_recovery(&mut self, val: bool) {
        if val {
            self.flags |= Funcdata::DOUBLE_PRECIS_ON;
        } else {
            self.flags &= !Funcdata::DOUBLE_PRECIS_ON;
        }
    }

    pub fn is_double_precis_on(&self) -> bool {
        (self.flags & Funcdata::DOUBLE_PRECIS_ON) != 0
    }

    pub fn has_no_struct_blocks(&self) -> bool {
        self.blocks[self.sblocks].get_size() == 0
    }

    pub fn clear(&mut self, glb: &mut Architecture) -> Result<()> {
        self.flags &= !(Funcdata::HIGHLEVEL_ON
            | Funcdata::BLOCKS_GENERATED
            | Funcdata::PROCESSING_STARTED
            | Funcdata::TYPERECOVERY_START
            | Funcdata::TYPERECOVERY_ON
            | Funcdata::DOUBLE_PRECIS_ON
            | Funcdata::RESTART_PENDING
            | Funcdata::NORMALIZATION_ON);
        self.clean_up_index = 0;
        self.high_level_index = 0;
        self.cast_phase_index = 0;
        self.min_laned_size = glb.get_minimum_laned_register_size() as u32;
        let localmap = self.localmap.expect("function has no local scope");
        {
            let types = glb.types.as_deref_mut().expect("architecture has no type factory");
            let symtab = glb.symboltab.as_deref_mut().expect("architecture has no symbol table");
            symtab.scope_clear_unlocked(localmap, types)?;
        }
        Database::local_reset_local_window(glb, self, localmap);
        self.clear_active_output();
        self.funcp.clear_unlocked_output(glb)?;
        self.union_map.clear();
        self.clear_blocks();
        self.obank.clear();
        self.vbank.clear();
        self.highs.clear();
        self.groups.clear();
        self.clear_call_specs();
        self.clear_jump_tables();
        self.heritage.clear();
        self.covermerge.clear();
        Ok(())
    }

    fn warning_message(&self, txt: &str) -> String {
        let mut msg = if (self.flags & Funcdata::JUMPTABLERECOVERY_ON) != 0 {
            String::from("WARNING (jumptable): ")
        } else {
            String::from("WARNING: ")
        };
        msg.push_str(txt);
        msg
    }

    pub fn warning(&self, txt: &str, ad: &Address, glb: &mut Architecture) {
        let msg = self.warning_message(txt);
        glb.commentdb
            .as_deref_mut()
            .expect("architecture has no comment database")
            .add_comment_no_duplicate(Comment::WARNING, &self.baseaddr, ad, &msg);
    }

    pub fn warning_header(&self, txt: &str, glb: &mut Architecture) {
        let msg = self.warning_message(txt);
        glb.commentdb
            .as_deref_mut()
            .expect("architecture has no comment database")
            .add_comment_no_duplicate(Comment::WARNINGHEADER, &self.baseaddr, &self.baseaddr, &msg);
    }

    pub fn start_processing(&mut self, glb: &mut Architecture) -> Result<()> {
        if (self.flags & Funcdata::PROCESSING_STARTED) != 0 {
            return Err(Error::Lowlevel("Function processing already started".to_string()));
        }
        self.flags |= Funcdata::PROCESSING_STARTED;
        if self.funcp.is_inline() {
            self.warning_header("This is an inlined function", glb);
        }
        let localmap = self.localmap.expect("function has no local scope");
        {
            let types = glb.types.as_deref_mut().expect("architecture has no type factory");
            let symtab = glb.symboltab.as_deref_mut().expect("architecture has no symbol table");
            symtab.scope_clear_unlocked(localmap, types)?;
        }
        self.funcp.clear_unlocked_output(glb)?;
        let spc = self.baseaddr.get_space().cloned();
        let baddr = Address::from_parts(spc.clone(), 0);
        let eaddr = Address::from_parts(spc, u64::MAX);
        self.follow_flow(&baddr, &eaddr, glb)?;
        self.structure_reset(glb)?;
        self.sort_call_specs();
        Heritage::build_info_list(self, glb);
        Override::apply_dead_code_delay(self, glb)?;
        Ok(())
    }

    pub fn stop_processing(&mut self, _glb: &mut Architecture) {
        self.flags |= Funcdata::PROCESSING_COMPLETE;
        self.obank.destroy_dead();
    }

    pub fn start_type_recovery(&mut self) -> bool {
        if (self.flags & Funcdata::TYPERECOVERY_START) != 0 {
            return false;
        }
        self.flags |= Funcdata::TYPERECOVERY_START;
        true
    }

    pub fn set_type_recovery(&mut self, val: bool) {
        self.flags = if val {
            self.flags | Funcdata::TYPERECOVERY_ON
        } else {
            self.flags & !Funcdata::TYPERECOVERY_ON
        };
    }

    pub fn set_type_recovery_exceeded(&mut self) {
        self.flags |= Funcdata::TYPERECOVERY_EXCEEDED;
    }

    pub fn set_normalization(&mut self, val: bool) {
        self.flags = if val {
            self.flags | Funcdata::NORMALIZATION_ON
        } else {
            self.flags & !Funcdata::NORMALIZATION_ON
        };
    }

    pub fn start_cast_phase(&mut self) {
        self.cast_phase_index = self.vbank.get_create_index();
    }

    pub fn get_cast_phase_index(&self) -> u32 {
        self.cast_phase_index
    }

    pub fn get_high_level_index(&self) -> u32 {
        self.high_level_index
    }

    pub fn start_clean_up(&mut self) {
        self.clean_up_index = self.vbank.get_create_index();
    }

    pub fn get_clean_up_index(&self) -> u32 {
        self.clean_up_index
    }

    pub fn print_raw(&self, out: &mut String, glb: &mut Architecture) -> Result<()> {
        if self.block(self.bblocks).get_size() == 0 {
            if self.obank.empty() {
                return Err(Error::Recov("No operations to print".to_string()));
            }
            out.push_str("Raw operations: \n");
            let ops: Vec<OpId> = self.obank.optree.values().copied().collect();
            for op in ops {
                let _ = write!(out, "{}:\t", self.op(op).get_seq_num());
                self.op_print_raw(op, out, glb);
                out.push('\n');
            }
        } else {
            self.block_print_raw(self.bblocks, out, glb);
        }
        Ok(())
    }

    pub fn print_varnode_tree(&self, out: &mut String, glb: &Architecture) {
        for vn in self.vbank.def_range(&self.vbank.begin_def(), &self.vbank.end_def()) {
            self.vn_print_info(vn, out, glb);
        }
    }

    pub fn print_local_range(&self, out: &mut String, glb: &Architecture) {
        let symtab = symbol_table(glb);
        let localmap = symtab.scope(self.localmap.expect("function has no local scope"));
        localmap.print_bounds(out);
        for child in localmap.children().values() {
            symtab.scope(*child).print_bounds(out);
        }
    }

    pub fn encode(
        &mut self,
        encoder: &mut dyn Encoder,
        id: u64,
        save_tree: bool,
        save_overrides: bool,
        glb: &Architecture,
    ) -> Result<()> {
        self.encode_open(encoder, id, glb)?;
        if save_tree {
            self.encode_tree(encoder, glb)?;
            self.encode_high(encoder, glb)?;
        }
        self.encode_close(encoder, save_overrides, glb)
    }

    pub fn encode_no_tree(
        &self,
        encoder: &mut dyn Encoder,
        id: u64,
        save_overrides: bool,
        glb: &Architecture,
    ) -> Result<()> {
        self.encode_open(encoder, id, glb)?;
        self.encode_close(encoder, save_overrides, glb)
    }

    fn encode_open(&self, encoder: &mut dyn Encoder, id: u64, glb: &Architecture) -> Result<()> {
        encoder.open_element(ELEM_FUNCTION);
        if id != 0 {
            encoder.write_unsigned_integer(ATTRIB_ID, id);
        }
        encoder.write_string(ATTRIB_NAME, &self.name);
        encoder.write_signed_integer(ATTRIB_SIZE, self.size as i64);
        if self.has_no_code() {
            encoder.write_bool(ATTRIB_NOCODE, true);
        }
        self.baseaddr.encode(encoder)?;
        if !self.has_no_code() {
            let localmap = self.localmap.expect("function has no local scope");
            Database::scope_encode_recursive(glb, localmap, encoder, false)?;
        }
        Ok(())
    }

    fn encode_close(&self, encoder: &mut dyn Encoder, save_overrides: bool, glb: &Architecture) -> Result<()> {
        self.encode_jump_table(encoder)?;
        self.funcp.encode(encoder, glb)?;
        if save_overrides {
            self.localoverride.encode(encoder, glb)?;
        }
        encoder.close_element(ELEM_FUNCTION);
        Ok(())
    }

    pub fn decode(&mut self, decoder: &mut dyn Decoder, glb: &mut Architecture) -> Result<u64> {
        self.name.clear();
        self.size = -1;
        let mut id: u64 = 0;
        let elem_id = decoder.open_element_expect(ELEM_FUNCTION)?;
        loop {
            let attrib_id = decoder.get_next_attribute_id()?;
            if attrib_id == 0 {
                break;
            }
            if attrib_id == ATTRIB_NAME {
                self.name = decoder.read_string()?;
            } else if attrib_id == ATTRIB_SIZE {
                self.size = decoder.read_signed_integer()? as i32;
            } else if attrib_id == ATTRIB_ID {
                id = decoder.read_unsigned_integer()?;
            } else if attrib_id == ATTRIB_NOCODE {
                if decoder.read_bool()? {
                    self.flags |= Funcdata::NO_CODE;
                }
            } else if attrib_id == ATTRIB_LABEL {
                self.display_name = decoder.read_string()?;
            }
        }
        if self.name.is_empty() {
            return Err(Error::Lowlevel("Missing function name".to_string()));
        }
        if self.display_name.is_empty() {
            self.display_name = self.name.clone();
        }
        if self.size == -1 {
            return Err(Error::Lowlevel("Missing function size".to_string()));
        }
        self.baseaddr = Address::decode(decoder)?;
        loop {
            let sub_id = decoder.peek_element()?;
            if sub_id == 0 {
                break;
            }
            if sub_id == ELEM_LOCALDB {
                if self.localmap.is_some() {
                    return Err(Error::Lowlevel(format!(
                        "Pre-existing local scope when restoring: {}",
                        self.name
                    )));
                }
                let scope = self.build_local_scope(id, glb)?;
                Database::decode_scope(glb, decoder, scope)?;
                self.localmap = Some(scope);
            } else if sub_id == ELEM_OVERRIDE {
                let mut localoverride = std::mem::take(&mut self.localoverride);
                let res = localoverride.decode(decoder, glb);
                self.localoverride = localoverride;
                res?;
            } else if sub_id == ELEM_PROTOTYPE {
                if self.localmap.is_none() {
                    self.attach_default_local_scope(id, glb)?;
                }
                let localmap = self.localmap.expect("function has no local scope");
                let startpoint = self.baseaddr.add(-1);
                self.funcp.set_scope(localmap, &startpoint, glb)?;
                self.funcp.decode(decoder, glb)?;
            } else if sub_id == ELEM_JUMPTABLELIST {
                self.decode_jump_table(decoder, glb)?;
            } else {
                return Err(Error::Decoder("unexpected child element of <function>".to_string()));
            }
        }
        decoder.close_element(elem_id)?;
        if self.localmap.is_none() {
            self.attach_default_local_scope(id, glb)?;
            let localmap = self.localmap.expect("function has no local scope");
            let startpoint = self.baseaddr.add(-1);
            self.funcp.set_scope(localmap, &startpoint, glb)?;
        }
        let localmap = self.localmap.expect("function has no local scope");
        Database::local_reset_local_window(glb, self, localmap);
        Ok(id)
    }

    fn attach_default_local_scope(&mut self, id: u64, glb: &mut Architecture) -> Result<()> {
        let scope = self.build_local_scope(id, glb)?;
        let global = symbol_table(glb).get_global_scope();
        symbol_table_mut(glb).attach_scope(scope, global)?;
        self.localmap = Some(scope);
        Ok(())
    }

    pub fn encode_jump_table(&self, encoder: &mut dyn Encoder) -> Result<()> {
        if self.jumpvec.is_empty() {
            return Ok(());
        }
        encoder.open_element(ELEM_JUMPTABLELIST);
        for jt in self.jumpvec.iter() {
            self.jump_table(*jt).encode(encoder)?;
        }
        encoder.close_element(ELEM_JUMPTABLELIST);
        Ok(())
    }

    pub fn decode_jump_table(&mut self, decoder: &mut dyn Decoder, _glb: &mut Architecture) -> Result<()> {
        let elem_id = decoder.open_element_expect(ELEM_JUMPTABLELIST)?;
        while decoder.peek_element()? != 0 {
            let mut jt = JumpTable::default();
            jt.decode(decoder)?;
            let id = self.jumptables.alloc(jt);
            self.jumpvec.push(id);
        }
        decoder.close_element(elem_id)?;
        Ok(())
    }

    pub fn encode_varnode(&self, encoder: &mut dyn Encoder, iter: &LocIter, enditer: &LocIter) -> Result<()> {
        for vn in self.vbank.loc_range(iter, enditer) {
            self.vn(vn).encode(encoder, self)?;
        }
        Ok(())
    }

    pub fn encode_tree(&self, encoder: &mut dyn Encoder, glb: &Architecture) -> Result<()> {
        encoder.open_element(ELEM_AST);
        encoder.open_element(ELEM_VARNODES);
        for index in 0..glb.manager.num_spaces() {
            let Some(base) = glb.manager.get_space(index) else {
                continue;
            };
            if base.get_type() == SpaceType::Iop {
                continue;
            }
            let iter = self.vbank.begin_loc_space(&base);
            let enditer = self.vbank.end_loc_space(&base, &glb.manager);
            self.encode_varnode(encoder, &iter, &enditer)?;
        }
        encoder.close_element(ELEM_VARNODES);
        let bblocks = self.block(self.bblocks);
        for index in 0..bblocks.get_size() {
            let bs = bblocks.get_block(index);
            encoder.open_element(ELEM_BLOCK);
            encoder.write_signed_integer(ATTRIB_INDEX, self.block(bs).get_index() as i64);
            self.block_encode_body(bs, encoder)?;
            for op in self.block(bs).basic().op.to_vec(&self.obank.ops) {
                self.op_encode(op, encoder, glb)?;
            }
            encoder.close_element(ELEM_BLOCK);
        }
        for index in 0..bblocks.get_size() {
            let bs = bblocks.get_block(index);
            if self.block(bs).size_in() == 0 {
                continue;
            }
            encoder.open_element(ELEM_BLOCKEDGE);
            encoder.write_signed_integer(ATTRIB_INDEX, self.block(bs).get_index() as i64);
            self.block_encode_edges(bs, encoder)?;
            encoder.close_element(ELEM_BLOCKEDGE);
        }
        encoder.close_element(ELEM_AST);
        Ok(())
    }

    pub fn encode_high(&mut self, encoder: &mut dyn Encoder, glb: &Architecture) -> Result<()> {
        if !self.is_high_on() {
            return Ok(());
        }
        encoder.open_element(ELEM_HIGHLIST);
        let all = self.vbank.loc_range(&self.vbank.begin_loc(), &self.vbank.end_loc());
        for vn in all.iter() {
            if self.vn(*vn).is_annotation() {
                continue;
            }
            let high = self.vn(*vn).get_high()?;
            if self.high(high).is_mark() {
                continue;
            }
            self.high_mut(high).set_mark();
            self.high_encode(high, encoder, glb)?;
        }
        for vn in all.iter() {
            if !self.vn(*vn).is_annotation() {
                let high = self.vn(*vn).get_high()?;
                self.high_mut(high).clear_mark();
            }
        }
        encoder.close_element(ELEM_HIGHLIST);
        Ok(())
    }

    pub fn get_override(&mut self) -> &mut Override {
        &mut self.localoverride
    }

    pub fn set_restart_pending(&mut self, val: bool) {
        self.flags = if val {
            self.flags | Funcdata::RESTART_PENDING
        } else {
            self.flags & !Funcdata::RESTART_PENDING
        };
    }

    pub fn has_restart_pending(&self) -> bool {
        (self.flags & Funcdata::RESTART_PENDING) != 0
    }

    pub fn has_unimplemented(&self) -> bool {
        (self.flags & Funcdata::UNIMPLEMENTED_PRESENT) != 0
    }

    pub fn has_bad_data(&self) -> bool {
        (self.flags & Funcdata::BADDATA_PRESENT) != 0
    }

    pub fn spacebase(&mut self, glb: &mut Architecture) -> Result<()> {
        let localmap = self.localmap.expect("function has no local scope");
        for index in 0..glb.manager.num_spaces() {
            let Some(spc) = glb.manager.get_space(index) else {
                continue;
            };
            let numspace = spc.num_spacebase();
            for base_index in 0..numspace {
                let point = spc.get_spacebase(base_index)?;
                let scope_id = symbol_table(glb).scope(localmap).get_id();
                let types = type_factory_mut(glb);
                let ct = types.get_type_spacebase(&spc, scope_id)?;
                let ptr = types.get_type_pointer(point.size as i32, ct, spc.get_word_size())?;
                let addr = Address::from_parts(point.space.clone(), point.offset);
                let mut iter = self.vbank.begin_loc_size(point.size as i32, &addr);
                let enditer = self.vbank.end_loc_size(point.size as i32, &addr);
                while iter != enditer {
                    let vn = self.vbank.loc_at(&iter).expect("location iterator is past the end");
                    iter = self.vbank.loc_next(&iter);
                    if self.vn(vn).is_free() {
                        continue;
                    }
                    if self.vn(vn).is_spacebase() {
                        if let Some(op) = self.vn(vn).get_def()
                            && self.op(op).code() == OpCode::IntAdd
                        {
                            self.split_uses(vn, glb)?;
                        }
                    } else {
                        self.vn_set_flags(vn, Varnode::SPACEBASE);
                        if self.vn(vn).is_input() {
                            self.vn_update_type_locked(vn, ptr, true, true, glb);
                        }
                    }
                }
            }
        }
        Ok(())
    }

    pub fn new_spacebase_ptr(&mut self, id: &SpaceRef, glb: &mut Architecture) -> Result<VarnodeId> {
        let point = id.get_spacebase(0)?;
        self.new_varnode(
            point.size as i32,
            &Address::from_parts(point.space, point.offset),
            None,
            glb,
        )
    }

    pub fn find_spacebase_input(&self, id: &SpaceRef) -> Result<Option<VarnodeId>> {
        let point = id.get_spacebase(0)?;
        Ok(self
            .vbank
            .find_input(point.size as i32, &Address::from_parts(point.space, point.offset)))
    }

    pub fn construct_spacebase_input(&mut self, id: &SpaceRef, glb: &mut Architecture) -> Result<VarnodeId> {
        if let Some(space_ptr) = self.find_spacebase_input(id)? {
            return Ok(space_ptr);
        }
        if id.num_spacebase() == 0 {
            return Err(Error::Lowlevel(format!(
                "Unable to construct pointer into space: {}",
                id.get_name()
            )));
        }
        let point = id.get_spacebase(0)?;
        let localmap = self.localmap.expect("function has no local scope");
        let scope_id = symbol_table(glb).scope(localmap).get_id();
        let types = type_factory_mut(glb);
        let ct = types.get_type_spacebase(id, scope_id)?;
        let ptr = types.get_type_pointer(point.size as i32, ct, id.get_word_size())?;
        let space_ptr = self.new_varnode(
            point.size as i32,
            &Address::from_parts(point.space.clone(), point.offset),
            Some(ptr),
            glb,
        )?;
        let space_ptr = self.set_input_varnode(space_ptr, glb)?;
        self.vn_set_flags(space_ptr, Varnode::SPACEBASE);
        self.vn_update_type_locked(space_ptr, ptr, true, true, glb);
        Ok(space_ptr)
    }

    pub fn construct_const_spacebase(&mut self, id: &SpaceRef, glb: &mut Architecture) -> Result<VarnodeId> {
        let types = type_factory_mut(glb);
        let ct = types.get_type_spacebase(id, 0)?;
        let ptr = types.get_type_pointer(id.get_addr_size() as i32, ct, id.get_word_size())?;
        let space_ptr = self.new_constant(id.get_addr_size() as i32, 0, glb);
        self.vn_update_type_locked(space_ptr, ptr, true, true, glb);
        self.vn_set_flags(space_ptr, Varnode::SPACEBASE);
        Ok(space_ptr)
    }

    pub fn spacebase_constant(
        &mut self,
        op: OpId,
        slot: i32,
        entry: EntryId,
        rampoint: &Address,
        origval: u64,
        origsize: i32,
        glb: &mut Architecture,
    ) -> Result<()> {
        let sz = rampoint.get_addr_size();
        let spaceid = rampoint.get_space().cloned().expect("rampoint has no space");
        let (sym, entry_offset) = {
            let symtab = symbol_table(glb);
            let entry_data = symtab.entry(entry);
            (entry_data.get_symbol(), entry_data.get_addr().get_offset())
        };
        let (scope_id, entrytype, sym_type_locked) = {
            let symtab = symbol_table(glb);
            let symbol = symtab.symbol(sym);
            (
                symtab.scope(symbol.get_scope()).get_id(),
                symbol.get_type().expect("symbol has no data-type"),
                symbol.is_type_locked(),
            )
        };
        let types = type_factory_mut(glb);
        let sb_type = types.get_type_spacebase(&spaceid, scope_id)?;
        let sb_type = types.get_type_pointer(sz, sb_type, spaceid.get_word_size())?;
        let mut extra = rampoint.get_offset().wrapping_sub(entry_offset);
        extra = crate::space::AddrSpace::byte_to_address(extra, spaceid.get_word_size());
        let mut add_op: Option<OpId> = None;
        let mut extra_op: Option<OpId> = None;
        let mut zext_op: Option<OpId> = None;
        let mut sub_op: Option<OpId> = None;
        let mut is_copy = false;
        if self.op(op).code() == OpCode::Copy {
            is_copy = true;
            if sz < origsize {
                zext_op = Some(op);
            } else {
                self.op_mut(op).insert_input(1);
                if origsize < sz {
                    sub_op = Some(op);
                } else if extra != 0 {
                    extra_op = Some(op);
                } else {
                    add_op = Some(op);
                }
            }
        }
        let spacebase_vn = self.new_constant(sz, 0, glb);
        self.vn_update_type_locked(spacebase_vn, sb_type, true, true, glb);
        self.vn_set_flags(spacebase_vn, Varnode::SPACEBASE);
        let op_addr = self.op(op).get_addr().clone();
        let add_op = match add_op {
            None => {
                let new_add = self.new_op(2, &op_addr);
                self.op_set_opcode(new_add, OpCode::Ptrsub, glb);
                self.new_unique_out(sz, new_add, glb)?;
                self.op_insert_before(new_add, op);
                new_add
            }
            Some(existing) => {
                self.op_set_opcode(existing, OpCode::Ptrsub, glb);
                existing
            }
        };
        let mut outvn = self.op(add_op).get_out().expect("PTRSUB has no output");
        let newconstoff = origval.wrapping_sub(extra);
        let newconst = self.new_constant(sz, newconstoff, glb);
        self.vn_mut(newconst)
            .set_symbol_check(Varnode::SYMCHECK_COMPLETE as u32);
        if spaceid.is_truncated() {
            self.op_mut(add_op).set_ptr_flow();
        }
        self.op_set_input(add_op, spacebase_vn, 0)?;
        self.op_set_input(add_op, newconst, 1)?;
        let ptrentrytype =
            type_factory_mut(glb).get_type_pointer_strip_array(sz, entrytype, spaceid.get_word_size())?;
        let mut typelock = sym_type_locked;
        if typelock && type_factory(glb).get(entrytype).get_metatype() == TypeMetatype::Unknown {
            typelock = false;
        }
        self.vn_update_type_locked(outvn, ptrentrytype, typelock, false, glb);
        if extra != 0 {
            let extra_op = match extra_op {
                None => {
                    let new_extra = self.new_op(2, &op_addr);
                    self.op_set_opcode(new_extra, OpCode::IntAdd, glb);
                    self.new_unique_out(sz, new_extra, glb)?;
                    self.op_insert_before(new_extra, op);
                    new_extra
                }
                Some(existing) => {
                    self.op_set_opcode(existing, OpCode::IntAdd, glb);
                    existing
                }
            };
            let extconst = self.new_constant(sz, extra, glb);
            self.vn_mut(extconst)
                .set_symbol_check(Varnode::SYMCHECK_COMPLETE as u32);
            self.op_set_input(extra_op, outvn, 0)?;
            self.op_set_input(extra_op, extconst, 1)?;
            outvn = self.op(extra_op).get_out().expect("INT_ADD has no output");
        }
        if sz < origsize {
            let zext_op = match zext_op {
                None => {
                    let new_zext = self.new_op(1, &op_addr);
                    self.op_set_opcode(new_zext, OpCode::IntZext, glb);
                    self.new_unique_out(origsize, new_zext, glb)?;
                    self.op_insert_before(new_zext, op);
                    new_zext
                }
                Some(existing) => {
                    self.op_set_opcode(existing, OpCode::IntZext, glb);
                    existing
                }
            };
            self.op_set_input(zext_op, outvn, 0)?;
            outvn = self.op(zext_op).get_out().expect("INT_ZEXT has no output");
        } else if origsize < sz {
            let sub_op = match sub_op {
                None => {
                    let new_sub = self.new_op(2, &op_addr);
                    self.op_set_opcode(new_sub, OpCode::Subpiece, glb);
                    self.new_unique_out(origsize, new_sub, glb)?;
                    self.op_insert_before(new_sub, op);
                    new_sub
                }
                Some(existing) => {
                    self.op_set_opcode(existing, OpCode::Subpiece, glb);
                    existing
                }
            };
            self.op_set_input(sub_op, outvn, 0)?;
            let zero = self.new_constant(4, 0, glb);
            self.op_set_input(sub_op, zero, 1)?;
            outvn = self.op(sub_op).get_out().expect("SUBPIECE has no output");
        }
        if !is_copy {
            self.op_set_input(op, outvn, slot)?;
        }
        Ok(())
    }

    pub fn get_heritage_pass(&self) -> i32 {
        self.heritage.get_pass()
    }

    pub fn num_heritage_passes(&mut self, spc: &SpaceRef) -> Result<i32> {
        self.heritage.num_heritage_passes(spc)
    }

    pub fn seen_deadcode(&mut self, spc: &SpaceRef) {
        self.heritage.seen_dead_code(spc)
    }

    pub fn set_dead_code_delay(&mut self, spc: &SpaceRef, delay: i32) -> Result<()> {
        self.heritage.set_dead_code_delay(spc, delay)
    }

    pub fn dead_removal_allowed(&self, spc: &SpaceRef) -> bool {
        self.heritage.dead_removal_allowed(spc)
    }

    pub fn dead_removal_allowed_seen(&mut self, spc: &SpaceRef) -> bool {
        self.heritage.dead_removal_allowed_seen(spc)
    }

    pub fn is_heritaged(&self, vn: VarnodeId) -> bool {
        self.heritage.heritage_pass(self.vn(vn).get_addr()) >= 0
    }

    pub fn get_load_guards(&self) -> &[LoadGuard] {
        self.heritage.get_load_guards()
    }

    pub fn get_store_guards(&self) -> &[LoadGuard] {
        self.heritage.get_store_guards()
    }

    pub fn get_store_guard(&self, op: OpId) -> Option<&LoadGuard> {
        self.heritage.get_store_guard(op)
    }

    pub fn num_calls(&self) -> i32 {
        self.qlst.len() as i32
    }

    pub fn get_call_specs(&self, index: i32) -> CallSpecId {
        self.qlst[index as usize]
    }

    pub fn get_call_specs_op(&self, op: OpId) -> Option<CallSpecId> {
        let vn = self.vn(self.op(op).get_in(0));
        if vn.get_space().map(|spc| spc.get_type()) == Some(SpaceType::Fspec) {
            return Some(FuncCallSpecs::get_fspec_from_const(vn.get_addr()));
        }
        self.qlst.iter().copied().find(|fc| self.call_spec(*fc).get_op() == op)
    }

    pub fn fillin_extrapop(&mut self, glb: &mut Architecture) -> Result<i32> {
        if self.has_no_code() {
            return Ok(self.funcp.get_extra_pop());
        }
        if self.funcp.get_extra_pop() != ProtoModel::EXTRAPOP_UNKNOWN {
            return Ok(self.funcp.get_extra_pop());
        }
        let Some(retop) = self.obank.begin(OpCode::Return) else {
            return Ok(0);
        };
        let mut buffer = [0u8; 4];
        let loader = glb.loader.clone().expect("architecture has no load image");
        loader.load_fill(&mut buffer, self.op(retop).get_addr())?;
        let mut extrapop: i32 = 4;
        if buffer[0] == 0xc2 {
            extrapop = buffer[2] as i32;
            extrapop <<= 8;
            extrapop += buffer[1] as i32;
            extrapop += 4;
        }
        self.funcp.set_extra_pop(extrapop);
        Ok(extrapop)
    }

    pub fn clear_call_specs(&mut self) {
        for fc in self.qlst.drain(..) {
            self.callspecs.remove(fc);
        }
    }

    pub fn issue_datatype_warning(&mut self, dt: TypeId, glb: &mut Architecture) {
        let warn = type_factory(glb).find_warning(dt);
        if !warn.is_empty() {
            self.warning_header(&warn, glb);
        }
    }

    pub fn compare_callspecs(&self, first: CallSpecId, second: CallSpecId) -> bool {
        let first_op = self.op(self.call_spec(first).get_op());
        let second_op = self.op(self.call_spec(second).get_op());
        let ind1 = self
            .block(first_op.get_parent().expect("call op has no parent block"))
            .get_index();
        let ind2 = self
            .block(second_op.get_parent().expect("call op has no parent block"))
            .get_index();
        if ind1 != ind2 {
            return ind1 < ind2;
        }
        first_op.get_seq_num().get_order() < second_op.get_seq_num().get_order()
    }

    pub fn sort_call_specs(&mut self) {
        let mut qlst = std::mem::take(&mut self.qlst);
        std_sort(&mut qlst, |first, second| self.compare_callspecs(*first, *second));
        self.qlst = qlst;
    }

    pub fn delete_call_specs(&mut self, op: OpId) {
        let position = self.qlst.iter().position(|fc| self.call_spec(*fc).get_op() == op);
        if let Some(position) = position {
            let fc = self.qlst.remove(position);
            self.callspecs.remove(fc);
        }
    }

    pub fn do_live_inject(
        &mut self,
        payload_id: i32,
        addr: &Address,
        bl: BlockId,
        pos: Option<OpId>,
        glb: &mut Architecture,
    ) -> Result<()> {
        let mut library = glb.pcodeinjectlib.take().expect("architecture has no inject library");
        let payload = library.take_payload(payload_id);
        let before = self.obank.deadlist.back();
        let result = {
            let context = library.get_cached_context();
            context.clear();
            context.base_mut().baseaddr = addr.clone();
            context.base_mut().nextaddr = addr.clone();
            let mut emitter = PcodeEmitFd::new(self, glb);
            payload.inject(context, &mut emitter)
        };
        library.restore_payload(payload_id, payload);
        glb.pcodeinjectlib = Some(library);
        result?;
        let mut deaditer = match before {
            Some(last) => self.obank.next_in_list(last, PcodeOp::INSERT_LIST),
            None => self.obank.begin_dead(),
        };
        while let Some(op) = deaditer {
            deaditer = self.obank.next_in_list(op, PcodeOp::INSERT_LIST);
            if self.op(op).is_call_or_branch() {
                return Err(Error::Lowlevel("Illegal branching injection".to_string()));
            }
            self.op_insert(op, bl, pos);
        }
        Ok(())
    }

    pub fn get_scope_local(&self) -> Option<ScopeId> {
        self.localmap
    }

    pub fn get_func_proto(&self) -> &FuncProto {
        &self.funcp
    }

    pub fn get_func_proto_mut(&mut self) -> &mut FuncProto {
        &mut self.funcp
    }

    pub fn clear_active_output(&mut self) {
        self.activeoutput = None;
    }

    pub fn get_active_output(&self) -> Option<&ParamActive> {
        self.activeoutput.as_deref()
    }

    pub fn get_active_output_mut(&mut self) -> Option<&mut ParamActive> {
        self.activeoutput.as_deref_mut()
    }

    pub fn clear_dead_ops(&mut self) {
        self.obank.destroy_dead();
    }

    pub fn get_merge(&mut self) -> &mut Merge {
        &mut self.covermerge
    }

    pub fn num_varnodes(&self) -> i32 {
        self.vbank.num_varnodes()
    }

    pub fn delete_varnode(&mut self, vn: VarnodeId) -> Result<()> {
        self.vbank.check_destroy(vn)?;
        self.vn_destroy(vn);
        self.vbank.destroy(vn)
    }

    pub fn find_covered_input(&self, size: i32, loc: &Address) -> Option<VarnodeId> {
        self.vbank.find_covered_input(size, loc)
    }

    pub fn find_covering_input(&self, size: i32, loc: &Address) -> Option<VarnodeId> {
        self.vbank.find_covering_input(size, loc)
    }

    pub fn has_input_intersection(&self, size: i32, loc: &Address) -> bool {
        self.vbank.has_input_intersection(size, loc)
    }

    pub fn find_varnode_input(&self, size: i32, loc: &Address) -> Option<VarnodeId> {
        self.vbank.find_input(size, loc)
    }

    pub fn find_varnode_written(&self, size: i32, loc: &Address, pc: &Address, uniq: u32) -> Option<VarnodeId> {
        self.vbank.find(size, loc, pc, uniq, &self.obank.ops)
    }

    pub fn begin_loc(&self) -> LocIter {
        self.vbank.begin_loc()
    }

    pub fn end_loc(&self) -> LocIter {
        self.vbank.end_loc()
    }

    pub fn begin_loc_space(&self, spaceid: &SpaceRef) -> LocIter {
        self.vbank.begin_loc_space(spaceid)
    }

    pub fn end_loc_space(&self, spaceid: &SpaceRef, glb: &Architecture) -> LocIter {
        self.vbank.end_loc_space(spaceid, &glb.manager)
    }

    pub fn begin_loc_addr(&self, addr: &Address) -> LocIter {
        self.vbank.begin_loc_addr(addr)
    }

    pub fn end_loc_addr(&self, addr: &Address, glb: &Architecture) -> LocIter {
        self.vbank.end_loc_addr(addr, &glb.manager)
    }

    pub fn begin_loc_size(&self, size: i32, addr: &Address) -> LocIter {
        self.vbank.begin_loc_size(size, addr)
    }

    pub fn end_loc_size(&self, size: i32, addr: &Address) -> LocIter {
        self.vbank.end_loc_size(size, addr)
    }

    pub fn begin_loc_flags(&self, size: i32, addr: &Address, fl: u32) -> LocIter {
        self.vbank.begin_loc_flags(size, addr, fl)
    }

    pub fn end_loc_flags(&self, size: i32, addr: &Address, fl: u32) -> LocIter {
        self.vbank.end_loc_flags(size, addr, fl)
    }

    pub fn begin_loc_pc(&self, size: i32, addr: &Address, pc: &Address, uniq: u32) -> LocIter {
        self.vbank.begin_loc_pc(size, addr, pc, uniq)
    }

    pub fn end_loc_pc(&self, size: i32, addr: &Address, pc: &Address, uniq: u32) -> LocIter {
        self.vbank.end_loc_pc(size, addr, pc, uniq)
    }

    pub fn overlap_loc(&self, iter: &LocIter, bounds: &mut Vec<LocIter>) -> u32 {
        self.vbank.overlap_loc(iter, bounds)
    }

    pub fn begin_def(&self) -> DefIter {
        self.vbank.begin_def()
    }

    pub fn end_def(&self) -> DefIter {
        self.vbank.end_def()
    }

    pub fn begin_def_flags(&self, fl: u32) -> Result<DefIter> {
        self.vbank.begin_def_flags(fl)
    }

    pub fn end_def_flags(&self, fl: u32) -> Result<DefIter> {
        self.vbank.end_def_flags(fl)
    }

    pub fn begin_def_addr(&self, fl: u32, addr: &Address) -> Result<DefIter> {
        self.vbank.begin_def_addr(fl, addr)
    }

    pub fn end_def_addr(&self, fl: u32, addr: &Address) -> Result<DefIter> {
        self.vbank.end_def_addr(fl, addr)
    }

    pub fn get_lane_access(&self) -> &BTreeMap<VarnodeData, usize> {
        &self.laned_map
    }

    pub fn clear_laned_access_map(&mut self) {
        self.laned_map.clear();
    }

    pub fn mark_return_copy(&mut self, op: OpId) {
        self.op_mut(op).flags |= PcodeOp::RETURN_COPY;
    }

    pub fn find_op(&self, sq: &crate::address::SeqNum) -> Option<OpId> {
        self.obank.find_op(sq)
    }

    pub fn op_dead_insert_after(&mut self, op: OpId, prev: OpId) -> Result<()> {
        self.obank.insert_after_dead(op, prev)
    }

    pub fn op_heritage(&mut self, glb: &mut Architecture) -> Result<()> {
        Heritage::heritage(self, glb)
    }

    pub fn op_dead_and_gone(&mut self, op: OpId) -> Result<()> {
        self.obank.destroy(op)
    }

    pub fn op_mark_start_basic(&mut self, op: OpId) {
        self.op_mut(op).set_flag(PcodeOp::STARTBASIC);
    }

    pub fn op_mark_start_instruction(&mut self, op: OpId) {
        self.op_mut(op).set_flag(PcodeOp::STARTMARK);
    }

    pub fn op_mark_non_printing(&mut self, op: OpId) {
        self.op_mut(op).set_flag(PcodeOp::NONPRINTING);
    }

    pub fn op_mark_special_print(&mut self, op: OpId) {
        self.op_mut(op).set_additional_flag(PcodeOp::SPECIAL_PRINT);
    }

    pub fn op_mark_no_collapse(&mut self, op: OpId) {
        self.op_mut(op).set_flag(PcodeOp::NOCOLLAPSE);
    }

    pub fn op_mark_cpool_transformed(&mut self, op: OpId) {
        self.op_mut(op).set_additional_flag(PcodeOp::IS_CPOOL_TRANSFORMED);
    }

    pub fn op_mark_calculated_bool(&mut self, op: OpId) {
        self.op_mut(op).set_flag(PcodeOp::CALCULATED_BOOL);
    }

    pub fn op_mark_spacebase_ptr(&mut self, op: OpId) {
        self.op_mut(op).set_flag(PcodeOp::SPACEBASE_PTR);
    }

    pub fn op_clear_spacebase_ptr(&mut self, op: OpId) {
        self.op_mut(op).clear_flag(PcodeOp::SPACEBASE_PTR);
    }

    pub fn op_flip_condition(&mut self, op: OpId) {
        self.op_mut(op).flip_flag(PcodeOp::BOOLEAN_FLIP);
    }

    pub fn target(&self, addr: &Address) -> Option<OpId> {
        self.obank.target(addr)
    }

    pub fn begin_op(&self, opc: OpCode) -> Option<OpId> {
        self.obank.begin(opc)
    }

    pub fn end_op(&self, opc: OpCode) -> Option<OpId> {
        self.obank.end(opc)
    }

    pub fn begin_op_alive(&self) -> Option<OpId> {
        self.obank.begin_alive()
    }

    pub fn end_op_alive(&self) -> Option<OpId> {
        self.obank.end_alive()
    }

    pub fn begin_op_dead(&self) -> Option<OpId> {
        self.obank.begin_dead()
    }

    pub fn end_op_dead(&self) -> Option<OpId> {
        self.obank.end_dead()
    }

    pub fn begin_op_main(&self) -> OpTreeIter {
        self.obank.begin_main()
    }

    pub fn end_op_main(&self) -> OpTreeIter {
        self.obank.end_main()
    }

    pub fn begin_op_main_addr(&self, addr: &Address) -> OpTreeIter {
        self.obank.begin_main_addr(addr)
    }

    pub fn end_op_main_addr(&self, addr: &Address) -> OpTreeIter {
        self.obank.end_main_addr(addr)
    }

    pub fn get_union_field(
        &self,
        unres_type: TypeId,
        op: OpId,
        slot: i32,
        glb: &Architecture,
    ) -> Option<&ResolvedUnion> {
        let types = type_factory(glb);
        let edge = ResolveEdge::new(unres_type, op, slot, self, types);
        let res = self.union_map.get(&edge)?;
        let dt = res.get_datatype();
        if types.get(unres_type).get_size() == types.get(dt).get_size() {
            return Some(res);
        }
        None
    }

    pub fn get_address_based_union_field(
        &self,
        unres_type: TypeId,
        addr: &Address,
        slot: i32,
        glb: &Architecture,
    ) -> Option<&ResolvedUnion> {
        let edge = ResolveEdge::new_address(unres_type, addr, slot, type_factory(glb));
        self.union_map.get(&edge)
    }

    pub fn get_union_resolution(
        &self,
        unres_type: TypeId,
        op: OpId,
        slot: i32,
        glb: &Architecture,
    ) -> Option<&ResolvedUnion> {
        let edge = ResolveEdge::new(unres_type, op, slot, self, type_factory(glb));
        self.union_map.get(&edge)
    }

    pub fn set_union_field(
        &mut self,
        unres_type: TypeId,
        op: OpId,
        slot: i32,
        resolve: &ResolvedUnion,
        glb: &Architecture,
    ) -> bool {
        let types = type_factory(glb);
        let edge = ResolveEdge::new(unres_type, op, slot, self, types);
        match self.union_map.entry(edge) {
            Entry::Vacant(vacant) => {
                vacant.insert(resolve.clone());
            }
            Entry::Occupied(mut occupied) => {
                if !occupied.get_mut().update(resolve) {
                    return !occupied.get().is_locked();
                }
            }
        }
        if self.op(op).code() == OpCode::Multiequal && slot >= 0 {
            let vn = self.op(op).get_in(slot);
            for index in 0..self.op(op).num_input() {
                if index == slot {
                    continue;
                }
                if self.op(op).get_in(index) != vn {
                    continue;
                }
                let dupedge = ResolveEdge::new(unres_type, op, index, self, types);
                match self.union_map.entry(dupedge) {
                    Entry::Vacant(vacant) => {
                        vacant.insert(resolve.clone());
                    }
                    Entry::Occupied(mut occupied) => {
                        occupied.get_mut().update(resolve);
                    }
                }
            }
        }
        true
    }

    pub fn set_address_based_union_field(
        &mut self,
        unres_type: TypeId,
        addr: &Address,
        slot: i32,
        resolve: &ResolvedUnion,
        glb: &Architecture,
    ) -> bool {
        let edge = ResolveEdge::new_address(unres_type, addr, slot, type_factory(glb));
        match self.union_map.entry(edge) {
            Entry::Vacant(vacant) => {
                vacant.insert(resolve.clone());
            }
            Entry::Occupied(mut occupied) => {
                if occupied.get().is_locked() {
                    return false;
                }
                *occupied.get_mut() = resolve.clone();
            }
        }
        true
    }

    pub fn update_union_field(
        &mut self,
        unres_type: TypeId,
        op: OpId,
        slot: i32,
        res_type: TypeId,
        glb: &Architecture,
    ) -> bool {
        let edge = ResolveEdge::new(unres_type, op, slot, self, type_factory(glb));
        match self.union_map.get_mut(&edge) {
            Some(res) => {
                res.set_resolve(res_type);
                true
            }
            None => false,
        }
    }

    pub fn force_facing_type(
        &mut self,
        unres_type: TypeId,
        field_num: i32,
        op: OpId,
        slot: i32,
        glb: &mut Architecture,
    ) {
        let mut unres_type = unres_type;
        let types = type_factory_mut(glb);
        let mut base_type = unres_type;
        if types.get(base_type).get_metatype() == TypeMetatype::Ptr {
            base_type = types.get(base_type).get_ptr_to();
        }
        if types.get(unres_type).is_pointer_rel() {
            let size = types.get(unres_type).get_size();
            let word_size = types.get(unres_type).get_word_size();
            unres_type = types
                .get_type_pointer(size, base_type, word_size)
                .expect("pointer data-type creation failed");
        }
        let resolve = ResolvedUnion::new_field(unres_type, field_num, types).expect("union resolution creation failed");
        self.set_union_field(unres_type, op, slot, &resolve, glb);
    }

    pub fn inherit_union_field(
        &mut self,
        unres_type: TypeId,
        op: OpId,
        slot: i32,
        old_op: OpId,
        old_slot: i32,
        glb: &Architecture,
    ) -> i32 {
        let mut slot = slot;
        if slot < 0 && self.op(old_op).is_marker() {
            slot = 0;
        }
        let edge = ResolveEdge::new(unres_type, old_op, old_slot, self, type_factory(glb));
        let Some(resolve) = self.union_map.get(&edge).cloned() else {
            return -1;
        };
        self.set_union_field(unres_type, op, slot, &resolve, glb);
        resolve.get_field_num()
    }

    pub fn inherit_union_field_ptr(
        &mut self,
        unres_ptr: TypeId,
        op: OpId,
        slot: i32,
        old_op: OpId,
        old_slot: i32,
        glb: &mut Architecture,
    ) -> i32 {
        let types = type_factory(glb);
        let parent = types
            .get(unres_ptr)
            .get_depend(0, types)
            .expect("pointer data-type has no component");
        let mut slot = slot;
        if slot < 0 && self.op(old_op).is_marker() {
            slot = 0;
        }
        let edge = ResolveEdge::new(parent, old_op, old_slot, self, types);
        let Some(field_num) = self.union_map.get(&edge).map(|res| res.get_field_num()) else {
            return -1;
        };
        let ptrres = ResolvedUnion::new_field(unres_ptr, field_num, type_factory_mut(glb))
            .expect("union resolution creation failed");
        self.set_union_field(unres_ptr, op, slot, &ptrres, glb);
        field_num
    }

    pub fn num_jump_tables(&self) -> i32 {
        self.jumpvec.len() as i32
    }

    pub fn get_jump_table(&self, index: i32) -> JumpTableId {
        self.jumpvec[index as usize]
    }

    pub fn get_structure(&self) -> BlockId {
        self.sblocks
    }

    pub fn get_basic_blocks(&self) -> BlockId {
        self.bblocks
    }

    pub fn set_basic_block_range(&mut self, bb: BlockId, beg: &Address, end: &Address) {
        self.blocks[bb].set_initial_range(beg, end)
    }

    pub fn enable_jt_callback(&mut self, jtcb: JumpTableCallback) {
        self.jtcallback = Some(jtcb);
    }

    pub fn disable_jt_callback(&mut self) {
        self.jtcallback = None;
    }

    pub fn debug_activate(&mut self) {
        if self.opactdbg_on {
            self.opactdbg_active = true;
        }
    }

    pub fn debug_deactivate(&mut self) {
        self.opactdbg_active = false;
    }

    pub fn debug_mod_check(&mut self, op: OpId, glb: &mut Architecture) {
        if self.op(op).is_modified() {
            return;
        }
        if !self.debug_check_range(op) {
            return;
        }
        self.op_mut(op).set_additional_flag(PcodeOp::MODIFIED);
        let mut before = String::new();
        self.op_print_debug(op, &mut before, glb);
        self.modify_list.push(op);
        self.modify_before.push(before);
    }

    pub fn debug_mod_clear(&mut self) {
        for op in self.modify_list.drain(..) {
            self.obank.ops.get_mut(op).clear_additional_flag(PcodeOp::MODIFIED);
        }
        self.modify_before.clear();
        self.opactdbg_active = false;
    }

    pub fn debug_mod_print(&mut self, actionname: &str, glb: &mut Architecture) {
        if !self.opactdbg_active {
            return;
        }
        self.opactdbg_active = false;
        if self.modify_list.is_empty() {
            return;
        }
        let mut out = String::new();
        self.opactdbg_breakon |= self.opactdbg_count == self.opactdbg_breakcount;
        let _ = writeln!(out, "DEBUG {}: {}", self.opactdbg_count, actionname);
        self.opactdbg_count += 1;
        let modify_list = std::mem::take(&mut self.modify_list);
        let modify_before = std::mem::take(&mut self.modify_before);
        for (op, before) in modify_list.iter().zip(modify_before.iter()) {
            out.push_str(before);
            out.push('\n');
            out.push_str("   ");
            self.op_print_debug(*op, &mut out, glb);
            out.push('\n');
            self.op_mut(*op).clear_additional_flag(PcodeOp::MODIFIED);
        }
        glb.print_debug(&out);
    }

    pub fn debug_break(&self) -> bool {
        self.opactdbg_on && self.opactdbg_breakon
    }

    pub fn debug_size(&self) -> i32 {
        self.opactdbg_pclow.len() as i32
    }

    pub fn debug_enable(&mut self) {
        self.opactdbg_on = true;
        self.opactdbg_count = 0;
    }

    pub fn debug_disable(&mut self) {
        self.opactdbg_on = false;
    }

    pub fn debug_clear(&mut self) {
        self.opactdbg_pclow.clear();
        self.opactdbg_pchigh.clear();
        self.opactdbg_uqlow.clear();
        self.opactdbg_uqhigh.clear();
    }

    pub fn debug_check_range(&mut self, op: OpId) -> bool {
        let pcode_op = self.op(op);
        for index in 0..self.opactdbg_pclow.len() {
            if !self.opactdbg_pclow[index].is_invalid() {
                if *pcode_op.get_addr() < self.opactdbg_pclow[index] {
                    continue;
                }
                if self.opactdbg_pchigh[index] < *pcode_op.get_addr() {
                    continue;
                }
            }
            if self.opactdbg_uqlow[index] != u32::MAX {
                if self.opactdbg_uqlow[index] > pcode_op.get_time() {
                    continue;
                }
                if self.opactdbg_uqhigh[index] < pcode_op.get_time() {
                    continue;
                }
            }
            return true;
        }
        false
    }

    pub fn debug_set_range(&mut self, pclow: &Address, pchigh: &Address, uqlow: u32, uqhigh: u32) {
        self.opactdbg_on = true;
        self.opactdbg_pclow.push(pclow.clone());
        self.opactdbg_pchigh.push(pchigh.clone());
        self.opactdbg_uqlow.push(uqlow);
        self.opactdbg_uqhigh.push(uqhigh);
    }

    pub fn debug_handle_break(&mut self) {
        self.opactdbg_breakon = false;
    }

    pub fn debug_set_break(&mut self, count: i32) {
        self.opactdbg_breakcount = count;
    }

    pub fn debug_print_range(&self, index: i32, glb: &mut Architecture) {
        let index = index as usize;
        let mut out = String::new();
        if !self.opactdbg_pclow[index].is_invalid() {
            out.push_str("PC = (");
            self.opactdbg_pclow[index].print_raw(&mut out);
            out.push(',');
            self.opactdbg_pchigh[index].print_raw(&mut out);
            out.push_str(")  ");
        } else {
            out.push_str("entire function ");
        }
        if self.opactdbg_uqlow[index] != u32::MAX {
            let _ = write!(
                out,
                "unique = ({:x},{:x})",
                self.opactdbg_uqlow[index], self.opactdbg_uqhigh[index]
            );
        }
        glb.print_debug(&out);
    }
}

pub struct PcodeEmitFd<'fd> {
    pub(crate) fd: &'fd mut Funcdata,
    pub(crate) glb: &'fd mut Architecture,
}

impl<'fd> PcodeEmitFd<'fd> {
    pub fn new(fd: &'fd mut Funcdata, glb: &'fd mut Architecture) -> PcodeEmitFd<'fd> {
        PcodeEmitFd { fd, glb }
    }

    pub fn set_funcdata(&mut self, fd: &'fd mut Funcdata) {
        self.fd = fd;
    }

    fn dump_op(
        &mut self,
        addr: &Address,
        opc: OpCode,
        outvar: Option<&VarnodeData>,
        vars: &[VarnodeData],
    ) -> Result<()> {
        let writes_constant = outvar
            .and_then(|output| output.space.as_ref())
            .is_some_and(|space| space.get_type() == SpaceType::Constant);
        if writes_constant {
            return Ok(());
        }
        let isize = vars.len() as i32;
        let op = self.fd.new_op(isize, addr);
        if let Some(outvar) = outvar {
            let oaddr = Address::from_parts(outvar.space.clone(), outvar.offset);
            self.fd.new_varnode_out(outvar.size as i32, &oaddr, op, self.glb)?;
        }
        self.fd.op_set_opcode(op, opc, self.glb);
        let mut slot = 0;
        if self.fd.op(op).is_code_ref() {
            let addrcode = Address::from_parts(vars[0].space.clone(), vars[0].offset);
            let coderef = self.fd.new_code_ref(&addrcode, self.glb);
            self.fd.op_set_input(op, coderef, 0)?;
            slot += 1;
        }
        while slot < isize {
            let var = &vars[slot as usize];
            let vn = self.fd.new_varnode(
                var.size as i32,
                &Address::from_parts(var.space.clone(), var.offset),
                None,
                self.glb,
            )?;
            self.fd.op_set_input(op, vn, slot)?;
            slot += 1;
        }
        Ok(())
    }
}

impl PcodeEmit for PcodeEmitFd<'_> {
    fn dump(&mut self, addr: &Address, opc: OpCode, outvar: Option<&VarnodeData>, vars: &[VarnodeData]) -> Result<()> {
        self.dump_op(addr, opc, outvar, vars)
    }
}
