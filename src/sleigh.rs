use std::collections::BTreeMap;
use std::sync::atomic::{AtomicBool, Ordering as AtomicOrdering};
use std::sync::{Arc, Mutex, MutexGuard, RwLock};

use crate::address::{Address, calc_mask, coveringmask};
use crate::context::{
    INITIAL_STATE_NUM, LengthOracle, MAX_INSTRUCTION_LEN, ParseState, ParserContext, ParserWalker, ParserWalkerChange,
};
use crate::error::{Error, Result};
use crate::globalcontext::{ContextCache, ContextDatabase};
use crate::loadimage::SharedLoadImage;
use crate::opcodes::OpCode;
use crate::pcoderaw::VarnodeData;
use crate::semantics::{ConstructTpl, LabelCounter, OpTpl, PcodeBuilder, VField, VarnodeTpl};
use crate::sleighbase::SleighBase;
use crate::slghsymbol::{Constructor, SymbolTable, SymbolType};
use crate::space::{AddrSpace, SpaceRef};
use crate::translate::{AssemblyEmit, PcodeEmit, Translate, TranslateBase, UniqueLayout};
use crate::xml::DocumentStorage;

pub type SharedContextDatabase = Arc<Mutex<dyn ContextDatabase + Send>>;

#[derive(Clone, Copy, Debug, Default)]
struct PcodeData {
    opc: Option<OpCode>,
    outvar: Option<usize>,
    invar: Option<usize>,
    isize: i32,
}

#[derive(Clone, Debug, Default)]
pub struct PcodeCacher {
    pool: Vec<VarnodeData>,
    issued: Vec<PcodeData>,
    label_refs: Vec<(usize, u64)>,
    labels: Vec<u64>,
}

impl PcodeCacher {
    pub fn new() -> PcodeCacher {
        PcodeCacher {
            pool: Vec::with_capacity(600),
            issued: Vec::new(),
            label_refs: Vec::new(),
            labels: Vec::new(),
        }
    }

    fn allocate_varnodes(&mut self, size: usize) -> usize {
        let start = self.pool.len();
        self.pool.resize(start + size, VarnodeData::default());
        start
    }

    fn allocate_instruction(&mut self) -> usize {
        self.issued.push(PcodeData::default());
        self.issued.len() - 1
    }

    fn add_label_ref(&mut self, ptr: usize) {
        self.label_refs.push((ptr, self.issued.len() as u64));
    }

    fn add_label(&mut self, id: u32) {
        while self.labels.len() <= id as usize {
            self.labels.push(0xbadbeef);
        }
        self.labels[id as usize] = self.issued.len() as u64;
    }

    pub fn clear(&mut self) {
        self.pool.clear();
        self.issued.clear();
        self.label_refs.clear();
        self.labels.clear();
    }

    fn resolve_relatives(&mut self) -> Result<()> {
        for (ptr, calling_index) in self.label_refs.iter() {
            let vn = &mut self.pool[*ptr];
            let id = vn.offset as u32;
            if id as usize >= self.labels.len() || self.labels[id as usize] == 0xbadbeef {
                return Err(Error::Lowlevel("Reference to non-existant sleigh label".to_string()));
            }
            let mut res = self.labels[id as usize].wrapping_sub(*calling_index);
            res &= calc_mask(vn.size as i32);
            vn.offset = res;
        }
        Ok(())
    }

    fn emit(&self, addr: &Address, emt: &mut dyn PcodeEmit) -> Result<()> {
        for op in self.issued.iter() {
            let outvar = op.outvar.map(|index| &self.pool[index]);
            let inputs: &[VarnodeData] = match op.invar {
                Some(start) => &self.pool[start..start + op.isize.max(0) as usize],
                None => &[],
            };
            emt.dump(addr, op.opc.unwrap_or(OpCode::Blank), outvar, inputs)?;
        }
        Ok(())
    }
}

#[derive(Clone, Debug)]
pub struct DisassemblyCache {
    minimumreuse: i32,
    mask: u32,
    list: Vec<ParserContext>,
    nextfree: i32,
    hashtable: Vec<usize>,
}

impl DisassemblyCache {
    fn new(context_size: i32, constspace: &SpaceRef, cachesize: i32, windowsize: i32) -> Result<DisassemblyCache> {
        let mask = (windowsize - 1) as u32;
        let masktest = coveringmask(mask as u64);
        if masktest != mask as u64 {
            return Err(Error::Lowlevel("Bad windowsize for disassembly cache".to_string()));
        }
        let mut list = Vec::with_capacity(cachesize.max(1) as usize);
        for _ in 0..cachesize.max(1) {
            let mut pos = ParserContext::new(context_size);
            pos.initialize(constspace.clone(), INITIAL_STATE_NUM);
            list.push(pos);
        }
        Ok(DisassemblyCache {
            minimumreuse: cachesize.max(1),
            mask,
            list,
            nextfree: 0,
            hashtable: vec![0; windowsize.max(1) as usize],
        })
    }

    fn hash_index(&self, addr: &Address) -> usize {
        ((addr.get_offset() as i32 as u32) & self.mask) as usize
    }

    fn lookup(&self, addr: &Address) -> Option<usize> {
        let res = self.hashtable[self.hash_index(addr)];
        if self.list[res].get_addr() == addr {
            return Some(res);
        }
        None
    }

    fn get_parser_context(&mut self, addr: &Address) -> usize {
        let hashindex = self.hash_index(addr);
        let res = self.hashtable[hashindex];
        if self.list[res].get_addr() == addr {
            return res;
        }
        let res = self.nextfree as usize;
        self.nextfree += 1;
        if self.nextfree >= self.minimumreuse {
            self.nextfree = 0;
        }
        self.list[res].set_addr(addr);
        self.list[res].set_parser_state(ParseState::Uninitialized);
        self.hashtable[hashindex] = res;
        res
    }

    pub fn get(&self, index: usize) -> &ParserContext {
        &self.list[index]
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct InstructionShape {
    pub length: i32,
    pub delay_slot: i32,
}

#[derive(Clone, Debug)]
pub struct SleighState {
    cache: ContextCache,
    discache: Option<DisassemblyCache>,
}

struct SleighBuilder<'a> {
    labels: LabelCounter,
    walker: ParserWalker<'a>,
    const_space: SpaceRef,
    uniq_space: SpaceRef,
    uniquemask: u64,
    uniqueoffset: u64,
    bitrange_ea: u64,
    discache: &'a DisassemblyCache,
    cache: &'a mut PcodeCacher,
    symtab: &'a SymbolTable,
    oracle: Option<LengthOracle<'a>>,
    pending_miss: Option<Address>,
    walker_in_delay_slot: bool,
}

fn same_space(space: &Option<SpaceRef>, other: &SpaceRef) -> bool {
    match space {
        Some(spc) => spc.get_index() == other.get_index(),
        None => false,
    }
}

impl<'a> SleighBuilder<'a> {
    fn set_unique_offset(&mut self, addr: &Address) {
        self.uniqueoffset = (addr.get_offset() & self.uniquemask) << 8;
    }

    fn generate_location(&self, vntpl: &VarnodeTpl) -> Result<VarnodeData> {
        let space = vntpl.get_space().fix_space(&self.walker)?;
        let size = vntpl.get_size().fix(&self.walker)? as u32;
        let fixed = vntpl.get_offset().fix(&self.walker)?;
        let offset = if space.get_index() == self.const_space.get_index() {
            fixed & calc_mask(size as i32)
        } else if space.get_index() == self.uniq_space.get_index() {
            fixed | self.uniqueoffset
        } else {
            space.wrap_offset(fixed)
        };
        Ok(VarnodeData {
            space: Some(space),
            offset,
            size,
        })
    }

    fn generate_pointer(&self, vntpl: &VarnodeTpl) -> (VarnodeData, Option<SpaceRef>) {
        let hand = self.walker.get_fixed_handle(vntpl.get_offset().get_handle_index());
        let space = hand.offset_space.clone();
        let size = hand.offset_size;
        let offset = if same_space(&space, &self.const_space) {
            hand.offset_offset & calc_mask(size as i32)
        } else if same_space(&space, &self.uniq_space) {
            hand.offset_offset | self.uniqueoffset
        } else {
            match &space {
                Some(spc) => spc.wrap_offset(hand.offset_offset),
                None => hand.offset_offset,
            }
        };
        (VarnodeData { space, offset, size }, hand.space.clone())
    }

    fn generate_pointer_add(&mut self, op: usize, vntpl: &VarnodeTpl) {
        let offset_plus = vntpl.get_offset().get_real() & 0xffff;
        if offset_plus == 0 {
            return;
        }
        let nextop = self.cache.allocate_instruction();
        let original = self.cache.issued[op];
        self.cache.issued[nextop] = original;
        let newparams = self.cache.allocate_varnodes(2);
        let invar = original.invar.unwrap_or(0);
        let first = self.cache.pool[invar + 1].clone();
        let size = first.size;
        self.cache.pool[newparams] = first;
        self.cache.pool[newparams + 1] = VarnodeData {
            space: Some(self.const_space.clone()),
            offset: offset_plus,
            size,
        };
        let outvar = invar + 1;
        self.cache.pool[outvar].space = Some(self.uniq_space.clone());
        self.cache.pool[outvar].offset = self.bitrange_ea;
        let data = &mut self.cache.issued[op];
        data.isize = 2;
        data.opc = Some(OpCode::IntAdd);
        data.invar = Some(newparams);
        data.outvar = Some(outvar);
    }

    fn space_pointer_constant(&self, spc: &Option<SpaceRef>) -> VarnodeData {
        VarnodeData {
            space: Some(self.const_space.clone()),
            offset: spc.as_ref().map(|spc| spc.get_index() as u64).unwrap_or(0),
            size: 8,
        }
    }

    fn build_empty(&mut self, ct: &'a Constructor, secnum: i32) -> Result<()> {
        let numops = ct.get_num_operands();
        for index in 0..numops {
            let Some(symid) = ct.get_operand(index) else {
                continue;
            };
            let Some(triple) = self.symtab.get(symid).operand().and_then(|oper| oper.triple) else {
                continue;
            };
            if self.symtab.get(triple).get_type() != SymbolType::Subtable {
                continue;
            }
            self.walker.push_operand(index)?;
            let Some(subct) = self.walker.get_constructor() else {
                self.walker.pop_operand();
                continue;
            };
            match subct.get_named_templ(secnum) {
                None => self.build_empty(subct, secnum)?,
                Some(construct) => self.build(Some(construct), secnum)?,
            }
            self.walker.pop_operand();
        }
        Ok(())
    }

    fn cached_context(&mut self, addr: &Address, message: &str) -> Result<&'a ParserContext> {
        match self.discache.lookup(addr) {
            None => {
                self.pending_miss = Some(addr.clone());
                Err(Error::Lowlevel(message.to_string()))
            }
            Some(index) => {
                let discache: &'a DisassemblyCache = self.discache;
                let pos = discache.get(index);
                if pos.get_parser_state() != ParseState::Pcode {
                    return Err(Error::Lowlevel(message.to_string()));
                }
                Ok(pos)
            }
        }
    }

    fn new_walker(&self, pos: &'a ParserContext, cross: Option<&'a ParserContext>) -> ParserWalker<'a> {
        let mut walker = match cross {
            Some(cross) => ParserWalker::new_cross(pos, cross, self.symtab),
            None => ParserWalker::new(pos, self.symtab),
        };
        walker.set_oracle(self.oracle);
        walker
    }
}

impl<'a> PcodeBuilder for SleighBuilder<'a> {
    fn label_counter(&mut self) -> &mut LabelCounter {
        &mut self.labels
    }

    fn dump(&mut self, op: &OpTpl) -> Result<()> {
        let isize = op.num_input();
        let invars = self.cache.allocate_varnodes(isize as usize);
        for index in 0..isize {
            let vn = op.get_in(index);
            if vn.is_dynamic(&self.walker) {
                let location = self.generate_location(vn)?;
                self.cache.pool[invars + index as usize] = location;
                let load_op = self.cache.allocate_instruction();
                let loadvars = self.cache.allocate_varnodes(2);
                {
                    let data = &mut self.cache.issued[load_op];
                    data.opc = Some(OpCode::Load);
                    data.outvar = Some(invars + index as usize);
                    data.isize = 2;
                    data.invar = Some(loadvars);
                }
                let (pointer, spc) = self.generate_pointer(vn);
                self.cache.pool[loadvars + 1] = pointer;
                self.cache.pool[loadvars] = self.space_pointer_constant(&spc);
                if vn.get_offset().get_select() == VField::VOffsetPlus {
                    self.generate_pointer_add(load_op, vn);
                }
            } else {
                let location = self.generate_location(vn)?;
                self.cache.pool[invars + index as usize] = location;
            }
        }
        if isize > 0 && op.get_in(0).is_relative() {
            let base = self.labels.labelbase as u64;
            let first = &mut self.cache.pool[invars];
            first.offset = first.offset.wrapping_add(base);
            self.cache.add_label_ref(invars);
        }
        let thisop = self.cache.allocate_instruction();
        {
            let data = &mut self.cache.issued[thisop];
            data.opc = Some(op.get_opcode());
            data.invar = Some(invars);
            data.isize = isize;
        }
        if let Some(outvn) = op.get_out() {
            if outvn.is_dynamic(&self.walker) {
                let storevars = self.cache.allocate_varnodes(3);
                let location = self.generate_location(outvn)?;
                self.cache.pool[storevars + 2] = location;
                self.cache.issued[thisop].outvar = Some(storevars + 2);
                let store_op = self.cache.allocate_instruction();
                {
                    let data = &mut self.cache.issued[store_op];
                    data.opc = Some(OpCode::Store);
                    data.isize = 3;
                    data.invar = Some(storevars);
                }
                let (pointer, spc) = self.generate_pointer(outvn);
                self.cache.pool[storevars + 1] = pointer;
                self.cache.pool[storevars] = self.space_pointer_constant(&spc);
                if outvn.get_offset().get_select() == VField::VOffsetPlus {
                    self.generate_pointer_add(store_op, outvn);
                }
            } else {
                let outvar = self.cache.allocate_varnodes(1);
                self.cache.issued[thisop].outvar = Some(outvar);
                let location = self.generate_location(outvn)?;
                self.cache.pool[outvar] = location;
            }
        }
        Ok(())
    }

    fn append_build(&mut self, bld: &OpTpl, secnum: i32) -> Result<()> {
        let index = bld.get_in(0).get_offset().get_real() as i32;
        let Some(ct) = self.walker.get_constructor() else {
            return Ok(());
        };
        let Some(symid) = ct.get_operand(index) else {
            return Ok(());
        };
        let Some(triple) = self.symtab.get(symid).operand().and_then(|oper| oper.triple) else {
            return Ok(());
        };
        if self.symtab.get(triple).get_type() != SymbolType::Subtable {
            return Ok(());
        }
        self.walker.push_operand(index)?;
        let ct = self.walker.get_constructor();
        if secnum >= 0 {
            match ct.and_then(|ct| ct.get_named_templ(secnum)) {
                None => {
                    if let Some(ct) = ct {
                        self.build_empty(ct, secnum)?;
                    }
                }
                Some(construct) => self.build(Some(construct), secnum)?,
            }
        } else {
            let construct: Option<&'a ConstructTpl> = ct.and_then(|ct| ct.get_templ());
            self.build(construct, -1)?;
        }
        self.walker.pop_operand();
        Ok(())
    }

    fn delay_slot(&mut self, _op: &OpTpl) -> Result<()> {
        let olduniqueoffset = self.uniqueoffset;
        let baseaddr = self.walker.get_addr().clone();
        let mut fall_offset = self.walker.get_length();
        let delay_slot_byte_cnt = self.walker.get_parser_context().get_delay_slot();
        let mut bytecount = 0;
        let mut saved: Option<(ParserWalker<'a>, bool)> = None;
        loop {
            let newaddr = &baseaddr + fall_offset as i64;
            self.set_unique_offset(&newaddr);
            let pos = self.cached_context(&newaddr, "Could not obtain cached delay slot instruction")?;
            let len = pos.get_length();
            let mut newwalker = self.new_walker(pos, None);
            newwalker.base_state();
            let previous = std::mem::replace(&mut self.walker, newwalker);
            let previous_flag = std::mem::replace(&mut self.walker_in_delay_slot, true);
            if saved.is_none() {
                saved = Some((previous, previous_flag));
            }
            let construct = self.walker.get_constructor().and_then(|ct| ct.get_templ());
            self.build(construct, -1)?;
            fall_offset += len;
            bytecount += len;
            if bytecount >= delay_slot_byte_cnt {
                break;
            }
        }
        if let Some((walker, flag)) = saved {
            self.walker = walker;
            self.walker_in_delay_slot = flag;
        }
        self.uniqueoffset = olduniqueoffset;
        Ok(())
    }

    fn set_label(&mut self, op: &OpTpl) -> Result<()> {
        let id = (op.get_in(0).get_offset().get_real() as u32).wrapping_add(self.labels.labelbase);
        self.cache.add_label(id);
        Ok(())
    }

    fn append_cross_build(&mut self, bld: &OpTpl, secnum: i32) -> Result<()> {
        if secnum >= 0 {
            return Err(Error::Lowlevel(
                "CROSSBUILD directive within a named section".to_string(),
            ));
        }
        let secnum = bld.get_in(1).get_offset().get_real() as i32;
        let vn = bld.get_in(0);
        let spc = vn.get_space().fix_space(&self.walker)?;
        let addr = spc.wrap_offset(vn.get_offset().fix(&self.walker)?);
        let olduniqueoffset = self.uniqueoffset;
        let newaddr = Address::new(spc, addr);
        self.set_unique_offset(&newaddr);
        let pos = self.cached_context(&newaddr, "Could not obtain cached crossbuild instruction")?;
        let cross = self.walker.get_parser_context();
        let mut newwalker = self.new_walker(pos, Some(cross));
        newwalker.base_state();
        let previous = std::mem::replace(&mut self.walker, newwalker);
        let ct = self.walker.get_constructor();
        match ct.and_then(|ct| ct.get_named_templ(secnum)) {
            None => {
                if let Some(ct) = ct {
                    self.build_empty(ct, secnum)?;
                }
            }
            Some(construct) => self.build(Some(construct), secnum)?,
        }
        self.walker = previous;
        self.uniqueoffset = olduniqueoffset;
        Ok(())
    }
}

pub struct Sleigh {
    base: SleighBase,
    loader: SharedLoadImage,
    context_db: SharedContextDatabase,
    cache: RwLock<ContextCache>,
    discache: RwLock<Option<DisassemblyCache>>,
    pcode_cache: RwLock<PcodeCacher>,
    n2_pending: RwLock<Vec<Address>>,
    unimpl_in_delay_slot: AtomicBool,
}

impl std::fmt::Debug for Sleigh {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        formatter.debug_struct("Sleigh").field("base", &self.base).finish()
    }
}

fn lock_database(database: &SharedContextDatabase) -> Result<MutexGuard<'_, dyn ContextDatabase + Send + 'static>> {
    database
        .lock()
        .map_err(|_| Error::Lowlevel("context database lock is poisoned".to_string()))
}

impl Sleigh {
    pub fn new(loader: SharedLoadImage, context_db: SharedContextDatabase) -> Sleigh {
        Sleigh {
            base: SleighBase::new(),
            loader,
            context_db,
            cache: RwLock::new(ContextCache::new()),
            discache: RwLock::new(None),
            pcode_cache: RwLock::new(PcodeCacher::new()),
            n2_pending: RwLock::new(Vec::new()),
            unimpl_in_delay_slot: AtomicBool::new(false),
        }
    }

    pub fn from_base(loader: SharedLoadImage, context_db: SharedContextDatabase, base: SleighBase) -> Sleigh {
        Sleigh {
            base,
            ..Sleigh::new(loader, context_db)
        }
    }

    pub fn reset(&mut self, loader: SharedLoadImage, context_db: SharedContextDatabase) {
        self.pcode_cache.write().expect("poisoned lock").clear();
        self.loader = loader;
        self.context_db = context_db;
        *self.cache.write().expect("poisoned lock") = ContextCache::new();
        *self.discache.write().expect("poisoned lock") = None;
    }

    pub fn base(&self) -> &SleighBase {
        &self.base
    }

    pub fn symbol_table(&self) -> &SymbolTable {
        &self.base.symtab
    }

    pub fn loader(&self) -> &SharedLoadImage {
        &self.loader
    }

    pub fn context_database(&self) -> &SharedContextDatabase {
        &self.context_db
    }

    pub fn is_initialized(&self) -> bool {
        self.base.is_initialized()
    }

    pub fn save_state(&self) -> SleighState {
        SleighState {
            cache: self.cache.read().expect("poisoned lock").clone(),
            discache: self.discache.read().expect("poisoned lock").clone(),
        }
    }

    pub fn restore_state(&self, state: SleighState) {
        *self.cache.write().expect("poisoned lock") = state.cache;
        *self.discache.write().expect("poisoned lock") = state.discache;
    }

    pub fn last_unimplemented_in_delay_slot(&self) -> bool {
        self.unimpl_in_delay_slot.load(AtomicOrdering::Relaxed)
    }

    pub fn initialize_from_sla(&mut self, sla: &[u8]) -> Result<()> {
        if !self.is_initialized() {
            let database = self.context_db.clone();
            let mut register = |name: &str, sbit: i32, ebit: i32| -> Result<()> {
                lock_database(&database)?.register_variable(name, sbit, ebit)
            };
            self.base.decode(sla, &mut register)?;
        } else {
            let database = self.context_db.clone();
            let mut register = |name: &str, sbit: i32, ebit: i32| -> Result<()> {
                lock_database(&database)?.register_variable(name, sbit, ebit)
            };
            self.base.reregister_context(&mut register)?;
        }
        self.create_disassembly_cache()
    }

    fn create_disassembly_cache(&mut self) -> Result<()> {
        let mut parser_cachesize = 2;
        let mut parser_windowsize = 32;
        if self.base.get_max_delay_slot_bytes() > 1 || self.base.get_unique_allocate_mask() != 0 {
            parser_cachesize = 8;
            parser_windowsize = 256;
        }
        let context_size = lock_database(&self.context_db)?.get_context_size();
        let constspace = self
            .base
            .get_constant_space()
            .ok_or_else(|| Error::Lowlevel("missing constant space".to_string()))?;
        let discache = DisassemblyCache::new(context_size, &constspace, parser_cachesize, parser_windowsize)?;
        *self.discache.write().expect("poisoned lock") = Some(discache);
        Ok(())
    }

    fn resolve(
        &self,
        pos: &mut ParserContext,
        contcache: &mut ContextCache,
        database: &dyn ContextDatabase,
    ) -> Result<()> {
        let symtab = &self.base.symtab;
        let addr = pos.get_addr().clone();
        self.loader
            .load_fill(&mut pos.get_buffer()[..MAX_INSTRUCTION_LEN as usize], &addr)?;
        pos.set_delay_slot(0);
        pos.clear_commits();
        pos.load_context(contcache, database);
        let mut walker = ParserWalkerChange::new(pos, symtab);
        walker.deallocate_state();
        walker.set_offset(0);
        let root = self
            .base
            .get_root()
            .ok_or_else(|| Error::Lowlevel("sleigh specification has no root".to_string()))?;
        let ct = symtab.get(root).resolve(&walker.view())?;
        walker.set_constructor(ct);
        if let Some(ct) = ct {
            symtab.get_constructor(ct).apply_context(&mut walker)?;
        }
        while walker.is_state() {
            let ct = walker
                .get_constructor_ref()
                .map(|ct| symtab.get_constructor(ct))
                .unwrap_or(Constructor::empty_static());
            let mut oper = walker.get_operand();
            let numoper = ct.get_num_operands();
            while oper < numoper {
                let symid = ct.get_operand(oper).unwrap_or(0);
                let sym = symtab.get(symid).operand();
                let (offset_base, relative_offset, minimum_length, triple) = match sym {
                    Some(sym) => (
                        sym.get_offset_base(),
                        sym.get_relative_offset(),
                        sym.get_minimum_length(),
                        sym.get_defining_symbol(),
                    ),
                    None => (-1, 0, 0, None),
                };
                let off = walker.get_offset(offset_base).wrapping_add(relative_offset);
                walker.allocate_operand(oper)?;
                walker.set_offset(off);
                if let Some(tsym) = triple {
                    let subct = symtab.get(tsym).resolve(&walker.view())?;
                    if let Some(subct) = subct {
                        walker.set_constructor(Some(subct));
                        symtab.get_constructor(subct).apply_context(&mut walker)?;
                        break;
                    }
                }
                walker.set_current_length(minimum_length);
                walker.pop_operand();
                oper += 1;
            }
            if oper >= numoper {
                walker.calc_current_length(ct.get_minimum_length(), numoper);
                walker.pop_operand();
                if let Some(templ) = ct.get_templ()
                    && templ.delay_slot() > 0
                {
                    walker.get_parser_context().set_delay_slot(templ.delay_slot() as i32);
                }
            }
        }
        let naddr = &addr + pos.get_length() as i64;
        pos.set_naddr(&naddr);
        pos.set_parser_state(ParseState::Disassembly);
        Ok(())
    }

    fn resolve_handles(&self, pos: &mut ParserContext) -> Result<()> {
        let symtab = &self.base.symtab;
        let const_space = pos.get_const_space().cloned();
        let mut walker = ParserWalkerChange::new(pos, symtab);
        walker.base_state();
        while walker.is_state() {
            let ct = walker
                .get_constructor_ref()
                .map(|ct| symtab.get_constructor(ct))
                .unwrap_or(Constructor::empty_static());
            let mut oper = walker.get_operand();
            let numoper = ct.get_num_operands();
            while oper < numoper {
                let symid = ct.get_operand(oper).unwrap_or(0);
                let sym = symtab.get(symid).operand();
                walker.push_operand(oper)?;
                let triple = sym.and_then(|sym| sym.get_defining_symbol());
                if let Some(triple) = triple {
                    let tsym = symtab.get(triple);
                    if tsym.get_type() == SymbolType::Subtable {
                        break;
                    }
                    let view = walker.view();
                    let mut hand = view.get_parent_handle().clone();
                    tsym.get_fixed_handle(&mut hand, &view)?;
                    drop(view);
                    *walker.get_parent_handle_mut() = hand;
                } else {
                    let res = match sym.and_then(|sym| sym.get_defining_expression()) {
                        Some(patexp) => patexp.get_value(&walker.view())?,
                        None => 0,
                    };
                    let hand = walker.get_parent_handle_mut();
                    hand.space = const_space.clone();
                    hand.offset_space = None;
                    hand.offset_offset = res as u64;
                    hand.size = 0;
                }
                walker.pop_operand();
                oper += 1;
            }
            if oper >= numoper {
                if let Some(templ) = ct.get_templ()
                    && let Some(res) = templ.get_result()
                {
                    let view = walker.view();
                    let mut hand = view.get_parent_handle().clone();
                    res.fix(&mut hand, &view)?;
                    drop(view);
                    *walker.get_parent_handle_mut() = hand;
                }
                walker.pop_operand();
            }
        }
        pos.set_parser_state(ParseState::Pcode);
        Ok(())
    }

    fn obtain_context(
        &self,
        discache: &mut DisassemblyCache,
        contcache: &mut ContextCache,
        database: &dyn ContextDatabase,
        addr: &Address,
        state: ParseState,
    ) -> Result<usize> {
        let index = discache.get_parser_context(addr);
        let pos = &mut discache.list[index];
        let curstate = pos.get_parser_state();
        if curstate >= state {
            return Ok(index);
        }
        if curstate == ParseState::Uninitialized {
            self.resolve(pos, contcache, database)?;
            if state == ParseState::Disassembly {
                return Ok(index);
            }
        }
        self.resolve_handles(pos)?;
        Ok(index)
    }

    fn with_caches<T>(
        &self,
        work: impl FnOnce(&mut DisassemblyCache, &mut ContextCache, &mut (dyn ContextDatabase + Send)) -> Result<T>,
    ) -> Result<T> {
        let mut discache_guard = self.discache.write().expect("poisoned lock");
        let Some(discache) = discache_guard.as_mut() else {
            return Err(Error::Lowlevel("sleigh translator is not initialized".to_string()));
        };
        let mut cache = self.cache.write().expect("poisoned lock");
        let mut database = lock_database(&self.context_db)?;
        work(discache, &mut cache, &mut *database)
    }

    pub fn obtain_pcode_context(&self, addr: &Address) -> Result<InstructionShape> {
        self.with_caches(|discache, cache, database| {
            let index = self.obtain_context(discache, cache, &*database, addr, ParseState::Pcode)?;
            let pos = &discache.list[index];
            Ok(InstructionShape {
                length: pos.get_length(),
                delay_slot: pos.get_delay_slot(),
            })
        })
    }

    fn detached_length(&self, addr: &Address) -> Result<i32> {
        let context_size = lock_database(&self.context_db)?.get_context_size();
        let constspace = self
            .base
            .get_constant_space()
            .ok_or_else(|| Error::Lowlevel("missing constant space".to_string()))?;
        let mut pos = ParserContext::new(context_size);
        pos.initialize(constspace, INITIAL_STATE_NUM);
        pos.set_addr(addr);
        {
            let mut cache = self.cache.write().expect("poisoned lock");
            let database = lock_database(&self.context_db)?;
            self.resolve(&mut pos, &mut cache, &*database)?;
        }
        self.n2_pending.write().expect("poisoned lock").push(addr.clone());
        Ok(pos.get_length())
    }

    fn flush_pending(&self) -> Result<()> {
        let pending: Vec<Address> = std::mem::take(&mut *self.n2_pending.write().expect("poisoned lock"));
        for addr in pending {
            self.with_caches(|discache, cache, database| {
                self.obtain_context(discache, cache, &*database, &addr, ParseState::Disassembly)?;
                Ok(())
            })?;
        }
        Ok(())
    }

    fn print_assembly_internal(&self, emit: &mut dyn AssemblyEmit, baseaddr: &Address) -> Result<i32> {
        let index = self.with_caches(|discache, cache, database| {
            self.obtain_context(discache, cache, &*database, baseaddr, ParseState::Disassembly)
        })?;
        let discache_guard = self.discache.read().expect("poisoned lock");
        let Some(discache) = discache_guard.as_ref() else {
            return Err(Error::Lowlevel("sleigh translator is not initialized".to_string()));
        };
        let pos = discache.get(index);
        let oracle = |addr: &Address| self.detached_length(addr);
        let mut walker = ParserWalker::new(pos, &self.base.symtab);
        walker.set_oracle(Some(&oracle));
        walker.base_state();
        let mut mons = String::new();
        let mut body = String::new();
        if let Some(ct) = walker.get_constructor() {
            ct.print_mnemonic(&mut mons, &mut walker)?;
            ct.print_body(&mut body, &mut walker)?;
        }
        emit.dump(baseaddr, &mons, &body);
        Ok(pos.get_length())
    }

    fn one_instruction_internal(&self, emit: &mut dyn PcodeEmit, baseaddr: &Address) -> Result<i32> {
        self.unimpl_in_delay_slot.store(false, AtomicOrdering::Relaxed);
        let alignment = self.base.translate.alignment;
        if alignment != 1 && !baseaddr.get_offset().is_multiple_of(alignment as u64) {
            let mut message = String::from("Instruction address not aligned: ");
            baseaddr.print_raw(&mut message);
            return Err(Error::Unimpl {
                message,
                instruction_length: 0,
            });
        }
        let (index, fall_offset) = self.with_caches(|discache, cache, database| {
            let index = self.obtain_context(discache, cache, &*database, baseaddr, ParseState::Pcode)?;
            discache.list[index].apply_commits(&self.base.symtab, cache, database)?;
            let mut fall_offset = discache.list[index].get_length();
            let delay = discache.list[index].get_delay_slot();
            if delay > 0 {
                let mut bytecount = 0;
                loop {
                    let delayaddr = discache.list[index].get_addr() + fall_offset as i64;
                    let delaypos = self.obtain_context(discache, cache, &*database, &delayaddr, ParseState::Pcode)?;
                    discache.list[delaypos].apply_commits(&self.base.symtab, cache, database)?;
                    let len = discache.list[delaypos].get_length();
                    fall_offset += len;
                    bytecount += len;
                    if bytecount >= delay {
                        break;
                    }
                }
                let naddr = discache.list[index].get_addr() + fall_offset as i64;
                discache.list[index].set_naddr(&naddr);
            }
            Ok((index, fall_offset))
        })?;
        let pending_miss;
        let res = {
            let discache_guard = self.discache.read().expect("poisoned lock");
            let Some(discache) = discache_guard.as_ref() else {
                return Err(Error::Lowlevel("sleigh translator is not initialized".to_string()));
            };
            let mut pcode_cache = self.pcode_cache.write().expect("poisoned lock");
            pcode_cache.clear();
            let const_space = self
                .base
                .get_constant_space()
                .ok_or_else(|| Error::Lowlevel("missing constant space".to_string()))?;
            let uniq_space = self
                .base
                .get_unique_space()
                .ok_or_else(|| Error::Lowlevel("missing unique space".to_string()))?;
            let oracle = |addr: &Address| self.detached_length(addr);
            let pos = discache.get(index);
            let mut walker = ParserWalker::new(pos, &self.base.symtab);
            walker.set_oracle(Some(&oracle));
            walker.base_state();
            let uniquemask = self.base.get_unique_allocate_mask() as u64;
            let uniqueoffset = (walker.get_addr().get_offset() & uniquemask) << 8;
            let mut builder = SleighBuilder {
                labels: LabelCounter::new(0),
                walker,
                const_space,
                uniq_space,
                uniquemask,
                uniqueoffset,
                bitrange_ea: self.base.translate.get_unique_start(UniqueLayout::RuntimeBitrangeEa) as u64,
                discache,
                cache: &mut pcode_cache,
                symtab: &self.base.symtab,
                oracle: Some(&oracle),
                pending_miss: None,
                walker_in_delay_slot: false,
            };
            let construct = builder.walker.get_constructor().and_then(|ct| ct.get_templ());
            let mut res = builder.build(construct, -1);
            if let Err(Error::Unimpl { .. }) = &res {
                self.unimpl_in_delay_slot
                    .store(builder.walker_in_delay_slot, AtomicOrdering::Relaxed);
                res = unimplemented_message(&mut builder.walker, fall_offset);
            }
            pending_miss = builder.pending_miss.take();
            drop(builder);
            match res {
                Ok(()) => match pcode_cache.resolve_relatives() {
                    Ok(()) => pcode_cache.emit(baseaddr, emit).map(|()| fall_offset),
                    Err(err) => Err(err),
                },
                Err(err) => Err(err),
            }
        };
        if let Some(addr) = pending_miss {
            let mut discache_guard = self.discache.write().expect("poisoned lock");
            if let Some(discache) = discache_guard.as_mut() {
                discache.get_parser_context(&addr);
            }
        }
        self.flush_pending()?;
        res
    }
}

fn unimplemented_message(cur: &mut ParserWalker<'_>, fall_offset: i32) -> Result<()> {
    let mut message = String::from("Instruction not implemented in pcode:\n ");
    cur.base_state();
    cur.get_addr().print_raw(&mut message);
    message.push_str(": ");
    if let Some(ct) = cur.get_constructor() {
        ct.print_mnemonic(&mut message, cur)?;
        message.push_str("  ");
        ct.print_body(&mut message, cur)?;
    } else {
        message.push_str("  ");
    }
    Err(Error::Unimpl {
        message,
        instruction_length: fall_offset,
    })
}

impl Translate for Sleigh {
    fn translate_base(&self) -> &TranslateBase {
        &self.base.translate
    }

    fn translate_base_mut(&mut self) -> &mut TranslateBase {
        &mut self.base.translate
    }

    fn as_sleigh(&self) -> Option<&Sleigh> {
        Some(self)
    }

    fn initialize(&mut self, store: &mut DocumentStorage) -> Result<()> {
        if !self.is_initialized() {
            let Some(el) = store.get_tag("sleigh") else {
                return Err(Error::Lowlevel("Could not find sleigh tag".to_string()));
            };
            let path = el.get_content().to_string();
            let data =
                std::fs::read(&path).map_err(|_| Error::Lowlevel(format!("Could not open .sla file: {path}")))?;
            self.initialize_from_sla(&data)
        } else {
            self.initialize_from_sla(&[])
        }
    }

    fn register_context(&mut self, name: &str, sbit: i32, ebit: i32) -> Result<()> {
        lock_database(&self.context_db)?.register_variable(name, sbit, ebit)
    }

    fn set_context_default(&mut self, name: &str, val: u32) -> Result<()> {
        lock_database(&self.context_db)?.set_variable_default(name, val)
    }

    fn allow_context_set(&self, val: bool) {
        self.cache.write().expect("poisoned lock").allow_set(val);
    }

    fn get_register(&self, nm: &str) -> Result<VarnodeData> {
        self.base.get_register(nm)
    }

    fn get_register_name(&self, base: &AddrSpace, off: u64, size: i32) -> String {
        self.base.get_register_name(base, off, size)
    }

    fn get_exact_register_name(&self, base: &AddrSpace, off: u64, size: i32) -> String {
        self.base.get_exact_register_name(base, off, size)
    }

    fn get_all_registers(&self, reglist: &mut BTreeMap<VarnodeData, String>) {
        self.base.get_all_registers(reglist)
    }

    fn get_user_op_names(&self, res: &mut Vec<String>) {
        self.base.get_user_op_names(res)
    }

    fn instruction_length(&self, baseaddr: &Address) -> Result<i32> {
        let index = self.with_caches(|discache, cache, database| {
            self.obtain_context(discache, cache, &*database, baseaddr, ParseState::Disassembly)
        })?;
        let discache_guard = self.discache.read().expect("poisoned lock");
        match discache_guard.as_ref() {
            Some(discache) => Ok(discache.get(index).get_length()),
            None => Err(Error::Lowlevel("sleigh translator is not initialized".to_string())),
        }
    }

    fn one_instruction(&self, emit: &mut dyn PcodeEmit, baseaddr: &Address) -> Result<i32> {
        self.one_instruction_internal(emit, baseaddr)
    }

    fn print_assembly(&self, emit: &mut dyn AssemblyEmit, baseaddr: &Address) -> Result<i32> {
        let res = self.print_assembly_internal(emit, baseaddr);
        self.flush_pending()?;
        res
    }
}

impl PcodeCacher {
    pub fn build_injection(
        &mut self,
        walker: ParserWalker<'_>,
        tpl: &ConstructTpl,
        const_space: SpaceRef,
        uniq_space: SpaceRef,
        bitrange_ea: u64,
        baseaddr: &Address,
        emit: &mut dyn PcodeEmit,
    ) -> Result<()> {
        let discache = DisassemblyCache::new(0, &const_space, 1, 2)?;
        let symtab = walker.symtab();
        let uniquemask: u64 = 0;
        let uniqueoffset = (walker.get_addr().get_offset() & uniquemask) << 8;
        {
            let mut builder = SleighBuilder {
                labels: LabelCounter::new(0),
                walker,
                const_space,
                uniq_space,
                uniquemask,
                uniqueoffset,
                bitrange_ea,
                discache: &discache,
                cache: self,
                symtab,
                oracle: None,
                pending_miss: None,
                walker_in_delay_slot: false,
            };
            builder.build(Some(tpl), -1)?;
        }
        self.resolve_relatives()?;
        self.emit(baseaddr, emit)
    }
}
