use std::sync::RwLock;

use crate::address::Address;
use crate::error::{Error, Result};
use crate::globalcontext::{ContextCache, ContextDatabase};
use crate::slghsymbol::{Constructor, SymbolId, SymbolTable, SymbolType};
use crate::space::{AddrSpace, SpaceRef};

#[derive(Clone, Debug)]
pub struct Token {
    name: String,
    size: i32,
    index: i32,
    bigendian: bool,
}

impl Token {
    pub fn new(name: &str, size: i32, bigendian: bool, index: i32) -> Token {
        Token {
            name: name.to_string(),
            size,
            index,
            bigendian,
        }
    }

    pub fn get_size(&self) -> i32 {
        self.size
    }

    pub fn is_big_endian(&self) -> bool {
        self.bigendian
    }

    pub fn get_index(&self) -> i32 {
        self.index
    }

    pub fn get_name(&self) -> &str {
        &self.name
    }
}

#[derive(Clone, Debug, Default)]
pub struct FixedHandle {
    pub space: Option<SpaceRef>,
    pub size: u32,
    pub offset_space: Option<SpaceRef>,
    pub offset_offset: u64,
    pub offset_size: u32,
    pub temp_space: Option<SpaceRef>,
    pub temp_offset: u64,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct ConstructorRef {
    pub table: SymbolId,
    pub index: u32,
}

pub type StateId = u32;

pub const NULL_STATE: StateId = 0;
pub const TEMP_STATE: StateId = u32::MAX;

pub const MAX_DEPTH: i32 = 32;
pub const MAX_OPERAND: i32 = 20;
pub const MAX_INSTRUCTION_LEN: i32 = 16;
pub const INITIAL_STATE_NUM: i32 = 64;
pub const STATE_GROWTH: i32 = 64;

#[derive(Clone, Debug)]
pub struct ConstructState {
    pub ct: Option<ConstructorRef>,
    pub hand: FixedHandle,
    pub resolve: [StateId; MAX_OPERAND as usize],
    pub parent: StateId,
    pub length: i32,
    pub offset: u32,
}

impl Default for ConstructState {
    fn default() -> ConstructState {
        ConstructState::new()
    }
}

impl ConstructState {
    pub fn new() -> ConstructState {
        ConstructState {
            ct: None,
            hand: FixedHandle::default(),
            resolve: [NULL_STATE; MAX_OPERAND as usize],
            parent: NULL_STATE,
            length: 0,
            offset: 0,
        }
    }
}

#[derive(Clone, Debug)]
pub struct ContextSet {
    pub sym: SymbolId,
    pub point: StateId,
    pub num: i32,
    pub mask: u32,
    pub value: u32,
    pub flow: bool,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum ParseState {
    Uninitialized = 0,
    Disassembly = 1,
    Pcode = 2,
}

pub type LengthOracle<'a> = &'a dyn Fn(&Address) -> Result<i32>;

#[derive(Debug)]
struct CachedAddress(RwLock<Address>);

impl CachedAddress {
    fn new() -> CachedAddress {
        CachedAddress(RwLock::new(Address::invalid()))
    }

    fn get(&self) -> Address {
        self.0.read().expect("poisoned address lock").clone()
    }

    fn set(&self, address: Address) {
        *self.0.write().expect("poisoned address lock") = address;
    }
}

impl Clone for CachedAddress {
    fn clone(&self) -> CachedAddress {
        CachedAddress(RwLock::new(self.get()))
    }
}

#[derive(Clone, Debug)]
pub struct ParserContext {
    parsestate: ParseState,
    const_space: Option<SpaceRef>,
    buf: [u8; MAX_INSTRUCTION_LEN as usize],
    context: Vec<u32>,
    contextcommit: Vec<ContextSet>,
    addr: Address,
    naddr: Address,
    n2addr: CachedAddress,
    calladdr: Address,
    arena: Vec<ConstructState>,
    state: Vec<StateId>,
    base_state: StateId,
    alloc: i32,
    delayslot: i32,
}

impl ParserContext {
    pub fn new(context_size: i32) -> ParserContext {
        ParserContext {
            parsestate: ParseState::Uninitialized,
            const_space: None,
            buf: [0; MAX_INSTRUCTION_LEN as usize],
            context: vec![0; context_size.max(0) as usize],
            contextcommit: Vec::new(),
            addr: Address::invalid(),
            naddr: Address::invalid(),
            n2addr: CachedAddress::new(),
            calladdr: Address::invalid(),
            arena: vec![ConstructState::new()],
            state: Vec::new(),
            base_state: NULL_STATE,
            alloc: 0,
            delayslot: 0,
        }
    }

    pub fn get_buffer(&mut self) -> &mut [u8; MAX_INSTRUCTION_LEN as usize] {
        &mut self.buf
    }

    pub fn initialize(&mut self, spc: SpaceRef, maxstate: i32) {
        self.const_space = Some(spc);
        let count = maxstate.max(1) as usize;
        self.state.clear();
        for _ in 0..count {
            self.arena.push(ConstructState::new());
            self.state.push((self.arena.len() - 1) as StateId);
        }
        self.base_state = self.state[count - 1];
    }

    pub fn get_parser_state(&self) -> ParseState {
        self.parsestate
    }

    pub fn set_parser_state(&mut self, st: ParseState) {
        self.parsestate = st;
    }

    pub fn set_addr(&mut self, ad: &Address) {
        self.addr = ad.clone();
        self.n2addr.set(Address::invalid());
    }

    pub fn set_naddr(&mut self, ad: &Address) {
        self.naddr = ad.clone();
    }

    pub fn set_calladdr(&mut self, ad: &Address) {
        self.calladdr = ad.clone();
    }

    pub fn add_commit(&mut self, sym: SymbolId, num: i32, mask: u32, flow: bool, point: StateId) {
        let value = self.context.get(num.max(0) as usize).copied().unwrap_or(0) & mask;
        self.contextcommit.push(ContextSet {
            sym,
            point,
            num,
            mask,
            value,
            flow,
        });
    }

    pub fn clear_commits(&mut self) {
        self.contextcommit.clear();
    }

    pub fn apply_commits(
        &self,
        symtab: &SymbolTable,
        contcache: &mut ContextCache,
        database: &mut dyn ContextDatabase,
    ) -> Result<()> {
        if self.contextcommit.is_empty() {
            return Ok(());
        }
        let mut walker = ParserWalker::new(self, symtab);
        walker.base_state();
        for set in self.contextcommit.iter() {
            let sym = symtab.get(set.sym);
            let mut commitaddr;
            if sym.get_type() == SymbolType::Operand {
                let index = sym.operand().map(|oper| oper.get_index()).unwrap_or(0);
                let point = self.state_ref(set.point);
                let child = point.resolve.get(index.max(0) as usize).copied().unwrap_or(NULL_STATE);
                let hand = &self.state_ref(child).hand;
                commitaddr = Address::from_parts(hand.space.clone(), hand.offset_offset);
            } else {
                let mut hand = FixedHandle::default();
                sym.get_fixed_handle(&mut hand, &walker)?;
                commitaddr = Address::from_parts(hand.space.clone(), hand.offset_offset);
            }
            if commitaddr.is_constant() {
                let space = self.addr.get_space().cloned();
                let wordsize = space.as_ref().map(|spc| spc.get_word_size()).unwrap_or(1);
                let newoff = AddrSpace::address_to_byte(commitaddr.get_offset(), wordsize);
                commitaddr = Address::from_parts(space, newoff);
            }
            if set.flow {
                contcache.set_context(database, &commitaddr, set.num, set.mask, set.value);
            } else {
                let nextaddr = &commitaddr + 1;
                if nextaddr.get_offset() < commitaddr.get_offset() {
                    contcache.set_context(database, &commitaddr, set.num, set.mask, set.value);
                } else {
                    contcache.set_context_region(database, &commitaddr, &nextaddr, set.num, set.mask, set.value);
                }
            }
        }
        Ok(())
    }

    pub fn get_addr(&self) -> &Address {
        &self.addr
    }

    pub fn get_naddr(&self) -> &Address {
        &self.naddr
    }

    pub fn get_n2addr(&self, oracle: Option<LengthOracle<'_>>) -> Result<Address> {
        if self.n2addr.get().is_invalid() {
            let Some(oracle) = oracle else {
                return Err(Error::Lowlevel("inst_next2 not available in this context".to_string()));
            };
            if self.parsestate == ParseState::Uninitialized {
                return Err(Error::Lowlevel("inst_next2 not available in this context".to_string()));
            }
            let length = oracle(&self.naddr)?;
            self.n2addr.set(&self.naddr + length as i64);
        }
        Ok(self.n2addr.get())
    }

    pub fn get_dest_addr(&self) -> &Address {
        &self.calladdr
    }

    pub fn get_ref_addr(&self) -> &Address {
        &self.calladdr
    }

    pub fn get_cur_space(&self) -> Option<&SpaceRef> {
        self.addr.get_space()
    }

    pub fn get_const_space(&self) -> Option<&SpaceRef> {
        self.const_space.as_ref()
    }

    pub fn get_instruction_bytes(&self, bytestart: i32, size: i32, off: u32) -> Result<u32> {
        let off = off.wrapping_add(bytestart as u32);
        if off >= MAX_INSTRUCTION_LEN as u32 {
            return Err(Error::BadData(format!(
                "Instruction is using more than {MAX_INSTRUCTION_LEN} bytes"
            )));
        }
        let mut res: u32 = 0;
        for index in 0..size.max(0) as usize {
            res = res.wrapping_shl(8);
            res |= self.buf.get(off as usize + index).copied().unwrap_or(0) as u32;
        }
        Ok(res)
    }

    pub fn get_instruction_bits(&self, startbit: i32, size: i32, off: u32) -> Result<u32> {
        let off = off.wrapping_add((startbit / 8) as u32);
        if off >= MAX_INSTRUCTION_LEN as u32 {
            return Err(Error::BadData(format!(
                "Instruction is using more than {MAX_INSTRUCTION_LEN} bytes"
            )));
        }
        let startbit = startbit % 8;
        let bytesize = (startbit + size - 1) / 8 + 1;
        let mut res: u32 = 0;
        for index in 0..bytesize.max(0) as usize {
            res = res.wrapping_shl(8);
            res |= self.buf.get(off as usize + index).copied().unwrap_or(0) as u32;
        }
        res = res.wrapping_shl((8 * (4 - bytesize) + startbit) as u32);
        res = res.wrapping_shr((32 - size) as u32);
        Ok(res)
    }

    pub fn get_context_bytes(&self, bytestart: i32, size: i32) -> u32 {
        let mut intstart = bytestart / 4;
        let mut res = self.context_word(intstart);
        let byte_offset = bytestart % 4;
        let mut unused_bytes = 4 - size;
        res = res.wrapping_shl((byte_offset * 8) as u32);
        res = res.wrapping_shr((unused_bytes * 8) as u32);
        let remaining = size - 4 + byte_offset;
        if remaining > 0 {
            intstart += 1;
            if intstart < self.context.len() as i32 {
                let mut res2 = self.context_word(intstart);
                unused_bytes = 4 - remaining;
                res2 = res2.wrapping_shr((unused_bytes * 8) as u32);
                res |= res2;
            }
        }
        res
    }

    pub fn get_context_bits(&self, startbit: i32, size: i32) -> u32 {
        let mut intstart = startbit / 32;
        let mut res = self.context_word(intstart);
        let bit_offset = startbit % 32;
        let mut unused_bits = 32 - size;
        res = res.wrapping_shl(bit_offset as u32);
        res = res.wrapping_shr(unused_bits as u32);
        let remaining = size - 32 + bit_offset;
        if remaining > 0 {
            intstart += 1;
            if intstart < self.context.len() as i32 {
                let mut res2 = self.context_word(intstart);
                unused_bits = 32 - remaining;
                res2 = res2.wrapping_shr(unused_bits as u32);
                res |= res2;
            }
        }
        res
    }

    fn context_word(&self, index: i32) -> u32 {
        if index < 0 {
            return 0;
        }
        self.context.get(index as usize).copied().unwrap_or(0)
    }

    pub fn set_context_word(&mut self, index: i32, val: u32, mask: u32) {
        if index < 0 {
            return;
        }
        if let Some(word) = self.context.get_mut(index as usize) {
            *word = (*word & !mask) | (mask & val);
        }
    }

    pub fn load_context(&mut self, contcache: &mut ContextCache, database: &dyn ContextDatabase) {
        let addr = self.addr.clone();
        contcache.get_context(database, &addr, &mut self.context);
    }

    pub fn get_length(&self) -> i32 {
        self.state_ref(self.base_state).length
    }

    pub fn set_delay_slot(&mut self, val: i32) {
        self.delayslot = val;
    }

    pub fn get_delay_slot(&self) -> i32 {
        self.delayslot
    }

    pub fn expand_state(&mut self, amount: i32) {
        let mut fresh = Vec::with_capacity(amount.max(0) as usize);
        for _ in 0..amount.max(0) {
            self.arena.push(ConstructState::new());
            fresh.push((self.arena.len() - 1) as StateId);
        }
        self.state.splice(0..0, fresh);
        self.alloc += amount;
    }

    pub fn state_ref(&self, id: StateId) -> &ConstructState {
        self.arena.get(id as usize).unwrap_or(&self.arena[0])
    }

    pub fn state_mut(&mut self, id: StateId) -> &mut ConstructState {
        if (id as usize) < self.arena.len() {
            &mut self.arena[id as usize]
        } else {
            &mut self.arena[0]
        }
    }

    pub fn base_state_id(&self) -> StateId {
        self.base_state
    }

    pub fn get_context_words(&self) -> &[u32] {
        &self.context
    }
}

#[derive(Clone)]
pub struct ParserWalker<'a> {
    const_context: &'a ParserContext,
    cross_context: Option<&'a ParserContext>,
    symtab: &'a SymbolTable,
    oracle: Option<LengthOracle<'a>>,
    point: StateId,
    depth: i32,
    breadcrumb: [i32; MAX_DEPTH as usize],
    temp_state: Option<Box<ConstructState>>,
}

impl<'a> ParserWalker<'a> {
    pub fn new(context: &'a ParserContext, symtab: &'a SymbolTable) -> ParserWalker<'a> {
        ParserWalker {
            const_context: context,
            cross_context: None,
            symtab,
            oracle: None,
            point: NULL_STATE,
            depth: 0,
            breadcrumb: [0; MAX_DEPTH as usize],
            temp_state: None,
        }
    }

    pub fn new_cross(
        context: &'a ParserContext,
        cross: &'a ParserContext,
        symtab: &'a SymbolTable,
    ) -> ParserWalker<'a> {
        let mut walker = ParserWalker::new(context, symtab);
        walker.cross_context = Some(cross);
        walker
    }

    pub fn set_oracle(&mut self, oracle: Option<LengthOracle<'a>>) {
        self.oracle = oracle;
    }

    pub fn get_oracle(&self) -> Option<LengthOracle<'a>> {
        self.oracle
    }

    pub fn get_parser_context(&self) -> &'a ParserContext {
        self.const_context
    }

    pub fn get_cross_context(&self) -> Option<&'a ParserContext> {
        self.cross_context
    }

    pub fn symtab(&self) -> &'a SymbolTable {
        self.symtab
    }

    pub fn base_state(&mut self) {
        self.point = self.const_context.base_state;
        self.depth = 0;
        self.breadcrumb[0] = 0;
    }

    pub fn point(&self) -> StateId {
        self.point
    }

    pub fn depth(&self) -> i32 {
        self.depth
    }

    fn state(&self, id: StateId) -> &ConstructState {
        if id == TEMP_STATE {
            match &self.temp_state {
                Some(temp) => temp,
                None => self.const_context.state_ref(NULL_STATE),
            }
        } else {
            self.const_context.state_ref(id)
        }
    }

    pub fn current_state(&self) -> &ConstructState {
        self.state(self.point)
    }

    pub fn set_out_of_band_state(&mut self, ct: ConstructorRef, index: i32, otherwalker: &ParserWalker<'_>) {
        let mut pt = otherwalker.point;
        let mut curdepth = otherwalker.depth;
        while otherwalker.state(pt).ct != Some(ct) {
            if curdepth <= 0 {
                return;
            }
            curdepth -= 1;
            pt = otherwalker.state(pt).parent;
        }
        let constructor = self.symtab.get_constructor(ct);
        let Some(sym) = constructor.get_operand(index).map(|id| self.symtab.get(id)) else {
            return;
        };
        let Some(oper) = sym.operand() else {
            return;
        };
        let ptstate = otherwalker.state(pt);
        let mut tempstate = ConstructState::new();
        if oper.get_offset_base() < 0 {
            tempstate.offset = ptstate.offset.wrapping_add(oper.get_relative_offset());
        } else {
            let child = ptstate
                .resolve
                .get(index.max(0) as usize)
                .copied()
                .unwrap_or(NULL_STATE);
            tempstate.offset = otherwalker.state(child).offset;
        }
        tempstate.ct = Some(ct);
        tempstate.length = ptstate.length;
        self.temp_state = Some(Box::new(tempstate));
        self.point = TEMP_STATE;
        self.depth = 0;
        self.breadcrumb[0] = 0;
    }

    pub fn is_state(&self) -> bool {
        self.point != NULL_STATE
    }

    pub fn push_operand(&mut self, index: i32) -> Result<()> {
        if self.depth > MAX_DEPTH - 2 {
            return Err(Error::Lowlevel("SLEIGH exceeded maximum parse depth".to_string()));
        }
        self.breadcrumb[self.depth as usize] = index + 1;
        self.depth += 1;
        self.point = self
            .state(self.point)
            .resolve
            .get(index.max(0) as usize)
            .copied()
            .unwrap_or(NULL_STATE);
        self.breadcrumb[self.depth as usize] = 0;
        Ok(())
    }

    pub fn pop_operand(&mut self) {
        self.point = self.state(self.point).parent;
        self.depth -= 1;
    }

    pub fn get_offset(&self, index: i32) -> u32 {
        let point = self.state(self.point);
        if index < 0 {
            return point.offset;
        }
        let child = point.resolve.get(index as usize).copied().unwrap_or(NULL_STATE);
        let op = self.state(child);
        op.offset.wrapping_add(op.length as u32)
    }

    pub fn get_constructor_ref(&self) -> Option<ConstructorRef> {
        self.state(self.point).ct
    }

    pub fn get_constructor(&self) -> Option<&'a Constructor> {
        self.state(self.point).ct.map(|ct| self.symtab.get_constructor(ct))
    }

    pub fn get_operand(&self) -> i32 {
        if self.depth < 0 {
            return 0;
        }
        self.breadcrumb[self.depth as usize]
    }

    pub fn get_parent_handle(&self) -> &FixedHandle {
        &self.state(self.point).hand
    }

    pub fn get_fixed_handle(&self, index: i32) -> &FixedHandle {
        let child = self
            .state(self.point)
            .resolve
            .get(index.max(0) as usize)
            .copied()
            .unwrap_or(NULL_STATE);
        &self.state(child).hand
    }

    pub fn get_cur_space(&self) -> Option<&'a SpaceRef> {
        self.const_context.get_cur_space()
    }

    pub fn get_const_space(&self) -> Option<&'a SpaceRef> {
        self.const_context.get_const_space()
    }

    pub fn get_addr(&self) -> &'a Address {
        match self.cross_context {
            Some(cross) => cross.get_addr(),
            None => self.const_context.get_addr(),
        }
    }

    pub fn get_naddr(&self) -> &'a Address {
        match self.cross_context {
            Some(cross) => cross.get_naddr(),
            None => self.const_context.get_naddr(),
        }
    }

    pub fn get_n2addr(&self) -> Result<Address> {
        match self.cross_context {
            Some(cross) => cross.get_n2addr(self.oracle),
            None => self.const_context.get_n2addr(self.oracle),
        }
    }

    pub fn get_ref_addr(&self) -> &'a Address {
        match self.cross_context {
            Some(cross) => cross.get_ref_addr(),
            None => self.const_context.get_ref_addr(),
        }
    }

    pub fn get_dest_addr(&self) -> &'a Address {
        match self.cross_context {
            Some(cross) => cross.get_dest_addr(),
            None => self.const_context.get_dest_addr(),
        }
    }

    pub fn get_length(&self) -> i32 {
        self.const_context.get_length()
    }

    pub fn get_instruction_bytes(&self, byteoff: i32, numbytes: i32) -> Result<u32> {
        self.const_context
            .get_instruction_bytes(byteoff, numbytes, self.state(self.point).offset)
    }

    pub fn get_context_bytes(&self, byteoff: i32, numbytes: i32) -> u32 {
        self.const_context.get_context_bytes(byteoff, numbytes)
    }

    pub fn get_instruction_bits(&self, startbit: i32, size: i32) -> Result<u32> {
        self.const_context
            .get_instruction_bits(startbit, size, self.state(self.point).offset)
    }

    pub fn get_context_bits(&self, startbit: i32, size: i32) -> u32 {
        self.const_context.get_context_bits(startbit, size)
    }
}

pub struct ParserWalkerChange<'a> {
    context: &'a mut ParserContext,
    symtab: &'a SymbolTable,
    point: StateId,
    depth: i32,
    breadcrumb: [i32; MAX_DEPTH as usize],
}

impl<'a> ParserWalkerChange<'a> {
    pub fn new(context: &'a mut ParserContext, symtab: &'a SymbolTable) -> ParserWalkerChange<'a> {
        ParserWalkerChange {
            context,
            symtab,
            point: NULL_STATE,
            depth: 0,
            breadcrumb: [0; MAX_DEPTH as usize],
        }
    }

    pub fn view(&self) -> ParserWalker<'_> {
        ParserWalker {
            const_context: self.context,
            cross_context: None,
            symtab: self.symtab,
            oracle: None,
            point: self.point,
            depth: self.depth,
            breadcrumb: self.breadcrumb,
            temp_state: None,
        }
    }

    pub fn symtab(&self) -> &'a SymbolTable {
        self.symtab
    }

    pub fn get_parser_context(&mut self) -> &mut ParserContext {
        self.context
    }

    pub fn context_ref(&self) -> &ParserContext {
        self.context
    }

    pub fn base_state(&mut self) {
        self.point = self.context.base_state;
        self.depth = 0;
        self.breadcrumb[0] = 0;
    }

    pub fn is_state(&self) -> bool {
        self.point != NULL_STATE
    }

    pub fn get_point(&self) -> StateId {
        self.point
    }

    pub fn get_operand(&self) -> i32 {
        if self.depth < 0 {
            return 0;
        }
        self.breadcrumb[self.depth as usize]
    }

    pub fn get_constructor_ref(&self) -> Option<ConstructorRef> {
        self.context.state_ref(self.point).ct
    }

    pub fn get_offset(&self, index: i32) -> u32 {
        let point = self.context.state_ref(self.point);
        if index < 0 {
            return point.offset;
        }
        let child = point.resolve.get(index as usize).copied().unwrap_or(NULL_STATE);
        let op = self.context.state_ref(child);
        op.offset.wrapping_add(op.length as u32)
    }

    pub fn set_offset(&mut self, off: u32) {
        self.context.state_mut(self.point).offset = off;
    }

    pub fn set_constructor(&mut self, ct: Option<ConstructorRef>) {
        self.context.state_mut(self.point).ct = ct;
    }

    pub fn set_current_length(&mut self, len: i32) {
        self.context.state_mut(self.point).length = len;
    }

    pub fn get_parent_handle_mut(&mut self) -> &mut FixedHandle {
        &mut self.context.state_mut(self.point).hand
    }

    pub fn push_operand(&mut self, index: i32) -> Result<()> {
        if self.depth > MAX_DEPTH - 2 {
            return Err(Error::Lowlevel("SLEIGH exceeded maximum parse depth".to_string()));
        }
        self.breadcrumb[self.depth as usize] = index + 1;
        self.depth += 1;
        self.point = self
            .context
            .state_ref(self.point)
            .resolve
            .get(index.max(0) as usize)
            .copied()
            .unwrap_or(NULL_STATE);
        self.breadcrumb[self.depth as usize] = 0;
        Ok(())
    }

    pub fn pop_operand(&mut self) {
        self.point = self.context.state_ref(self.point).parent;
        self.depth -= 1;
    }

    pub fn calc_current_length(&mut self, length: i32, numopers: i32) {
        let point = self.context.state_ref(self.point);
        let mut length = (length as u32).wrapping_add(point.offset) as i32;
        for index in 0..numopers.max(0) as usize {
            let child = point.resolve.get(index).copied().unwrap_or(NULL_STATE);
            let subpoint = self.context.state_ref(child);
            let sublength = (subpoint.length as u32).wrapping_add(subpoint.offset) as i32;
            if sublength > length {
                length = sublength;
            }
        }
        let offset = point.offset;
        self.context.state_mut(self.point).length = (length as u32).wrapping_sub(offset) as i32;
    }

    pub fn deallocate_state(&mut self) {
        self.context.alloc = self.context.state.len() as i32 - 2;
        self.base_state();
    }

    pub fn allocate_operand(&mut self, index: i32) -> Result<()> {
        if index >= MAX_OPERAND {
            return Err(Error::Lowlevel("SLEIGH parser out of state space".to_string()));
        }
        if self.context.alloc < 0 {
            self.context.expand_state(STATE_GROWTH);
        }
        let opstate = self.context.state[self.context.alloc as usize];
        self.context.alloc -= 1;
        let parent = self.point;
        {
            let state = self.context.state_mut(opstate);
            state.parent = parent;
            state.ct = None;
            state.hand = FixedHandle::default();
        }
        if index >= 0 {
            self.context.state_mut(parent).resolve[index as usize] = opstate;
        }
        if self.depth > MAX_DEPTH - 2 {
            return Err(Error::Lowlevel("SLEIGH exceeded maximum parse depth".to_string()));
        }
        self.breadcrumb[self.depth as usize] += 1;
        self.depth += 1;
        self.point = opstate;
        self.breadcrumb[self.depth as usize] = 0;
        Ok(())
    }
}
