use std::collections::BTreeMap;

use crate::address::Address;
use crate::error::{Error, Result};
use crate::memstate::MemoryState;
use crate::opbehavior::{OpBehavior, OpBehaviorRef, register_instructions};
use crate::opcodes::OpCode;
use crate::pcoderaw::{PcodeOpRaw, VarnodeData};
use crate::space::AddrSpace;
use crate::translate::{PcodeEmit, Translate};

pub type StandaloneEmulate<'e> = dyn Emulate<'static, Context = ()> + 'e;

pub trait BreakTable {
    fn do_pcode_op_break(&mut self, curop: &PcodeOpRaw, emulate: &mut StandaloneEmulate<'_>) -> Result<bool>;

    fn do_address_break(&mut self, addr: &Address, emulate: &mut StandaloneEmulate<'_>) -> Result<bool>;
}

pub trait BreakCallBack {
    fn pcode_callback(&mut self, _op: &PcodeOpRaw, _emulate: &mut StandaloneEmulate<'_>) -> Result<bool> {
        Ok(true)
    }

    fn address_callback(&mut self, _addr: &Address, _emulate: &mut StandaloneEmulate<'_>) -> Result<bool> {
        Ok(true)
    }
}

pub struct BreakTableCallBack<'a> {
    pub trans: &'a dyn Translate,
    pub addresscallback: BTreeMap<Address, Box<dyn BreakCallBack + 'a>>,
    pub pcodecallback: BTreeMap<u64, Box<dyn BreakCallBack + 'a>>,
}

impl<'a> BreakTableCallBack<'a> {
    pub fn new(trans: &'a dyn Translate) -> BreakTableCallBack<'a> {
        BreakTableCallBack {
            trans,
            addresscallback: BTreeMap::new(),
            pcodecallback: BTreeMap::new(),
        }
    }

    pub fn register_pcode_callback(&mut self, nm: &str, func: Box<dyn BreakCallBack + 'a>) -> Result<()> {
        let mut userops = Vec::new();
        self.trans.get_user_op_names(&mut userops);
        for (index, userop) in userops.iter().enumerate() {
            if userop == nm {
                self.pcodecallback.insert(index as u64, func);
                return Ok(());
            }
        }
        Err(Error::Lowlevel(format!("Bad userop name: {}", nm)))
    }

    pub fn register_address_callback(&mut self, addr: &Address, func: Box<dyn BreakCallBack + 'a>) {
        self.addresscallback.insert(addr.clone(), func);
    }
}

impl BreakTable for BreakTableCallBack<'_> {
    fn do_pcode_op_break(&mut self, curop: &PcodeOpRaw, emulate: &mut StandaloneEmulate<'_>) -> Result<bool> {
        let val = curop.get_input(0).offset;
        match self.pcodecallback.get_mut(&val) {
            None => Ok(false),
            Some(callback) => callback.pcode_callback(curop, emulate),
        }
    }

    fn do_address_break(&mut self, addr: &Address, emulate: &mut StandaloneEmulate<'_>) -> Result<bool> {
        match self.addresscallback.get_mut(addr) {
            None => Ok(false),
            Some(callback) => callback.address_callback(addr, emulate),
        }
    }
}

#[derive(Clone, Debug)]
pub struct EmulateBase {
    pub emu_halted: bool,
    pub current_behave: Option<OpCode>,
}

impl EmulateBase {
    pub fn new() -> EmulateBase {
        EmulateBase {
            emu_halted: true,
            current_behave: None,
        }
    }
}

impl Default for EmulateBase {
    fn default() -> EmulateBase {
        EmulateBase::new()
    }
}

pub trait Emulate<'c> {
    type Context: ?Sized;

    fn base(&self) -> &EmulateBase;

    fn base_mut(&mut self) -> &mut EmulateBase;

    fn get_behavior(&self, ctx: &Self::Context, opc: OpCode) -> Option<OpBehaviorRef>;

    fn execute_unary(&mut self, ctx: &mut Self::Context) -> Result<()>;

    fn execute_binary(&mut self, ctx: &mut Self::Context) -> Result<()>;

    fn execute_load(&mut self, ctx: &mut Self::Context) -> Result<()>;

    fn execute_store(&mut self, ctx: &mut Self::Context) -> Result<()>;

    fn execute_branch(&mut self, ctx: &mut Self::Context) -> Result<()>;

    fn execute_cbranch(&mut self, ctx: &mut Self::Context) -> Result<bool>;

    fn execute_branchind(&mut self, ctx: &mut Self::Context) -> Result<()>;

    fn execute_call(&mut self, ctx: &mut Self::Context) -> Result<()>;

    fn execute_callind(&mut self, ctx: &mut Self::Context) -> Result<()>;

    fn execute_callother(&mut self, ctx: &mut Self::Context) -> Result<()>;

    fn execute_multiequal(&mut self, ctx: &mut Self::Context) -> Result<()>;

    fn execute_indirect(&mut self, ctx: &mut Self::Context) -> Result<()>;

    fn execute_segment_op(&mut self, ctx: &mut Self::Context) -> Result<()>;

    fn execute_cpool_ref(&mut self, ctx: &mut Self::Context) -> Result<()>;

    fn execute_new(&mut self, ctx: &mut Self::Context) -> Result<()>;

    fn fallthru_op(&mut self, ctx: &mut Self::Context) -> Result<()>;

    fn set_execute_address(&mut self, ctx: &mut Self::Context, addr: &Address) -> Result<()>;

    fn get_execute_address(&self, ctx: &Self::Context) -> Address;

    fn set_halt(&mut self, val: bool) {
        self.base_mut().emu_halted = val;
    }

    fn get_halt(&self) -> bool {
        self.base().emu_halted
    }

    fn execute_current_op(&mut self, ctx: &mut Self::Context) -> Result<()> {
        let behave = match self.base().current_behave {
            None => None,
            Some(opc) => self.get_behavior(ctx, opc),
        };
        let behave = match behave {
            None => return self.fallthru_op(ctx),
            Some(behave) => behave,
        };
        if behave.is_special() {
            match behave.get_opcode() {
                OpCode::Load => {
                    self.execute_load(ctx)?;
                    self.fallthru_op(ctx)
                }
                OpCode::Store => {
                    self.execute_store(ctx)?;
                    self.fallthru_op(ctx)
                }
                OpCode::Branch => self.execute_branch(ctx),
                OpCode::Cbranch => {
                    if self.execute_cbranch(ctx)? {
                        self.execute_branch(ctx)
                    } else {
                        self.fallthru_op(ctx)
                    }
                }
                OpCode::Branchind => self.execute_branchind(ctx),
                OpCode::Call => self.execute_call(ctx),
                OpCode::Callind => self.execute_callind(ctx),
                OpCode::Callother => self.execute_callother(ctx),
                OpCode::Return => self.execute_branchind(ctx),
                OpCode::Multiequal => {
                    self.execute_multiequal(ctx)?;
                    self.fallthru_op(ctx)
                }
                OpCode::Indirect => {
                    self.execute_indirect(ctx)?;
                    self.fallthru_op(ctx)
                }
                OpCode::Segmentop => {
                    self.execute_segment_op(ctx)?;
                    self.fallthru_op(ctx)
                }
                OpCode::Cpoolref => {
                    self.execute_cpool_ref(ctx)?;
                    self.fallthru_op(ctx)
                }
                OpCode::New => {
                    self.execute_new(ctx)?;
                    self.fallthru_op(ctx)
                }
                _ => Err(Error::Lowlevel("Bad special op".to_string())),
            }
        } else if behave.is_unary() {
            self.execute_unary(ctx)?;
            self.fallthru_op(ctx)
        } else {
            self.execute_binary(ctx)?;
            self.fallthru_op(ctx)
        }
    }
}

pub struct EmulateMemory<'a> {
    pub base: EmulateBase,
    pub memstate: MemoryState<'a>,
}

impl<'a> EmulateMemory<'a> {
    pub fn new(mem: MemoryState<'a>) -> EmulateMemory<'a> {
        EmulateMemory {
            base: EmulateBase::new(),
            memstate: mem,
        }
    }

    pub fn get_memory_state(&mut self) -> &mut MemoryState<'a> {
        &mut self.memstate
    }

    fn space_from_const(&self, vn: &VarnodeData) -> Result<crate::space::SpaceRef> {
        vn.get_space_from_const(self.memstate.trans.manager())
            .ok_or_else(|| Error::Lowlevel("constant does not encode an address space".to_string()))
    }

    fn output_of(op: &PcodeOpRaw) -> Result<&VarnodeData> {
        op.get_output()
            .ok_or_else(|| Error::Lowlevel("p-code op has no output".to_string()))
    }

    pub fn execute_unary(&mut self, op: &PcodeOpRaw, behave: &dyn OpBehavior) -> Result<()> {
        let in1 = self.memstate.get_value_varnode(op.get_input(0))?;
        let out = EmulateMemory::output_of(op)?;
        let res = behave.evaluate_unary(out.size as i32, op.get_input(0).size as i32, in1)?;
        self.memstate.set_value_varnode(out, res)
    }

    pub fn execute_binary(&mut self, op: &PcodeOpRaw, behave: &dyn OpBehavior) -> Result<()> {
        let in1 = self.memstate.get_value_varnode(op.get_input(0))?;
        let in2 = self.memstate.get_value_varnode(op.get_input(1))?;
        let out = EmulateMemory::output_of(op)?;
        let res = behave.evaluate_binary(out.size as i32, op.get_input(0).size as i32, in1, in2)?;
        self.memstate.set_value_varnode(out, res)
    }

    pub fn execute_load(&mut self, op: &PcodeOpRaw) -> Result<()> {
        let mut off = self.memstate.get_value_varnode(op.get_input(1))?;
        let spc = self.space_from_const(op.get_input(0))?;
        off = AddrSpace::address_to_byte(off, spc.get_word_size());
        let out = EmulateMemory::output_of(op)?;
        let res = self.memstate.get_value(&spc, off, out.size as i32)?;
        self.memstate.set_value_varnode(out, res)
    }

    pub fn execute_store(&mut self, op: &PcodeOpRaw) -> Result<()> {
        let val = self.memstate.get_value_varnode(op.get_input(2))?;
        let mut off = self.memstate.get_value_varnode(op.get_input(1))?;
        let spc = self.space_from_const(op.get_input(0))?;
        off = AddrSpace::address_to_byte(off, spc.get_word_size());
        self.memstate.set_value(&spc, off, op.get_input(2).size as i32, val)
    }

    pub fn execute_branch(&mut self, op: &PcodeOpRaw) -> Result<Address> {
        Ok(op.get_input(0).get_addr())
    }

    pub fn execute_cbranch(&mut self, op: &PcodeOpRaw) -> Result<bool> {
        let cond = self.memstate.get_value_varnode(op.get_input(1))?;
        Ok(cond != 0)
    }

    pub fn execute_branchind(&mut self, op: &PcodeOpRaw) -> Result<Address> {
        let off = self.memstate.get_value_varnode(op.get_input(0))?;
        Ok(Address::from_parts(op.get_addr().get_space().cloned(), off))
    }

    pub fn execute_call(&mut self, op: &PcodeOpRaw) -> Result<Address> {
        Ok(op.get_input(0).get_addr())
    }

    pub fn execute_callind(&mut self, op: &PcodeOpRaw) -> Result<Address> {
        let off = self.memstate.get_value_varnode(op.get_input(0))?;
        Ok(Address::from_parts(op.get_addr().get_space().cloned(), off))
    }

    pub fn execute_callother(&mut self) -> Result<()> {
        Err(Error::Lowlevel(
            "CALLOTHER emulation not currently supported".to_string(),
        ))
    }

    pub fn execute_multiequal(&mut self) -> Result<()> {
        Err(Error::Lowlevel("MULTIEQUAL appearing in unheritaged code?".to_string()))
    }

    pub fn execute_indirect(&mut self) -> Result<()> {
        Err(Error::Lowlevel("INDIRECT appearing in unheritaged code?".to_string()))
    }

    pub fn execute_segment_op(&mut self) -> Result<()> {
        Err(Error::Lowlevel(
            "SEGMENTOP emulation not currently supported".to_string(),
        ))
    }

    pub fn execute_cpool_ref(&mut self) -> Result<()> {
        Err(Error::Lowlevel("Cannot currently emulate cpool operator".to_string()))
    }

    pub fn execute_new(&mut self) -> Result<()> {
        Err(Error::Lowlevel("Cannot currently emulate new operator".to_string()))
    }
}

pub struct PcodeEmitCache<'c> {
    pub opcache: &'c mut Vec<PcodeOpRaw>,
    pub uniq: u32,
}

impl<'c> PcodeEmitCache<'c> {
    pub fn new(ocache: &'c mut Vec<PcodeOpRaw>, uniq_reserve: u64) -> PcodeEmitCache<'c> {
        PcodeEmitCache {
            opcache: ocache,
            uniq: uniq_reserve as u32,
        }
    }

    pub fn create_varnode(&mut self, var: &VarnodeData) -> VarnodeData {
        var.clone()
    }
}

impl PcodeEmit for PcodeEmitCache<'_> {
    fn dump(&mut self, addr: &Address, opc: OpCode, outvar: Option<&VarnodeData>, vars: &[VarnodeData]) -> Result<()> {
        let mut op = PcodeOpRaw::new(opc);
        op.set_seq_num(addr, self.uniq);
        self.uniq = self.uniq.wrapping_add(1);
        if let Some(outvar) = outvar {
            let outvn = self.create_varnode(outvar);
            op.set_output(Some(outvn));
        }
        for var in vars {
            let invn = self.create_varnode(var);
            op.add_input(invn);
        }
        self.opcache.push(op);
        Ok(())
    }
}

pub struct EmulatePcodeCache<'a> {
    pub memory: EmulateMemory<'a>,
    pub trans: &'a dyn Translate,
    pub opcache: Vec<PcodeOpRaw>,
    pub inst: Vec<Option<OpBehaviorRef>>,
    pub breaktable: Option<&'a mut dyn BreakTable>,
    pub current_address: Address,
    pub instruction_start: bool,
    pub current_op: i32,
    pub instruction_length: i32,
}

impl<'a> EmulatePcodeCache<'a> {
    pub fn new(
        trans: &'a dyn Translate,
        state: MemoryState<'a>,
        breaktable: Option<&'a mut dyn BreakTable>,
    ) -> EmulatePcodeCache<'a> {
        let mut inst = Vec::new();
        register_instructions(&mut inst, &trans.translate_base().floatformats);
        EmulatePcodeCache {
            memory: EmulateMemory::new(state),
            trans,
            opcache: Vec::new(),
            inst,
            breaktable,
            current_address: Address::default(),
            instruction_start: false,
            current_op: 0,
            instruction_length: 0,
        }
    }

    pub fn clear_cache(&mut self) {
        self.opcache.clear();
    }

    pub fn create_instruction(&mut self, addr: &Address) -> Result<()> {
        self.clear_cache();
        let mut emit = PcodeEmitCache::new(&mut self.opcache, 0);
        self.instruction_length = self.trans.one_instruction(&mut emit, addr)?;
        self.current_op = 0;
        self.instruction_start = true;
        Ok(())
    }

    pub fn establish_op(&mut self) {
        if (self.current_op as usize) < self.opcache.len() && self.current_op >= 0 {
            let opc = self.opcache[self.current_op as usize].get_opcode();
            let present = matches!(self.inst.get(opc.index()), Some(Some(_)));
            self.memory.base.current_behave = if present { Some(opc) } else { None };
            return;
        }
        self.memory.base.current_behave = None;
    }

    pub fn is_instruction_start(&self) -> bool {
        self.instruction_start
    }

    pub fn num_current_ops(&self) -> i32 {
        self.opcache.len() as i32
    }

    pub fn get_current_op_index(&self) -> i32 {
        self.current_op
    }

    pub fn get_op_by_index(&self, index: i32) -> &PcodeOpRaw {
        &self.opcache[index as usize]
    }

    pub fn execute_instruction(&mut self) -> Result<()> {
        if self.instruction_start {
            let current = self.current_address.clone();
            if let Some(breaktable) = self.breaktable.take() {
                let res = breaktable.do_address_break(&current, self);
                self.breaktable = Some(breaktable);
                if res? {
                    return Ok(());
                }
            }
        }
        loop {
            self.execute_current_op(&mut ())?;
            if self.instruction_start {
                break;
            }
        }
        Ok(())
    }

    fn current_raw_op(&self) -> Result<&PcodeOpRaw> {
        self.opcache
            .get(self.current_op as usize)
            .ok_or_else(|| Error::Lowlevel("no current p-code op".to_string()))
    }

    fn current_behavior(&self) -> Result<OpBehaviorRef> {
        self.memory
            .base
            .current_behave
            .and_then(|opc| self.get_behavior(&(), opc))
            .ok_or_else(|| Error::Lowlevel("no current op behavior".to_string()))
    }
}

impl<'c> Emulate<'c> for EmulatePcodeCache<'_> {
    type Context = ();

    fn base(&self) -> &EmulateBase {
        &self.memory.base
    }

    fn base_mut(&mut self) -> &mut EmulateBase {
        &mut self.memory.base
    }

    fn get_behavior(&self, _ctx: &(), opc: OpCode) -> Option<OpBehaviorRef> {
        self.inst.get(opc.index()).cloned().flatten()
    }

    fn execute_unary(&mut self, _ctx: &mut ()) -> Result<()> {
        let behave = self.current_behavior()?;
        let op = self
            .opcache
            .get(self.current_op as usize)
            .ok_or_else(|| Error::Lowlevel("no current p-code op".to_string()))?;
        self.memory.execute_unary(op, behave.as_ref())
    }

    fn execute_binary(&mut self, _ctx: &mut ()) -> Result<()> {
        let behave = self.current_behavior()?;
        let op = self
            .opcache
            .get(self.current_op as usize)
            .ok_or_else(|| Error::Lowlevel("no current p-code op".to_string()))?;
        self.memory.execute_binary(op, behave.as_ref())
    }

    fn execute_load(&mut self, _ctx: &mut ()) -> Result<()> {
        let op = self
            .opcache
            .get(self.current_op as usize)
            .ok_or_else(|| Error::Lowlevel("no current p-code op".to_string()))?;
        self.memory.execute_load(op)
    }

    fn execute_store(&mut self, _ctx: &mut ()) -> Result<()> {
        let op = self
            .opcache
            .get(self.current_op as usize)
            .ok_or_else(|| Error::Lowlevel("no current p-code op".to_string()))?;
        self.memory.execute_store(op)
    }

    fn execute_branch(&mut self, ctx: &mut ()) -> Result<()> {
        let destaddr = self.current_raw_op()?.get_input(0).get_addr();
        if destaddr.is_constant() {
            let mut id = destaddr.get_offset() as u32;
            id = id.wrapping_add(self.current_op as u32);
            self.current_op = id as i32;
            if self.current_op as usize == self.opcache.len() && self.current_op >= 0 {
                self.fallthru_op(ctx)
            } else if self.current_op < 0 || self.current_op as usize >= self.opcache.len() {
                Err(Error::Lowlevel("Bad intra-instruction branch".to_string()))
            } else {
                self.establish_op();
                Ok(())
            }
        } else {
            self.set_execute_address(ctx, &destaddr)
        }
    }

    fn execute_cbranch(&mut self, _ctx: &mut ()) -> Result<bool> {
        let op = self
            .opcache
            .get(self.current_op as usize)
            .ok_or_else(|| Error::Lowlevel("no current p-code op".to_string()))?;
        self.memory.execute_cbranch(op)
    }

    fn execute_branchind(&mut self, ctx: &mut ()) -> Result<()> {
        let op = self
            .opcache
            .get(self.current_op as usize)
            .ok_or_else(|| Error::Lowlevel("no current p-code op".to_string()))?;
        let dest = self.memory.execute_branchind(op)?;
        self.set_execute_address(ctx, &dest)
    }

    fn execute_call(&mut self, ctx: &mut ()) -> Result<()> {
        let op = self
            .opcache
            .get(self.current_op as usize)
            .ok_or_else(|| Error::Lowlevel("no current p-code op".to_string()))?;
        let dest = self.memory.execute_call(op)?;
        self.set_execute_address(ctx, &dest)
    }

    fn execute_callind(&mut self, ctx: &mut ()) -> Result<()> {
        let op = self
            .opcache
            .get(self.current_op as usize)
            .ok_or_else(|| Error::Lowlevel("no current p-code op".to_string()))?;
        let dest = self.memory.execute_callind(op)?;
        self.set_execute_address(ctx, &dest)
    }

    fn execute_callother(&mut self, ctx: &mut ()) -> Result<()> {
        let op = self.current_raw_op()?.clone();
        let hooked = match self.breaktable.take() {
            None => false,
            Some(breaktable) => {
                let res = breaktable.do_pcode_op_break(&op, self);
                self.breaktable = Some(breaktable);
                res?
            }
        };
        if !hooked {
            return Err(Error::Lowlevel("Userop not hooked".to_string()));
        }
        self.fallthru_op(ctx)
    }

    fn execute_multiequal(&mut self, _ctx: &mut ()) -> Result<()> {
        self.memory.execute_multiequal()
    }

    fn execute_indirect(&mut self, _ctx: &mut ()) -> Result<()> {
        self.memory.execute_indirect()
    }

    fn execute_segment_op(&mut self, _ctx: &mut ()) -> Result<()> {
        self.memory.execute_segment_op()
    }

    fn execute_cpool_ref(&mut self, _ctx: &mut ()) -> Result<()> {
        self.memory.execute_cpool_ref()
    }

    fn execute_new(&mut self, _ctx: &mut ()) -> Result<()> {
        self.memory.execute_new()
    }

    fn fallthru_op(&mut self, _ctx: &mut ()) -> Result<()> {
        self.instruction_start = false;
        self.current_op += 1;
        if self.current_op as usize >= self.opcache.len() {
            self.current_address = self.current_address.add(self.instruction_length as i64);
            let addr = self.current_address.clone();
            self.create_instruction(&addr)?;
        }
        self.establish_op();
        Ok(())
    }

    fn set_execute_address(&mut self, _ctx: &mut (), addr: &Address) -> Result<()> {
        self.current_address = addr.clone();
        let current = self.current_address.clone();
        self.create_instruction(&current)?;
        self.establish_op();
        Ok(())
    }

    fn get_execute_address(&self, _ctx: &()) -> Address {
        self.current_address.clone()
    }
}
