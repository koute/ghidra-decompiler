use std::collections::BTreeMap;

use crate::address::{Address, byte_swap, calc_mask};
use crate::architecture::Architecture;
use crate::emulate::{Emulate, EmulateBase, PcodeEmitCache};
use crate::error::{Error, Result};
use crate::funcdata::Funcdata;
use crate::op::OpId;
use crate::opbehavior::OpBehaviorRef;
use crate::opcodes::{OpCode, get_opname};
use crate::pcoderaw::{PcodeOpRaw, VarnodeData};
use crate::space::{AddrSpace, SpaceRef, SpaceType};
use crate::varnode::VarnodeId;

pub fn load_image_value(glb: &Architecture, spc: &SpaceRef, off: u64, sz: i32) -> Result<u64> {
    let loadimage = glb
        .loader
        .as_ref()
        .ok_or_else(|| Error::Lowlevel("missing load image".to_string()))?;
    let mut bytes = [0u8; 8];
    loadimage.load_fill(&mut bytes, &Address::new(spc.clone(), off))?;
    let mut res = u64::from_le_bytes(bytes);
    if spc.is_big_endian() {
        res = byte_swap(res, 8);
    }
    if spc.is_big_endian() && sz < 8 {
        res = res.wrapping_shr(((8 - sz) * 8) as u32);
    } else {
        res &= calc_mask(sz);
    }
    Ok(res)
}

pub struct PcodeOpContext<'c> {
    pub data: &'c mut Funcdata,
    pub glb: &'c mut Architecture,
}

impl<'c> PcodeOpContext<'c> {
    pub fn new(data: &'c mut Funcdata, glb: &'c mut Architecture) -> PcodeOpContext<'c> {
        PcodeOpContext { data, glb }
    }
}

#[derive(Clone, Debug, Default)]
pub struct EmulatePcodeOpBase {
    pub emulate: EmulateBase,
    pub current_op: Option<OpId>,
    pub last_op: Option<OpId>,
}

impl EmulatePcodeOpBase {
    pub fn new() -> EmulatePcodeOpBase {
        EmulatePcodeOpBase {
            emulate: EmulateBase::new(),
            current_op: None,
            last_op: None,
        }
    }
}

fn current_pcode_op(base: &EmulatePcodeOpBase) -> Result<OpId> {
    base.current_op
        .ok_or_else(|| Error::Lowlevel("no current p-code op".to_string()))
}

fn output_varnode(data: &Funcdata, op: OpId) -> Result<VarnodeId> {
    data.op(op)
        .get_out()
        .ok_or_else(|| Error::Lowlevel("p-code op has no output".to_string()))
}

pub trait EmulatePcodeOp<'c>: Emulate<'c, Context = PcodeOpContext<'c>> {
    fn pcode_base(&self) -> &EmulatePcodeOpBase;

    fn pcode_base_mut(&mut self) -> &mut EmulatePcodeOpBase;

    fn set_varnode_value(&mut self, vn: VarnodeId, val: u64);

    fn get_varnode_value(&self, ctx: &PcodeOpContext<'c>, vn: VarnodeId) -> Result<u64>;

    fn get_load_image_value(&self, glb: &Architecture, spc: &SpaceRef, offset: u64, sz: i32) -> Result<u64> {
        load_image_value(glb, spc, offset, sz)
    }

    fn pcode_get_behavior(&self, ctx: &PcodeOpContext<'c>, opc: OpCode) -> Option<OpBehaviorRef> {
        ctx.glb
            .inst
            .get(opc.index())
            .and_then(|slot| slot.as_ref())
            .and_then(|top| top.base().behave.clone())
    }

    fn set_current_op(&mut self, data: &Funcdata, op: OpId) {
        let opc = data.op(op).code();
        self.pcode_base_mut().current_op = Some(op);
        self.pcode_base_mut().emulate.current_behave = Some(opc);
    }

    fn pcode_get_execute_address(&self, data: &Funcdata) -> Address {
        let op = self.pcode_base().current_op.expect("no current op");
        data.op(op).get_addr().clone()
    }

    fn pcode_current_behavior(&self, ctx: &PcodeOpContext<'c>) -> Result<OpBehaviorRef> {
        self.pcode_base()
            .emulate
            .current_behave
            .and_then(|opc| self.pcode_get_behavior(ctx, opc))
            .ok_or_else(|| Error::Lowlevel("no current op behavior".to_string()))
    }

    fn pcode_execute_unary(&mut self, ctx: &mut PcodeOpContext<'c>) -> Result<()> {
        let op = current_pcode_op(self.pcode_base())?;
        let in0 = ctx.data.op(op).get_in(0);
        let in1 = self.get_varnode_value(ctx, in0)?;
        let out = output_varnode(ctx.data, op)?;
        let behave = self.pcode_current_behavior(ctx)?;
        let res = behave.evaluate_unary(ctx.data.vn(out).get_size(), ctx.data.vn(in0).get_size(), in1)?;
        self.set_varnode_value(out, res);
        Ok(())
    }

    fn pcode_execute_binary(&mut self, ctx: &mut PcodeOpContext<'c>) -> Result<()> {
        let op = current_pcode_op(self.pcode_base())?;
        let in0 = ctx.data.op(op).get_in(0);
        let in1vn = ctx.data.op(op).get_in(1);
        let in1 = self.get_varnode_value(ctx, in0)?;
        let in2 = self.get_varnode_value(ctx, in1vn)?;
        let out = output_varnode(ctx.data, op)?;
        let behave = self.pcode_current_behavior(ctx)?;
        let res = behave.evaluate_binary(ctx.data.vn(out).get_size(), ctx.data.vn(in0).get_size(), in1, in2)?;
        self.set_varnode_value(out, res);
        Ok(())
    }

    fn pcode_execute_load(&mut self, ctx: &mut PcodeOpContext<'c>) -> Result<()> {
        let op = current_pcode_op(self.pcode_base())?;
        let in1vn = ctx.data.op(op).get_in(1);
        let mut off = self.get_varnode_value(ctx, in1vn)?;
        let in0 = ctx.data.op(op).get_in(0);
        let spc = ctx
            .data
            .vn(in0)
            .get_space_from_const(&ctx.glb.manager)
            .ok_or_else(|| Error::Lowlevel("constant does not encode an address space".to_string()))?;
        off = AddrSpace::address_to_byte(off, spc.get_word_size());
        let out = output_varnode(ctx.data, op)?;
        let sz = ctx.data.vn(out).get_size();
        let res = self.get_load_image_value(ctx.glb, &spc, off, sz)?;
        self.set_varnode_value(out, res);
        Ok(())
    }

    fn pcode_execute_store(&mut self, _ctx: &mut PcodeOpContext<'c>) -> Result<()> {
        Ok(())
    }

    fn pcode_execute_cbranch(&mut self, ctx: &mut PcodeOpContext<'c>) -> Result<bool> {
        let op = current_pcode_op(self.pcode_base())?;
        let in1vn = ctx.data.op(op).get_in(1);
        let cond = self.get_varnode_value(ctx, in1vn)?;
        Ok((cond != 0) != ctx.data.op(op).is_boolean_flip())
    }

    fn pcode_execute_multiequal(&mut self, ctx: &mut PcodeOpContext<'c>) -> Result<()> {
        let op = current_pcode_op(self.pcode_base())?;
        let last = self
            .pcode_base()
            .last_op
            .ok_or_else(|| Error::Lowlevel("Could not execute MULTIEQUAL".to_string()))?;
        let bl = ctx.data.op(op).get_parent().expect("p-code op without parent block");
        let last_bl = ctx.data.op(last).get_parent().expect("p-code op without parent block");
        let size_in = ctx.data.block(bl).size_in();
        let mut slot = 0;
        while slot < size_in {
            if ctx.data.block(bl).get_in(slot) == last_bl {
                break;
            }
            slot += 1;
        }
        if slot == size_in {
            return Err(Error::Lowlevel("Could not execute MULTIEQUAL".to_string()));
        }
        let invn = ctx.data.op(op).get_in(slot);
        let val = self.get_varnode_value(ctx, invn)?;
        let out = output_varnode(ctx.data, op)?;
        self.set_varnode_value(out, val);
        Ok(())
    }

    fn pcode_execute_indirect(&mut self, ctx: &mut PcodeOpContext<'c>) -> Result<()> {
        let op = current_pcode_op(self.pcode_base())?;
        let in0 = ctx.data.op(op).get_in(0);
        let val = self.get_varnode_value(ctx, in0)?;
        let out = output_varnode(ctx.data, op)?;
        self.set_varnode_value(out, val);
        Ok(())
    }

    fn pcode_execute_segment_op(&mut self, ctx: &mut PcodeOpContext<'c>) -> Result<()> {
        let op = current_pcode_op(self.pcode_base())?;
        let in0 = ctx.data.op(op).get_in(0);
        let spc = ctx.data.vn(in0).get_space_from_const(&ctx.glb.manager);
        let segdef = match spc {
            None => None,
            Some(spc) => ctx.glb.userops.get_segment_op(spc.get_index()).cloned(),
        };
        let segdef = segdef.ok_or_else(|| Error::Lowlevel("Segment operand missing definition".to_string()))?;
        let in1vn = ctx.data.op(op).get_in(1);
        let in2vn = ctx.data.op(op).get_in(2);
        let in1 = self.get_varnode_value(ctx, in1vn)?;
        let in2 = self.get_varnode_value(ctx, in2vn)?;
        let bindlist = vec![in1, in2];
        let res = segdef.execute(&bindlist, ctx.glb)?;
        let out = output_varnode(ctx.data, op)?;
        self.set_varnode_value(out, res);
        Ok(())
    }

    fn pcode_execute_cpool_ref(&mut self, _ctx: &mut PcodeOpContext<'c>) -> Result<()> {
        Ok(())
    }

    fn pcode_execute_new(&mut self, _ctx: &mut PcodeOpContext<'c>) -> Result<()> {
        Ok(())
    }
}

#[derive(Clone, Debug, Default)]
pub struct EmulateSnippet {
    pub base: EmulateBase,
    pub op_list: Vec<PcodeOpRaw>,
    pub temp_values: BTreeMap<u64, u64>,
    pub current_op: Option<usize>,
    pub pos: i32,
}

impl EmulateSnippet {
    pub fn new() -> EmulateSnippet {
        EmulateSnippet {
            base: EmulateBase::new(),
            op_list: Vec::new(),
            temp_values: BTreeMap::new(),
            current_op: None,
            pos: 0,
        }
    }

    pub fn get_load_image_value(&self, glb: &Architecture, spc: &SpaceRef, offset: u64, sz: i32) -> Result<u64> {
        load_image_value(glb, spc, offset, sz)
    }

    pub fn reset_memory(&mut self) {
        self.temp_values.clear();
        self.set_current_op(0);
        self.base.emu_halted = false;
    }

    pub fn build_emitter(&mut self, uniq_reserve: u64) -> PcodeEmitCache<'_> {
        PcodeEmitCache::new(&mut self.op_list, uniq_reserve)
    }

    pub fn check_for_legal_code(&self) -> bool {
        for op in self.op_list.iter() {
            let opc = op.get_opcode();
            if matches!(
                opc,
                OpCode::Branchind
                    | OpCode::Call
                    | OpCode::Callind
                    | OpCode::Callother
                    | OpCode::Store
                    | OpCode::Segmentop
                    | OpCode::Cpoolref
                    | OpCode::New
                    | OpCode::Multiequal
                    | OpCode::Indirect
            ) {
                return false;
            }
            if opc == OpCode::Branch {
                let vn = op.get_input(0);
                if space_type(vn) != Some(SpaceType::Constant) {
                    return false;
                }
            }
            if let Some(vn) = op.get_output()
                && space_type(vn) != Some(SpaceType::Internal)
            {
                return false;
            }
            for slot in 0..op.num_input() {
                let vn = op.get_input(slot);
                if space_type(vn) == Some(SpaceType::Processor) {
                    return false;
                }
            }
        }
        true
    }

    pub fn set_current_op(&mut self, index: i32) {
        self.pos = index;
        self.current_op = Some(index as usize);
        self.base.current_behave = self.op_list.get(index as usize).map(|op| op.get_opcode());
    }

    pub fn set_varnode_value(&mut self, offset: u64, val: u64) {
        self.temp_values.insert(offset, val);
    }

    pub fn get_varnode_value(&self, glb: &Architecture, vn: &VarnodeData) -> Result<u64> {
        let spc = vn
            .space
            .clone()
            .ok_or_else(|| Error::Lowlevel("varnode without space".to_string()))?;
        if spc.get_type() == SpaceType::Constant {
            return Ok(vn.offset);
        }
        if spc.get_type() == SpaceType::Internal {
            return match self.temp_values.get(&vn.offset) {
                Some(val) => Ok(*val),
                None => Err(Error::Lowlevel("Read before write in snippet emulation".to_string())),
            };
        }
        self.get_load_image_value(glb, &spc, vn.offset, vn.size as i32)
    }

    pub fn get_temp_value(&self, offset: u64) -> u64 {
        match self.temp_values.get(&offset) {
            None => 0,
            Some(val) => *val,
        }
    }

    fn current_raw_op(&self) -> Result<&PcodeOpRaw> {
        self.current_op
            .and_then(|index| self.op_list.get(index))
            .ok_or_else(|| Error::Lowlevel("no current p-code op".to_string()))
    }

    fn illegal_op_error(&self) -> Error {
        let opname = match self.current_raw_op() {
            Ok(op) => get_opname(op.get_opcode()),
            Err(_) => "",
        };
        Error::Lowlevel(format!("Illegal p-code operation in snippet: {}", opname))
    }

    fn current_behavior(&self, glb: &Architecture) -> Result<OpBehaviorRef> {
        self.base
            .current_behave
            .and_then(|opc| self.get_behavior(glb, opc))
            .ok_or_else(|| Error::Lowlevel("no current op behavior".to_string()))
    }
}

fn space_type(vn: &VarnodeData) -> Option<SpaceType> {
    vn.space.as_ref().map(|spc| spc.get_type())
}

fn raw_output(op: &PcodeOpRaw) -> Result<&VarnodeData> {
    op.get_output()
        .ok_or_else(|| Error::Lowlevel("p-code op has no output".to_string()))
}

impl<'c> Emulate<'c> for EmulateSnippet {
    type Context = Architecture;

    fn base(&self) -> &EmulateBase {
        &self.base
    }

    fn base_mut(&mut self) -> &mut EmulateBase {
        &mut self.base
    }

    fn get_behavior(&self, ctx: &Architecture, opc: OpCode) -> Option<OpBehaviorRef> {
        ctx.pcodeinjectlib
            .as_deref()
            .and_then(|library| library.get_behaviors().get(opc.index()).cloned())
            .flatten()
    }

    fn execute_unary(&mut self, ctx: &mut Architecture) -> Result<()> {
        let op = self.current_raw_op()?.clone();
        let in1 = self.get_varnode_value(ctx, op.get_input(0))?;
        let out = raw_output(&op)?;
        let behave = self.current_behavior(ctx)?;
        let res = behave.evaluate_unary(out.size as i32, op.get_input(0).size as i32, in1)?;
        self.set_varnode_value(out.offset, res);
        Ok(())
    }

    fn execute_binary(&mut self, ctx: &mut Architecture) -> Result<()> {
        let op = self.current_raw_op()?.clone();
        let in1 = self.get_varnode_value(ctx, op.get_input(0))?;
        let in2 = self.get_varnode_value(ctx, op.get_input(1))?;
        let out = raw_output(&op)?;
        let behave = self.current_behavior(ctx)?;
        let res = behave.evaluate_binary(out.size as i32, op.get_input(0).size as i32, in1, in2)?;
        self.set_varnode_value(out.offset, res);
        Ok(())
    }

    fn execute_load(&mut self, ctx: &mut Architecture) -> Result<()> {
        let op = self.current_raw_op()?.clone();
        let mut off = self.get_varnode_value(ctx, op.get_input(1))?;
        let spc = op
            .get_input(0)
            .get_space_from_const(&ctx.manager)
            .ok_or_else(|| Error::Lowlevel("constant does not encode an address space".to_string()))?;
        off = AddrSpace::address_to_byte(off, spc.get_word_size());
        let out = raw_output(&op)?;
        let res = self.get_load_image_value(ctx, &spc, off, out.size as i32)?;
        self.set_varnode_value(out.offset, res);
        Ok(())
    }

    fn execute_store(&mut self, _ctx: &mut Architecture) -> Result<()> {
        Err(self.illegal_op_error())
    }

    fn execute_branch(&mut self, _ctx: &mut Architecture) -> Result<()> {
        let vn = self.current_raw_op()?.get_input(0).clone();
        if space_type(&vn) != Some(SpaceType::Constant) {
            return Err(Error::Lowlevel(
                "Tried to emulate absolute branch in snippet code".to_string(),
            ));
        }
        let rel = vn.offset as i32;
        self.pos = self.pos.wrapping_add(rel);
        if self.pos < 0 || self.pos as usize > self.op_list.len() {
            return Err(Error::Lowlevel(
                "Relative branch out of bounds in snippet code".to_string(),
            ));
        }
        if self.pos as usize == self.op_list.len() {
            self.base.emu_halted = true;
            return Ok(());
        }
        self.set_current_op(self.pos);
        Ok(())
    }

    fn execute_cbranch(&mut self, ctx: &mut Architecture) -> Result<bool> {
        let op = self.current_raw_op()?.clone();
        let cond = self.get_varnode_value(ctx, op.get_input(1))?;
        Ok(cond != 0)
    }

    fn execute_branchind(&mut self, _ctx: &mut Architecture) -> Result<()> {
        Err(self.illegal_op_error())
    }

    fn execute_call(&mut self, _ctx: &mut Architecture) -> Result<()> {
        Err(self.illegal_op_error())
    }

    fn execute_callind(&mut self, _ctx: &mut Architecture) -> Result<()> {
        Err(self.illegal_op_error())
    }

    fn execute_callother(&mut self, _ctx: &mut Architecture) -> Result<()> {
        Err(self.illegal_op_error())
    }

    fn execute_multiequal(&mut self, _ctx: &mut Architecture) -> Result<()> {
        Err(self.illegal_op_error())
    }

    fn execute_indirect(&mut self, _ctx: &mut Architecture) -> Result<()> {
        Err(self.illegal_op_error())
    }

    fn execute_segment_op(&mut self, _ctx: &mut Architecture) -> Result<()> {
        Err(self.illegal_op_error())
    }

    fn execute_cpool_ref(&mut self, _ctx: &mut Architecture) -> Result<()> {
        Err(self.illegal_op_error())
    }

    fn execute_new(&mut self, _ctx: &mut Architecture) -> Result<()> {
        Err(self.illegal_op_error())
    }

    fn fallthru_op(&mut self, _ctx: &mut Architecture) -> Result<()> {
        self.pos += 1;
        if self.pos as usize == self.op_list.len() {
            self.base.emu_halted = true;
            return Ok(());
        }
        self.set_current_op(self.pos);
        Ok(())
    }

    fn set_execute_address(&mut self, _ctx: &mut Architecture, _addr: &Address) -> Result<()> {
        self.set_current_op(0);
        Ok(())
    }

    fn get_execute_address(&self, _ctx: &Architecture) -> Address {
        self.op_list[self.current_op.expect("no current op")].get_addr().clone()
    }
}
