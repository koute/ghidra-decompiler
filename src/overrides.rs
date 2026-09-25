use std::collections::BTreeMap;

use crate::address::Address;
use crate::architecture::Architecture;
use crate::error::{Error, Result};
use crate::fspec::{CallSpecId, FuncProto};
use crate::funcdata::Funcdata;
use crate::marshal::{ATTRIB_SPACE, ATTRIB_TYPE, Decoder, ElementId, Encoder};
use crate::opcodes::OpCode;
use crate::space::{ATTRIB_DELAY, SpaceRef};

pub const ELEM_DEADCODEDELAY: ElementId = ElementId::new("deadcodedelay", 218);
pub const ELEM_FLOW: ElementId = ElementId::new("flow", 219);
pub const ELEM_FORCEGOTO: ElementId = ElementId::new("forcegoto", 220);
pub const ELEM_CALLDEST: ElementId = ElementId::new("calldest", 221);
pub const ELEM_MULTISTAGEJUMP: ElementId = ElementId::new("multistagejump", 222);
pub const ELEM_OVERRIDE: ElementId = ElementId::new("override", 223);
pub const ELEM_PROTOOVERRIDE: ElementId = ElementId::new("protooverride", 224);

#[derive(Clone, Debug)]
pub enum OverrideRecord {
    Branch,
    Call,
    CallReturn,
    Return,
    CallotherCall { call_address: Address },
    CallotherBranch { branch_address: Address },
    CallCall { call_address: Address },
}

fn space_by_index(glb: &Architecture, index: usize) -> Result<SpaceRef> {
    glb.manager
        .get_space(index as i32)
        .ok_or_else(|| Error::Lowlevel(format!("missing address space with index {}", index)))
}

impl OverrideRecord {
    pub const BRANCH_NAME: &'static str = "branch";
    pub const CALL_NAME: &'static str = "call";
    pub const CALLRETURN_NAME: &'static str = "callreturn";
    pub const RETURN_NAME: &'static str = "return";
    pub const CALLOTHER_CALL_NAME: &'static str = "callother_call";
    pub const CALLOTHER_BRANCH_NAME: &'static str = "callother_branch";
    pub const CALL_CALL_NAME: &'static str = "call_call";

    pub fn new_callother_call(dest: &Address) -> OverrideRecord {
        OverrideRecord::CallotherCall {
            call_address: dest.clone(),
        }
    }

    pub fn new_callother_branch(dest: &Address) -> OverrideRecord {
        OverrideRecord::CallotherBranch {
            branch_address: dest.clone(),
        }
    }

    pub fn new_call_call(dest: &Address) -> OverrideRecord {
        OverrideRecord::CallCall {
            call_address: dest.clone(),
        }
    }

    fn find_dead_branch(
        data: &Funcdata,
        addr: &Address,
        find_branch: bool,
        find_call: bool,
        find_callother: bool,
        find_return: bool,
        message: &str,
    ) -> Result<crate::op::OpId> {
        match data.find_primary_branch(addr, find_branch, find_call, find_callother, find_return) {
            Some(op) if data.op(op).is_dead() => Ok(op),
            _ => Err(Error::Lowlevel(message.to_string())),
        }
    }

    pub fn perform_override(&self, addr: &Address, data: &mut Funcdata, glb: &mut Architecture) -> Result<()> {
        match self {
            OverrideRecord::Branch => {
                let op = OverrideRecord::find_dead_branch(
                    data,
                    addr,
                    false,
                    true,
                    false,
                    true,
                    "Could not apply BRANCH override",
                )?;
                let opc = data.op(op).code();
                if opc == OpCode::Call {
                    data.op_set_opcode(op, OpCode::Branch, glb);
                } else if opc == OpCode::Callind || opc == OpCode::Return {
                    data.op_set_opcode(op, OpCode::Branchind, glb);
                }
                Ok(())
            }
            OverrideRecord::Call => {
                let op = OverrideRecord::find_dead_branch(
                    data,
                    addr,
                    true,
                    false,
                    false,
                    true,
                    "Could not apply CALL override",
                )?;
                let opc = data.op(op).code();
                if opc == OpCode::Branch {
                    data.op_set_opcode(op, OpCode::Call, glb);
                } else if opc == OpCode::Branchind {
                    data.op_set_opcode(op, OpCode::Callind, glb);
                } else if opc == OpCode::Cbranch {
                    return Err(Error::Lowlevel(
                        "Do not currently support CBRANCH overrides".to_string(),
                    ));
                } else if opc == OpCode::Return {
                    data.op_set_opcode(op, OpCode::Callind, glb);
                }
                Ok(())
            }
            OverrideRecord::CallReturn => {
                let op = OverrideRecord::find_dead_branch(
                    data,
                    addr,
                    true,
                    true,
                    false,
                    true,
                    "Could not apply CALL_RETURN override",
                )?;
                let opc = data.op(op).code();
                if opc == OpCode::Branch {
                    data.op_set_opcode(op, OpCode::Call, glb);
                } else if opc == OpCode::Branchind {
                    data.op_set_opcode(op, OpCode::Callind, glb);
                } else if opc == OpCode::Cbranch {
                    return Err(Error::Lowlevel(
                        "Do not currently support CBRANCH overrides".to_string(),
                    ));
                } else if opc == OpCode::Return {
                    data.op_set_opcode(op, OpCode::Callind, glb);
                }
                let new_return = data.new_op(1, addr);
                data.op_set_opcode(new_return, OpCode::Return, glb);
                let constant = data.new_constant(1, 0, glb);
                data.op_set_input(new_return, constant, 0)?;
                data.op_dead_insert_after(new_return, op)
            }
            OverrideRecord::Return => {
                let op = OverrideRecord::find_dead_branch(
                    data,
                    addr,
                    true,
                    true,
                    false,
                    false,
                    "Could not apply RETURN override",
                )?;
                let opc = data.op(op).code();
                if opc == OpCode::Branch || opc == OpCode::Cbranch || opc == OpCode::Call {
                    return Err(Error::Lowlevel(
                        "Do not currently support complex overrides".to_string(),
                    ));
                } else if opc == OpCode::Branchind || opc == OpCode::Callind {
                    data.op_set_opcode(op, OpCode::Return, glb);
                }
                Ok(())
            }
            OverrideRecord::CallotherCall { call_address } => {
                let op = OverrideRecord::find_dead_branch(
                    data,
                    addr,
                    false,
                    false,
                    true,
                    false,
                    "Could not apply CALLOTHER->CALL override",
                )?;
                data.op_set_opcode(op, OpCode::Call, glb);
                let dest = data.new_code_ref(call_address, glb);
                data.op_set_input(op, dest, 0)
            }
            OverrideRecord::CallotherBranch { branch_address } => {
                let op = OverrideRecord::find_dead_branch(
                    data,
                    addr,
                    false,
                    false,
                    true,
                    false,
                    "Could not apply CALLOTHER->BRANCH override",
                )?;
                data.op_set_opcode(op, OpCode::Branch, glb);
                let dest = data.new_code_ref(branch_address, glb);
                data.op_set_input(op, dest, 0)
            }
            OverrideRecord::CallCall { call_address } => {
                let op = OverrideRecord::find_dead_branch(
                    data,
                    addr,
                    false,
                    true,
                    false,
                    false,
                    "Could not apply CALL destination override",
                )?;
                data.op_set_opcode(op, OpCode::Call, glb);
                let dest = data.new_code_ref(call_address, glb);
                data.op_set_input(op, dest, 0)
            }
        }
    }

    fn get_name(&self) -> &'static str {
        match self {
            OverrideRecord::Branch => OverrideRecord::BRANCH_NAME,
            OverrideRecord::Call => OverrideRecord::CALL_NAME,
            OverrideRecord::CallReturn => OverrideRecord::CALLRETURN_NAME,
            OverrideRecord::Return => OverrideRecord::RETURN_NAME,
            OverrideRecord::CallotherCall { .. } => OverrideRecord::CALLOTHER_CALL_NAME,
            OverrideRecord::CallotherBranch { .. } => OverrideRecord::CALLOTHER_BRANCH_NAME,
            OverrideRecord::CallCall { .. } => OverrideRecord::CALL_CALL_NAME,
        }
    }

    pub fn encode(&self, encoder: &mut dyn Encoder, addr: &Address) -> Result<()> {
        match self {
            OverrideRecord::Branch | OverrideRecord::Call | OverrideRecord::CallReturn | OverrideRecord::Return => {
                encoder.open_element(ELEM_FLOW);
                encoder.write_string(ATTRIB_TYPE, self.get_name());
                addr.encode(encoder)?;
                encoder.close_element(ELEM_FLOW);
            }
            OverrideRecord::CallotherCall { call_address: dest }
            | OverrideRecord::CallotherBranch { branch_address: dest }
            | OverrideRecord::CallCall { call_address: dest } => {
                encoder.open_element(ELEM_CALLDEST);
                encoder.write_string(ATTRIB_TYPE, self.get_name());
                addr.encode(encoder)?;
                dest.encode(encoder)?;
                encoder.close_element(ELEM_CALLDEST);
            }
        }
        Ok(())
    }

    pub fn print_raw(&self, out: &mut String, addr: &Address) {
        let text = match self {
            OverrideRecord::Branch => format!("override CALL, CALLIND, or RETURN at {} to a BRANCH\n", addr),
            OverrideRecord::Call => format!("override BRANCH, BRANCHIND, or RETURN at {} to a CALL\n", addr),
            OverrideRecord::CallReturn => {
                format!(
                    "override BRANCH, BRANCHIND, or RETURN at {} to a CALL followed by a RETURN\n",
                    addr
                )
            }
            OverrideRecord::Return => format!("override BRANCHIND or CALLIND at {} to a RETURN\n", addr),
            OverrideRecord::CallotherCall { call_address } => {
                format!("override CALLOTHER at {} to CALL directly to {}\n", addr, call_address)
            }
            OverrideRecord::CallotherBranch { branch_address } => {
                format!(
                    "override CALLOTHER at {} to BRANCH directly to {}\n",
                    addr, branch_address
                )
            }
            OverrideRecord::CallCall { call_address } => {
                format!("override CALL at {} to call to a new address {}\n", addr, call_address)
            }
        };
        out.push_str(&text);
    }

    pub fn allocate_flow(name: &str) -> Result<OverrideRecord> {
        match name {
            OverrideRecord::BRANCH_NAME => Ok(OverrideRecord::Branch),
            OverrideRecord::CALL_NAME => Ok(OverrideRecord::Call),
            OverrideRecord::CALLRETURN_NAME => Ok(OverrideRecord::CallReturn),
            OverrideRecord::RETURN_NAME => Ok(OverrideRecord::Return),
            _ => Err(Error::Lowlevel(format!("Unknown flow override name: {}", name))),
        }
    }

    pub fn allocate_call_dest(name: &str, dest: &Address) -> Result<OverrideRecord> {
        match name {
            OverrideRecord::CALLOTHER_CALL_NAME => Ok(OverrideRecord::new_callother_call(dest)),
            OverrideRecord::CALLOTHER_BRANCH_NAME => Ok(OverrideRecord::new_callother_branch(dest)),
            OverrideRecord::CALL_CALL_NAME => Ok(OverrideRecord::new_call_call(dest)),
            _ => Err(Error::Lowlevel(format!(
                "Unknown call destination override name: {}",
                name
            ))),
        }
    }
}

#[derive(Default)]
pub struct Override {
    pcodeover: BTreeMap<Address, OverrideRecord>,
    forcegoto: BTreeMap<Address, Address>,
    deadcodedelay: Vec<i32>,
    deindirect: BTreeMap<Address, Address>,
    protoover: BTreeMap<Address, Box<FuncProto>>,
    multistagejump: Vec<Address>,
}

impl Override {
    pub fn new() -> Override {
        Override::default()
    }

    pub fn clear(&mut self) {
        self.protoover.clear();
        self.pcodeover.clear();
        self.forcegoto.clear();
        self.deadcodedelay.clear();
        self.deindirect.clear();
        self.multistagejump.clear();
    }

    fn generate_deadcode_delay_message(index: i32, glb: &Architecture) -> Result<String> {
        let spc = space_by_index(glb, index as usize)?;
        Ok(format!(
            "Restarted to delay deadcode elimination for space: {}",
            spc.get_name()
        ))
    }

    pub fn insert_force_goto(&mut self, targetpc: &Address, destpc: &Address) {
        self.forcegoto.insert(targetpc.clone(), destpc.clone());
    }

    pub fn insert_deadcode_delay(&mut self, spc: &SpaceRef, delay: i32) {
        let index = spc.get_index() as usize;
        while self.deadcodedelay.len() <= index {
            self.deadcodedelay.push(-1);
        }
        self.deadcodedelay[index] = delay;
    }

    pub fn has_deadcode_delay(&self, spc: &SpaceRef) -> bool {
        let index = spc.get_index() as usize;
        if index >= self.deadcodedelay.len() {
            return false;
        }
        let val = self.deadcodedelay[index];
        if val == -1 {
            return false;
        }
        val != spc.get_deadcode_delay()
    }

    pub fn insert_deindirect(&mut self, call_point: &Address, direct_addr: &Address) {
        self.deindirect.insert(call_point.clone(), direct_addr.clone());
    }

    pub fn insert_proto_override(&mut self, callpoint: &Address, mut proto: Box<FuncProto>) {
        proto.set_override(true);
        self.protoover.insert(callpoint.clone(), proto);
    }

    pub fn insert_multistage_jump(&mut self, addr: &Address) {
        self.multistagejump.push(addr.clone());
    }

    pub fn insert_flow_override(&mut self, addr: &Address, tp: &str) -> Result<()> {
        let rec = OverrideRecord::allocate_flow(tp)?;
        self.pcodeover.insert(addr.clone(), rec);
        Ok(())
    }

    pub fn insert_destination_override(&mut self, addr: &Address, dest: &Address, tp: &str) -> Result<()> {
        let rec = OverrideRecord::allocate_call_dest(tp, dest)?;
        self.pcodeover.insert(addr.clone(), rec);
        Ok(())
    }

    pub fn apply_prototype(data: &mut Funcdata, _glb: &mut Architecture, fspecs: CallSpecId) -> Result<()> {
        if data.localoverride.protoover.is_empty() {
            return Ok(());
        }
        let op = data.callspecs.get(fspecs).get_op();
        let addr = data.op(op).get_addr().clone();
        if let Some(proto) = data.localoverride.protoover.get(&addr) {
            data.callspecs.get_mut(fspecs).copy(proto)?;
        }
        Ok(())
    }

    pub fn apply_indirect(data: &mut Funcdata, _glb: &mut Architecture, fspecs: CallSpecId) -> Result<()> {
        if data.localoverride.deindirect.is_empty() {
            return Ok(());
        }
        let op = data.callspecs.get(fspecs).get_op();
        let addr = data.op(op).get_addr().clone();
        if let Some(dest) = data.localoverride.deindirect.get(&addr) {
            let dest = dest.clone();
            data.callspecs.get_mut(fspecs).set_address(&dest);
        }
        Ok(())
    }

    pub fn query_multistage_jumptable(&self, addr: &Address) -> bool {
        self.multistagejump.iter().any(|jump| jump == addr)
    }

    pub fn apply_dead_code_delay(data: &mut Funcdata, glb: &mut Architecture) -> Result<()> {
        let delays = data.localoverride.deadcodedelay.clone();
        for (index, delay) in delays.into_iter().enumerate() {
            if delay < 0 {
                continue;
            }
            let spc = space_by_index(glb, index)?;
            data.set_dead_code_delay(&spc, delay)?;
        }
        Ok(())
    }

    pub fn apply_force_goto(data: &mut Funcdata, _glb: &mut Architecture) -> Result<()> {
        let gotos: Vec<(Address, Address)> = data
            .localoverride
            .forcegoto
            .iter()
            .map(|(target, dest)| (target.clone(), dest.clone()))
            .collect();
        for (target, dest) in gotos {
            data.force_goto(&target, &dest);
        }
        Ok(())
    }

    pub fn has_pcode_override(&self) -> bool {
        !self.pcodeover.is_empty()
    }

    pub fn get_pcode_override(&self, addr: &Address) -> Option<&OverrideRecord> {
        self.pcodeover.get(addr)
    }

    pub fn print_raw(&mut self, out: &mut String, glb: &Architecture) -> Result<()> {
        for (target, dest) in self.forcegoto.iter() {
            out.push_str(&format!("force goto at {} jumping to {}\n", target, dest));
        }
        for (index, delay) in self.deadcodedelay.iter().enumerate() {
            if *delay < 0 {
                continue;
            }
            let spc = space_by_index(glb, index)?;
            out.push_str(&format!("dead code delay on {} set to {}\n", spc.get_name(), delay));
        }
        for (call_point, dest) in self.deindirect.iter() {
            out.push_str(&format!(
                "override indirect at {} to call directly to {}\n",
                call_point, dest
            ));
        }
        for (addr, rec) in self.pcodeover.iter() {
            rec.print_raw(out, addr);
        }
        for (addr, proto) in self.protoover.iter_mut() {
            out.push_str(&format!("override prototype at {} to ", addr));
            proto.print_raw("func", out, glb);
            out.push('\n');
        }
        Ok(())
    }

    pub fn generate_override_messages(&self, messagelist: &mut Vec<String>, glb: &Architecture) -> Result<()> {
        for (index, delay) in self.deadcodedelay.iter().enumerate() {
            if *delay >= 0 {
                messagelist.push(Override::generate_deadcode_delay_message(index as i32, glb)?);
            }
        }
        Ok(())
    }

    pub fn encode(&self, encoder: &mut dyn Encoder, glb: &Architecture) -> Result<()> {
        if self.forcegoto.is_empty()
            && self.deadcodedelay.is_empty()
            && self.deindirect.is_empty()
            && self.protoover.is_empty()
            && self.multistagejump.is_empty()
            && self.pcodeover.is_empty()
        {
            return Ok(());
        }
        encoder.open_element(ELEM_OVERRIDE);
        for (target, dest) in self.forcegoto.iter() {
            encoder.open_element(ELEM_FORCEGOTO);
            target.encode(encoder)?;
            dest.encode(encoder)?;
            encoder.close_element(ELEM_FORCEGOTO);
        }
        for (index, delay) in self.deadcodedelay.iter().enumerate() {
            if *delay < 0 {
                continue;
            }
            let spc = space_by_index(glb, index)?;
            encoder.open_element(ELEM_DEADCODEDELAY);
            encoder.write_space(ATTRIB_SPACE, &spc);
            encoder.write_signed_integer(ATTRIB_DELAY, *delay as i64);
            encoder.close_element(ELEM_DEADCODEDELAY);
        }
        for (addr, proto) in self.protoover.iter() {
            encoder.open_element(ELEM_PROTOOVERRIDE);
            addr.encode(encoder)?;
            proto.encode(encoder, glb)?;
            encoder.close_element(ELEM_PROTOOVERRIDE);
        }
        for addr in self.multistagejump.iter() {
            encoder.open_element(ELEM_MULTISTAGEJUMP);
            addr.encode(encoder)?;
            encoder.close_element(ELEM_MULTISTAGEJUMP);
        }
        for (addr, rec) in self.pcodeover.iter() {
            rec.encode(encoder, addr)?;
        }
        encoder.close_element(ELEM_OVERRIDE);
        Ok(())
    }

    pub fn decode(&mut self, decoder: &mut dyn Decoder, glb: &mut Architecture) -> Result<()> {
        let elem_id = decoder.open_element_expect(ELEM_OVERRIDE)?;
        loop {
            let sub_id = decoder.open_element()?;
            if sub_id == 0 {
                break;
            }
            if sub_id == ELEM_PROTOOVERRIDE {
                let callpoint = Address::decode(decoder)?;
                let mut fp = Box::new(FuncProto::new());
                let model = glb
                    .defaultfp
                    .ok_or_else(|| Error::Lowlevel("missing default prototype model".to_string()))?;
                let void_type = glb
                    .types
                    .as_mut()
                    .ok_or_else(|| Error::Lowlevel("missing type factory".to_string()))?
                    .get_type_void()?;
                fp.set_internal(model, void_type, glb);
                fp.decode(decoder, glb)?;
                self.insert_proto_override(&callpoint, fp);
            } else if sub_id == ELEM_FORCEGOTO {
                let targetpc = Address::decode(decoder)?;
                let destpc = Address::decode(decoder)?;
                self.insert_force_goto(&targetpc, &destpc);
            } else if sub_id == ELEM_DEADCODEDELAY {
                let delay = decoder.read_signed_integer_attr(ATTRIB_DELAY)? as i32;
                let spc = decoder.read_space_attr(ATTRIB_SPACE)?;
                if delay < 0 {
                    return Err(Error::Lowlevel("Bad deadcodedelay tag".to_string()));
                }
                self.insert_deadcode_delay(&spc, delay);
            } else if sub_id == ELEM_MULTISTAGEJUMP {
                let callpoint = Address::decode(decoder)?;
                self.insert_multistage_jump(&callpoint);
            } else if sub_id == ELEM_FLOW {
                let tp = decoder.read_string_attr(ATTRIB_TYPE)?;
                let addr = Address::decode(decoder)?;
                if addr.is_invalid() {
                    return Err(Error::Lowlevel("Bad flow override address".to_string()));
                }
                self.pcodeover.insert(addr, OverrideRecord::allocate_flow(&tp)?);
            } else if sub_id == ELEM_CALLDEST {
                let tp = decoder.read_string_attr(ATTRIB_TYPE)?;
                let addr = Address::decode(decoder)?;
                let dest = Address::decode(decoder)?;
                if addr.is_invalid() || dest.is_invalid() {
                    return Err(Error::Lowlevel("Bad destination override address".to_string()));
                }
                self.pcodeover
                    .insert(addr, OverrideRecord::allocate_call_dest(&tp, &dest)?);
            }
            decoder.close_element(sub_id)?;
        }
        decoder.close_element(elem_id)
    }
}
