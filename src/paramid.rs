use crate::address::{Address, ELEM_ADDR};
use crate::architecture::Architecture;
use crate::error::Result;
use crate::fspec::ProtoModel;
use crate::funcdata::Funcdata;
use crate::marshal::{
    ATTRIB_EXTRAPOP, ATTRIB_MODEL, ATTRIB_NAME, ATTRIB_VAL, ELEM_INPUT, ELEM_OUTPUT, ElementId, Encoder,
};
use crate::op::{OpId, PcodeOp};
use crate::opcodes::OpCode;
use crate::pcoderaw::VarnodeData;
use crate::types::TypeId;
use crate::varnode::{Varnode, VarnodeId};

pub const ELEM_PARAMMEASURES: ElementId = ElementId::new("parammeasures", 106);
pub const ELEM_PROTO: ElementId = ElementId::new("proto", 107);
pub const ELEM_RANK: ElementId = ElementId::new("rank", 108);

const MAXDEPTH: i32 = 10;

#[repr(i32)]
#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum ParamIdIo {
    Input = 0,
    Output = 1,
}

#[repr(i32)]
#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum ParamRank {
    DirectWriteWithoutRead = 1,
    DirectRead = 2,
    DirectWriteUnknownRead = 3,
    SubFnParam = 4,
    SubFnReturn = 5,
    Indirect = 6,
    WorstRank = 7,
}

impl ParamRank {
    pub const BESTRANK: ParamRank = ParamRank::DirectWriteWithoutRead;
    pub const DIRECTWRITEWITHREAD: ParamRank = ParamRank::DirectRead;
    pub const THISFNPARAM: ParamRank = ParamRank::SubFnParam;
    pub const THISFNRETURN: ParamRank = ParamRank::SubFnReturn;
}

#[derive(Clone, Copy, Debug)]
pub struct WalkState {
    pub best: bool,
    pub depth: i32,
    pub terminalrank: ParamRank,
}

#[derive(Clone, Debug)]
pub struct ParamMeasure {
    vndata: VarnodeData,
    vntype: TypeId,
    rank: ParamRank,
    io: ParamIdIo,
    numcalls: i32,
}

fn is_loop_in(data: &Funcdata, op: OpId, slot: i32) -> bool {
    let parent = data.op(op).get_parent().expect("p-code op has no parent block");
    data.block(parent).is_loop_in(slot)
}

impl ParamMeasure {
    pub fn new(addr: &Address, sz: i32, dt: TypeId, io_in: ParamIdIo) -> ParamMeasure {
        ParamMeasure {
            vndata: VarnodeData {
                space: addr.get_space().cloned(),
                offset: addr.get_offset(),
                size: sz as u32,
            },
            vntype: dt,
            rank: ParamRank::WorstRank,
            io: io_in,
            numcalls: 0,
        }
    }

    pub fn walkforward(&mut self, state: &mut WalkState, ignoreop: Option<OpId>, vn: VarnodeId, data: &Funcdata) {
        state.depth += 1;
        if state.depth >= MAXDEPTH {
            state.depth -= 1;
            return;
        }
        let descend: Vec<OpId> = data.vn(vn).descend().to_vec();
        let mut index = 0usize;
        while self.rank != state.terminalrank && index < descend.len() {
            let op = descend[index];
            if Some(op) != ignoreop {
                let pcode = data.op(op);
                match pcode.code() {
                    OpCode::Branch | OpCode::Branchind => {
                        if pcode.get_slot(vn) == 0 {
                            self.updaterank(ParamRank::DirectRead, state.best);
                        }
                    }
                    OpCode::Cbranch => {
                        if pcode.get_slot(vn) < 2 {
                            self.updaterank(ParamRank::DirectRead, state.best);
                        }
                    }
                    OpCode::Call | OpCode::Callind => {
                        if pcode.get_slot(vn) == 0 {
                            self.updaterank(ParamRank::DirectRead, state.best);
                        } else {
                            self.numcalls += 1;
                            self.updaterank(ParamRank::SubFnParam, state.best);
                        }
                    }
                    OpCode::Callother => {
                        self.updaterank(ParamRank::DirectRead, state.best);
                    }
                    OpCode::Return => {
                        self.updaterank(ParamRank::THISFNRETURN, state.best);
                    }
                    OpCode::Indirect => {
                        self.updaterank(ParamRank::Indirect, state.best);
                    }
                    OpCode::Multiequal => {
                        if !is_loop_in(data, op, pcode.get_slot(vn)) {
                            let out = pcode.get_out().expect("MULTIEQUAL has no output");
                            self.walkforward(state, None, out, data);
                        }
                    }
                    _ => {
                        self.updaterank(ParamRank::DirectRead, state.best);
                    }
                }
            }
            index += 1;
        }
        state.depth -= 1;
    }

    pub fn walkbackward(&mut self, state: &mut WalkState, ignoreop: Option<OpId>, vn: VarnodeId, data: &Funcdata) {
        let varnode = data.vn(vn);
        if varnode.is_input() {
            self.updaterank(ParamRank::THISFNPARAM, state.best);
            return;
        } else if !varnode.is_written() {
            self.updaterank(ParamRank::THISFNPARAM, state.best);
            return;
        }

        let op = varnode.get_def().expect("written varnode has no defining op");
        let pcode = data.op(op);
        match pcode.code() {
            OpCode::Branch | OpCode::Branchind | OpCode::Cbranch | OpCode::Call | OpCode::Callind => {}
            OpCode::Callother => {
                if pcode.get_out().is_some() {
                    self.updaterank(ParamRank::DirectRead, state.best);
                }
            }
            OpCode::Return => {
                self.updaterank(ParamRank::SubFnReturn, state.best);
            }
            OpCode::Indirect => {
                self.updaterank(ParamRank::Indirect, state.best);
            }
            OpCode::Multiequal => {
                let mut slot = 0;
                while slot < pcode.num_input() && self.rank != state.terminalrank {
                    if !is_loop_in(data, op, slot) {
                        self.walkbackward(state, Some(op), pcode.get_in(slot), data);
                    }
                    slot += 1;
                }
            }
            _ => {
                let mut pmfw = ParamMeasure::new(
                    varnode.get_addr(),
                    varnode.get_size(),
                    varnode.get_type(),
                    ParamIdIo::Input,
                );
                pmfw.calculate_rank(false, vn, ignoreop, data);
                if pmfw.get_measure() == ParamRank::DirectRead as i32 {
                    self.updaterank(ParamRank::DIRECTWRITEWITHREAD, state.best);
                } else {
                    self.updaterank(ParamRank::DirectWriteWithoutRead, state.best);
                }
            }
        }
    }

    pub fn updaterank(&mut self, rank_in: ParamRank, best: bool) {
        self.rank = if best {
            self.rank.min(rank_in)
        } else {
            self.rank.max(rank_in)
        };
    }

    pub fn calculate_rank(&mut self, best: bool, basevn: VarnodeId, ignoreop: Option<OpId>, data: &Funcdata) {
        let mut state = WalkState {
            best,
            depth: 0,
            terminalrank: ParamRank::Indirect,
        };
        if best {
            self.rank = ParamRank::WorstRank;
            state.terminalrank = if self.io == ParamIdIo::Input {
                ParamRank::DirectRead
            } else {
                ParamRank::DirectWriteWithoutRead
            };
        } else {
            self.rank = ParamRank::BESTRANK;
            state.terminalrank = ParamRank::Indirect;
        }
        self.numcalls = 0;
        if self.io == ParamIdIo::Input {
            self.walkforward(&mut state, ignoreop, basevn, data);
        } else {
            self.walkbackward(&mut state, ignoreop, basevn, data);
        }
    }

    pub fn encode(
        &self,
        encoder: &mut dyn Encoder,
        tag: ElementId,
        moredetail: bool,
        glb: &Architecture,
    ) -> Result<()> {
        encoder.open_element(tag);
        encoder.open_element(ELEM_ADDR);
        self.vndata
            .space
            .as_ref()
            .expect("parameter measure has no address space")
            .encode_attributes_size(encoder, self.vndata.offset, self.vndata.size as i32)?;
        encoder.close_element(ELEM_ADDR);
        let types = glb.types.as_deref().expect("architecture has no type factory");
        types.get(self.vntype).encode_ref(encoder, glb)?;
        if moredetail {
            encoder.open_element(ELEM_RANK);
            encoder.write_signed_integer(ATTRIB_VAL, self.rank as i64);
            encoder.close_element(ELEM_RANK);
        }
        encoder.close_element(tag);
        Ok(())
    }

    pub fn save_pretty(&self, out: &mut String, _moredetail: bool, hex: bool) {
        let number = |value: u64| {
            if hex {
                format!("{:x}", value)
            } else {
                format!("{}", value)
            }
        };
        out.push_str("  Space: ");
        out.push_str(
            self.vndata
                .space
                .as_ref()
                .expect("parameter measure has no address space")
                .get_name(),
        );
        out.push('\n');
        out.push_str(&format!("  Addr: {}\n", number(self.vndata.offset)));
        out.push_str(&format!("  Size: {}\n", number(self.vndata.size as u64)));
        let rank = self.rank as i32;
        let rank_text = if hex {
            format!("{:x}", rank)
        } else {
            format!("{}", rank)
        };
        out.push_str(&format!("  Rank: {}\n", rank_text));
    }

    pub fn get_measure(&self) -> i32 {
        self.rank as i32
    }
}

pub struct ParamIdAnalysis {
    input_param_measures: Vec<ParamMeasure>,
    output_param_measures: Vec<ParamMeasure>,
}

impl ParamIdAnalysis {
    pub fn new(fd_in: &mut Funcdata, justproto: bool, glb: &mut Architecture) -> ParamIdAnalysis {
        let mut analysis = ParamIdAnalysis {
            input_param_measures: Vec::new(),
            output_param_measures: Vec::new(),
        };
        if justproto {
            let num = fd_in.funcp.num_params(glb);
            for index in 0..num {
                let (addr, size, tp) = {
                    let param = fd_in.funcp.get_param(index, glb).expect("missing input parameter");
                    (param.get_address(glb), param.get_size(glb), param.get_type(glb))
                };
                analysis
                    .input_param_measures
                    .push(ParamMeasure::new(&addr, size, tp, ParamIdIo::Input));
                if let Some(vn) = fd_in.find_varnode_input(size, &addr) {
                    analysis
                        .input_param_measures
                        .last_mut()
                        .expect("measure was just added")
                        .calculate_rank(true, vn, None, fd_in);
                }
            }

            let (out_addr, out_size, out_type) = {
                let outparam = fd_in.funcp.get_output_ref().expect("prototype has no output parameter");
                (
                    outparam.get_address(glb),
                    outparam.get_size(glb),
                    outparam.get_type(glb),
                )
            };
            if !out_addr.is_invalid() {
                analysis.output_param_measures.push(ParamMeasure::new(
                    &out_addr,
                    out_size,
                    out_type,
                    ParamIdIo::Output,
                ));
                let mut rtn_iter = fd_in.begin_op(OpCode::Return);
                while let Some(rtn_op) = rtn_iter {
                    let rtn = fd_in.op(rtn_op);
                    if rtn.num_input() == 2
                        && let Some(ovn) = rtn.get_in_option(1)
                    {
                        analysis
                            .output_param_measures
                            .last_mut()
                            .expect("measure was just added")
                            .calculate_rank(true, ovn, Some(rtn_op), fd_in);
                        break;
                    }
                    rtn_iter = fd_in.obank.next_in_list(rtn_op, PcodeOp::CODE_LIST);
                }
            }
        } else {
            let inputs: Vec<VarnodeId> = {
                let begin = fd_in
                    .begin_def_flags(Varnode::INPUT)
                    .expect("input varnode range is valid");
                let end = fd_in
                    .end_def_flags(Varnode::INPUT)
                    .expect("input varnode range is valid");
                fd_in.vbank.def_range(&begin, &end)
            };
            for invn in inputs {
                let varnode = fd_in.vn(invn);
                analysis.input_param_measures.push(ParamMeasure::new(
                    varnode.get_addr(),
                    varnode.get_size(),
                    varnode.get_type(),
                    ParamIdIo::Input,
                ));
                analysis
                    .input_param_measures
                    .last_mut()
                    .expect("measure was just added")
                    .calculate_rank(true, invn, None, fd_in);
            }
        }
        analysis
    }

    pub fn encode(&self, encoder: &mut dyn Encoder, moredetail: bool, fd: &Funcdata, glb: &Architecture) -> Result<()> {
        encoder.open_element(ELEM_PARAMMEASURES);
        encoder.write_string(ATTRIB_NAME, fd.get_name());
        fd.get_address().encode(encoder)?;
        encoder.open_element(ELEM_PROTO);

        encoder.write_string(ATTRIB_MODEL, fd.funcp.get_model_name(glb));
        let extrapop = fd.funcp.get_extra_pop();
        if extrapop == ProtoModel::EXTRAPOP_UNKNOWN {
            encoder.write_string(ATTRIB_EXTRAPOP, "unknown");
        } else {
            encoder.write_signed_integer(ATTRIB_EXTRAPOP, extrapop as i64);
        }
        encoder.close_element(ELEM_PROTO);
        for pm in &self.input_param_measures {
            pm.encode(encoder, ELEM_INPUT, moredetail, glb)?;
        }
        for pm in &self.output_param_measures {
            pm.encode(encoder, ELEM_OUTPUT, moredetail, glb)?;
        }
        encoder.close_element(ELEM_PARAMMEASURES);
        Ok(())
    }

    pub fn save_pretty(&self, out: &mut String, moredetail: bool, fd: &Funcdata, glb: &Architecture) {
        out.push_str("Param Measures\nFunction: ");
        out.push_str(fd.get_name());
        out.push_str(&format!("\nAddress: 0x{:x}\n", fd.get_address().get_offset()));
        out.push_str("Model: ");
        out.push_str(fd.funcp.get_model_name(glb));
        out.push_str(&format!("\nExtrapop: {:x}\n", fd.funcp.get_extra_pop()));
        out.push_str(&format!("Num Params: {:x}\n", self.input_param_measures.len()));
        for pm in &self.input_param_measures {
            pm.save_pretty(out, moredetail, true);
        }
        out.push_str(&format!("Num Returns: {:x}\n", self.output_param_measures.len()));
        for pm in &self.output_param_measures {
            pm.save_pretty(out, moredetail, true);
        }
        out.push('\n');
    }
}
