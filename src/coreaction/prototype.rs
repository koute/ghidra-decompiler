use crate::action::{Action, ActionBase, ActionGroupList, RULE_ONCEPERFUNC};
use crate::address::Address;
use crate::architecture::Architecture;
use crate::bitfield::list_sort;
use crate::block::BlockId;
use crate::database::{Database, Symbol};
use crate::dynamic::DynamicHash;
use crate::error::Result;
use crate::fspec::{ParamActive, ProtoParameter};
use crate::funcdata::Funcdata;
use crate::merge::Merge;
use crate::op::{OpId, PcodeOp};
use crate::opcodes::OpCode;
use crate::pcoderaw::VarnodeData;
use crate::typeop::with_type_op;
use crate::types::{Datatype, TypeFactory, TypeId, TypeMetatype};
use crate::varnode::{Varnode, VarnodeId};

use super::{loc_step_until, symbol_table, symbol_table_mut, type_factory, type_factory_mut};

#[derive(Clone, Debug)]
pub struct InputRef {
    pub addr: Address,
    pub data_type: TypeId,
}

impl InputRef {
    pub fn new(ad: &Address, dt: TypeId) -> InputRef {
        InputRef {
            addr: ad.clone(),
            data_type: dt,
        }
    }

    pub fn less_than(&self, op2: &InputRef, types: &TypeFactory) -> bool {
        if self.addr != op2.addr {
            return self.addr < op2.addr;
        }
        if self.data_type == op2.data_type {
            return false;
        }
        let first = types.get(self.data_type);
        let second = types.get(op2.data_type);
        if first.get_size() != second.get_size() {
            return second.get_size() < first.get_size();
        }
        first.type_order(second, types) <= 0
    }

    pub fn dedup(refs: &mut Vec<InputRef>, types: &TypeFactory) {
        if refs.is_empty() {
            return;
        }
        let mut last_addr = refs[0].addr.clone();
        let mut size = types.get(refs[0].data_type).get_size();
        let mut index = 1;
        while index < refs.len() {
            if refs[index].addr.overlap(0, &last_addr, size) >= 0 {
                refs.remove(index);
            } else {
                last_addr = refs[index].addr.clone();
                size = types.get(refs[index].data_type).get_size();
                index += 1;
            }
        }
    }
}

#[derive(Clone, Debug)]
pub struct PropagationState {
    pub vn: VarnodeId,
    pub iter: usize,
    pub op: Option<OpId>,
    pub inslot: i32,
    pub slot: i32,
}

impl PropagationState {
    pub fn new(vn: VarnodeId, data: &Funcdata) -> PropagationState {
        let descend = data.vn(vn).descend();
        if !descend.is_empty() {
            let op = descend[0];
            let slot = if data.op(op).get_out().is_some() { -1 } else { 0 };
            PropagationState {
                vn,
                iter: 1,
                op: Some(op),
                inslot: data.op(op).get_slot(vn),
                slot,
            }
        } else {
            PropagationState {
                vn,
                iter: 0,
                op: data.vn(vn).get_def(),
                inslot: -1,
                slot: 0,
            }
        }
    }

    pub fn step(&mut self, data: &Funcdata) {
        self.slot += 1;
        let op = self.op.expect("propagation state has no op");
        if self.slot < data.op(op).num_input() {
            return;
        }
        let descend = data.vn(self.vn).descend();
        if self.iter < descend.len() {
            let next = descend[self.iter];
            self.iter += 1;
            self.op = Some(next);
            self.slot = if data.op(next).get_out().is_some() { -1 } else { 0 };
            self.inslot = data.op(next).get_slot(self.vn);
            return;
        }
        if self.inslot == -1 {
            self.op = None;
        } else {
            self.op = data.vn(self.vn).get_def();
        }
        self.inslot = -1;
        self.slot = 0;
    }

    pub fn valid(&self) -> bool {
        self.op.is_some()
    }
}

pub struct ActionSwitchNorm {
    pub base: ActionBase,
}

impl ActionSwitchNorm {
    pub fn new(group: &str) -> ActionSwitchNorm {
        ActionSwitchNorm {
            base: ActionBase::new(0, "switchnorm", group),
        }
    }
}

impl Action for ActionSwitchNorm {
    fn base(&self) -> &ActionBase {
        &self.base
    }

    fn base_mut(&mut self) -> &mut ActionBase {
        &mut self.base
    }

    fn clone_action(&self, grouplist: &ActionGroupList) -> Option<Box<dyn Action>> {
        if !grouplist.contains(self.get_group()) {
            return None;
        }
        Some(Box::new(ActionSwitchNorm::new(self.get_group())))
    }

    fn apply(&mut self, data: &mut Funcdata, glb: &mut Architecture) -> Result<i32> {
        let mut index = 0;
        while index < data.num_jump_tables() {
            let jt = data.get_jump_table(index);
            index += 1;
            if !data.jump_table(jt).is_labelled() {
                data.with_jump_table(jt, |table, data| -> Result<()> {
                    table.match_model(data, glb)?;
                    table.recover_labels(data, glb)?;
                    table.fold_in_normalization(data, glb)
                })?;
                self.base.count += 1;
            }
            if data.with_jump_table(jt, |table, data| table.fold_in_guards(data, glb))? {
                let structure = data.sblocks;
                data.block_clear(structure);
                self.base.count += 1;
            }
        }
        Ok(0)
    }
}

pub struct ActionNormalizeSetup {
    pub base: ActionBase,
}

impl ActionNormalizeSetup {
    pub fn new(group: &str) -> ActionNormalizeSetup {
        ActionNormalizeSetup {
            base: ActionBase::new(RULE_ONCEPERFUNC, "normalizesetup", group),
        }
    }
}

impl Action for ActionNormalizeSetup {
    fn base(&self) -> &ActionBase {
        &self.base
    }

    fn base_mut(&mut self) -> &mut ActionBase {
        &mut self.base
    }

    fn clone_action(&self, grouplist: &ActionGroupList) -> Option<Box<dyn Action>> {
        if !grouplist.contains(self.get_group()) {
            return None;
        }
        Some(Box::new(ActionNormalizeSetup::new(self.get_group())))
    }

    fn apply(&mut self, data: &mut Funcdata, glb: &mut Architecture) -> Result<i32> {
        let fp = data.get_func_proto_mut();
        fp.clear_input(glb);
        fp.set_model_lock(false);
        fp.set_output_lock(false, glb);
        Ok(0)
    }
}

pub struct ActionPrototypeTypes {
    pub base: ActionBase,
}

impl ActionPrototypeTypes {
    pub fn new(group: &str) -> ActionPrototypeTypes {
        ActionPrototypeTypes {
            base: ActionBase::new(RULE_ONCEPERFUNC, "prototypetypes", group),
        }
    }

    pub fn extend_input(
        &mut self,
        data: &mut Funcdata,
        glb: &mut Architecture,
        invn: VarnodeId,
        param: &ProtoParameter,
        topbl: BlockId,
    ) -> Result<()> {
        let mut vdata = VarnodeData::default();
        let addr = data.vn(invn).get_addr().clone();
        let size = data.vn(invn).get_size();
        let mut res = data
            .get_func_proto()
            .assumed_input_extension(&addr, size, &mut vdata, glb);
        if res == OpCode::Copy {
            return Ok(());
        }
        if res == OpCode::Piece {
            if type_factory(glb).get(param.get_type(glb)).get_metatype() == TypeMetatype::Int {
                res = OpCode::IntSext;
            } else {
                res = OpCode::IntZext;
            }
        }
        let start = data.block(topbl).get_start();
        let op = data.new_op(1, &start);
        data.new_varnode_out(vdata.size as i32, &vdata.get_addr(), op, glb)?;
        data.op_set_opcode(op, res, glb);
        data.op_set_input(op, invn, 0)?;
        data.op_insert_begin(op, topbl);
        Ok(())
    }
}

impl Action for ActionPrototypeTypes {
    fn base(&self) -> &ActionBase {
        &self.base
    }

    fn base_mut(&mut self) -> &mut ActionBase {
        &mut self.base
    }

    fn clone_action(&self, grouplist: &ActionGroupList) -> Option<Box<dyn Action>> {
        if !grouplist.contains(self.get_group()) {
            return None;
        }
        Some(Box::new(ActionPrototypeTypes::new(self.get_group())))
    }

    fn apply(&mut self, data: &mut Funcdata, glb: &mut Architecture) -> Result<i32> {
        let evalfp = match glb.evalfp_current {
            Some(model) => Some(model),
            None => glb.defaultfp,
        };
        if !data.get_func_proto().is_model_locked() && !data.get_func_proto().has_matching_model(evalfp) {
            data.get_func_proto_mut().set_model(evalfp, glb);
        }
        if data.get_func_proto().has_this_pointer() {
            data.prepare_this_pointer(glb)?;
        }
        let mut iter = data.begin_op(OpCode::Return);
        while let Some(op) = iter {
            iter = data.obank.next_in_list(op, PcodeOp::CODE_LIST);
            if data.op(op).is_dead() {
                continue;
            }
            let in0 = data.op(op).get_in(0);
            if !data.vn(in0).is_constant() {
                let size = data.vn(in0).get_size();
                let vn = data.new_constant(size, 0, glb);
                data.op_set_input(op, vn, 0)?;
            }
        }
        if data.get_func_proto().is_output_locked(glb) {
            let (outtype, outsize, outaddr) = {
                let outparam = data
                    .get_func_proto()
                    .get_output_ref()
                    .expect("prototype has no output parameter");
                (
                    outparam.get_type(glb),
                    outparam.get_size(glb),
                    outparam.get_address(glb),
                )
            };
            if type_factory(glb).get(outtype).get_metatype() != TypeMetatype::Void {
                let mut iter = data.begin_op(OpCode::Return);
                while let Some(op) = iter {
                    iter = data.obank.next_in_list(op, PcodeOp::CODE_LIST);
                    if data.op(op).is_dead() {
                        continue;
                    }
                    if data.op(op).get_halt_type() != 0 {
                        continue;
                    }
                    let vn = data.new_varnode(outsize, &outaddr, None, glb)?;
                    let numinput = data.op(op).num_input();
                    data.op_insert_input(op, vn, numinput)?;
                    data.vn_update_type_locked(vn, outtype, true, true, glb);
                }
            }
        } else {
            data.init_active_output(glb);
        }
        let spc = glb
            .manager
            .get_default_code_space()
            .expect("missing default code space");
        if spc.is_truncated() {
            let stackspc = glb.manager.get_stack_space();
            let topbl = if data.block(data.bblocks).get_size() > 0 {
                Some(data.block(data.bblocks).get_block(0))
            } else {
                None
            };
            if let (Some(stackspc), Some(topbl)) = (stackspc, topbl) {
                for index in 0..stackspc.num_spacebase() {
                    let full_reg = stackspc.get_spacebase_full(index)?;
                    let trunc_reg = stackspc.get_spacebase(index)?;
                    let invn = data.new_varnode(trunc_reg.size as i32, &trunc_reg.get_addr(), None, glb)?;
                    let invn = data.set_input_varnode(invn, glb)?;
                    let start = data.block(topbl).get_start();
                    let extop = data.new_op(1, &start);
                    data.new_varnode_out(full_reg.size as i32, &full_reg.get_addr(), extop, glb)?;
                    data.op_set_opcode(extop, OpCode::IntZext, glb);
                    data.op_set_input(extop, invn, 0)?;
                    data.op_insert_begin(extop, topbl);
                }
            }
        }
        if data.get_func_proto_mut().is_input_locked(glb) {
            let ptr_size = if spc.is_truncated() {
                spc.get_addr_size() as i32
            } else {
                0
            };
            let topbl = if data.block(data.bblocks).get_size() > 0 {
                Some(data.block(data.bblocks).get_block(0))
            } else {
                None
            };
            let numparams = data.get_func_proto().num_params(glb);
            for index in 0..numparams {
                let param = data
                    .get_func_proto_mut()
                    .get_param(index, glb)
                    .expect("parameter is missing")
                    .clone();
                let paddr = param.get_address(glb);
                let vn = data.new_varnode(param.get_size(glb), &paddr, None, glb)?;
                let vn = data.set_input_varnode(vn, glb)?;
                data.vn_mut(vn).set_locked_input();
                if let Some(topbl) = topbl {
                    self.extend_input(data, glb, vn, &param, topbl)?;
                }
                if ptr_size > 0 {
                    let ct = type_factory(glb).get(param.get_type(glb));
                    if ct.get_metatype() == TypeMetatype::Ptr && ct.get_size() == ptr_size {
                        data.vn_mut(vn).set_ptr_flow();
                    }
                }
            }
        }
        Ok(0)
    }
}

pub struct ActionInputPrototype {
    pub base: ActionBase,
}

impl ActionInputPrototype {
    pub fn new(group: &str) -> ActionInputPrototype {
        ActionInputPrototype {
            base: ActionBase::new(RULE_ONCEPERFUNC, "inputprototype", group),
        }
    }

    pub fn gather_param_spacebase_refs(
        &mut self,
        refs: &mut Vec<InputRef>,
        data: &mut Funcdata,
        glb: &mut Architecture,
    ) -> Result<()> {
        let localscope = data.get_scope_local().expect("function has no local scope");
        let spcid = symbol_table(glb).scope(localscope).local_data().get_space_id().clone();
        let spcvn = match data.find_spacebase_input(&spcid)? {
            Some(spcvn) => spcvn,
            None => return Ok(()),
        };
        let spctype = data.vn(spcvn).get_type();
        if type_factory(glb).get(spctype).get_metatype() != TypeMetatype::Ptr {
            return Ok(());
        }
        let sbtype = type_factory(glb).get(spctype).get_ptr_to();
        if type_factory(glb).get(sbtype).get_metatype() != TypeMetatype::Spacebase {
            return Ok(());
        }
        let param_range = data.get_func_proto().get_param_range(glb).clone();
        let descend = data.vn(spcvn).descend().to_vec();
        for op in descend {
            let opc = data.op(op).code();
            let addr;
            if opc == OpCode::Ptrsub {
                let vn = data.op(op).get_in(1);
                let point = data.op(op).get_addr().clone();
                addr = type_factory(glb).get(sbtype).get_address(
                    data.vn(vn).get_offset(),
                    data.vn(vn).get_size(),
                    &point,
                    glb,
                );
            } else if opc == OpCode::Ptradd {
                let vn = data.op(op).get_in(1);
                if data.vn(vn).is_constant() {
                    let off = data
                        .vn(vn)
                        .get_offset()
                        .wrapping_mul(data.vn(data.op(op).get_in(2)).get_offset());
                    let point = data.op(op).get_addr().clone();
                    addr = type_factory(glb)
                        .get(sbtype)
                        .get_address(off, data.vn(vn).get_size(), &point, glb);
                } else {
                    continue;
                }
            } else {
                continue;
            }
            if param_range.in_range(&addr, 1) {
                let outvn = data.op(op).get_out().expect("op has no output");
                let mut dt = data.vn_get_type_def_facing(outvn, glb);
                if type_factory(glb).get(dt).get_metatype() == TypeMetatype::Ptr {
                    dt = type_factory(glb).get(dt).get_ptr_to();
                    if type_factory(glb).get(dt).get_size() == 0 {
                        dt = type_factory_mut(glb).get_base(1, TypeMetatype::Unknown)?;
                    }
                } else {
                    dt = type_factory_mut(glb).get_base(1, TypeMetatype::Unknown)?;
                }
                let dtsize = type_factory(glb).get(dt).get_size();
                if !data.get_func_proto_mut().possible_input_param(&addr, dtsize, glb) {
                    let mut v_data = VarnodeData::default();
                    if data
                        .get_func_proto_mut()
                        .unjustified_input_param(&addr, dtsize, &mut v_data, glb)
                        && v_data.get_addr() == addr
                        && v_data.size as i32 > dtsize
                    {
                        dt = type_factory_mut(glb).get_base(v_data.size as i32, TypeMetatype::Unknown)?;
                    }
                }
                refs.push(InputRef::new(&addr, dt));
            }
        }
        let types = type_factory(glb);
        *refs = list_sort(std::mem::take(refs), &mut |first: &InputRef, second: &InputRef| {
            first.less_than(second, types)
        });
        InputRef::dedup(refs, types);
        Ok(())
    }

    pub fn mark_active_input_refs(
        &mut self,
        active: &mut ParamActive,
        refs: &mut [InputRef],
        type_list: &mut Vec<TypeId>,
        data: &mut Funcdata,
        glb: &mut Architecture,
    ) {
        for reference in refs.iter() {
            let size = type_factory(glb).get(reference.data_type).get_size();
            if data.has_input_intersection(size, &reference.addr) {
                continue;
            }
            if !data
                .get_func_proto_mut()
                .possible_input_param(&reference.addr, size, glb)
            {
                continue;
            }
            let slot = active.get_num_trials();
            active.register_trial(&reference.addr, size);
            type_list.push(reference.data_type);
            active.get_trial_mut(slot).mark_active();
        }
    }

    pub fn add_ref_only_symbols(
        &mut self,
        refs: &mut [InputRef],
        data: &mut Funcdata,
        glb: &mut Architecture,
    ) -> Result<()> {
        let localscope = data.get_scope_local().expect("function has no local scope");
        for reference in refs.iter() {
            let size = type_factory(glb).get(reference.data_type).get_size();
            if symbol_table(glb)
                .scope_find_overlap(localscope, &reference.addr, size)
                .is_some()
            {
                continue;
            }
            Database::scope_add_symbol_at(
                glb,
                localscope,
                "",
                Some(reference.data_type),
                &reference.addr,
                &Address::invalid(),
            )?;
        }
        Ok(())
    }
}

impl Action for ActionInputPrototype {
    fn base(&self) -> &ActionBase {
        &self.base
    }

    fn base_mut(&mut self) -> &mut ActionBase {
        &mut self.base
    }

    fn clone_action(&self, grouplist: &ActionGroupList) -> Option<Box<dyn Action>> {
        if !grouplist.contains(self.get_group()) {
            return None;
        }
        Some(Box::new(ActionInputPrototype::new(self.get_group())))
    }

    fn apply(&mut self, data: &mut Funcdata, glb: &mut Architecture) -> Result<i32> {
        let mut type_list: Vec<TypeId> = Vec::new();
        let mut active = ParamActive::new(false);
        let mut input_refs: Vec<InputRef> = Vec::new();
        let localscope = data.get_scope_local().expect("function has no local scope");
        symbol_table_mut(glb).scope_clear_category(localscope, Symbol::FAKE_INPUT as i32);
        data.get_func_proto_mut().clear_unlocked_input(glb);
        if symbol_table(glb).scope(localscope).local_data().has_open_param_refs() {
            self.gather_param_spacebase_refs(&mut input_refs, data, glb)?;
        }
        if !data.get_func_proto_mut().is_input_locked(glb) {
            let begin = data.begin_def_flags(Varnode::INPUT)?;
            let end = data.end_def_flags(Varnode::INPUT)?;
            let use_high = data.is_high_on();
            for vn in data.vbank.def_range(&begin, &end) {
                let addr = data.vn(vn).get_addr().clone();
                let size = data.vn(vn).get_size();
                if !data.get_func_proto_mut().possible_input_param(&addr, size, glb) {
                    continue;
                }
                let slot = active.get_num_trials();
                if data.vn(vn).is_persist() {
                    let mut disjoint_size = 0;
                    let disjoint_addr = data.find_disjoint_cover(vn, &mut disjoint_size);
                    let ct = if disjoint_size == size {
                        if use_high {
                            let high = data.vn(vn).get_high()?;
                            data.high_get_type(high, glb)
                        } else {
                            data.vn(vn).get_type()
                        }
                    } else {
                        type_factory_mut(glb).get_base(disjoint_size, TypeMetatype::Unknown)?
                    };
                    active.register_trial(&disjoint_addr, disjoint_size);
                    type_list.push(ct);
                } else {
                    active.register_trial(&addr, size);
                    let ct = if use_high {
                        let high = data.vn(vn).get_high()?;
                        data.high_get_type(high, glb)
                    } else {
                        data.vn(vn).get_type()
                    };
                    type_list.push(ct);
                }
                if !data.vn(vn).has_no_descend() {
                    active.get_trial_mut(slot).mark_active();
                }
            }
            self.mark_active_input_refs(&mut active, &mut input_refs, &mut type_list, data, glb);
            data.get_func_proto_mut().resolve_model(&mut active, glb)?;
            data.get_func_proto().derive_input_map(&mut active, glb)?;
            for index in 0..active.get_num_trials() {
                let (unref, used, size, addr) = {
                    let paramtrial = active.get_trial(index);
                    (
                        paramtrial.is_unref(),
                        paramtrial.is_used(),
                        paramtrial.get_size(),
                        paramtrial.get_address().clone(),
                    )
                };
                if unref && used {
                    if data.has_input_intersection(size, &addr) {
                        active.get_trial_mut(index).mark_no_use();
                    } else {
                        let slot = type_list.len() as i32;
                        type_list.push(type_factory_mut(glb).get_base(size, TypeMetatype::Unknown)?);
                        active.get_trial_mut(index).set_slot(slot + 1);
                    }
                }
            }
            let mut proto = std::mem::take(&mut data.funcp);
            let result = proto.update_input_types(data, &type_list, &mut active, glb);
            data.funcp = proto;
            result?;
        }
        self.add_ref_only_symbols(&mut input_refs, data, glb)?;
        data.clear_dead_varnodes()?;
        Ok(0)
    }
}

pub struct ActionOutputPrototype {
    pub base: ActionBase,
}

impl ActionOutputPrototype {
    pub fn new(group: &str) -> ActionOutputPrototype {
        ActionOutputPrototype {
            base: ActionBase::new(RULE_ONCEPERFUNC, "outputprototype", group),
        }
    }
}

impl Action for ActionOutputPrototype {
    fn base(&self) -> &ActionBase {
        &self.base
    }

    fn base_mut(&mut self) -> &mut ActionBase {
        &mut self.base
    }

    fn clone_action(&self, grouplist: &ActionGroupList) -> Option<Box<dyn Action>> {
        if !grouplist.contains(self.get_group()) {
            return None;
        }
        Some(Box::new(ActionOutputPrototype::new(self.get_group())))
    }

    fn apply(&mut self, data: &mut Funcdata, glb: &mut Architecture) -> Result<i32> {
        let (type_locked, size_type_locked) = {
            let outparam = data
                .get_func_proto()
                .get_output_ref()
                .expect("prototype has no output parameter");
            (outparam.is_type_locked(glb), outparam.is_size_type_locked(glb))
        };
        if !type_locked || size_type_locked {
            let mut vnlist: Vec<VarnodeId> = Vec::new();
            if let Some(op) = data.get_first_return_op() {
                for slot in 1..data.op(op).num_input() {
                    vnlist.push(data.op(op).get_in(slot));
                }
            }
            let mut proto = std::mem::take(&mut data.funcp);
            let result = if data.is_high_on() {
                proto.update_output_types(&vnlist, data, glb)
            } else {
                proto.update_output_no_types(&vnlist, data, glb)
            };
            data.funcp = proto;
            result?;
        }
        Ok(0)
    }
}

pub struct ActionUnjustifiedParams {
    pub base: ActionBase,
}

impl ActionUnjustifiedParams {
    pub fn new(group: &str) -> ActionUnjustifiedParams {
        ActionUnjustifiedParams {
            base: ActionBase::new(0, "unjustparams", group),
        }
    }
}

impl Action for ActionUnjustifiedParams {
    fn base(&self) -> &ActionBase {
        &self.base
    }

    fn base_mut(&mut self) -> &mut ActionBase {
        &mut self.base
    }

    fn clone_action(&self, grouplist: &ActionGroupList) -> Option<Box<dyn Action>> {
        if !grouplist.contains(self.get_group()) {
            return None;
        }
        Some(Box::new(ActionUnjustifiedParams::new(self.get_group())))
    }

    fn apply(&mut self, data: &mut Funcdata, glb: &mut Architecture) -> Result<i32> {
        let mut iter = data.begin_def_flags(Varnode::INPUT)?;
        let mut enditer = data.end_def_flags(Varnode::INPUT)?;
        while iter != enditer {
            let vn = data.vbank.def_at(&iter).expect("definition iterator is invalid");
            iter = data.vbank.def_next(&iter);
            let mut vdata = VarnodeData::default();
            let addr = data.vn(vn).get_addr().clone();
            let size = data.vn(vn).get_size();
            if !data
                .get_func_proto_mut()
                .unjustified_input_param(&addr, size, &mut vdata, glb)
            {
                continue;
            }
            loop {
                let begiter = data.begin_def_flags(Varnode::INPUT)?;
                let mut overlaps = false;
                let earlier = data.vbank.def_range(&begiter, &iter);
                for &prior in earlier.iter().rev() {
                    let same_space = match (data.vn(prior).get_space(), vdata.space.as_ref()) {
                        (Some(first), Some(second)) => first.get_index() == second.get_index(),
                        (None, None) => true,
                        _ => false,
                    };
                    if !same_space {
                        continue;
                    }
                    let prior_offset = data.vn(prior).get_offset();
                    let offset = prior_offset
                        .wrapping_add(data.vn(prior).get_size() as i64 as u64)
                        .wrapping_sub(1);
                    if offset >= vdata.offset && prior_offset < vdata.offset {
                        overlaps = true;
                        let endpoint = vdata.offset.wrapping_add(vdata.size as u64);
                        vdata.offset = prior_offset;
                        vdata.size = endpoint.wrapping_sub(vdata.offset) as u32;
                    }
                }
                if !overlaps {
                    break;
                }
                let container_addr = vdata.get_addr();
                let container_size = vdata.size as i32;
                let newcontainer =
                    data.get_func_proto_mut()
                        .unjustified_input_param(&container_addr, container_size, &mut vdata, glb);
                if !newcontainer {
                    break;
                }
            }
            let container_addr = vdata.get_addr();
            data.adjust_input_varnodes(&container_addr, vdata.size as i32, glb)?;
            iter = data.begin_def_addr(Varnode::INPUT, &container_addr)?;
            enditer = data.end_def_flags(Varnode::INPUT)?;
            self.base.count += 1;
        }
        Ok(0)
    }
}

pub struct ActionHideShadow {
    pub base: ActionBase,
}

impl ActionHideShadow {
    pub fn new(group: &str) -> ActionHideShadow {
        ActionHideShadow {
            base: ActionBase::new(RULE_ONCEPERFUNC, "hideshadow", group),
        }
    }
}

impl Action for ActionHideShadow {
    fn base(&self) -> &ActionBase {
        &self.base
    }

    fn base_mut(&mut self) -> &mut ActionBase {
        &mut self.base
    }

    fn clone_action(&self, grouplist: &ActionGroupList) -> Option<Box<dyn Action>> {
        if !grouplist.contains(self.get_group()) {
            return None;
        }
        Some(Box::new(ActionHideShadow::new(self.get_group())))
    }

    fn apply(&mut self, data: &mut Funcdata, _glb: &mut Architecture) -> Result<i32> {
        let enditer = data.end_def_flags(Varnode::WRITTEN)?;
        let begin = data.begin_def();
        let varnodes = data.vbank.def_range(&begin, &enditer);
        for &vn in varnodes.iter() {
            let high = data.vn(vn).get_high()?;
            if data.high(high).is_mark() {
                continue;
            }
            if Merge::hide_shadows(data, high)? {
                self.base.count += 1;
            }
            data.high_mut(high).set_mark();
        }
        for &vn in varnodes.iter() {
            let high = data.vn(vn).get_high()?;
            data.high_mut(high).clear_mark();
        }
        Ok(0)
    }
}

fn process_dynamic_entries(data: &mut Funcdata, glb: &mut Architecture, late: bool) -> Result<i32> {
    let localmap = data.get_scope_local().expect("function has no local scope");
    let mut dhash = DynamicHash::new();
    let mut changes = 0;
    let mut next = symbol_table(glb).scope_dynamic_entries(localmap).first().copied();
    while let Some(entry) = next {
        let following = {
            let entries = symbol_table(glb).scope_dynamic_entries(localmap);
            let position = entries.iter().position(|candidate| *candidate == entry);
            position.and_then(|position| entries.get(position + 1).copied())
        };
        let changed = if late {
            data.attempt_dynamic_mapping_late(entry, &mut dhash, glb)?
        } else {
            data.attempt_dynamic_mapping(entry, &mut dhash, glb)?
        };
        if changed {
            changes += 1;
        }
        next = following;
    }
    Ok(changes)
}

pub struct ActionDynamicMapping {
    pub base: ActionBase,
}

impl ActionDynamicMapping {
    pub fn new(group: &str) -> ActionDynamicMapping {
        ActionDynamicMapping {
            base: ActionBase::new(0, "dynamicmapping", group),
        }
    }
}

impl Action for ActionDynamicMapping {
    fn base(&self) -> &ActionBase {
        &self.base
    }

    fn base_mut(&mut self) -> &mut ActionBase {
        &mut self.base
    }

    fn clone_action(&self, grouplist: &ActionGroupList) -> Option<Box<dyn Action>> {
        if !grouplist.contains(self.get_group()) {
            return None;
        }
        Some(Box::new(ActionDynamicMapping::new(self.get_group())))
    }

    fn apply(&mut self, data: &mut Funcdata, glb: &mut Architecture) -> Result<i32> {
        self.base.count += process_dynamic_entries(data, glb, false)?;
        Ok(0)
    }
}

pub struct ActionDynamicSymbols {
    pub base: ActionBase,
}

impl ActionDynamicSymbols {
    pub fn new(group: &str) -> ActionDynamicSymbols {
        ActionDynamicSymbols {
            base: ActionBase::new(RULE_ONCEPERFUNC, "dynamicsymbols", group),
        }
    }
}

impl Action for ActionDynamicSymbols {
    fn base(&self) -> &ActionBase {
        &self.base
    }

    fn base_mut(&mut self) -> &mut ActionBase {
        &mut self.base
    }

    fn clone_action(&self, grouplist: &ActionGroupList) -> Option<Box<dyn Action>> {
        if !grouplist.contains(self.get_group()) {
            return None;
        }
        Some(Box::new(ActionDynamicSymbols::new(self.get_group())))
    }

    fn apply(&mut self, data: &mut Funcdata, glb: &mut Architecture) -> Result<i32> {
        self.base.count += process_dynamic_entries(data, glb, true)?;
        Ok(0)
    }
}

pub struct ActionPrototypeWarnings {
    pub base: ActionBase,
}

impl ActionPrototypeWarnings {
    pub fn new(group: &str) -> ActionPrototypeWarnings {
        ActionPrototypeWarnings {
            base: ActionBase::new(RULE_ONCEPERFUNC, "prototypewarnings", group),
        }
    }
}

impl Action for ActionPrototypeWarnings {
    fn base(&self) -> &ActionBase {
        &self.base
    }

    fn base_mut(&mut self) -> &mut ActionBase {
        &mut self.base
    }

    fn clone_action(&self, grouplist: &ActionGroupList) -> Option<Box<dyn Action>> {
        if !grouplist.contains(self.get_group()) {
            return None;
        }
        Some(Box::new(ActionPrototypeWarnings::new(self.get_group())))
    }

    fn apply(&mut self, data: &mut Funcdata, glb: &mut Architecture) -> Result<i32> {
        let mut overridemessages: Vec<String> = Vec::new();
        data.localoverride
            .generate_override_messages(&mut overridemessages, glb)?;
        for message in overridemessages.iter() {
            data.warning_header(message, glb);
        }
        if data.get_func_proto().has_input_errors() {
            data.warning_header(
                "Cannot assign parameter locations for this function: Prototype may be inaccurate",
                glb,
            );
        }
        if data.get_func_proto().has_output_errors() {
            data.warning_header(
                "Cannot assign location of return value for this function: Return value may be inaccurate",
                glb,
            );
        }
        if data.get_func_proto().is_model_unknown(glb) {
            let mut message = String::from("Unknown calling convention");
            if data.get_func_proto().print_model_in_decl(glb) {
                message.push_str(": ");
                message.push_str(data.get_func_proto().get_model_name(glb));
            }
            if !data.get_func_proto().has_custom_storage()
                && (data.get_func_proto_mut().is_input_locked(glb) || data.get_func_proto().is_output_locked(glb))
            {
                message.push_str(" -- yet parameter storage is locked");
            }
            data.warning_header(&message, glb);
        }
        let numcalls = data.num_calls();
        for index in 0..numcalls {
            let fc = data.get_call_specs(index);
            let fd_name = data
                .call_spec(fc)
                .get_funcdata()
                .map(|sym| symbol_table(glb).symbol(sym).get_name().to_string());
            let entry = data.call_spec(fc).get_entry_address().clone();
            if data.call_spec(fc).has_input_errors() {
                let message = format!(
                    "Cannot assign parameter location for function {}: Prototype may be inaccurate",
                    fd_name.as_deref().unwrap_or("<indirect>")
                );
                data.warning(&message, &entry, glb);
            }
            if data.call_spec(fc).has_output_errors() {
                let message = format!(
                    "Cannot assign location of return value for function {}: Return value may be inaccurate",
                    fd_name.as_deref().unwrap_or("<indirect>")
                );
                data.warning(&message, &entry, glb);
            }
        }
        Ok(0)
    }
}

pub struct ActionInternalStorage {
    pub base: ActionBase,
}

impl ActionInternalStorage {
    pub fn new(group: &str) -> ActionInternalStorage {
        ActionInternalStorage {
            base: ActionBase::new(RULE_ONCEPERFUNC, "internalstorage", group),
        }
    }
}

impl Action for ActionInternalStorage {
    fn base(&self) -> &ActionBase {
        &self.base
    }

    fn base_mut(&mut self) -> &mut ActionBase {
        &mut self.base
    }

    fn clone_action(&self, grouplist: &ActionGroupList) -> Option<Box<dyn Action>> {
        if !grouplist.contains(self.get_group()) {
            return None;
        }
        Some(Box::new(ActionInternalStorage::new(self.get_group())))
    }

    fn apply(&mut self, data: &mut Funcdata, glb: &mut Architecture) -> Result<i32> {
        let storage: Vec<VarnodeData> = data.get_func_proto().get_internal_storage(glb).to_vec();
        for vdata in storage.iter() {
            let addr = vdata.get_addr();
            let size = vdata.size as i32;
            let viter = data.begin_loc_size(size, &addr);
            let endviter = data.end_loc_size(size, &addr);
            for vn in data.vbank.loc_range(&viter, &endviter) {
                let descend = data.vn(vn).descend().to_vec();
                for op in descend {
                    if data.op(op).code() == OpCode::Store && data.vn_is_eventual_constant(vn, 3, 0) {
                        data.op_mut(op).set_store_unmapped();
                    }
                }
            }
        }
        Ok(0)
    }
}

pub struct ActionInferTypes {
    pub base: ActionBase,
    pub localcount: i32,
}

impl ActionInferTypes {
    pub fn new(group: &str) -> ActionInferTypes {
        ActionInferTypes {
            base: ActionBase::new(0, "infertypes", group),
            localcount: 0,
        }
    }

    fn temp_type(data: &Funcdata, vn: VarnodeId) -> TypeId {
        data.vn(vn).get_temp_type().expect("varnode has no temporary data-type")
    }

    pub fn build_localtypes(data: &mut Funcdata, glb: &mut Architecture) -> Result<()> {
        let begin = data.begin_loc();
        let end = data.end_loc();
        for vn in data.vbank.loc_range(&begin, &end) {
            if data.vn(vn).is_annotation() {
                continue;
            }
            if !data.vn(vn).is_written() && data.vn(vn).has_no_descend() {
                continue;
            }
            let mut needs_block = false;
            let entry = data.vn(vn).get_symbol_entry();
            let mut use_entry = false;
            if let Some(entry) = entry {
                let symbol = symbol_table(glb).entry(entry).get_symbol();
                if !data.vn(vn).is_type_lock() && symbol_table(glb).symbol(symbol).is_type_locked() {
                    use_entry = true;
                }
            }
            let ct = if use_entry {
                let entry = entry.expect("symbol entry is missing");
                let db = symbol_table(glb);
                let symbol = db.entry(entry).get_symbol();
                let mut cur_off = db.entry(entry).get_offset();
                if !db.entry(entry).is_dynamic() {
                    let delta = data
                        .vn(vn)
                        .get_addr()
                        .get_offset()
                        .wrapping_sub(db.entry(entry).get_addr().get_offset());
                    cur_off = cur_off.wrapping_add(delta as i32);
                }
                let symtype = db.symbol(symbol).get_type().expect("symbol has no data-type");
                let size = data.vn(vn).get_size();
                let piece = type_factory_mut(glb).get_exact_piece(symtype, cur_off, size)?;
                match piece {
                    Some(piece) if type_factory(glb).get(piece).get_metatype() != TypeMetatype::Unknown => piece,
                    _ => data.vn_get_local_type(vn, &mut needs_block, glb)?,
                }
            } else {
                data.vn_get_local_type(vn, &mut needs_block, glb)?
            };
            if needs_block {
                data.vn_mut(vn).set_stop_up_propagation();
            }
            data.vn_mut(vn).set_temp_type(Some(ct));
        }
        Ok(())
    }

    pub fn write_back(data: &mut Funcdata, _glb: &mut Architecture) -> bool {
        let mut change = false;
        let begin = data.begin_loc();
        let end = data.end_loc();
        for vn in data.vbank.loc_range(&begin, &end) {
            if data.vn(vn).is_annotation() {
                continue;
            }
            if !data.vn(vn).is_written() && data.vn(vn).has_no_descend() {
                continue;
            }
            let ct = ActionInferTypes::temp_type(data, vn);
            if data.vn_update_type(vn, ct) {
                change = true;
            }
        }
        change
    }

    pub fn propagate_type_edge(
        data: &mut Funcdata,
        glb: &mut Architecture,
        op: OpId,
        inslot: i32,
        outslot: i32,
    ) -> Result<bool> {
        if inslot == outslot {
            return Ok(false);
        }
        let invn = if inslot == -1 {
            data.op(op).get_out().expect("op has no output")
        } else {
            data.op(op).get_in(inslot)
        };
        let mut alttype = ActionInferTypes::temp_type(data, invn);
        if type_factory(glb).get(alttype).needs_resolution() {
            let res_type = Datatype::resolve_in_flow(alttype, op, inslot, data, glb)?;
            if !data.op(op).is_marker() {
                alttype = res_type;
            }
        }
        let outvn = if outslot < 0 {
            data.op(op).get_out().expect("op has no output")
        } else {
            let outvn = data.op(op).get_in(outslot);
            if data.vn(outvn).is_annotation() {
                return Ok(false);
            }
            outvn
        };
        if data.vn(outvn).is_type_lock() {
            return Ok(false);
        }
        if data.vn(outvn).stops_up_propagation() && outslot >= 0 {
            return Ok(false);
        }
        if type_factory(glb).get(alttype).get_metatype() == TypeMetatype::Bool && data.vn(outvn).get_nz_mask() > 1 {
            return Ok(false);
        }
        let opc = data.op(op).code();
        let newtype = with_type_op(glb, opc, |top, glb| {
            top.propagate_type(alttype, op, invn, outvn, inslot, outslot, data, glb)
        })?;
        let newtype = match newtype {
            Some(newtype) => newtype,
            None => return Ok(false),
        };
        let types = type_factory(glb);
        let outtemp = ActionInferTypes::temp_type(data, outvn);
        if 0 > types.get(newtype).type_order(types.get(outtemp), types) {
            data.vn_mut(outvn).set_temp_type(Some(newtype));
            return Ok(!data.vn(outvn).is_mark());
        }
        Ok(false)
    }

    pub fn propagate_one_type(data: &mut Funcdata, glb: &mut Architecture, vn: VarnodeId) -> Result<()> {
        let mut state: Vec<PropagationState> = Vec::new();
        state.push(PropagationState::new(vn, data));
        data.vn_mut(vn).set_mark();
        while let Some(top) = state.last().cloned() {
            if !top.valid() {
                data.vn_mut(top.vn).clear_mark();
                state.pop();
                continue;
            }
            let op = top.op.expect("propagation state has no op");
            if ActionInferTypes::propagate_type_edge(data, glb, op, top.inslot, top.slot)? {
                let nextvn = if top.slot == -1 {
                    data.op(op).get_out().expect("op has no output")
                } else {
                    data.op(op).get_in(top.slot)
                };
                state.last_mut().expect("propagation stack is empty").step(data);
                state.push(PropagationState::new(nextvn, data));
                data.vn_mut(nextvn).set_mark();
            } else {
                state.last_mut().expect("propagation stack is empty").step(data);
            }
        }
        Ok(())
    }

    pub fn propagate_ref(data: &mut Funcdata, glb: &mut Architecture, vn: VarnodeId, addr: &Address) -> Result<()> {
        let ct = ActionInferTypes::temp_type(data, vn);
        if type_factory(glb).get(ct).get_metatype() != TypeMetatype::Ptr {
            return Ok(());
        }
        let ct = type_factory(glb).get(ct).get_ptr_to();
        let meta = type_factory(glb).get(ct).get_metatype();
        if meta == TypeMetatype::Spacebase {
            return Ok(());
        }
        if meta == TypeMetatype::Unknown {
            return Ok(());
        }
        let off = addr.get_offset();
        let ctsize = type_factory(glb).get(ct).get_size();
        let endaddr = addr.add(ctsize as i64);
        let enditer = if endaddr.get_offset() < off {
            let spc = addr.get_space().expect("address has no space").clone();
            data.end_loc_space(&spc, glb)
        } else {
            data.end_loc_addr(&endaddr, glb)
        };
        let mut iter = data.begin_loc_addr(addr);
        let mut lastoff: u64 = 0;
        let mut lastsize = ctsize;
        let mut lastct = Some(ct);
        while let Some((curvn, next)) = loc_step_until(data, &iter, &enditer) {
            iter = next;
            if data.vn(curvn).is_annotation() {
                continue;
            }
            if !data.vn(curvn).is_written() && data.vn(curvn).has_no_descend() {
                continue;
            }
            if data.vn(curvn).is_type_lock() {
                continue;
            }
            if data.vn(curvn).get_symbol_entry().is_some() {
                continue;
            }
            let curoff = data.vn(curvn).get_offset().wrapping_sub(off);
            let cursize = data.vn(curvn).get_size();
            if curoff.wrapping_add(cursize as i64 as u64) > ctsize as i64 as u64 {
                continue;
            }
            if cursize != lastsize || curoff != lastoff {
                lastoff = curoff;
                lastsize = cursize;
                lastct = type_factory_mut(glb).get_exact_piece(ct, curoff as i32, cursize)?;
            }
            let piece = match lastct {
                Some(piece) => piece,
                None => continue,
            };
            let types = type_factory(glb);
            let curtemp = ActionInferTypes::temp_type(data, curvn);
            if 0 > types.get(piece).type_order(types.get(curtemp), types) {
                data.vn_mut(curvn).set_temp_type(Some(piece));
                ActionInferTypes::propagate_one_type(data, glb, curvn)?;
            }
        }
        Ok(())
    }

    pub fn propagate_spacebase_ref(data: &mut Funcdata, glb: &mut Architecture, spcvn: VarnodeId) -> Result<()> {
        let spctype = data.vn(spcvn).get_type();
        if type_factory(glb).get(spctype).get_metatype() != TypeMetatype::Ptr {
            return Ok(());
        }
        let sbtype = type_factory(glb).get(spctype).get_ptr_to();
        if type_factory(glb).get(sbtype).get_metatype() != TypeMetatype::Spacebase {
            return Ok(());
        }
        let descend = data.vn(spcvn).descend().to_vec();
        for op in descend {
            let point = data.op(op).get_addr().clone();
            match data.op(op).code() {
                OpCode::Copy => {
                    let vn = data.op(op).get_in(0);
                    let addr = type_factory(glb)
                        .get(sbtype)
                        .get_address(0, data.vn(vn).get_size(), &point, glb);
                    let outvn = data.op(op).get_out().expect("COPY has no output");
                    ActionInferTypes::propagate_ref(data, glb, outvn, &addr)?;
                }
                OpCode::IntAdd | OpCode::Ptrsub => {
                    let vn = data.op(op).get_in(1);
                    if data.vn(vn).is_constant() {
                        let addr = type_factory(glb).get(sbtype).get_address(
                            data.vn(vn).get_offset(),
                            data.vn(vn).get_size(),
                            &point,
                            glb,
                        );
                        let outvn = data.op(op).get_out().expect("op has no output");
                        ActionInferTypes::propagate_ref(data, glb, outvn, &addr)?;
                    }
                }
                OpCode::Ptradd => {
                    let vn = data.op(op).get_in(1);
                    if data.vn(vn).is_constant() {
                        let off = data
                            .vn(vn)
                            .get_offset()
                            .wrapping_mul(data.vn(data.op(op).get_in(2)).get_offset());
                        let addr = type_factory(glb)
                            .get(sbtype)
                            .get_address(off, data.vn(vn).get_size(), &point, glb);
                        let outvn = data.op(op).get_out().expect("PTRADD has no output");
                        ActionInferTypes::propagate_ref(data, glb, outvn, &addr)?;
                    }
                }
                _ => {}
            }
        }
        Ok(())
    }

    pub fn canonical_return_op(data: &Funcdata, glb: &Architecture) -> Option<OpId> {
        let types = type_factory(glb);
        let mut res: Option<OpId> = None;
        let mut bestdt: Option<TypeId> = None;
        let mut iter = data.begin_op(OpCode::Return);
        while let Some(retop) = iter {
            iter = data.obank.next_in_list(retop, PcodeOp::CODE_LIST);
            if data.op(retop).is_dead() {
                continue;
            }
            if data.op(retop).get_halt_type() != 0 {
                continue;
            }
            if data.op(retop).num_input() > 1 {
                let vn = data.op(retop).get_in(1);
                let ct = ActionInferTypes::temp_type(data, vn);
                match bestdt {
                    None => {
                        res = Some(retop);
                        bestdt = Some(ct);
                    }
                    Some(best) => {
                        if types.get(ct).type_order(types.get(best), types) < 0 {
                            res = Some(retop);
                            bestdt = Some(ct);
                        }
                    }
                }
            }
        }
        res
    }

    pub fn propagate_across_returns(data: &mut Funcdata, glb: &mut Architecture) -> Result<()> {
        if data.get_func_proto().is_output_locked(glb) {
            return Ok(());
        }
        let op = match ActionInferTypes::canonical_return_op(data, glb) {
            Some(op) => op,
            None => return Ok(()),
        };
        let base_vn = data.op(op).get_in(1);
        let ct = ActionInferTypes::temp_type(data, base_vn);
        let base_size = data.vn(base_vn).get_size();
        let is_bool = type_factory(glb).get(ct).get_metatype() == TypeMetatype::Bool;
        let mut iter = data.begin_op(OpCode::Return);
        while let Some(retop) = iter {
            iter = data.obank.next_in_list(retop, PcodeOp::CODE_LIST);
            if retop == op {
                continue;
            }
            if data.op(retop).is_dead() {
                continue;
            }
            if data.op(retop).get_halt_type() != 0 {
                continue;
            }
            if data.op(retop).num_input() > 1 {
                let vn = data.op(retop).get_in(1);
                if data.vn(vn).get_size() != base_size {
                    continue;
                }
                if is_bool && data.vn(vn).get_nz_mask() > 1 {
                    continue;
                }
                if data.vn(vn).get_temp_type() == Some(ct) {
                    continue;
                }
                data.vn_mut(vn).set_temp_type(Some(ct));
                ActionInferTypes::propagate_one_type(data, glb, vn)?;
            }
        }
        Ok(())
    }
}

impl Action for ActionInferTypes {
    fn base(&self) -> &ActionBase {
        &self.base
    }

    fn base_mut(&mut self) -> &mut ActionBase {
        &mut self.base
    }

    fn clone_action(&self, grouplist: &ActionGroupList) -> Option<Box<dyn Action>> {
        if !grouplist.contains(self.get_group()) {
            return None;
        }
        Some(Box::new(ActionInferTypes::new(self.get_group())))
    }

    fn reset(&mut self, _data: &mut Funcdata, _glb: &mut Architecture) {
        self.localcount = 0;
    }

    fn apply(&mut self, data: &mut Funcdata, glb: &mut Architecture) -> Result<i32> {
        if !data.has_type_recovery_started() {
            return Ok(0);
        }
        if self.localcount >= 7 {
            if self.localcount == 7 {
                data.warning_header("Type propagation algorithm not settling", glb);
                data.set_type_recovery_exceeded();
                self.localcount += 1;
            }
            return Ok(0);
        }
        let localscope = data.get_scope_local().expect("function has no local scope");
        Database::local_apply_type_recommendations(glb, data, localscope)?;
        ActionInferTypes::build_localtypes(data, glb)?;
        let begin = data.begin_loc();
        let end = data.end_loc();
        let mut iter = begin;
        while let Some((vn, next)) = loc_step_until(data, &iter, &end) {
            iter = next;
            if data.vn(vn).is_annotation() {
                continue;
            }
            if !data.vn(vn).is_written() && data.vn(vn).has_no_descend() {
                continue;
            }
            ActionInferTypes::propagate_one_type(data, glb, vn)?;
        }
        ActionInferTypes::propagate_across_returns(data, glb)?;
        let spcid = symbol_table(glb).scope(localscope).local_data().get_space_id().clone();
        if let Some(spcvn) = data.find_spacebase_input(&spcid)? {
            ActionInferTypes::propagate_spacebase_ref(data, glb, spcvn)?;
        }
        if ActionInferTypes::write_back(data, glb) {
            self.localcount += 1;
        }
        Ok(0)
    }
}
