mod markup;
mod prototype;

pub use markup::*;
pub use prototype::*;

use std::ops::Bound;

use crate::action::{Action, ActionBase, ActionGroupList, RULE_ONCEPERFUNC};
use crate::address::{Address, bit_transitions, calc_mask};
use crate::architecture::Architecture;
use crate::block::BlockId;
use crate::database::{Database, EntryId};
use crate::double::SplitVarnode;
use crate::error::{Error, Result};
use crate::expression::functional_equality_level;
use crate::fspec::{CallSpecId, EffectRecord, FuncCallSpecs, FuncProto, ParamActive, ProtoModel};
use crate::funcdata::{AncestorRealistic, Funcdata};
use crate::globalcontext::TrackedSet;
use crate::merge::Merge;
use crate::op::{OpId, PcodeOp};
use crate::opcodes::OpCode;
use crate::oplist::LinkedNode;
use crate::overrides::Override;
use crate::pcoderaw::VarnodeData;
use crate::space::{AddrSpace, SpaceRef, SpaceType};
use crate::subflow::LaneDivide;
use crate::transform::{LaneDescription, LanedRegister};
use crate::types::{TypeFactory, TypeMetatype};
use crate::varmap::AliasChecker;
use crate::varnode::{LocIter, Varnode, VarnodeId};

pub(crate) fn type_factory(glb: &Architecture) -> &TypeFactory {
    glb.types.as_deref().expect("missing type factory")
}

pub(crate) fn type_factory_mut(glb: &mut Architecture) -> &mut TypeFactory {
    glb.types.as_deref_mut().expect("missing type factory")
}

pub(crate) fn symbol_table(glb: &Architecture) -> &Database {
    glb.symboltab.as_deref().expect("missing symbol table")
}

pub(crate) fn symbol_table_mut(glb: &mut Architecture) -> &mut Database {
    glb.symboltab.as_deref_mut().expect("missing symbol table")
}

pub(crate) fn loc_step(data: &Funcdata, iter: &LocIter) -> Option<(VarnodeId, LocIter)> {
    let (_, vn, next) = data.vbank.loc_entry_from(iter.as_ref()?)?;
    Some((vn, next))
}

pub(crate) fn loc_step_until(data: &Funcdata, iter: &LocIter, enditer: &LocIter) -> Option<(VarnodeId, LocIter)> {
    let (current, vn, next) = data.vbank.loc_entry_from(iter.as_ref()?)?;
    if enditer.as_ref().is_some_and(|endkey| current >= *endkey) {
        return None;
    }
    Some((vn, next))
}

pub(crate) fn space_type_of(data: &Funcdata, vn: VarnodeId) -> Option<SpaceType> {
    data.vn(vn).get_space().map(|spc| spc.get_type())
}

pub(crate) fn basic_prev(data: &Funcdata, op: OpId) -> Option<OpId> {
    data.obank.ops.get(op).links(PcodeOp::BASIC_LIST).prev
}

pub(crate) fn basic_next(data: &Funcdata, op: OpId) -> Option<OpId> {
    data.obank.ops.get(op).links(PcodeOp::BASIC_LIST).next
}

#[derive(Clone, Copy, Debug, Default)]
pub struct StackEqn {
    pub var1: i32,
    pub var2: i32,
    pub rhs: i32,
}

impl StackEqn {
    pub fn compare(first: &StackEqn, second: &StackEqn) -> bool {
        first.var1 < second.var1
    }
}

#[derive(Clone, Debug, Default)]
pub struct StackSolver {
    pub eqs: Vec<StackEqn>,
    pub guess: Vec<StackEqn>,
    pub vnlist: Vec<VarnodeId>,
    pub companion: Vec<i32>,
    pub spacebase: Address,
    pub soln: Vec<i32>,
    pub missedvariables: i32,
}

impl StackSolver {
    pub fn duplicate(&mut self) {
        let size = self.eqs.len();
        for index in 0..size {
            let eqn = StackEqn {
                var1: self.eqs[index].var2,
                var2: self.eqs[index].var1,
                rhs: self.eqs[index].rhs.wrapping_neg(),
            };
            self.eqs.push(eqn);
        }
        self.eqs.sort_by_key(|first| first.var1);
    }

    pub fn propagate(&mut self, varnum: i32, val: i32) {
        if self.soln[varnum as usize] != 65535 {
            return;
        }
        self.soln[varnum as usize] = val;
        let mut workstack: Vec<i32> = Vec::with_capacity(self.soln.len());
        workstack.push(varnum);
        while let Some(current) = workstack.pop() {
            let mut top = self.eqs.partition_point(|eqn| eqn.var1 < current);
            while top < self.eqs.len() && self.eqs[top].var1 == current {
                let var2 = self.eqs[top].var2;
                if self.soln[var2 as usize] == 65535 {
                    self.soln[var2 as usize] = self.soln[current as usize].wrapping_sub(self.eqs[top].rhs);
                    workstack.push(var2);
                }
                top += 1;
            }
        }
    }

    pub fn solve(&mut self) {
        self.soln.clear();
        self.soln.resize(self.vnlist.len(), 65535);
        self.duplicate();
        self.propagate(0, 0);
        let size = self.guess.len();
        let mut lastcount = size as i32 + 2;
        loop {
            let mut count = 0;
            for index in 0..size {
                let var1 = self.guess[index].var1;
                let var2 = self.guess[index].var2;
                let sol1 = self.soln[var1 as usize];
                let sol2 = self.soln[var2 as usize];
                if sol1 != 65535 && sol2 == 65535 {
                    self.propagate(var2, sol1.wrapping_sub(self.guess[index].rhs));
                } else if sol1 == 65535 && sol2 != 65535 {
                    self.propagate(var1, sol2.wrapping_add(self.guess[index].rhs));
                } else if sol1 == 65535 && sol2 == 65535 {
                    count += 1;
                }
            }
            if count == lastcount {
                break;
            }
            lastcount = count;
            if count <= 0 {
                break;
            }
        }
    }

    fn variable_index(&self, data: &Funcdata, othervn: VarnodeId) -> i32 {
        self.vnlist.partition_point(|vn| data.vn_compare_pointers(*vn, othervn)) as i32
    }

    pub fn build(&mut self, data: &Funcdata, id: &SpaceRef, spcbase: i32) -> Result<()> {
        let spacebasedata = id.get_spacebase(spcbase)?;
        self.spacebase = Address::from_parts(spacebasedata.space.clone(), spacebasedata.offset);
        let begiter = data.begin_loc_size(spacebasedata.size as i32, &self.spacebase);
        let enditer = data.end_loc_size(spacebasedata.size as i32, &self.spacebase);
        for vn in data.vbank.loc_range(&begiter, &enditer) {
            if data.vn(vn).is_free() {
                break;
            }
            self.vnlist.push(vn);
            self.companion.push(-1);
        }
        self.missedvariables = 0;
        if self.vnlist.is_empty() {
            return Ok(());
        }
        if !data.vn(self.vnlist[0]).is_input() {
            return Err(Error::Lowlevel("Input value of stackpointer is not used".to_string()));
        }
        for index in 1..self.vnlist.len() {
            let vn = self.vnlist[index];
            let op = data.vn(vn).get_def().expect("stack pointer varnode has no defining op");
            let opc = data.op(op).code();
            if opc == OpCode::IntAdd || opc == OpCode::IntAnd {
                let mut othervn = data.op(op).get_in(0);
                let mut constvn = data.op(op).get_in(1);
                if data.vn(othervn).is_constant() {
                    constvn = othervn;
                    othervn = data.op(op).get_in(1);
                }
                if !data.vn(constvn).is_constant() {
                    self.missedvariables += 1;
                    continue;
                }
                if *data.vn(othervn).get_addr() != self.spacebase {
                    self.missedvariables += 1;
                    continue;
                }
                let eqn = StackEqn {
                    var1: index as i32,
                    var2: self.variable_index(data, othervn),
                    rhs: if opc == OpCode::IntAdd {
                        data.vn(constvn).get_offset() as i32
                    } else {
                        0
                    },
                };
                self.eqs.push(eqn);
            } else if opc == OpCode::Copy {
                let othervn = data.op(op).get_in(0);
                if *data.vn(othervn).get_addr() != self.spacebase {
                    self.missedvariables += 1;
                    continue;
                }
                let eqn = StackEqn {
                    var1: index as i32,
                    var2: self.variable_index(data, othervn),
                    rhs: 0,
                };
                self.eqs.push(eqn);
            } else if opc == OpCode::Indirect {
                let othervn = data.op(op).get_in(0);
                if *data.vn(othervn).get_addr() != self.spacebase {
                    self.missedvariables += 1;
                    continue;
                }
                let mut eqn = StackEqn {
                    var1: index as i32,
                    var2: self.variable_index(data, othervn),
                    rhs: 0,
                };
                self.companion[index] = eqn.var2;
                let iopvn = data.op(op).get_in(1);
                if data.vn(iopvn).get_space().map(|spc| spc.get_type()) == Some(SpaceType::Iop) {
                    let iop = PcodeOp::get_op_from_const(data.vn(iopvn).get_addr());
                    if let Some(fc) = data.get_call_specs_op(iop)
                        && data.call_spec(fc).get_extra_pop() != ProtoModel::EXTRAPOP_UNKNOWN
                    {
                        eqn.rhs = data.call_spec(fc).get_extra_pop();
                        self.eqs.push(eqn);
                        continue;
                    }
                }
                eqn.rhs = 4;
                self.guess.push(eqn);
            } else if opc == OpCode::Multiequal {
                for slot in 0..data.op(op).num_input() {
                    let othervn = data.op(op).get_in(slot);
                    if *data.vn(othervn).get_addr() != self.spacebase {
                        self.missedvariables += 1;
                        continue;
                    }
                    let eqn = StackEqn {
                        var1: index as i32,
                        var2: self.variable_index(data, othervn),
                        rhs: 0,
                    };
                    self.eqs.push(eqn);
                }
            } else {
                self.missedvariables += 1;
            }
        }
        Ok(())
    }

    pub fn get_num_variables(&self) -> i32 {
        self.vnlist.len() as i32
    }

    pub fn get_variable(&self, index: i32) -> VarnodeId {
        self.vnlist[index as usize]
    }

    pub fn get_companion(&self, index: i32) -> i32 {
        self.companion[index as usize]
    }

    pub fn get_solution(&self, index: i32) -> i32 {
        self.soln[index as usize]
    }
}

pub struct ActionStart {
    pub base: ActionBase,
}

impl ActionStart {
    pub fn new(group: &str) -> ActionStart {
        ActionStart {
            base: ActionBase::new(0, "start", group),
        }
    }
}

impl Action for ActionStart {
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
        Some(Box::new(ActionStart::new(self.get_group())))
    }

    fn apply(&mut self, data: &mut Funcdata, glb: &mut Architecture) -> Result<i32> {
        data.start_processing(glb)?;
        Ok(0)
    }
}

pub struct ActionStop {
    pub base: ActionBase,
}

impl ActionStop {
    pub fn new(group: &str) -> ActionStop {
        ActionStop {
            base: ActionBase::new(0, "stop", group),
        }
    }
}

impl Action for ActionStop {
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
        Some(Box::new(ActionStop::new(self.get_group())))
    }

    fn apply(&mut self, data: &mut Funcdata, glb: &mut Architecture) -> Result<i32> {
        data.stop_processing(glb);
        Ok(0)
    }
}

pub struct ActionStartCleanUp {
    pub base: ActionBase,
}

impl ActionStartCleanUp {
    pub fn new(group: &str) -> ActionStartCleanUp {
        ActionStartCleanUp {
            base: ActionBase::new(0, "startcleanup", group),
        }
    }
}

impl Action for ActionStartCleanUp {
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
        Some(Box::new(ActionStartCleanUp::new(self.get_group())))
    }

    fn apply(&mut self, data: &mut Funcdata, _glb: &mut Architecture) -> Result<i32> {
        data.start_clean_up();
        Ok(0)
    }
}

pub struct ActionStartTypes {
    pub base: ActionBase,
}

impl ActionStartTypes {
    pub fn new(group: &str) -> ActionStartTypes {
        ActionStartTypes {
            base: ActionBase::new(0, "starttypes", group),
        }
    }
}

impl Action for ActionStartTypes {
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
        Some(Box::new(ActionStartTypes::new(self.get_group())))
    }

    fn reset(&mut self, data: &mut Funcdata, _glb: &mut Architecture) {
        data.set_type_recovery(true);
    }

    fn apply(&mut self, data: &mut Funcdata, _glb: &mut Architecture) -> Result<i32> {
        if data.start_type_recovery() {
            self.base.count += 1;
        }
        Ok(0)
    }
}

pub struct ActionStackPtrFlow {
    pub base: ActionBase,
    pub stackspace: Option<SpaceRef>,
    pub analysis_finished: bool,
}

impl ActionStackPtrFlow {
    pub fn new(group: &str, stackspace: Option<SpaceRef>) -> ActionStackPtrFlow {
        ActionStackPtrFlow {
            base: ActionBase::new(0, "stackptrflow", group),
            stackspace,
            analysis_finished: false,
        }
    }

    pub fn analyze_extra_pop(
        data: &mut Funcdata,
        glb: &mut Architecture,
        stackspace: &SpaceRef,
        spcbase: i32,
    ) -> Result<()> {
        let myfp = match glb.evalfp_called {
            Some(model) => Some(model),
            None => glb.defaultfp,
        };
        let myfp = myfp.expect("missing default prototype model");
        if glb.proto_models.get(myfp).get_extra_pop() != ProtoModel::EXTRAPOP_UNKNOWN {
            return Ok(());
        }
        let mut solver = StackSolver::default();
        if let Err(err) = solver.build(data, stackspace, spcbase) {
            if err.is_lowlevel() {
                let message = format!("Stack frame is not setup normally: {}", err.explain());
                data.warning_header(&message, glb);
                return Ok(());
            }
            return Err(err);
        }
        if solver.get_num_variables() == 0 {
            return Ok(());
        }
        solver.solve();
        let invn = solver.get_variable(0);
        let mut warningprinted = false;
        for index in 1..solver.get_num_variables() {
            let vn = solver.get_variable(index);
            let soln = solver.get_solution(index);
            if soln == 65535 {
                if !warningprinted {
                    let message = format!("Unable to track spacebase fully for {}", stackspace.get_name());
                    data.warning_header(&message, glb);
                    warningprinted = true;
                }
                continue;
            }
            let op = data.vn(vn).get_def().expect("stack pointer varnode has no defining op");
            if data.op(op).code() == OpCode::Indirect {
                let iopvn = data.op(op).get_in(1);
                if data.vn(iopvn).get_space().map(|spc| spc.get_type()) == Some(SpaceType::Iop) {
                    let iop = PcodeOp::get_op_from_const(data.vn(iopvn).get_addr());
                    if let Some(fc) = data.get_call_specs_op(iop) {
                        let mut soln2 = 0;
                        let comp = solver.get_companion(index);
                        if comp >= 0 {
                            soln2 = solver.get_solution(comp);
                        }
                        data.call_spec_mut(fc).set_effective_extra_pop(soln.wrapping_sub(soln2));
                    }
                }
            }
            let mut paramlist: Vec<VarnodeId> = Vec::new();
            paramlist.push(invn);
            let size = data.vn(invn).get_size();
            let constvn = data.new_constant(size, (soln as i64 as u64) & calc_mask(size), glb);
            paramlist.push(constvn);
            data.op_set_opcode(op, OpCode::IntAdd, glb);
            data.op_set_all_input(op, &paramlist)?;
        }
        Ok(())
    }

    pub fn is_stack_relative(data: &Funcdata, spcbasein: VarnodeId, vn: VarnodeId, constval: &mut u64) -> bool {
        if spcbasein == vn {
            *constval = 0;
            return true;
        }
        if !data.vn(vn).is_written() {
            return false;
        }
        let addop = data.vn(vn).get_def().expect("written varnode has no defining op");
        if data.op(addop).code() != OpCode::IntAdd {
            return false;
        }
        if data.op(addop).get_in(0) != spcbasein {
            return false;
        }
        let constvn = data.op(addop).get_in(1);
        if !data.vn(constvn).is_constant() {
            return false;
        }
        *constval = data.vn(constvn).get_offset();
        true
    }

    pub fn adjust_load(data: &mut Funcdata, glb: &mut Architecture, loadop: OpId, storeop: OpId) -> Result<bool> {
        let mut vn = data.op(storeop).get_in(2);
        if data.vn(vn).is_constant() {
            let size = data.vn(vn).get_size();
            let offset = data.vn(vn).get_offset();
            vn = data.new_constant(size, offset, glb);
        } else if data.vn(vn).is_free() {
            return Ok(false);
        }
        data.op_remove_input(loadop, 1);
        data.op_set_opcode(loadop, OpCode::Copy, glb);
        data.op_set_input(loadop, vn, 0)?;
        Ok(true)
    }

    pub fn repair(
        data: &mut Funcdata,
        glb: &mut Architecture,
        id: &SpaceRef,
        spcbasein: VarnodeId,
        loadop: OpId,
        constz: u64,
    ) -> Result<i32> {
        let loadout = data.op(loadop).get_out().expect("LOAD has no output");
        let loadsize = data.vn(loadout).get_size();
        let mut curblock = data.op(loadop).get_parent().expect("LOAD is not in a basic block");
        let mut begiter = data.block(curblock).get_op_list().front();
        let mut iter = Some(loadop);
        loop {
            if iter == begiter {
                if data.block(curblock).size_in() != 1 {
                    return Ok(0);
                }
                curblock = data.block(curblock).get_in(0);
                begiter = data.block(curblock).get_op_list().front();
                iter = None;
                continue;
            }
            iter = match iter {
                None => data.block(curblock).get_op_list().back(),
                Some(cur) => basic_prev(data, cur),
            };
            let curop = iter.expect("basic block op list is inconsistent");
            if data.op(curop).is_call() {
                return Ok(0);
            }
            if data.op(curop).code() == OpCode::Store {
                let ptrvn = data.op(curop).get_in(1);
                let datavn = data.op(curop).get_in(2);
                let mut constnew: u64 = 0;
                if ActionStackPtrFlow::is_stack_relative(data, spcbasein, ptrvn, &mut constnew) {
                    let datasize = data.vn(datavn).get_size();
                    if constnew == constz && loadsize == datasize {
                        if ActionStackPtrFlow::adjust_load(data, glb, loadop, curop)? {
                            return Ok(1);
                        }
                        return Ok(0);
                    } else if constnew <= constz.wrapping_add((loadsize - 1) as i64 as u64)
                        && constnew.wrapping_add((datasize - 1) as i64 as u64) >= constz
                    {
                        return Ok(0);
                    }
                } else {
                    return Ok(0);
                }
            } else if let Some(outvn) = data.op(curop).get_out()
                && data.vn(outvn).get_space().map(|spc| spc.get_index()) == Some(id.get_index())
            {
                return Ok(0);
            }
        }
    }

    pub fn check_clog(data: &mut Funcdata, glb: &mut Architecture, id: &SpaceRef, spcbase: i32) -> Result<i32> {
        let spacebasedata = id.get_spacebase(spcbase)?;
        let spacebase = Address::from_parts(spacebasedata.space.clone(), spacebasedata.offset);
        let mut clogcount = 0;
        let begiter = data.begin_loc_size(spacebasedata.size as i32, &spacebase);
        let enditer = data.end_loc_size(spacebasedata.size as i32, &spacebase);
        let candidates = data.vbank.loc_range(&begiter, &enditer);
        if candidates.is_empty() {
            return Ok(clogcount);
        }
        let spcbasein = candidates[0];
        if !data.vn(spcbasein).is_input() {
            return Ok(clogcount);
        }
        for &outvn in candidates.iter().skip(1) {
            if !data.vn(outvn).is_written() {
                continue;
            }
            let addop = data.vn(outvn).get_def().expect("written varnode has no defining op");
            if data.op(addop).code() != OpCode::IntAdd {
                continue;
            }
            let mut yvn = data.op(addop).get_in(1);
            if !data.vn(yvn).is_written() {
                continue;
            }
            let mut xvn = data.op(addop).get_in(0);
            let mut constx: u64 = 0;
            if !ActionStackPtrFlow::is_stack_relative(data, spcbasein, xvn, &mut constx) {
                xvn = yvn;
                yvn = data.op(addop).get_in(0);
                if !ActionStackPtrFlow::is_stack_relative(data, spcbasein, xvn, &mut constx) {
                    continue;
                }
            }
            let mut loadop = match data.vn(yvn).get_def() {
                Some(def) => def,
                None => continue,
            };
            if data.op(loadop).code() == OpCode::IntMult {
                let constvn = data.op(loadop).get_in(1);
                if !data.vn(constvn).is_constant() {
                    continue;
                }
                if data.vn(constvn).get_offset() != calc_mask(data.vn(constvn).get_size()) {
                    continue;
                }
                yvn = data.op(loadop).get_in(0);
                if !data.vn(yvn).is_written() {
                    continue;
                }
                loadop = data.vn(yvn).get_def().expect("written varnode has no defining op");
            }
            if data.op(loadop).code() != OpCode::Load {
                continue;
            }
            let ptrvn = data.op(loadop).get_in(1);
            let mut constz: u64 = 0;
            if !ActionStackPtrFlow::is_stack_relative(data, spcbasein, ptrvn, &mut constz) {
                continue;
            }
            clogcount += ActionStackPtrFlow::repair(data, glb, id, spcbasein, loadop, constz)?;
        }
        Ok(clogcount)
    }
}

impl Action for ActionStackPtrFlow {
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
        Some(Box::new(ActionStackPtrFlow::new(
            self.get_group(),
            self.stackspace.clone(),
        )))
    }

    fn reset(&mut self, _data: &mut Funcdata, _glb: &mut Architecture) {
        self.analysis_finished = false;
    }

    fn apply(&mut self, data: &mut Funcdata, glb: &mut Architecture) -> Result<i32> {
        if self.analysis_finished {
            return Ok(0);
        }
        let stackspace = match &self.stackspace {
            Some(spc) => spc.clone(),
            None => {
                self.analysis_finished = true;
                return Ok(0);
            }
        };
        let numchange = ActionStackPtrFlow::check_clog(data, glb, &stackspace, 0)?;
        if numchange > 0 {
            self.base.count += 1;
        }
        if numchange == 0 {
            ActionStackPtrFlow::analyze_extra_pop(data, glb, &stackspace, 0)?;
            self.analysis_finished = true;
        }
        Ok(0)
    }
}

pub struct ActionLaneDivide {
    pub base: ActionBase,
}

impl ActionLaneDivide {
    pub fn new(group: &str) -> ActionLaneDivide {
        ActionLaneDivide {
            base: ActionBase::new(RULE_ONCEPERFUNC, "lanedivide", group),
        }
    }

    pub fn collect_lane_sizes(
        &mut self,
        data: &Funcdata,
        vn: VarnodeId,
        allowed_lanes: &LanedRegister,
        check_lanes: &mut LanedRegister,
    ) {
        let descend = data.vn(vn).descend().to_vec();
        let mut iter = 0;
        let mut step = 0;
        if iter == descend.len() {
            step = 1;
        }
        while step < 2 {
            let cur_size;
            if step == 0 {
                let op = descend[iter];
                iter += 1;
                if iter == descend.len() {
                    step = 1;
                }
                if data.op(op).code() != OpCode::Subpiece {
                    continue;
                }
                let out = data.op(op).get_out().expect("SUBPIECE has no output");
                cur_size = data.vn(out).get_size();
            } else {
                step = 2;
                if !data.vn(vn).is_written() {
                    continue;
                }
                let op = data.vn(vn).get_def().expect("written varnode has no defining op");
                if data.op(op).code() != OpCode::Piece {
                    continue;
                }
                let mut size = data.vn(data.op(op).get_in(0)).get_size();
                let tmp_size = data.vn(data.op(op).get_in(1)).get_size();
                if tmp_size < size {
                    size = tmp_size;
                }
                cur_size = size;
            }
            if allowed_lanes.allowed_lane(cur_size) {
                check_lanes.add_lane_size(cur_size);
            }
        }
    }

    pub fn process_varnode(
        &mut self,
        data: &mut Funcdata,
        glb: &mut Architecture,
        vn: VarnodeId,
        laned_register: &LanedRegister,
        mode: i32,
    ) -> Result<bool> {
        let mut check_lanes = LanedRegister::new();
        let allow_downcast = mode > 0;
        if mode < 2 {
            self.collect_lane_sizes(data, vn, laned_register, &mut check_lanes);
        } else {
            let default_size = type_factory(glb).get_size_of_pointer();
            if default_size == 4 && laned_register.allowed_lane(4) {
                check_lanes.add_lane_size(4);
            } else if laned_register.allowed_lane(8) {
                check_lanes.add_lane_size(8);
            } else if laned_register.allowed_lane(4) {
                check_lanes.add_lane_size(4);
            }
        }
        let enditer = check_lanes.end();
        let mut iter = check_lanes.begin();
        while iter != enditer {
            let cur_size = iter.get();
            let description = LaneDescription::new(laned_register.get_whole_size(), cur_size);
            let mut lane_divide = LaneDivide::new(data, glb, vn, &description, allow_downcast);
            if lane_divide.do_trace(data, glb) {
                lane_divide.manager.apply(data, glb)?;
                self.base.count += 1;
                return Ok(true);
            }
            iter.increment();
        }
        Ok(false)
    }
}

impl Action for ActionLaneDivide {
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
        Some(Box::new(ActionLaneDivide::new(self.get_group())))
    }

    fn apply(&mut self, data: &mut Funcdata, glb: &mut Architecture) -> Result<i32> {
        data.set_laned_reg_generated();
        for mode in 0..3 {
            let mut all_storage_processed = true;
            let mut entry = data.laned_map.iter().next().map(|(key, value)| (key.clone(), *value));
            while let Some((storage, laned_index)) = entry {
                let laned_reg = glb.lanerecords[laned_index].clone();
                let addr = storage.get_addr();
                let size = storage.size as i32;
                let mut viter = data.begin_loc_size(size, &addr);
                let mut venditer = data.end_loc_size(size, &addr);
                let mut all_varnodes_processed = true;
                while viter != venditer {
                    let vn = data.vbank.loc_at(&viter).expect("varnode location iterator is invalid");
                    if data.vn(vn).has_no_descend() {
                        viter = data.vbank.loc_next(&viter);
                        continue;
                    }
                    if self.process_varnode(data, glb, vn, &laned_reg, mode)? {
                        viter = data.begin_loc_size(size, &addr);
                        venditer = data.end_loc_size(size, &addr);
                        all_varnodes_processed = true;
                    } else {
                        viter = data.vbank.loc_next(&viter);
                        all_varnodes_processed = false;
                    }
                }
                if !all_varnodes_processed {
                    all_storage_processed = false;
                }
                entry = data
                    .laned_map
                    .range((Bound::Excluded(storage), Bound::Unbounded))
                    .next()
                    .map(|(key, value)| (key.clone(), *value));
            }
            if all_storage_processed {
                break;
            }
        }
        data.clear_laned_access_map();
        Ok(0)
    }
}

pub struct ActionSegmentize {
    pub base: ActionBase,
    pub localcount: i32,
}

impl ActionSegmentize {
    pub fn new(group: &str) -> ActionSegmentize {
        ActionSegmentize {
            base: ActionBase::new(0, "segmentize", group),
            localcount: 0,
        }
    }
}

impl Action for ActionSegmentize {
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
        Some(Box::new(ActionSegmentize::new(self.get_group())))
    }

    fn reset(&mut self, _data: &mut Funcdata, _glb: &mut Architecture) {
        self.localcount = 0;
    }

    fn apply(&mut self, data: &mut Funcdata, glb: &mut Architecture) -> Result<i32> {
        let numops = glb.userops.num_segment_ops();
        if numops == 0 {
            return Ok(0);
        }
        if self.localcount > 0 {
            return Ok(0);
        }
        self.localcount = 1;
        let mut bindlist: Vec<Option<VarnodeId>> = vec![None, None];
        for index in 0..numops {
            let segdef = match glb.userops.get_segment_op(index) {
                Some(segdef) => segdef.clone(),
                None => continue,
            };
            let spc = segdef
                .as_segment()
                .and_then(|segment| segment.get_space().cloned())
                .expect("segment op has no address space");
            let uindex = segdef.useropindex;
            let mut iter = data.begin_op(OpCode::Callother);
            while let Some(segroot) = iter {
                iter = data.obank.next_in_list(segroot, PcodeOp::CODE_LIST);
                if data.op(segroot).is_dead() {
                    continue;
                }
                if data.vn(data.op(segroot).get_in(0)).get_offset() != uindex as i64 as u64 {
                    continue;
                }
                if !segdef.unify(data, segroot, &mut bindlist, glb) {
                    let mut err = String::from("Segment op in wrong form at ");
                    data.op(segroot).get_addr().print_raw(&mut err);
                    return Err(Error::Lowlevel(err));
                }
                if segdef.get_num_variable_terms() == 1 {
                    bindlist[0] = Some(data.new_constant(4, 0, glb));
                }
                data.op_set_opcode(segroot, OpCode::Segmentop, glb);
                let spcvn = data.new_varnode_space(&spc, glb);
                data.op_set_input(segroot, spcvn, 0)?;
                data.op_set_input(segroot, bindlist[0].expect("segment op binding is missing"), 1)?;
                data.op_set_input(segroot, bindlist[1].expect("segment op binding is missing"), 2)?;
                let mut slot = data.op(segroot).num_input() - 1;
                while slot > 2 {
                    data.op_remove_input(segroot, slot);
                    slot -= 1;
                }
                self.base.count += 1;
            }
        }
        Ok(0)
    }
}

pub struct ActionForceGoto {
    pub base: ActionBase,
}

impl ActionForceGoto {
    pub fn new(group: &str) -> ActionForceGoto {
        ActionForceGoto {
            base: ActionBase::new(0, "forcegoto", group),
        }
    }
}

impl Action for ActionForceGoto {
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
        Some(Box::new(ActionForceGoto::new(self.get_group())))
    }

    fn apply(&mut self, data: &mut Funcdata, glb: &mut Architecture) -> Result<i32> {
        Override::apply_force_goto(data, glb)?;
        Ok(0)
    }
}

pub struct ActionMultiCse {
    pub base: ActionBase,
}

impl ActionMultiCse {
    pub fn new(group: &str) -> ActionMultiCse {
        ActionMultiCse {
            base: ActionBase::new(0, "multicse", group),
        }
    }

    pub fn preferred_output(data: &Funcdata, out1: VarnodeId, out2: VarnodeId) -> bool {
        for &op in data.vn(out1).descend() {
            if data.op(op).code() == OpCode::Return {
                return false;
            }
        }
        for &op in data.vn(out2).descend() {
            if data.op(op).code() == OpCode::Return {
                return true;
            }
        }
        if !data.vn(out1).is_addr_tied() {
            if data.vn(out2).is_addr_tied() {
                return true;
            } else if space_type_of(data, out1) == Some(SpaceType::Internal)
                && space_type_of(data, out2) != Some(SpaceType::Internal)
            {
                return true;
            }
        }
        false
    }

    fn skip_copy(data: &Funcdata, vn: VarnodeId) -> VarnodeId {
        if data.vn(vn).is_written() {
            let def = data.vn(vn).get_def().expect("written varnode has no defining op");
            if data.op(def).code() == OpCode::Copy {
                return data.op(def).get_in(0);
            }
        }
        vn
    }

    pub fn find_match(data: &Funcdata, bl: BlockId, target: OpId, input: VarnodeId) -> Option<OpId> {
        let mut iter = data.block(bl).get_op_list().front();
        loop {
            let op = iter.expect("target op is not in its basic block");
            iter = basic_next(data, op);
            if op == target {
                break;
            }
            let numinput = data.op(op).num_input();
            let mut slot = 0;
            while slot < numinput {
                let vn = ActionMultiCse::skip_copy(data, data.op(op).get_in(slot));
                if vn == input {
                    break;
                }
                slot += 1;
            }
            if slot < numinput {
                let mut buf1: [Option<VarnodeId>; 2] = [None, None];
                let mut buf2: [Option<VarnodeId>; 2] = [None, None];
                let mut index = 0;
                while index < numinput {
                    let in1 = ActionMultiCse::skip_copy(data, data.op(op).get_in(index));
                    let in2 = ActionMultiCse::skip_copy(data, data.op(target).get_in(index));
                    if in1 == in2 {
                        index += 1;
                        continue;
                    }
                    if functional_equality_level(in1, in2, &mut buf1, &mut buf2, data) != 0 {
                        break;
                    }
                    index += 1;
                }
                if index == numinput {
                    return Some(op);
                }
            }
        }
        None
    }

    pub fn process_block(&mut self, data: &mut Funcdata, _glb: &mut Architecture, bl: BlockId) -> Result<bool> {
        let mut vnlist: Vec<VarnodeId> = Vec::new();
        let mut targetop: Option<OpId> = None;
        let mut pairop: Option<OpId> = None;
        let mut iter = data.block(bl).get_op_list().front();
        while let Some(op) = iter {
            iter = basic_next(data, op);
            let opc = data.op(op).code();
            if opc == OpCode::Copy {
                continue;
            }
            if opc != OpCode::Multiequal {
                break;
            }
            let vnpos = vnlist.len();
            let numinput = data.op(op).num_input();
            let mut slot = 0;
            while slot < numinput {
                let vn = ActionMultiCse::skip_copy(data, data.op(op).get_in(slot));
                vnlist.push(vn);
                if data.vn(vn).is_mark() {
                    pairop = ActionMultiCse::find_match(data, bl, op, vn);
                    if pairop.is_some() {
                        break;
                    }
                }
                slot += 1;
            }
            if slot < numinput {
                targetop = Some(op);
                break;
            }
            for &vn in vnlist.iter().skip(vnpos) {
                data.vn_mut(vn).set_mark();
            }
        }
        for &vn in vnlist.iter() {
            data.vn_mut(vn).clear_mark();
        }
        if let Some(targetop) = targetop {
            let pairop = pairop.expect("matching MULTIEQUAL is missing");
            let out1 = data.op(pairop).get_out().expect("MULTIEQUAL has no output");
            let out2 = data.op(targetop).get_out().expect("MULTIEQUAL has no output");
            if ActionMultiCse::preferred_output(data, out1, out2) {
                data.total_replace(out1, out2)?;
                data.op_destroy(pairop)?;
            } else {
                data.total_replace(out2, out1)?;
                data.op_destroy(targetop)?;
            }
            self.base.count += 1;
            return Ok(true);
        }
        Ok(false)
    }
}

impl Action for ActionMultiCse {
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
        Some(Box::new(ActionMultiCse::new(self.get_group())))
    }

    fn apply(&mut self, data: &mut Funcdata, glb: &mut Architecture) -> Result<i32> {
        let size = data.block(data.bblocks).get_size();
        for index in 0..size {
            let bl = data.block(data.bblocks).get_block(index);
            while self.process_block(data, glb, bl)? {}
        }
        Ok(0)
    }
}

pub struct ActionShadowVar {
    pub base: ActionBase,
}

impl ActionShadowVar {
    pub fn new(group: &str) -> ActionShadowVar {
        ActionShadowVar {
            base: ActionBase::new(0, "shadowvar", group),
        }
    }
}

impl Action for ActionShadowVar {
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
        Some(Box::new(ActionShadowVar::new(self.get_group())))
    }

    fn apply(&mut self, data: &mut Funcdata, glb: &mut Architecture) -> Result<i32> {
        let mut vnlist: Vec<VarnodeId> = Vec::new();
        let mut oplist: Vec<OpId> = Vec::new();
        let size = data.block(data.bblocks).get_size();
        for index in 0..size {
            vnlist.clear();
            let bl = data.block(data.bblocks).get_block(index);
            let startoffset = data.block(bl).get_start().get_offset();
            let mut iter = data.block(bl).get_op_list().front();
            while let Some(op) = iter {
                iter = basic_next(data, op);
                if data.op(op).get_addr().get_offset() != startoffset {
                    break;
                }
                if data.op(op).code() != OpCode::Multiequal {
                    continue;
                }
                let vn = data.op(op).get_in(0);
                if data.vn(vn).is_mark() {
                    oplist.push(op);
                } else {
                    data.vn_mut(vn).set_mark();
                    vnlist.push(vn);
                }
            }
            for &vn in vnlist.iter() {
                data.vn_mut(vn).clear_mark();
            }
        }
        for &op in oplist.iter() {
            let mut op2 = data.op_previous_op(op);
            while let Some(prev) = op2 {
                if data.op(prev).code() == OpCode::Multiequal {
                    let numinput = data.op(op).num_input();
                    let mut slot = 0;
                    while slot < numinput {
                        if data.op(op).get_in(slot) != data.op(prev).get_in(slot) {
                            break;
                        }
                        slot += 1;
                    }
                    if slot == data.op(op).num_input() {
                        let plist = vec![data.op(prev).get_out().expect("MULTIEQUAL has no output")];
                        data.op_set_opcode(op, OpCode::Copy, glb);
                        data.op_set_all_input(op, &plist)?;
                        self.base.count += 1;
                    }
                }
                op2 = data.op_previous_op(prev);
            }
        }
        Ok(0)
    }
}

pub struct ActionConstantPtr {
    pub base: ActionBase,
    pub localcount: i32,
}

impl ActionConstantPtr {
    pub fn new(group: &str) -> ActionConstantPtr {
        ActionConstantPtr {
            base: ActionBase::new(0, "constantptr", group),
            localcount: 0,
        }
    }

    pub fn search_for_space_attribute(
        data: &Funcdata,
        glb: &Architecture,
        vn: VarnodeId,
        op: OpId,
    ) -> Option<SpaceRef> {
        let mut vn = vn;
        let mut op = op;
        for _ in 0..3 {
            let dt = type_factory(glb).get(data.vn(vn).get_type());
            if dt.get_metatype() == TypeMetatype::Ptr
                && let Some(spc) = dt.get_space()
                && spc.get_addr_size() as i32 == data.vn(vn).get_size()
            {
                return Some(spc.clone());
            }
            match data.op(op).code() {
                OpCode::IntAdd | OpCode::Copy | OpCode::Indirect | OpCode::Multiequal => {
                    vn = data.op(op).get_out().expect("op has no output");
                    match data.vn(vn).lone_descend() {
                        Some(next) => op = next,
                        None => break,
                    }
                }
                OpCode::Load => {
                    return data.vn(data.op(op).get_in(0)).get_space_from_const(&glb.manager);
                }
                OpCode::Store => {
                    if data.op(op).get_in(1) == vn {
                        return data.vn(data.op(op).get_in(0)).get_space_from_const(&glb.manager);
                    }
                    return None;
                }
                _ => return None,
            }
        }
        for &descop in data.vn(vn).descend() {
            let opc = data.op(descop).code();
            if opc == OpCode::Load {
                return data.vn(data.op(descop).get_in(0)).get_space_from_const(&glb.manager);
            } else if opc == OpCode::Store && data.op(descop).get_in(1) == vn {
                return data.vn(data.op(descop).get_in(0)).get_space_from_const(&glb.manager);
            }
        }
        None
    }

    pub fn select_infer_space(
        data: &Funcdata,
        glb: &Architecture,
        vn: VarnodeId,
        op: OpId,
        space_list: &[SpaceRef],
    ) -> Option<SpaceRef> {
        let mut res_space: Option<SpaceRef> = None;
        let dt = type_factory(glb).get(data.vn(vn).get_type());
        if dt.get_metatype() == TypeMetatype::Ptr
            && let Some(spc) = dt.get_space()
            && spc.get_addr_size() as i32 == data.vn(vn).get_size()
        {
            return Some(spc.clone());
        }
        for spc in space_list.iter() {
            let min_size = spc.get_minimum_ptr_size();
            if min_size == 0 {
                if data.vn(vn).get_size() != spc.get_addr_size() as i32 {
                    continue;
                }
            } else if data.vn(vn).get_size() < min_size {
                continue;
            }
            if res_space.is_some() {
                if let Some(search_spc) = ActionConstantPtr::search_for_space_attribute(data, glb, vn, op) {
                    res_space = Some(search_spc);
                }
                break;
            }
            res_space = Some(spc.clone());
        }
        res_space
    }

    pub fn check_copy(op: OpId, data: &mut Funcdata, glb: &mut Architecture) -> bool {
        let vn = data.op(op).get_out().expect("COPY has no output");
        let ret_op = data.vn(vn).lone_descend();
        if let Some(ret_op) = ret_op
            && data.op(ret_op).code() == OpCode::Return
            && data.get_func_proto().is_output_locked(glb)
        {
            let outtype = data
                .get_func_proto()
                .get_output_ref()
                .expect("prototype has no output parameter")
                .get_type(glb);
            let meta = type_factory(glb).get(outtype).get_metatype();
            if meta != TypeMetatype::Ptr && meta != TypeMetatype::Unknown {
                return false;
            }
            return true;
        }
        glb.infer_pointers
    }

    pub fn is_pointer(
        spc: &SpaceRef,
        vn: VarnodeId,
        op: OpId,
        slot: i32,
        rampoint: &mut Address,
        full_encoding: &mut u64,
        data: &mut Funcdata,
        glb: &mut Architecture,
    ) -> Result<Option<EntryId>> {
        let mut needexacthit;
        data.vn_mut(vn).set_symbol_check(Varnode::SYMCHECK_COMPLETE as u32);
        let readtype = data.vn_get_type_read_facing(vn, op, glb);
        if type_factory(glb).get(readtype).get_metatype() == TypeMetatype::Ptr {
            let offset = data.vn(vn).get_offset();
            let size = data.vn(vn).get_size();
            let addr = data.op(op).get_addr().clone();
            *rampoint = glb.resolve_constant(spc, offset, size, &addr, full_encoding)?;
            needexacthit = false;
        } else {
            if data.vn(vn).is_type_lock() {
                return Ok(None);
            }
            needexacthit = true;
            match data.op(op).code() {
                OpCode::Call | OpCode::Callind => {
                    if slot == 0 {
                        return Ok(None);
                    }
                    let fc = data.get_call_specs_op(op);
                    let locked = match fc {
                        Some(fc) => {
                            data.call_spec_mut(fc).is_input_locked(glb) && data.call_spec(fc).num_params(glb) > slot - 1
                        }
                        None => false,
                    };
                    if locked {
                        let fc = fc.expect("call specification is missing");
                        let paramtype = data
                            .call_spec_mut(fc)
                            .get_param(slot - 1, glb)
                            .expect("parameter is missing")
                            .get_type(glb);
                        let meta = type_factory(glb).get(paramtype).get_metatype();
                        if meta != TypeMetatype::Ptr && meta != TypeMetatype::Unknown {
                            return Ok(None);
                        }
                    } else if !glb.infer_pointers {
                        return Ok(None);
                    }
                }
                OpCode::Copy => {
                    if !ActionConstantPtr::check_copy(op, data, glb) {
                        return Ok(None);
                    }
                }
                OpCode::Piece | OpCode::IntEqual | OpCode::IntNotequal | OpCode::IntLess | OpCode::IntLessequal => {
                    if !glb.infer_pointers {
                        return Ok(None);
                    }
                }
                OpCode::IntAdd => {
                    let outvn = data.op(op).get_out().expect("INT_ADD has no output");
                    let outtype = data.vn_get_type_def_facing(outvn, glb);
                    if type_factory(glb).get(outtype).get_metatype() == TypeMetatype::Ptr {
                        let othervn = data.op(op).get_in(1 - slot);
                        let othertype = data.vn_get_type_read_facing(othervn, op, glb);
                        if type_factory(glb).get(othertype).get_metatype() == TypeMetatype::Ptr {
                            return Ok(None);
                        }
                        needexacthit = false;
                    } else if !glb.infer_pointers {
                        return Ok(None);
                    }
                }
                OpCode::Store => {
                    if slot != 2 {
                        return Ok(None);
                    }
                }
                _ => return Ok(None),
            }
            let offset = data.vn(vn).get_offset();
            if spc.get_pointer_lower_bound() > offset {
                return Ok(None);
            }
            if spc.get_pointer_upper_bound() < offset {
                return Ok(None);
            }
            if bit_transitions(offset, data.vn(vn).get_size()) < 3 {
                return Ok(None);
            }
            let size = data.vn(vn).get_size();
            let addr = data.op(op).get_addr().clone();
            *rampoint = glb.resolve_constant(spc, offset, size, &addr, full_encoding)?;
        }
        if rampoint.is_invalid() {
            return Ok(None);
        }
        if !rampoint.high_ptr_possible(1, &glb.manager) {
            return Ok(None);
        }
        let db = symbol_table(glb);
        let localscope = data.get_scope_local().expect("function has no local scope");
        let parent = db.scope(localscope).get_parent().expect("local scope has no parent");
        let entry = db.scope_query_container(parent, rampoint, 1, &Address::invalid());
        if let Some(entry) = entry {
            let symbol = db.entry(entry).get_symbol();
            if let Some(ptr_type) = db.symbol(symbol).get_type() {
                let ptr_dt = type_factory(glb).get(ptr_type);
                if ptr_dt.get_metatype() == TypeMetatype::Array {
                    let ct = ptr_dt.get_base();
                    if type_factory(glb).get(ct).is_char_print() {
                        needexacthit = false;
                    }
                }
            }
            if needexacthit && *db.entry(entry).get_addr() != *rampoint {
                data.vn_mut(vn).set_symbol_check(Varnode::SYMCHECK_INCOMPLETE as u32);
                return Ok(None);
            }
        }
        Ok(entry)
    }
}

impl Action for ActionConstantPtr {
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
        Some(Box::new(ActionConstantPtr::new(self.get_group())))
    }

    fn reset(&mut self, _data: &mut Funcdata, _glb: &mut Architecture) {
        self.localcount = 0;
    }

    fn apply(&mut self, data: &mut Funcdata, glb: &mut Architecture) -> Result<i32> {
        if !data.has_type_recovery_started() {
            return Ok(0);
        }
        if self.localcount >= 4 {
            return Ok(0);
        }
        self.localcount += 1;
        let cspc = glb.manager.get_constant_space().expect("missing constant space");
        let mut begiter = data.begin_loc_space(&cspc);
        let enditer = data.end_loc_space(&cspc, glb);
        let infer_spaces = glb.infer_ptr_spaces.clone();
        while begiter != enditer {
            let vn = match data.vbank.loc_at(&begiter) {
                Some(vn) => vn,
                None => break,
            };
            begiter = data.vbank.loc_next(&begiter);
            if !data.vn(vn).is_constant() {
                break;
            }
            if data.vn(vn).get_offset() == 0 {
                continue;
            }
            let check = data.vn(vn).get_symbol_check();
            if check == Varnode::SYMCHECK_COMPLETE as u32 {
                continue;
            }
            if check == Varnode::SYMCHECK_INCOMPLETE as u32
                && type_factory(glb).get(data.vn(vn).get_type()).get_metatype() != TypeMetatype::Ptr
            {
                continue;
            }
            if data.vn(vn).has_no_descend() {
                continue;
            }
            if data.vn(vn).is_spacebase() {
                continue;
            }
            let op = match data.vn(vn).lone_descend() {
                Some(op) => op,
                None => continue,
            };
            let rspc = match ActionConstantPtr::select_infer_space(data, glb, vn, op, &infer_spaces) {
                Some(rspc) => rspc,
                None => continue,
            };
            let slot = data.op(op).get_slot(vn);
            let opc = data.op(op).code();
            if opc == OpCode::IntAdd {
                if data.vn(data.op(op).get_in(1 - slot)).is_spacebase() {
                    continue;
                }
            } else if opc == OpCode::Ptrsub || opc == OpCode::Ptradd {
                continue;
            }
            let mut rampoint = Address::invalid();
            let mut full_encoding: u64 = 0;
            let entry =
                ActionConstantPtr::is_pointer(&rspc, vn, op, slot, &mut rampoint, &mut full_encoding, data, glb)?;
            if let Some(entry) = entry {
                let size = data.vn(vn).get_size();
                data.spacebase_constant(op, slot, entry, &rampoint, full_encoding, size, glb)?;
                if opc == OpCode::IntAdd && slot == 1 {
                    data.op_swap_input(op, 0, 1);
                }
                self.base.count += 1;
            }
        }
        Ok(0)
    }
}

pub struct ActionDeindirect {
    pub base: ActionBase,
}

impl ActionDeindirect {
    pub fn new(group: &str) -> ActionDeindirect {
        ActionDeindirect {
            base: ActionBase::new(0, "deindirect", group),
        }
    }
}

impl Action for ActionDeindirect {
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
        Some(Box::new(ActionDeindirect::new(self.get_group())))
    }

    fn apply(&mut self, data: &mut Funcdata, glb: &mut Architecture) -> Result<i32> {
        let mut index = 0;
        while index < data.num_calls() {
            let fc = data.get_call_specs(index);
            index += 1;
            let op = data.call_spec(fc).get_op();
            if data.op(op).code() != OpCode::Callind {
                continue;
            }
            let mut vn = data.op(op).get_in(0);
            while data.vn(vn).is_written() {
                let def = data.vn(vn).get_def().expect("written varnode has no defining op");
                if data.op(def).code() != OpCode::Copy {
                    break;
                }
                vn = data.op(def).get_in(0);
            }
            if data.vn(vn).is_persist() && data.vn(vn).is_external_ref() {
                let newfd = {
                    let db = symbol_table(glb);
                    let localscope = data.get_scope_local().expect("function has no local scope");
                    let parent = db.scope(localscope).get_parent().expect("local scope has no parent");
                    db.scope_query_external_ref_function(parent, data.vn(vn).get_addr())
                };
                if let Some(newfd) = newfd {
                    FuncCallSpecs::deindirect(data, fc, newfd, glb)?;
                    self.base.count += 1;
                    continue;
                }
            } else if data.vn(vn).is_constant() {
                let sp = data
                    .get_address()
                    .get_space()
                    .expect("function address has no space")
                    .clone();
                let mut offset = AddrSpace::address_to_byte(data.vn(vn).get_offset(), sp.get_word_size());
                let align = glb.funcptr_align;
                if align != 0 {
                    offset = offset.wrapping_shr(align as u32);
                    offset = offset.wrapping_shl(align as u32);
                }
                let codeaddr = Address::new(sp, offset);
                let newfd = {
                    let db = symbol_table(glb);
                    let localscope = data.get_scope_local().expect("function has no local scope");
                    let parent = db.scope(localscope).get_parent().expect("local scope has no parent");
                    db.scope_query_function(parent, &codeaddr)
                };
                if let Some(newfd) = newfd {
                    FuncCallSpecs::deindirect(data, fc, newfd, glb)?;
                    self.base.count += 1;
                    continue;
                }
            }
            if data.has_type_recovery_started() {
                let invn = data.op(op).get_in(0);
                let ct = data.vn_get_type_read_facing(invn, op, glb);
                let ctdt = type_factory(glb).get(ct);
                if ctdt.get_metatype() == TypeMetatype::Ptr {
                    let ptrto = ctdt.get_ptr_to();
                    let tc = type_factory(glb).get(ptrto);
                    if tc.get_metatype() == TypeMetatype::Code {
                        let copied = match tc.get_prototype() {
                            Some(proto) => {
                                let mut fp = FuncProto::new();
                                fp.copy(proto)?;
                                Some(fp)
                            }
                            None => None,
                        };
                        if let Some(mut fp) = copied
                            && !data.call_spec_mut(fc).is_input_locked(glb)
                        {
                            FuncCallSpecs::force_set(data, fc, &mut fp, glb)?;
                            self.base.count += 1;
                        }
                    }
                }
            }
        }
        Ok(0)
    }
}

pub struct ActionVarnodeProps {
    pub base: ActionBase,
}

impl ActionVarnodeProps {
    pub fn new(group: &str) -> ActionVarnodeProps {
        ActionVarnodeProps {
            base: ActionBase::new(0, "varnodeprops", group),
        }
    }

    pub fn handle_extended_zero(&mut self, vn: VarnodeId, data: &mut Funcdata, glb: &mut Architecture) -> Result<()> {
        let zext = data.vn(vn).get_def().expect("written varnode has no defining op");
        if data.op(zext).code() != OpCode::IntZext {
            return Ok(());
        }
        if !data.vn(data.op(zext).get_in(0)).constant_match(0) {
            return Ok(());
        }
        let mut iter = 0;
        while iter < data.vn(vn).descend().len() {
            let subop = data.vn(vn).descend()[iter];
            iter += 1;
            match data.op(subop).code() {
                OpCode::IntAdd | OpCode::IntOr | OpCode::IntXor => {
                    let slot = data.op(subop).get_slot(vn);
                    data.op_remove_input(subop, slot);
                    data.op_set_opcode(subop, OpCode::Copy, glb);
                    iter = 0;
                    self.base.count += 1;
                }
                OpCode::Int2comp => {
                    data.op_set_opcode(subop, OpCode::Copy, glb);
                    self.base.count += 1;
                }
                OpCode::IntLeft
                | OpCode::IntRight
                | OpCode::IntSright
                | OpCode::IntDiv
                | OpCode::IntSdiv
                | OpCode::IntRem
                | OpCode::IntSrem => {
                    if data.op(subop).get_in(0) != vn {
                        continue;
                    }
                    data.op_remove_input(subop, 1);
                    data.op_set_opcode(subop, OpCode::Copy, glb);
                    iter = 0;
                    self.base.count += 1;
                }
                OpCode::IntMult | OpCode::IntAnd => {
                    let slot = data.op(subop).get_slot(vn);
                    data.op_remove_input(subop, 1 - slot);
                    data.op_set_opcode(subop, OpCode::Copy, glb);
                    iter = 0;
                    self.base.count += 1;
                }
                _ => {}
            }
        }
        Ok(())
    }
}

impl Action for ActionVarnodeProps {
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
        Some(Box::new(ActionVarnodeProps::new(self.get_group())))
    }

    fn apply(&mut self, data: &mut Funcdata, glb: &mut Architecture) -> Result<i32> {
        let cachereadonly = glb.readonlypropagate;
        let pass = data.get_heritage_pass();
        let mut iter = data.begin_loc();
        while let Some((vn, next)) = loc_step(data, &iter) {
            iter = next;
            if data.vn(vn).is_annotation() {
                continue;
            }
            let vn_size = data.vn(vn).get_size();
            if data.vn(vn).is_auto_live_hold() {
                if pass > 0 {
                    if data.vn(vn).is_written() {
                        let load_op = data.vn(vn).get_def().expect("written varnode has no defining op");
                        if data.op(load_op).code() == OpCode::Load {
                            let mut ptr = data.op(load_op).get_in(1);
                            if data.vn(ptr).is_constant() || data.vn(ptr).is_read_only() {
                                continue;
                            }
                            if data.vn(ptr).is_written() {
                                let copy_op = data.vn(ptr).get_def().expect("written varnode has no defining op");
                                if data.op(copy_op).code() == OpCode::Copy {
                                    ptr = data.op(copy_op).get_in(0);
                                    if data.vn(ptr).is_constant() || data.vn(ptr).is_read_only() {
                                        continue;
                                    }
                                }
                            }
                        }
                    }
                    data.vn_mut(vn).clear_auto_live_hold();
                    self.base.count += 1;
                }
            } else if data.vn(vn).has_action_property() {
                if cachereadonly && data.vn(vn).is_read_only() {
                    if data.fillin_read_only(vn, glb)? {
                        self.base.count += 1;
                    }
                } else if data.vn(vn).is_volatile() && data.replace_volatile(vn, glb)? {
                    self.base.count += 1;
                }
            } else if (data.vn(vn).get_nz_mask() & data.vn(vn).get_consume()) == 0 {
                if data.vn(vn).is_constant() {
                    continue;
                }
                if data.vn(vn).is_written() {
                    if vn_size > 8 {
                        self.handle_extended_zero(vn, data, glb)?;
                        continue;
                    }
                    let def = data.vn(vn).get_def().expect("written varnode has no defining op");
                    if data.op(def).code() == OpCode::Copy {
                        let invn = data.op(def).get_in(0);
                        if data.vn(invn).is_constant() && data.vn(invn).get_offset() == 0 {
                            continue;
                        }
                    }
                }
                if !data.vn(vn).has_no_descend() {
                    data.total_replace_constant(vn, 0, glb)?;
                    self.base.count += 1;
                }
            }
        }
        Ok(0)
    }
}

pub struct ActionDirectWrite {
    pub base: ActionBase,
    pub propagate_indirect: bool,
}

impl ActionDirectWrite {
    pub fn new(group: &str, propagate_indirect: bool) -> ActionDirectWrite {
        ActionDirectWrite {
            base: ActionBase::new(0, "directwrite", group),
            propagate_indirect,
        }
    }
}

impl Action for ActionDirectWrite {
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
        Some(Box::new(ActionDirectWrite::new(
            self.get_group(),
            self.propagate_indirect,
        )))
    }

    fn apply(&mut self, data: &mut Funcdata, glb: &mut Architecture) -> Result<i32> {
        let mut worklist: Vec<VarnodeId> = Vec::new();
        let begin = data.begin_loc();
        let end = data.end_loc();
        for vn in data.vbank.loc_range(&begin, &end) {
            data.vn_mut(vn).clear_direct_write();
            if data.vn(vn).is_input() {
                if data.vn(vn).is_persist() || data.vn(vn).is_spacebase() {
                    data.vn_mut(vn).set_direct_write();
                    worklist.push(vn);
                } else {
                    let addr = data.vn(vn).get_addr().clone();
                    let size = data.vn(vn).get_size();
                    if data.get_func_proto_mut().possible_input_param(&addr, size, glb) {
                        data.vn_mut(vn).set_direct_write();
                        worklist.push(vn);
                    }
                }
            } else if data.vn(vn).is_written() {
                let op = data.vn(vn).get_def().expect("written varnode has no defining op");
                if !data.op(op).is_marker() {
                    if data.vn(vn).is_persist() {
                        data.vn_mut(vn).set_direct_write();
                        worklist.push(vn);
                    } else if data.op(op).code() == OpCode::Copy {
                        if data.vn(vn).is_stack_store() {
                            let mut invn = data.op(op).get_in(0);
                            if data.vn(invn).is_written() {
                                let curop = data.vn(invn).get_def().expect("written varnode has no defining op");
                                if data.op(curop).code() == OpCode::Copy {
                                    invn = data.op(curop).get_in(0);
                                }
                            }
                            if data.vn(invn).is_written() {
                                let indop = data.vn(invn).get_def().expect("written varnode has no defining op");
                                if data.op(indop).is_marker() {
                                    data.vn_mut(vn).set_direct_write();
                                    worklist.push(vn);
                                }
                            }
                        }
                    } else if data.op(op).code() != OpCode::Piece && data.op(op).code() != OpCode::Subpiece {
                        data.vn_mut(vn).set_direct_write();
                        worklist.push(vn);
                    }
                } else if !self.propagate_indirect && data.op(op).code() == OpCode::Indirect {
                    let outvn = data.op(op).get_out().expect("INDIRECT has no output");
                    let invn = data.op(op).get_in(0);
                    if data.vn(invn).get_addr() != data.vn(outvn).get_addr() || data.vn(outvn).is_persist() {
                        data.vn_mut(vn).set_direct_write();
                    }
                }
            } else if data.vn(vn).is_constant() && !data.vn(vn).is_indirect_zero() {
                data.vn_mut(vn).set_direct_write();
                worklist.push(vn);
            }
        }
        while let Some(vn) = worklist.pop() {
            let descend = data.vn(vn).descend().to_vec();
            for op in descend {
                if !data.op(op).is_assignment() {
                    continue;
                }
                let dvn = data.op(op).get_out().expect("assignment has no output");
                if !data.vn(dvn).is_direct_write() {
                    data.vn_mut(dvn).set_direct_write();
                    if self.propagate_indirect
                        || data.op(op).code() != OpCode::Indirect
                        || data.op(op).is_indirect_store()
                    {
                        worklist.push(dvn);
                    }
                }
            }
        }
        Ok(0)
    }
}

pub struct ActionConstbase {
    pub base: ActionBase,
}

impl ActionConstbase {
    pub fn new(group: &str) -> ActionConstbase {
        ActionConstbase {
            base: ActionBase::new(0, "constbase", group),
        }
    }
}

impl Action for ActionConstbase {
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
        Some(Box::new(ActionConstbase::new(self.get_group())))
    }

    fn apply(&mut self, data: &mut Funcdata, glb: &mut Architecture) -> Result<i32> {
        if data.block(data.bblocks).get_size() == 0 {
            return Ok(0);
        }
        let bb = data.block(data.bblocks).get_block(0);
        let injectid = data.get_func_proto().get_inject_upon_entry(glb);
        if injectid >= 0 {
            let start = data.block(bb).get_start();
            let first = data.block(bb).get_op_list().front();
            data.do_live_inject(injectid, &start, bb, first, glb)?;
        }
        let trackset: TrackedSet = {
            let context = glb.context.as_ref().expect("missing context database");
            let guard = context.lock().expect("context database lock is poisoned");
            guard.get_tracked_set(data.get_address()).clone()
        };
        for ctx in trackset.iter() {
            let addr = Address::from_parts(ctx.loc.space.clone(), ctx.loc.offset);
            let start = data.block(bb).get_start();
            let op = data.new_op(1, &start);
            data.new_varnode_out(ctx.loc.size as i32, &addr, op, glb)?;
            let vnin = data.new_constant(ctx.loc.size as i32, ctx.val, glb);
            data.op_set_opcode(op, OpCode::Copy, glb);
            data.op_set_input(op, vnin, 0)?;
            data.op_insert_begin(op, bb);
        }
        Ok(0)
    }
}

pub struct ActionSpacebase {
    pub base: ActionBase,
}

impl ActionSpacebase {
    pub fn new(group: &str) -> ActionSpacebase {
        ActionSpacebase {
            base: ActionBase::new(0, "spacebase", group),
        }
    }
}

impl Action for ActionSpacebase {
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
        Some(Box::new(ActionSpacebase::new(self.get_group())))
    }

    fn apply(&mut self, data: &mut Funcdata, glb: &mut Architecture) -> Result<i32> {
        data.spacebase(glb)?;
        Ok(0)
    }
}

pub struct ActionHeritage {
    pub base: ActionBase,
}

impl ActionHeritage {
    pub fn new(group: &str) -> ActionHeritage {
        ActionHeritage {
            base: ActionBase::new(0, "heritage", group),
        }
    }
}

impl Action for ActionHeritage {
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
        Some(Box::new(ActionHeritage::new(self.get_group())))
    }

    fn apply(&mut self, data: &mut Funcdata, glb: &mut Architecture) -> Result<i32> {
        data.op_heritage(glb)?;
        Ok(0)
    }
}

pub struct ActionNonzeroMask {
    pub base: ActionBase,
}

impl ActionNonzeroMask {
    pub fn new(group: &str) -> ActionNonzeroMask {
        ActionNonzeroMask {
            base: ActionBase::new(0, "nonzeromask", group),
        }
    }
}

impl Action for ActionNonzeroMask {
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
        Some(Box::new(ActionNonzeroMask::new(self.get_group())))
    }

    fn apply(&mut self, data: &mut Funcdata, glb: &mut Architecture) -> Result<i32> {
        data.calc_nz_mask(glb);
        Ok(0)
    }
}

pub struct ActionAssignHigh {
    pub base: ActionBase,
}

impl ActionAssignHigh {
    pub fn new(group: &str) -> ActionAssignHigh {
        ActionAssignHigh {
            base: ActionBase::new(RULE_ONCEPERFUNC, "assignhigh", group),
        }
    }
}

impl Action for ActionAssignHigh {
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
        Some(Box::new(ActionAssignHigh::new(self.get_group())))
    }

    fn apply(&mut self, data: &mut Funcdata, glb: &mut Architecture) -> Result<i32> {
        data.set_high_level(glb)?;
        Ok(0)
    }
}

pub struct ActionMarkIndirectOnly {
    pub base: ActionBase,
}

impl ActionMarkIndirectOnly {
    pub fn new(group: &str) -> ActionMarkIndirectOnly {
        ActionMarkIndirectOnly {
            base: ActionBase::new(RULE_ONCEPERFUNC, "markindirectonly", group),
        }
    }
}

impl Action for ActionMarkIndirectOnly {
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
        Some(Box::new(ActionMarkIndirectOnly::new(self.get_group())))
    }

    fn apply(&mut self, data: &mut Funcdata, _glb: &mut Architecture) -> Result<i32> {
        data.mark_indirect_only();
        Ok(0)
    }
}

pub struct ActionMergeRequired {
    pub base: ActionBase,
}

impl ActionMergeRequired {
    pub fn new(group: &str) -> ActionMergeRequired {
        ActionMergeRequired {
            base: ActionBase::new(RULE_ONCEPERFUNC, "mergerequired", group),
        }
    }
}

impl Action for ActionMergeRequired {
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
        Some(Box::new(ActionMergeRequired::new(self.get_group())))
    }

    fn apply(&mut self, data: &mut Funcdata, glb: &mut Architecture) -> Result<i32> {
        Merge::merge_addr_tied(data, glb)?;
        Merge::group_partials(data, glb)?;
        Merge::merge_marker(data, glb)?;
        Ok(0)
    }
}

pub struct ActionMergeAdjacent {
    pub base: ActionBase,
}

impl ActionMergeAdjacent {
    pub fn new(group: &str) -> ActionMergeAdjacent {
        ActionMergeAdjacent {
            base: ActionBase::new(RULE_ONCEPERFUNC, "mergeadjacent", group),
        }
    }
}

impl Action for ActionMergeAdjacent {
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
        Some(Box::new(ActionMergeAdjacent::new(self.get_group())))
    }

    fn apply(&mut self, data: &mut Funcdata, glb: &mut Architecture) -> Result<i32> {
        Merge::merge_adjacent(data, glb)?;
        Ok(0)
    }
}

pub struct ActionMergeCopy {
    pub base: ActionBase,
}

impl ActionMergeCopy {
    pub fn new(group: &str) -> ActionMergeCopy {
        ActionMergeCopy {
            base: ActionBase::new(RULE_ONCEPERFUNC, "mergecopy", group),
        }
    }
}

impl Action for ActionMergeCopy {
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
        Some(Box::new(ActionMergeCopy::new(self.get_group())))
    }

    fn apply(&mut self, data: &mut Funcdata, glb: &mut Architecture) -> Result<i32> {
        Merge::merge_opcode(data, glb, OpCode::Copy)?;
        Ok(0)
    }
}

pub struct ActionMergeMultiEntry {
    pub base: ActionBase,
}

impl ActionMergeMultiEntry {
    pub fn new(group: &str) -> ActionMergeMultiEntry {
        ActionMergeMultiEntry {
            base: ActionBase::new(RULE_ONCEPERFUNC, "mergemultientry", group),
        }
    }
}

impl Action for ActionMergeMultiEntry {
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
        Some(Box::new(ActionMergeMultiEntry::new(self.get_group())))
    }

    fn apply(&mut self, data: &mut Funcdata, glb: &mut Architecture) -> Result<i32> {
        Merge::merge_multi_entry(data, glb)?;
        Ok(0)
    }
}

pub struct ActionMergeType {
    pub base: ActionBase,
}

impl ActionMergeType {
    pub fn new(group: &str) -> ActionMergeType {
        ActionMergeType {
            base: ActionBase::new(RULE_ONCEPERFUNC, "mergetype", group),
        }
    }
}

impl Action for ActionMergeType {
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
        Some(Box::new(ActionMergeType::new(self.get_group())))
    }

    fn apply(&mut self, data: &mut Funcdata, glb: &mut Architecture) -> Result<i32> {
        let varnodes = data.vbank.loc_range(&data.begin_loc(), &data.end_loc());
        Merge::merge_by_datatype(data, glb, &varnodes)?;
        Ok(0)
    }
}

pub struct ActionDefaultParams {
    pub base: ActionBase,
}

impl ActionDefaultParams {
    pub fn new(group: &str) -> ActionDefaultParams {
        ActionDefaultParams {
            base: ActionBase::new(RULE_ONCEPERFUNC, "defaultparams", group),
        }
    }
}

impl Action for ActionDefaultParams {
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
        Some(Box::new(ActionDefaultParams::new(self.get_group())))
    }

    fn apply(&mut self, data: &mut Funcdata, glb: &mut Architecture) -> Result<i32> {
        let evalfp = match glb.evalfp_called {
            Some(model) => Some(model),
            None => glb.defaultfp,
        };
        let size = data.num_calls();
        for index in 0..size {
            let fc = data.get_call_specs(index);
            if !data.call_spec(fc).has_model() {
                let otherproto = match data.call_spec(fc).get_funcdata() {
                    Some(othersym) => {
                        if data.get_symbol() == Some(othersym) {
                            let mut proto = FuncProto::new();
                            proto.copy(data.get_func_proto())?;
                            Some(proto)
                        } else {
                            match Database::symbol_get_function(glb, othersym)? {
                                Some(otherfunc) => {
                                    let mut proto = FuncProto::new();
                                    proto.copy(otherfunc.get_func_proto())?;
                                    Some(proto)
                                }
                                None => None,
                            }
                        }
                    }
                    None => None,
                };
                match otherproto {
                    Some(proto) => {
                        data.call_spec_mut(fc).copy(&proto)?;
                        if !data.call_spec(fc).is_model_locked() && !data.call_spec(fc).has_matching_model(evalfp) {
                            data.call_spec_mut(fc).set_model(evalfp, glb);
                        }
                    }
                    None => {
                        let voidtype = type_factory_mut(glb).get_type_void()?;
                        let model = evalfp.expect("missing default prototype model");
                        data.call_spec_mut(fc).set_internal(model, voidtype, glb);
                    }
                }
            }
            FuncCallSpecs::insert_pcode(data, fc, glb)?;
        }
        Ok(0)
    }
}

pub struct ActionExtraPopSetup {
    pub base: ActionBase,
    pub stackspace: Option<SpaceRef>,
}

impl ActionExtraPopSetup {
    pub fn new(group: &str, stackspace: Option<SpaceRef>) -> ActionExtraPopSetup {
        ActionExtraPopSetup {
            base: ActionBase::new(RULE_ONCEPERFUNC, "extrapopsetup", group),
            stackspace,
        }
    }
}

impl Action for ActionExtraPopSetup {
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
        Some(Box::new(ActionExtraPopSetup::new(
            self.get_group(),
            self.stackspace.clone(),
        )))
    }

    fn apply(&mut self, data: &mut Funcdata, glb: &mut Architecture) -> Result<i32> {
        let stackspace = match &self.stackspace {
            Some(spc) => spc.clone(),
            None => return Ok(0),
        };
        let point = stackspace.get_spacebase(0)?;
        let sb_addr = Address::from_parts(point.space.clone(), point.offset);
        let sb_size = point.size as i32;
        let mut index = 0;
        while index < data.num_calls() {
            let fc = data.get_call_specs(index);
            index += 1;
            let extrapop = data.call_spec(fc).get_extra_pop();
            if extrapop == 0 {
                continue;
            }
            let fcop = data.call_spec(fc).get_op();
            if extrapop != ProtoModel::EXTRAPOP_UNKNOWN {
                data.call_spec_mut(fc).set_effective_extra_pop(extrapop);
                let addr = data.op(fcop).get_addr().clone();
                let op = data.new_op(2, &addr);
                data.new_varnode_out(sb_size, &sb_addr, op, glb)?;
                let invn = data.new_varnode(sb_size, &sb_addr, None, glb)?;
                data.op_set_input(op, invn, 0)?;
                data.op_set_opcode(op, OpCode::IntAdd, glb);
                let constvn = data.new_constant(sb_size, extrapop as i64 as u64, glb);
                data.op_set_input(op, constvn, 1)?;
                data.op_insert_after(op, fcop);
            } else {
                let op = data.new_indirect(fcop, glb)?;
                data.new_varnode_out(sb_size, &sb_addr, op, glb)?;
                let invn = data.new_varnode(sb_size, &sb_addr, None, glb)?;
                data.op_set_input(op, invn, 0)?;
                data.op_insert_before(op, fcop);
            }
        }
        Ok(0)
    }
}

pub struct ActionFuncLink {
    pub base: ActionBase,
}

impl ActionFuncLink {
    pub fn new(group: &str) -> ActionFuncLink {
        ActionFuncLink {
            base: ActionBase::new(RULE_ONCEPERFUNC, "funclink", group),
        }
    }

    pub fn func_link_input(fc: CallSpecId, data: &mut Funcdata, glb: &mut Architecture) -> Result<()> {
        let inputlocked = data.call_spec_mut(fc).is_input_locked(glb);
        let varargs = data.call_spec(fc).is_dotdotdot();
        let mut spacebase: Option<SpaceRef> = data.call_spec(fc).get_spacebase(glb).cloned();
        if !inputlocked || varargs {
            data.call_spec_mut(fc).init_active_input(glb);
        }
        if inputlocked {
            let op = data.call_spec(fc).get_op();
            let numparam = data.call_spec(fc).num_params(glb);
            let mut setplaceholder = varargs;
            for index in 0..numparam {
                let (paddr, psize) = {
                    let param = data
                        .call_spec_mut(fc)
                        .get_param(index, glb)
                        .expect("parameter is missing");
                    (param.get_address(glb), param.get_size(glb))
                };
                {
                    let active = data.call_spec_mut(fc).get_active_input();
                    active.register_trial(&paddr, psize);
                    active.get_trial_mut(index).mark_active();
                    if varargs {
                        active.get_trial_mut(index).set_fixed_position(index);
                    }
                }
                let spc = paddr.get_space().expect("parameter address has no space").clone();
                let off = paddr.get_offset();
                let size = psize;
                if spc.get_type() == SpaceType::Spacebase {
                    let loadval = data.op_stack_load(&spc, off, size as u32, op, None, false, glb)?;
                    let numinput = data.op(op).num_input();
                    data.op_insert_input(op, loadval, numinput)?;
                    if !setplaceholder {
                        setplaceholder = true;
                        data.vn_mut(loadval).set_spacebase_placeholder();
                        spacebase = None;
                    }
                    continue;
                }
                if spc.get_type() == SpaceType::Join {
                    let join = glb.manager.find_join(off)?;
                    let mut index_piece = -1;
                    if join.get_piece(0).space.as_ref().map(|piece| piece.get_type()) == Some(SpaceType::Spacebase) {
                        index_piece = 0;
                    } else if join
                        .get_piece(join.num_pieces() - 1)
                        .space
                        .as_ref()
                        .map(|piece| piece.get_type())
                        == Some(SpaceType::Spacebase)
                    {
                        index_piece = join.num_pieces() - 1;
                    }
                    if index_piece >= 0 {
                        let stack = join.get_piece(index_piece).clone();
                        let remain = glb.manager.strip_join_piece(&join, index_piece)?;
                        let stackspc = stack.space.clone().expect("join piece has no space");
                        let loadval = data.op_stack_load(&stackspc, stack.offset, stack.size, op, None, false, glb)?;
                        let remainaddr = Address::from_parts(remain.space.clone(), remain.offset);
                        let remainval = data.new_varnode(remain.size as i32, &remainaddr, None, glb)?;
                        let opaddr = data.op(op).get_addr().clone();
                        let concat_op = data.new_op(2, &opaddr);
                        data.op_set_opcode(concat_op, OpCode::Piece, glb);
                        if index_piece == 0 {
                            data.op_set_input(concat_op, loadval, 0)?;
                            data.op_set_input(concat_op, remainval, 1)?;
                        } else {
                            data.op_set_input(concat_op, remainval, 0)?;
                            data.op_set_input(concat_op, loadval, 1)?;
                        }
                        let outvn = data.new_unique_out(size, concat_op, glb)?;
                        data.op_insert_before(concat_op, op);
                        let numinput = data.op(op).num_input();
                        data.op_insert_input(op, outvn, numinput)?;
                        continue;
                    }
                }
                let newvn = data.new_varnode(psize, &paddr, None, glb)?;
                let numinput = data.op(op).num_input();
                data.op_insert_input(op, newvn, numinput)?;
            }
        }
        if let Some(spacebase) = spacebase {
            FuncCallSpecs::create_placeholder(data, fc, &spacebase, glb)?;
        }
        Ok(())
    }

    pub fn func_link_output(fc: CallSpecId, data: &mut Funcdata, glb: &mut Architecture) -> Result<()> {
        let callop = data.call_spec(fc).get_op();
        if let Some(outvn) = data.op(callop).get_out() {
            if space_type_of(data, outvn) == Some(SpaceType::Internal) {
                let mut message = String::from("CALL op at ");
                data.op(callop).get_addr().print_raw(&mut message);
                message.push_str(" has an unexpected output varnode");
                return Err(Error::Lowlevel(message));
            }
            data.op_unset_output(callop)?;
        }
        if data.call_spec(fc).is_output_locked(glb) {
            let (outtype, size, addr) = {
                let outparam = data
                    .call_spec(fc)
                    .get_output_ref()
                    .expect("prototype has no output parameter");
                (
                    outparam.get_type(glb),
                    outparam.get_size(glb),
                    outparam.get_address(glb),
                )
            };
            let meta = type_factory(glb).get(outtype).get_metatype();
            if meta != TypeMetatype::Void {
                if meta == TypeMetatype::Bool && data.is_type_recovery_on() {
                    data.op_mark_calculated_bool(callop);
                }
                if addr.get_space().map(|spc| spc.get_type()) == Some(SpaceType::Spacebase) {
                    data.call_spec_mut(fc).set_stack_output_lock(true);
                    return Ok(());
                }
                data.new_varnode_out(size, &addr, callop, glb)?;
                let mut vdata = VarnodeData::default();
                let mut res = data
                    .call_spec(fc)
                    .assumed_output_extension(&addr, size, &mut vdata, glb);
                if res == OpCode::Piece {
                    if meta == TypeMetatype::Int {
                        res = OpCode::IntSext;
                    } else {
                        res = OpCode::IntZext;
                    }
                }
                if res != OpCode::Copy {
                    let calladdr = data.op(callop).get_addr().clone();
                    let op = data.new_op(1, &calladdr);
                    data.new_varnode_out(vdata.size as i32, &vdata.get_addr(), op, glb)?;
                    let invn = data.new_varnode(size, &addr, None, glb)?;
                    data.op_set_input(op, invn, 0)?;
                    data.op_set_opcode(op, res, glb);
                    data.op_insert_after(op, callop);
                }
            }
        } else {
            data.call_spec_mut(fc).init_active_output();
        }
        Ok(())
    }
}

impl Action for ActionFuncLink {
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
        Some(Box::new(ActionFuncLink::new(self.get_group())))
    }

    fn apply(&mut self, data: &mut Funcdata, glb: &mut Architecture) -> Result<i32> {
        let size = data.num_calls();
        for index in 0..size {
            let fc = data.get_call_specs(index);
            ActionFuncLink::func_link_input(fc, data, glb)?;
            let fc = data.get_call_specs(index);
            ActionFuncLink::func_link_output(fc, data, glb)?;
        }
        Ok(0)
    }
}

pub struct ActionFuncLinkOutOnly {
    pub base: ActionBase,
}

impl ActionFuncLinkOutOnly {
    pub fn new(group: &str) -> ActionFuncLinkOutOnly {
        ActionFuncLinkOutOnly {
            base: ActionBase::new(RULE_ONCEPERFUNC, "funclink_outonly", group),
        }
    }
}

impl Action for ActionFuncLinkOutOnly {
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
        Some(Box::new(ActionFuncLinkOutOnly::new(self.get_group())))
    }

    fn apply(&mut self, data: &mut Funcdata, glb: &mut Architecture) -> Result<i32> {
        let size = data.num_calls();
        for index in 0..size {
            let fc = data.get_call_specs(index);
            ActionFuncLink::func_link_output(fc, data, glb)?;
        }
        Ok(0)
    }
}

pub struct ActionParamDouble {
    pub base: ActionBase,
}

impl ActionParamDouble {
    pub fn new(group: &str) -> ActionParamDouble {
        ActionParamDouble {
            base: ActionBase::new(0, "paramdouble", group),
        }
    }
}

impl Action for ActionParamDouble {
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
        Some(Box::new(ActionParamDouble::new(self.get_group())))
    }

    fn apply(&mut self, data: &mut Funcdata, glb: &mut Architecture) -> Result<i32> {
        let mut index = 0;
        while index < data.num_calls() {
            let fc = data.get_call_specs(index);
            index += 1;
            let op = data.call_spec(fc).get_op();
            if data.call_spec(fc).is_input_active() {
                let mut trialindex: i32 = -1;
                loop {
                    trialindex += 1;
                    if trialindex >= data.call_spec_mut(fc).get_active_input().get_num_trials() {
                        break;
                    }
                    let paramtrial = data.call_spec_mut(fc).get_active_input().get_trial(trialindex).clone();
                    if paramtrial.is_checked() {
                        continue;
                    }
                    if paramtrial.is_unref() {
                        continue;
                    }
                    let spc = paramtrial
                        .get_address()
                        .get_space()
                        .expect("trial address has no space")
                        .clone();
                    if spc.get_type() != SpaceType::Spacebase {
                        continue;
                    }
                    let slot = paramtrial.get_slot();
                    let vn = data.op(op).get_in(slot);
                    if !data.vn(vn).is_written() {
                        continue;
                    }
                    let concatop = data.vn(vn).get_def().expect("written varnode has no defining op");
                    if data.op(concatop).code() != OpCode::Piece {
                        continue;
                    }
                    if !data.call_spec(fc).has_model() {
                        continue;
                    }
                    let mostvn = data.op(concatop).get_in(0);
                    let leastvn = data.op(concatop).get_in(1);
                    let splitsize = if spc.is_big_endian() {
                        data.vn(mostvn).get_size()
                    } else {
                        data.vn(leastvn).get_size()
                    };
                    if data.call_spec(fc).check_input_split(
                        paramtrial.get_address(),
                        paramtrial.get_size(),
                        splitsize,
                        glb,
                    ) {
                        data.call_spec_mut(fc)
                            .get_active_input()
                            .split_trial(trialindex, splitsize)?;
                        if spc.is_big_endian() {
                            data.op_insert_input(op, mostvn, slot)?;
                            data.op_set_input(op, leastvn, slot + 1)?;
                        } else {
                            data.op_insert_input(op, leastvn, slot)?;
                            data.op_set_input(op, mostvn, slot + 1)?;
                        }
                        self.base.count += 1;
                        trialindex -= 1;
                    }
                }
            } else if !data.call_spec_mut(fc).is_input_locked(glb) && data.is_double_precis_on() {
                let mut max = data.op(op).num_input() - 1;
                let mut slot = 0;
                loop {
                    slot += 1;
                    if slot >= max {
                        break;
                    }
                    let vn1 = data.op(op).get_in(slot);
                    let vn2 = data.op(op).get_in(slot + 1);
                    let mut whole = SplitVarnode::new();
                    let isslothi;
                    if whole.in_hand_hi(vn1, data) {
                        if whole.get_lo() != Some(vn2) {
                            continue;
                        }
                        isslothi = true;
                    } else if whole.in_hand_lo(vn1, data) {
                        if whole.get_hi() != Some(vn2) {
                            continue;
                        }
                        isslothi = false;
                    } else {
                        continue;
                    }
                    if FuncCallSpecs::check_input_join_varnodes(data, fc, slot, isslothi, vn1, vn2, glb) {
                        let wholevn = whole.get_whole().expect("double precision whole is missing");
                        data.op_set_input(op, wholevn, slot)?;
                        data.op_remove_input(op, slot + 1);
                        FuncCallSpecs::do_input_join(data, fc, slot, isslothi, glb)?;
                        max = data.op(op).num_input() - 1;
                        self.base.count += 1;
                    }
                }
            }
        }
        if data.get_func_proto_mut().is_input_locked(glb) && data.is_double_precis_on() {
            let mut lovec: Vec<VarnodeId> = Vec::new();
            let mut hivec: Vec<VarnodeId> = Vec::new();
            let min_double_size = glb.manager.get_default_size();
            let numparams = data.get_func_proto().num_params(glb);
            for paramindex in 0..numparams {
                let (tp, paddr) = {
                    let param = data
                        .get_func_proto_mut()
                        .get_param(paramindex, glb)
                        .expect("parameter is missing");
                    (param.get_type(glb), param.get_address(glb))
                };
                let types = type_factory(glb);
                if !types.get(tp).is_primitive_whole(types) {
                    continue;
                }
                let tpsize = types.get(tp).get_size();
                let vn = match data.find_varnode_input(tpsize, &paddr) {
                    Some(vn) => vn,
                    None => continue,
                };
                if data.vn(vn).get_size() < min_double_size {
                    continue;
                }
                let half_size = data.vn(vn).get_size() / 2;
                lovec.clear();
                hivec.clear();
                let mut other_use = false;
                for &subop in data.vn(vn).descend() {
                    if data.op(subop).code() != OpCode::Subpiece {
                        continue;
                    }
                    let outvn = data.op(subop).get_out().expect("SUBPIECE has no output");
                    if data.vn(outvn).get_size() != half_size {
                        continue;
                    }
                    let cut = data.vn(data.op(subop).get_in(1)).get_offset();
                    if cut == 0 {
                        lovec.push(outvn);
                    } else if cut == half_size as u64 {
                        hivec.push(outvn);
                    } else {
                        other_use = true;
                        break;
                    }
                }
                if !other_use && !lovec.is_empty() && !hivec.is_empty() {
                    for &piecevn in lovec.iter() {
                        if !data.vn(piecevn).is_precis_lo() {
                            data.vbank.get_mut(piecevn).set_precis_lo(&mut data.highs);
                            self.base.count += 1;
                        }
                    }
                    for &piecevn in hivec.iter() {
                        if !data.vn(piecevn).is_precis_hi() {
                            data.vbank.get_mut(piecevn).set_precis_hi(&mut data.highs);
                            self.base.count += 1;
                        }
                    }
                }
            }
        }
        Ok(0)
    }
}

pub struct ActionActiveParam {
    pub base: ActionBase,
}

impl ActionActiveParam {
    pub fn new(group: &str) -> ActionActiveParam {
        ActionActiveParam {
            base: ActionBase::new(0, "activeparam", group),
        }
    }

    fn process_call(
        &mut self,
        data: &mut Funcdata,
        glb: &mut Architecture,
        fc: CallSpecId,
        aliascheck: &mut AliasChecker,
    ) -> Result<()> {
        if !data.call_spec(fc).is_input_active() {
            return Ok(());
        }
        let op = data.call_spec(fc).get_op();
        let trimmable = {
            let numpasses = data.call_spec_mut(fc).get_active_input().get_num_passes();
            numpasses > 0 || data.op(op).code() != OpCode::Callind
        };
        if !data.call_spec_mut(fc).get_active_input().is_fully_checked() {
            FuncCallSpecs::check_input_trial_use(data, fc, aliascheck, glb)?;
        }
        {
            let activeinput = data.call_spec_mut(fc).get_active_input();
            activeinput.finish_pass();
            if activeinput.get_num_passes() > activeinput.get_max_pass() {
                activeinput.mark_fully_checked();
            } else {
                self.base.count += 1;
            }
        }
        if trimmable && data.call_spec_mut(fc).get_active_input().is_fully_checked() {
            if data.call_spec_mut(fc).get_active_input().needs_final_check() {
                FuncCallSpecs::final_input_check(data, fc);
            }
            let mut activeinput = std::mem::replace(data.call_spec_mut(fc).get_active_input(), ParamActive::new(false));
            let resolved = data.call_spec_mut(fc).resolve_model(&mut activeinput, glb);
            let derived = match resolved {
                Ok(()) => data.call_spec(fc).derive_input_map(&mut activeinput, glb),
                Err(err) => Err(err),
            };
            *data.call_spec_mut(fc).get_active_input() = activeinput;
            derived?;
            FuncCallSpecs::build_input_from_trials(data, fc, glb)?;
            data.call_spec_mut(fc).clear_active_input();
            self.base.count += 1;
        }
        Ok(())
    }
}

impl Action for ActionActiveParam {
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
        Some(Box::new(ActionActiveParam::new(self.get_group())))
    }

    fn apply(&mut self, data: &mut Funcdata, glb: &mut Architecture) -> Result<i32> {
        let mut aliascheck = AliasChecker::new();
        if let Some(stackspace) = glb.manager.get_stack_space() {
            aliascheck.gather(data, &stackspace, true, glb);
        }
        let mut index = 0;
        while index < data.num_calls() {
            let fc = data.get_call_specs(index);
            index += 1;
            if let Err(err) = self.process_call(data, glb, fc, &mut aliascheck) {
                if !err.is_lowlevel() {
                    return Err(err);
                }
                let mut message = format!("Error processing {}", data.call_spec(fc).get_name());
                let op = data.call_spec(fc).get_op();
                message.push_str(&format!(" called at {}", data.op(op).get_seq_num()));
                message.push_str(&format!(": {}", err.explain()));
                return Err(Error::Lowlevel(message));
            }
        }
        Ok(0)
    }
}

pub struct ActionActiveReturn {
    pub base: ActionBase,
}

impl ActionActiveReturn {
    pub fn new(group: &str) -> ActionActiveReturn {
        ActionActiveReturn {
            base: ActionBase::new(0, "activereturn", group),
        }
    }
}

impl Action for ActionActiveReturn {
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
        Some(Box::new(ActionActiveReturn::new(self.get_group())))
    }

    fn apply(&mut self, data: &mut Funcdata, glb: &mut Architecture) -> Result<i32> {
        let mut index = 0;
        while index < data.num_calls() {
            let fc = data.get_call_specs(index);
            index += 1;
            if data.call_spec(fc).is_output_active() {
                let mut trialvn: Vec<Option<VarnodeId>> = Vec::new();
                FuncCallSpecs::check_output_trial_use(data, fc, &mut trialvn, glb)?;
                let mut activeoutput =
                    std::mem::replace(data.call_spec_mut(fc).get_active_output(), ParamActive::new(false));
                let derived = data.call_spec(fc).derive_output_map(&mut activeoutput, glb);
                *data.call_spec_mut(fc).get_active_output() = activeoutput;
                derived?;
                FuncCallSpecs::build_output_from_trials(data, fc, &mut trialvn, glb)?;
                data.call_spec_mut(fc).clear_active_output();
                self.base.count += 1;
            }
        }
        Ok(0)
    }
}

pub struct ActionReturnRecovery {
    pub base: ActionBase,
}

impl ActionReturnRecovery {
    pub fn new(group: &str) -> ActionReturnRecovery {
        ActionReturnRecovery {
            base: ActionBase::new(0, "returnrecovery", group),
        }
    }

    fn recover(&mut self, data: &mut Funcdata, glb: &mut Architecture, active: &mut ParamActive) -> Result<bool> {
        let maxancestor = glb.trim_recurse_max;
        let mut ancestor_real = AncestorRealistic::new();
        let mut iter = data.begin_op(OpCode::Return);
        while let Some(op) = iter {
            iter = data.obank.next_in_list(op, PcodeOp::CODE_LIST);
            if data.op(op).is_dead() {
                continue;
            }
            if data.op(op).get_halt_type() != 0 {
                continue;
            }
            for index in 0..active.get_num_trials() {
                let trial = active.get_trial_mut(index);
                if trial.is_checked() {
                    continue;
                }
                let slot = trial.get_slot();
                let vn = data.op(op).get_in(slot);
                if ancestor_real.execute(data, op, slot, trial, false)
                    && data.ancestor_op_use(maxancestor, vn, op, trial, 0, 0)
                {
                    trial.mark_active();
                }
                self.base.count += 1;
            }
        }
        active.finish_pass();
        if active.get_num_passes() > active.get_max_pass() {
            active.mark_fully_checked();
        }
        if active.is_fully_checked() {
            data.get_func_proto().derive_output_map(active, glb)?;
            let mut iter = data.begin_op(OpCode::Return);
            while let Some(op) = iter {
                iter = data.obank.next_in_list(op, PcodeOp::CODE_LIST);
                if data.op(op).is_dead() {
                    continue;
                }
                if data.op(op).get_halt_type() != 0 {
                    continue;
                }
                ActionReturnRecovery::build_return_output(active, op, data, glb)?;
            }
            data.clear_active_output();
            self.base.count += 1;
            return Ok(true);
        }
        Ok(false)
    }

    pub fn build_return_output(
        active: &mut ParamActive,
        retop: OpId,
        data: &mut Funcdata,
        glb: &mut Architecture,
    ) -> Result<()> {
        let mut newparam: Vec<VarnodeId> = Vec::new();
        newparam.push(data.op(retop).get_in(0));
        for index in 0..active.get_num_trials() {
            let curtrial = active.get_trial(index);
            if !curtrial.is_used() {
                break;
            }
            if curtrial.get_slot() >= data.op(retop).num_input() {
                break;
            }
            newparam.push(data.op(retop).get_in(curtrial.get_slot()));
        }
        if newparam.len() <= 2 {
            data.op_set_all_input(retop, &newparam)?;
        } else if newparam.len() == 3 {
            let lovn = newparam[1];
            let hivn = newparam[2];
            let triallo = active.get_trial(0).clone();
            let trialhi = active.get_trial(1).clone();
            let joinaddr = glb.manager.construct_join_address(
                glb.translate.as_deref().expect("missing translator"),
                trialhi.get_address(),
                trialhi.get_size(),
                triallo.get_address(),
                triallo.get_size(),
            )?;
            let retaddr = data.op(retop).get_addr().clone();
            let newop = data.new_op(2, &retaddr);
            data.op_set_opcode(newop, OpCode::Piece, glb);
            let newwhole = data.new_varnode_out(trialhi.get_size() + triallo.get_size(), &joinaddr, newop, glb)?;
            data.vn_mut(newwhole).set_write_mask();
            data.op_insert_before(newop, retop);
            newparam.pop();
            *newparam.last_mut().expect("return parameter list is empty") = newwhole;
            data.op_set_all_input(retop, &newparam)?;
            data.op_set_input(newop, hivn, 0)?;
            data.op_set_input(newop, lovn, 1)?;
        } else {
            newparam.clear();
            newparam.push(data.op(retop).get_in(0));
            let mut offmatch = 0;
            let mut preexist: Option<VarnodeId> = None;
            for index in 0..active.get_num_trials() {
                let curtrial = active.get_trial(index).clone();
                if !curtrial.is_used() {
                    break;
                }
                if curtrial.get_slot() >= data.op(retop).num_input() {
                    break;
                }
                match preexist {
                    None => {
                        preexist = Some(data.op(retop).get_in(curtrial.get_slot()));
                        offmatch = curtrial.get_offset() + curtrial.get_size();
                    }
                    Some(prevn) => {
                        if offmatch != curtrial.get_offset() {
                            break;
                        }
                        offmatch += curtrial.get_size();
                        let vn = data.op(retop).get_in(curtrial.get_slot());
                        let retaddr = data.op(retop).get_addr().clone();
                        let newop = data.new_op(2, &retaddr);
                        data.op_set_opcode(newop, OpCode::Piece, glb);
                        let mut addr = data.vn(prevn).get_addr().clone();
                        if *data.vn(vn).get_addr() < addr {
                            addr = data.vn(vn).get_addr().clone();
                        }
                        let newsize = data.vn(prevn).get_size() + data.vn(vn).get_size();
                        let newout = data.new_varnode_out(newsize, &addr, newop, glb)?;
                        data.vn_mut(newout).set_write_mask();
                        data.op_set_input(newop, vn, 0)?;
                        data.op_set_input(newop, prevn, 1)?;
                        data.op_insert_before(newop, retop);
                        preexist = Some(newout);
                    }
                }
            }
            if let Some(prevn) = preexist {
                newparam.push(prevn);
            }
            data.op_set_all_input(retop, &newparam)?;
        }
        Ok(())
    }
}

impl Action for ActionReturnRecovery {
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
        Some(Box::new(ActionReturnRecovery::new(self.get_group())))
    }

    fn apply(&mut self, data: &mut Funcdata, glb: &mut Architecture) -> Result<i32> {
        let mut active = match data.activeoutput.take() {
            Some(active) => active,
            None => return Ok(0),
        };
        match self.recover(data, glb, &mut active) {
            Ok(cleared) => {
                if !cleared {
                    data.activeoutput = Some(active);
                }
                Ok(0)
            }
            Err(err) => {
                data.activeoutput = Some(active);
                Err(err)
            }
        }
    }
}

pub struct ActionRestrictLocal {
    pub base: ActionBase,
}

impl ActionRestrictLocal {
    pub fn new(group: &str) -> ActionRestrictLocal {
        ActionRestrictLocal {
            base: ActionBase::new(0, "restrictlocal", group),
        }
    }
}

impl Action for ActionRestrictLocal {
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
        Some(Box::new(ActionRestrictLocal::new(self.get_group())))
    }

    fn apply(&mut self, data: &mut Funcdata, glb: &mut Architecture) -> Result<i32> {
        let localscope = data.get_scope_local().expect("function has no local scope");
        let mut index = 0;
        while index < data.num_calls() {
            let fc = data.get_call_specs(index);
            index += 1;
            if !data.call_spec_mut(fc).is_input_locked(glb) {
                continue;
            }
            let spacebase_offset = data.call_spec(fc).get_spacebase_offset();
            if spacebase_offset == FuncCallSpecs::OFFSET_UNKNOWN {
                continue;
            }
            let numparam = data.call_spec(fc).num_params(glb);
            for paramindex in 0..numparam {
                let (addr, psize) = {
                    let param = data
                        .call_spec_mut(fc)
                        .get_param(paramindex, glb)
                        .expect("parameter is missing");
                    (param.get_address(glb), param.get_size(glb))
                };
                let spc = addr.get_space().expect("parameter address has no space").clone();
                let tp = spc.get_type();
                if tp == SpaceType::Spacebase {
                    let off = spc.wrap_offset(spacebase_offset.wrapping_add(addr.get_offset()));
                    Database::local_mark_not_mapped(glb, data, localscope, &spc, off, psize, true);
                } else if tp == SpaceType::Join {
                    let join_rec = glb.manager.find_join(addr.get_offset())?;
                    for piece in 0..join_rec.num_pieces() {
                        let vdata = join_rec.get_piece(piece).clone();
                        let piecespc = vdata.space.clone().expect("join piece has no space");
                        if piecespc.get_type() == SpaceType::Spacebase {
                            let off = piecespc.wrap_offset(spacebase_offset.wrapping_add(vdata.offset));
                            Database::local_mark_not_mapped(
                                glb,
                                data,
                                localscope,
                                &piecespc,
                                off,
                                vdata.size as i32,
                                true,
                            );
                        }
                    }
                }
            }
        }
        let effects: Vec<EffectRecord> = data.get_func_proto().get_effects(glb).to_vec();
        for effect in effects.iter() {
            if effect.get_type() == EffectRecord::KILLEDBYCALL {
                continue;
            }
            let vn = data.find_varnode_input(effect.get_size(), &effect.get_address());
            if let Some(vn) = vn
                && data.vn(vn).is_unaffected()
            {
                let descend = data.vn(vn).descend().to_vec();
                for op in descend {
                    if data.op(op).code() != OpCode::Copy {
                        continue;
                    }
                    let outvn = data.op(op).get_out().expect("COPY has no output");
                    if !symbol_table(glb)
                        .scope(localscope)
                        .local_data()
                        .is_unaffected_storage(data, outvn)
                    {
                        continue;
                    }
                    let outspc = data.vn(outvn).get_space().expect("varnode has no space").clone();
                    let outoff = data.vn(outvn).get_offset();
                    let outsize = data.vn(outvn).get_size();
                    Database::local_mark_not_mapped(glb, data, localscope, &outspc, outoff, outsize, false);
                }
            }
        }
        Ok(0)
    }
}

pub struct ActionLikelyTrash {
    pub base: ActionBase,
}

impl ActionLikelyTrash {
    pub fn new(group: &str) -> ActionLikelyTrash {
        ActionLikelyTrash {
            base: ActionBase::new(0, "likelytrash", group),
        }
    }

    pub fn count_marks(data: &Funcdata, op: OpId) -> u32 {
        let mut res = 0;
        for slot in 0..data.op(op).num_input() {
            let mut vn = data.op(op).get_in(slot);
            loop {
                if data.vn(vn).is_mark() {
                    res += 1;
                    break;
                }
                if !data.vn(vn).is_written() {
                    break;
                }
                let def_op = data.vn(vn).get_def().expect("written varnode has no defining op");
                if def_op == op {
                    res += 1;
                    break;
                } else if data.op(def_op).code() != OpCode::Indirect {
                    break;
                }
                vn = data.op(def_op).get_in(0);
            }
        }
        res
    }

    pub fn trace_trash(data: &mut Funcdata, vn: VarnodeId, indlist: &mut Vec<OpId>) -> bool {
        let mut allroutes: Vec<OpId> = Vec::new();
        let mut markedlist: Vec<VarnodeId> = Vec::new();
        let mut traced = 0;
        data.vn_mut(vn).set_mark();
        markedlist.push(vn);
        let mut istrash = true;
        while traced < markedlist.len() {
            let curvn = markedlist[traced];
            traced += 1;
            let descend = data.vn(curvn).descend().to_vec();
            for op in descend {
                let outvn = data.op(op).get_out();
                match data.op(op).code() {
                    OpCode::Indirect => {
                        let outvn = outvn.expect("INDIRECT has no output");
                        if data.vn(outvn).is_persist() {
                            istrash = false;
                        } else if data.op(op).is_indirect_store() {
                            if !data.vn(outvn).is_mark() {
                                data.vn_mut(outvn).set_mark();
                                markedlist.push(outvn);
                            }
                        } else {
                            indlist.push(op);
                        }
                    }
                    OpCode::Subpiece => {
                        let outvn = outvn.expect("SUBPIECE has no output");
                        if data.vn(outvn).is_persist() {
                            istrash = false;
                        } else if !data.vn(outvn).is_mark() {
                            data.vn_mut(outvn).set_mark();
                            markedlist.push(outvn);
                        }
                    }
                    OpCode::Multiequal | OpCode::Piece => {
                        let outvn = outvn.expect("op has no output");
                        if data.vn(outvn).is_persist() {
                            istrash = false;
                        } else {
                            if !data.op(op).is_mark() {
                                data.op_mut(op).set_mark();
                                allroutes.push(op);
                            }
                            let nummark = ActionLikelyTrash::count_marks(data, op);
                            if nummark == data.op(op).num_input() as u32 && !data.vn(outvn).is_mark() {
                                data.vn_mut(outvn).set_mark();
                                markedlist.push(outvn);
                            }
                        }
                    }
                    OpCode::IntAnd => {
                        let constvn = data.op(op).get_in(1);
                        let mut matched = false;
                        if data.vn(constvn).is_constant() {
                            let val = data.vn(constvn).get_offset();
                            let mask = calc_mask(data.vn(constvn).get_size());
                            if val == (mask.wrapping_shl(8) & mask)
                                || val == (mask.wrapping_shl(16) & mask)
                                || val == (mask.wrapping_shl(32) & mask)
                            {
                                indlist.push(op);
                                matched = true;
                            }
                        }
                        if !matched {
                            istrash = false;
                        }
                    }
                    _ => {
                        istrash = false;
                    }
                }
                if !istrash {
                    break;
                }
            }
            if !istrash {
                break;
            }
        }
        for &op in allroutes.iter() {
            let outvn = data.op(op).get_out().expect("op has no output");
            if !data.vn(outvn).is_mark() {
                istrash = false;
            }
            data.op_mut(op).clear_mark();
        }
        for &markedvn in markedlist.iter() {
            data.vn_mut(markedvn).clear_mark();
        }
        istrash
    }
}

impl Action for ActionLikelyTrash {
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
        Some(Box::new(ActionLikelyTrash::new(self.get_group())))
    }

    fn apply(&mut self, data: &mut Funcdata, glb: &mut Architecture) -> Result<i32> {
        let mut indlist: Vec<OpId> = Vec::new();
        let trash: Vec<VarnodeData> = data.get_func_proto().get_trash(glb).to_vec();
        for vdata in trash.iter() {
            let vn = match data.find_covered_input(vdata.size as i32, &vdata.get_addr()) {
                Some(vn) => vn,
                None => continue,
            };
            if data.vn(vn).is_type_lock() || data.vn(vn).is_name_lock() {
                continue;
            }
            indlist.clear();
            if !ActionLikelyTrash::trace_trash(data, vn, &mut indlist) {
                continue;
            }
            for &op in indlist.iter() {
                if data.op(op).code() == OpCode::Indirect {
                    let outvn = data.op(op).get_out().expect("INDIRECT has no output");
                    let size = data.vn(outvn).get_size();
                    let constvn = data.new_constant(size, 0, glb);
                    data.op_set_input(op, constvn, 0)?;
                    data.mark_indirect_creation(op, false, glb)?;
                } else if data.op(op).code() == OpCode::IntAnd {
                    let size = data.vn(data.op(op).get_in(1)).get_size();
                    let constvn = data.new_constant(size, 0, glb);
                    data.op_set_input(op, constvn, 1)?;
                }
                self.base.count += 1;
            }
        }
        Ok(0)
    }
}

pub struct ActionRestructureVarnode {
    pub base: ActionBase,
    pub numpass: i32,
}

impl ActionRestructureVarnode {
    pub fn new(group: &str) -> ActionRestructureVarnode {
        ActionRestructureVarnode {
            base: ActionBase::new(0, "restructure_varnode", group),
            numpass: 0,
        }
    }

    pub fn is_copy_constant(data: &Funcdata, vn: VarnodeId) -> bool {
        if data.vn(vn).is_constant() {
            return true;
        }
        if !data.vn(vn).is_written() {
            return false;
        }
        let def = data.vn(vn).get_def().expect("written varnode has no defining op");
        if data.op(def).code() != OpCode::Copy {
            return false;
        }
        data.vn(data.op(def).get_in(0)).is_constant()
    }

    pub fn is_delayed_constant(data: &Funcdata, vn: VarnodeId) -> bool {
        if data.vn(vn).is_constant() {
            return true;
        }
        if !data.vn(vn).is_written() {
            return false;
        }
        let op = data.vn(vn).get_def().expect("written varnode has no defining op");
        let opc = data.op(op).code();
        if opc == OpCode::Copy {
            return data.vn(data.op(op).get_in(0)).is_constant();
        }
        if opc != OpCode::IntAdd {
            return false;
        }
        if !ActionRestructureVarnode::is_copy_constant(data, data.op(op).get_in(1)) {
            return false;
        }
        if !ActionRestructureVarnode::is_copy_constant(data, data.op(op).get_in(0)) {
            return false;
        }
        true
    }

    pub fn protect_switch_path_indirects(data: &mut Funcdata, op: OpId) {
        let mut last_indirect: Option<OpId> = None;
        let mut cur_vn = data.op(op).get_in(0);
        while data.vn(cur_vn).is_written() {
            let cur_op = data.vn(cur_vn).get_def().expect("written varnode has no defining op");
            let eval_type = data.op(cur_op).get_eval_type();
            if (eval_type & (PcodeOp::BINARY | PcodeOp::TERNARY)) != 0 {
                if data.op(cur_op).num_input() > 1 {
                    if ActionRestructureVarnode::is_delayed_constant(data, data.op(cur_op).get_in(1)) {
                        cur_vn = data.op(cur_op).get_in(0);
                    } else if ActionRestructureVarnode::is_delayed_constant(data, data.op(cur_op).get_in(0)) {
                        cur_vn = data.op(cur_op).get_in(1);
                    } else {
                        return;
                    }
                } else {
                    cur_vn = data.op(cur_op).get_in(0);
                }
            } else if (eval_type & PcodeOp::UNARY) != 0 {
                cur_vn = data.op(cur_op).get_in(0);
            } else if data.op(cur_op).code() == OpCode::Indirect {
                last_indirect = Some(cur_op);
                cur_vn = data.op(cur_op).get_in(0);
            } else if data.op(cur_op).code() == OpCode::Load {
                cur_vn = data.op(cur_op).get_in(1);
            } else if data.op(cur_op).code() == OpCode::Multiequal {
                for slot in 0..data.op(cur_op).num_input() {
                    let invn = data.op(cur_op).get_in(slot);
                    if !data.vn(invn).is_written() {
                        continue;
                    }
                    let in_op = data.vn(invn).get_def().expect("written varnode has no defining op");
                    if data.op(in_op).code() == OpCode::Indirect {
                        data.op_mut(in_op).set_no_indirect_collapse();
                        break;
                    }
                }
                return;
            } else {
                return;
            }
        }
        if !data.vn(cur_vn).is_constant() {
            return;
        }
        if let Some(last_indirect) = last_indirect {
            data.op_mut(last_indirect).set_no_indirect_collapse();
        }
    }

    pub fn protect_switch_paths(data: &mut Funcdata, _glb: &mut Architecture) {
        let size = data.block(data.bblocks).get_size();
        for index in 0..size {
            let bl = data.block(data.bblocks).get_block(index);
            let op = match data.block_last_op(bl) {
                Some(op) => op,
                None => continue,
            };
            if data.op(op).code() != OpCode::Branchind {
                continue;
            }
            ActionRestructureVarnode::protect_switch_path_indirects(data, op);
        }
    }
}

impl Action for ActionRestructureVarnode {
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
        Some(Box::new(ActionRestructureVarnode::new(self.get_group())))
    }

    fn reset(&mut self, _data: &mut Funcdata, _glb: &mut Architecture) {
        self.numpass = 0;
    }

    fn apply(&mut self, data: &mut Funcdata, glb: &mut Architecture) -> Result<i32> {
        let l1 = data.get_scope_local().expect("function has no local scope");
        let aliasyes = self.numpass != 0;
        Database::local_restructure_varnode(glb, data, l1, aliasyes)?;
        if data.sync_varnodes_with_symbols(l1, false, aliasyes, glb)? {
            self.base.count += 1;
        }
        if data.is_jumptable_recovery_on() {
            ActionRestructureVarnode::protect_switch_paths(data, glb);
        }
        self.numpass += 1;
        Ok(0)
    }
}

pub struct ActionMappedLocalSync {
    pub base: ActionBase,
}

impl ActionMappedLocalSync {
    pub fn new(group: &str) -> ActionMappedLocalSync {
        ActionMappedLocalSync {
            base: ActionBase::new(0, "mapped_local_sync", group),
        }
    }
}

impl Action for ActionMappedLocalSync {
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
        Some(Box::new(ActionMappedLocalSync::new(self.get_group())))
    }

    fn apply(&mut self, data: &mut Funcdata, glb: &mut Architecture) -> Result<i32> {
        let l1 = data.get_scope_local().expect("function has no local scope");
        if data.sync_varnodes_with_symbols(l1, true, true, glb)? {
            self.base.count += 1;
        }
        if symbol_table(glb).scope(l1).local_data().has_overlap_probems() {
            data.warning_header("Could not reconcile some variable overlaps", glb);
        }
        Ok(0)
    }
}

pub struct ActionMapGlobals {
    pub base: ActionBase,
}

impl ActionMapGlobals {
    pub fn new(group: &str) -> ActionMapGlobals {
        ActionMapGlobals {
            base: ActionBase::new(RULE_ONCEPERFUNC, "mapglobals", group),
        }
    }
}

impl Action for ActionMapGlobals {
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
        Some(Box::new(ActionMapGlobals::new(self.get_group())))
    }

    fn apply(&mut self, data: &mut Funcdata, glb: &mut Architecture) -> Result<i32> {
        data.map_globals(glb)?;
        Ok(0)
    }
}

pub struct ActionDominantCopy {
    pub base: ActionBase,
}

impl ActionDominantCopy {
    pub fn new(group: &str) -> ActionDominantCopy {
        ActionDominantCopy {
            base: ActionBase::new(RULE_ONCEPERFUNC, "dominantcopy", group),
        }
    }
}

impl Action for ActionDominantCopy {
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
        Some(Box::new(ActionDominantCopy::new(self.get_group())))
    }

    fn apply(&mut self, data: &mut Funcdata, glb: &mut Architecture) -> Result<i32> {
        Merge::process_copy_trims(data, glb)?;
        Ok(0)
    }
}

pub struct ActionCopyMarker {
    pub base: ActionBase,
}

impl ActionCopyMarker {
    pub fn new(group: &str) -> ActionCopyMarker {
        ActionCopyMarker {
            base: ActionBase::new(RULE_ONCEPERFUNC, "copymarker", group),
        }
    }
}

impl Action for ActionCopyMarker {
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
        Some(Box::new(ActionCopyMarker::new(self.get_group())))
    }

    fn apply(&mut self, data: &mut Funcdata, _glb: &mut Architecture) -> Result<i32> {
        Merge::mark_internal_copies(data)?;
        Ok(0)
    }
}
