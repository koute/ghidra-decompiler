use std::collections::BTreeMap;

use crate::action::{ActionGroupList, Rule, RuleBase};
use crate::address::{Address, calc_mask, leastsigbit_set, mostsigbit_set, popcount};
use crate::architecture::Architecture;
use crate::error::Result;
use crate::float::FloatFormat;
use crate::funcdata::Funcdata;
use crate::merge::Merge;
use crate::op::{OpId, PcodeOp};
use crate::opcodes::OpCode;
use crate::options::OptionSplitDatatypes;
use crate::space::{AddrSpace, SpaceRef};
use crate::transform::{LaneDescription, TransformFlavor, TransformManager};
use crate::typeop::TypeOpFloatInt2Float;
use crate::types::{TypeFactory, TypeId, TypeMetatype};
use crate::unionresolve::ResolveCache;
use crate::varnode::VarnodeId;

fn types(glb: &Architecture) -> &TypeFactory {
    glb.types.as_deref().expect("type factory is not initialized")
}

fn types_mut(glb: &mut Architecture) -> &mut TypeFactory {
    glb.types.as_deref_mut().expect("type factory is not initialized")
}

fn varnode_metatype(vn: VarnodeId, data: &Funcdata, glb: &Architecture) -> TypeMetatype {
    types(glb).get(data.vn(vn).get_type()).get_metatype()
}

fn varnode_type_size(vn: VarnodeId, data: &Funcdata, glb: &Architecture) -> i32 {
    types(glb).get(data.vn(vn).get_type()).get_size()
}

fn space_from_const(vn: VarnodeId, data: &Funcdata, glb: &Architecture) -> SpaceRef {
    data.vn(vn)
        .get_space_from_const(&glb.manager)
        .expect("invalid space constant")
}

fn return_ops(data: &Funcdata) -> Vec<OpId> {
    let mut res = Vec::new();
    let mut current = data.begin_op(OpCode::Return);
    while let Some(op) = current {
        res.push(op);
        current = data.obank.next_in_list(op, PcodeOp::CODE_LIST);
    }
    res
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum ReplaceVarnodeRef {
    Mapped(VarnodeId),
    New(usize),
}

#[derive(Clone, Debug, Default)]
pub struct ReplaceVarnode {
    pub(crate) vn: Option<VarnodeId>,
    pub(crate) replacement: Option<VarnodeId>,
    pub(crate) mask: u64,
    pub(crate) val: u64,
    pub(crate) def: Option<usize>,
}

#[derive(Clone, Debug)]
pub struct ReplaceOp {
    pub(crate) op: Option<OpId>,
    pub(crate) replacement: Option<OpId>,
    pub(crate) opc: OpCode,
    pub(crate) numparams: i32,
    pub(crate) output: Option<ReplaceVarnodeRef>,
    pub(crate) input: Vec<Option<ReplaceVarnodeRef>>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PatchType {
    CopyPatch,
    ComparePatch,
    ParameterPatch,
    ExtensionPatch,
    PushPatch,
    Int2FloatPatch,
}

#[derive(Clone, Debug)]
pub struct PatchRecord {
    pub(crate) patch_type: PatchType,
    pub(crate) patch_op: Option<OpId>,
    pub(crate) in1: Option<ReplaceVarnodeRef>,
    pub(crate) in2: Option<ReplaceVarnodeRef>,
    pub(crate) slot: i32,
}

impl PatchRecord {
    fn new(patch_type: PatchType, patch_op: OpId, in1: ReplaceVarnodeRef) -> PatchRecord {
        PatchRecord {
            patch_type,
            patch_op: Some(patch_op),
            in1: Some(in1),
            in2: None,
            slot: 0,
        }
    }
}

#[derive(Clone, Debug)]
pub struct SubvariableFlow {
    pub(crate) flowsize: i32,
    pub(crate) bitsize: i32,
    pub(crate) returns_traversed: bool,
    pub(crate) aggressive: bool,
    pub(crate) sextrestrictions: bool,
    pub(crate) valid: bool,
    pub(crate) varmap: BTreeMap<VarnodeId, ReplaceVarnode>,
    pub(crate) newvarlist: Vec<ReplaceVarnode>,
    pub(crate) oplist: Vec<ReplaceOp>,
    pub(crate) patchlist: Vec<PatchRecord>,
    pub(crate) worklist: Vec<ReplaceVarnodeRef>,
    pub(crate) pullcount: i32,
}

impl SubvariableFlow {
    pub fn new(
        data: &mut Funcdata,
        glb: &mut Architecture,
        root: VarnodeId,
        mask: u64,
        aggr: bool,
        sext: bool,
        big: bool,
    ) -> SubvariableFlow {
        let mut flow = SubvariableFlow {
            flowsize: 0,
            bitsize: 0,
            returns_traversed: false,
            aggressive: aggr,
            sextrestrictions: sext,
            valid: true,
            varmap: BTreeMap::new(),
            newvarlist: Vec::new(),
            oplist: Vec::new(),
            patchlist: Vec::new(),
            worklist: Vec::new(),
            pullcount: 0,
        };
        if mask == 0 {
            flow.valid = false;
            return flow;
        }
        flow.bitsize = (mostsigbit_set(mask) - leastsigbit_set(mask)) + 1;
        if flow.bitsize <= 8 {
            flow.flowsize = 1;
        } else if flow.bitsize <= 16 {
            flow.flowsize = 2;
        } else if flow.bitsize <= 24 {
            flow.flowsize = 3;
        } else if flow.bitsize <= 32 {
            flow.flowsize = 4;
        } else if flow.bitsize <= 64 {
            if !big {
                flow.valid = false;
                return flow;
            }
            flow.flowsize = 8;
        } else {
            flow.valid = false;
            return flow;
        }
        flow.create_link(None, mask, 0, root, data, glb);
        flow
    }

    pub fn replace_varnode(&self, rvn: ReplaceVarnodeRef) -> &ReplaceVarnode {
        match rvn {
            ReplaceVarnodeRef::Mapped(vn) => self.varmap.get(&vn).expect("missing mapped replacement varnode"),
            ReplaceVarnodeRef::New(index) => &self.newvarlist[index],
        }
    }

    pub fn replace_varnode_mut(&mut self, rvn: ReplaceVarnodeRef) -> &mut ReplaceVarnode {
        match rvn {
            ReplaceVarnodeRef::Mapped(vn) => self.varmap.get_mut(&vn).expect("missing mapped replacement varnode"),
            ReplaceVarnodeRef::New(index) => &mut self.newvarlist[index],
        }
    }

    fn rvn_vn(&self, rvn: ReplaceVarnodeRef) -> VarnodeId {
        self.replace_varnode(rvn)
            .vn
            .expect("replacement node without original varnode")
    }

    fn rvn_mask(&self, rvn: ReplaceVarnodeRef) -> u64 {
        self.replace_varnode(rvn).mask
    }

    fn does_or_set(orop: OpId, mask: u64, data: &Funcdata) -> i32 {
        let op = data.op(orop);
        let index = if data.vn(op.get_in(1)).is_constant() { 1 } else { 0 };
        let constvn = data.vn(op.get_in(index));
        if !constvn.is_constant() {
            return -1;
        }
        let orval = constvn.get_offset();
        if (mask & !orval) == 0 {
            return index;
        }
        -1
    }

    fn does_and_clear(andop: OpId, mask: u64, data: &Funcdata) -> i32 {
        let op = data.op(andop);
        let index = if data.vn(op.get_in(1)).is_constant() { 1 } else { 0 };
        let constvn = data.vn(op.get_in(index));
        if !constvn.is_constant() {
            return -1;
        }
        let andval = constvn.get_offset();
        if (mask & andval) == 0 {
            return index;
        }
        -1
    }

    fn get_replacement_address(&self, rvn: ReplaceVarnodeRef, data: &Funcdata) -> Result<Address> {
        let original = data.vn(self.rvn_vn(rvn));
        let mut addr = original.get_addr().clone();
        let sa = leastsigbit_set(self.rvn_mask(rvn)) / 8;
        if addr.is_big_endian() {
            addr = addr.add((original.get_size() - self.flowsize - sa) as i64);
        } else {
            addr = addr.add(sa as i64);
        }
        addr.renormalize(self.flowsize)?;
        Ok(addr)
    }

    fn set_replacement(
        &mut self,
        vn: VarnodeId,
        mask: u64,
        inworklist: &mut bool,
        data: &mut Funcdata,
        glb: &Architecture,
    ) -> Option<ReplaceVarnodeRef> {
        let original = data.vn(vn);
        if original.is_mark() {
            let res = self
                .varmap
                .get(&vn)
                .expect("marked varnode missing from subvariable map");
            *inworklist = false;
            if res.mask != mask {
                return None;
            }
            return Some(ReplaceVarnodeRef::Mapped(vn));
        }

        if original.is_constant() {
            *inworklist = false;
            if self.sextrestrictions {
                let cval = original.get_offset();
                let smallval = cval & mask;
                let sextval = sign_extend_value(smallval, self.flowsize, original.get_size());
                if sextval != cval {
                    return None;
                }
            }
            return Some(self.add_constant(None, mask, 0, vn, data));
        }

        if original.is_free() {
            return None;
        }

        if original.is_addr_force() && original.get_size() != self.flowsize {
            return None;
        }

        if self.sextrestrictions {
            if original.get_size() != self.flowsize {
                if !self.aggressive && original.is_input() {
                    return None;
                }
                if original.is_persist() {
                    return None;
                }
            }
            if original.is_type_lock()
                && varnode_metatype(vn, data, glb) != TypeMetatype::PartialStruct
                && varnode_type_size(vn, data, glb) != self.flowsize
            {
                return None;
            }
        } else {
            if self.bitsize >= 8 {
                if !self.aggressive && (original.get_consume() & !mask) != 0 {
                    return None;
                }
                if original.is_type_lock() && varnode_metatype(vn, data, glb) != TypeMetatype::PartialStruct {
                    let size = varnode_type_size(vn, data, glb);
                    if size != self.flowsize {
                        return None;
                    }
                }
            }

            if original.is_input() {
                if self.bitsize < 8 {
                    return None;
                }
                if (mask & 1) == 0 {
                    return None;
                }
            }
        }

        let mut res = ReplaceVarnode {
            vn: Some(vn),
            replacement: None,
            mask,
            val: 0,
            def: None,
        };
        *inworklist = true;
        if original.get_size() == self.flowsize {
            if mask == calc_mask(self.flowsize) {
                *inworklist = false;
                res.replacement = Some(vn);
            } else if mask == 1 && original.is_written() {
                let def = original.get_def().expect("written varnode without defining op");
                if data.op(def).is_bool_output() {
                    *inworklist = false;
                    res.replacement = Some(vn);
                }
            }
        }
        match self.varmap.get_mut(&vn) {
            Some(entry) => {
                entry.vn = res.vn;
                entry.replacement = res.replacement;
                entry.mask = res.mask;
                entry.def = res.def;
            }
            None => {
                self.varmap.insert(vn, res);
            }
        }
        data.vn_mut(vn).set_mark();
        Some(ReplaceVarnodeRef::Mapped(vn))
    }

    fn create_op(&mut self, opc: OpCode, numparam: i32, outrvn: ReplaceVarnodeRef, data: &Funcdata) -> usize {
        if let Some(def) = self.replace_varnode(outrvn).def {
            return def;
        }
        let original = self.rvn_vn(outrvn);
        let rop = self.oplist.len();
        self.oplist.push(ReplaceOp {
            op: data.vn(original).get_def(),
            replacement: None,
            opc,
            numparams: numparam,
            output: Some(outrvn),
            input: Vec::new(),
        });
        self.replace_varnode_mut(outrvn).def = Some(rop);
        rop
    }

    fn create_op_down(&mut self, opc: OpCode, numparam: i32, op: OpId, inrvn: ReplaceVarnodeRef, slot: i32) -> usize {
        let rop = self.oplist.len();
        let mut input = Vec::new();
        while input.len() <= slot as usize {
            input.push(None);
        }
        input[slot as usize] = Some(inrvn);
        self.oplist.push(ReplaceOp {
            op: Some(op),
            replacement: None,
            opc,
            numparams: numparam,
            output: None,
            input,
        });
        rop
    }

    fn try_call_pull(
        &mut self,
        op: OpId,
        rvn: ReplaceVarnodeRef,
        slot: i32,
        data: &mut Funcdata,
        glb: &Architecture,
    ) -> bool {
        if slot == 0 {
            return false;
        }
        if !self.aggressive && (data.vn(self.rvn_vn(rvn)).get_consume() & !self.rvn_mask(rvn)) != 0 {
            return false;
        }
        let fc = match data.get_call_specs_op(op) {
            None => return false,
            Some(fc) => fc,
        };
        if data.call_spec(fc).is_input_active() {
            return false;
        }
        if data.call_spec_mut(fc).is_input_locked(glb) && !data.call_spec(fc).is_dotdotdot() {
            return false;
        }

        let mut patch = PatchRecord::new(PatchType::ParameterPatch, op, rvn);
        patch.slot = slot;
        self.patchlist.push(patch);
        self.pullcount += 1;
        true
    }

    fn try_return_pull(
        &mut self,
        op: OpId,
        rvn: ReplaceVarnodeRef,
        slot: i32,
        data: &mut Funcdata,
        glb: &Architecture,
    ) -> bool {
        if slot == 0 {
            return false;
        }
        if data.get_func_proto().is_output_locked(glb) {
            return false;
        }
        if !self.aggressive && (data.vn(self.rvn_vn(rvn)).get_consume() & !self.rvn_mask(rvn)) != 0 {
            return false;
        }

        if !self.returns_traversed {
            for retop in return_ops(data) {
                if data.op(retop).get_halt_type() != 0 {
                    continue;
                }
                let retvn = data.op(retop).get_in(slot);
                let mut inworklist = false;
                let mask = self.rvn_mask(rvn);
                let rep = match self.set_replacement(retvn, mask, &mut inworklist, data, glb) {
                    None => return false,
                    Some(rep) => rep,
                };
                if inworklist {
                    self.worklist.push(rep);
                } else if data.vn(retvn).is_constant() && retop != op {
                    let mut patch = PatchRecord::new(PatchType::ParameterPatch, retop, rep);
                    patch.slot = slot;
                    self.patchlist.push(patch);
                    self.pullcount += 1;
                }
            }
            self.returns_traversed = true;
        }
        let mut patch = PatchRecord::new(PatchType::ParameterPatch, op, rvn);
        patch.slot = slot;
        self.patchlist.push(patch);
        self.pullcount += 1;
        true
    }

    fn try_call_return_push(
        &mut self,
        op: OpId,
        rvn: ReplaceVarnodeRef,
        data: &mut Funcdata,
        glb: &Architecture,
    ) -> bool {
        if !self.aggressive && (data.vn(self.rvn_vn(rvn)).get_consume() & !self.rvn_mask(rvn)) != 0 {
            return false;
        }
        if (self.rvn_mask(rvn) & 1) == 0 {
            return false;
        }
        if self.bitsize < 8 {
            return false;
        }
        let fc = match data.get_call_specs_op(op) {
            None => return false,
            Some(fc) => fc,
        };
        if data.call_spec(fc).is_output_locked(glb) {
            return false;
        }
        if data.call_spec(fc).is_output_active() {
            return false;
        }

        self.add_push(op, rvn);
        true
    }

    fn try_switch_pull(&mut self, op: OpId, rvn: ReplaceVarnodeRef, data: &Funcdata) -> bool {
        if (self.rvn_mask(rvn) & 1) == 0 {
            return false;
        }
        if (data.vn(self.rvn_vn(rvn)).get_consume() & !self.rvn_mask(rvn)) != 0 {
            return false;
        }
        let mut patch = PatchRecord::new(PatchType::ParameterPatch, op, rvn);
        patch.slot = 0;
        self.patchlist.push(patch);
        self.pullcount += 1;
        true
    }

    fn try_int2_float_pull(&mut self, op: OpId, rvn: ReplaceVarnodeRef, data: &Funcdata) -> bool {
        let mask = self.rvn_mask(rvn);
        if (mask & 1) == 0 {
            return false;
        }
        let vn = self.rvn_vn(rvn);
        let original = data.vn(vn);
        if (original.get_nz_mask() & !mask) != 0 {
            return false;
        }
        if original.get_size() == self.flowsize {
            return false;
        }
        let mut pull_modification = true;
        if original.is_written() {
            let def = original.get_def().expect("written varnode without defining op");
            if data.op(def).code() == OpCode::IntZext
                && original.get_size() == TypeOpFloatInt2Float::preferred_zext_size(self.flowsize)
                && original.lone_descend() == Some(op)
            {
                pull_modification = false;
            }
        }
        self.patchlist
            .push(PatchRecord::new(PatchType::Int2FloatPatch, op, rvn));
        if pull_modification {
            self.pullcount += 1;
        }
        true
    }

    fn trace_forward(&mut self, rvn: ReplaceVarnodeRef, data: &mut Funcdata, glb: &Architecture) -> bool {
        let mut dcount = 0;
        let mut hcount = 0;
        let mut callcount = 0;

        let rvn_vn = self.rvn_vn(rvn);
        let descend: Vec<OpId> = data.vn(rvn_vn).descend().to_vec();
        for (iter, &op) in descend.iter().enumerate() {
            let mask = self.rvn_mask(rvn);
            let outvn_opt = data.op(op).get_out();
            if let Some(outvn) = outvn_opt
                && data.vn(outvn).is_mark()
                && !data.op(op).is_call()
            {
                continue;
            }
            dcount += 1;
            let mut slot = data.op(op).get_slot(rvn_vn);
            let opc = data.op(op).code();
            match opc {
                OpCode::Copy | OpCode::Multiequal | OpCode::IntNegate | OpCode::IntXor => {
                    let rop = self.create_op_down(opc, data.op(op).num_input(), op, rvn, slot);
                    if !self.create_link(Some(rop), mask, -1, outvn_opt.expect("op without output"), data, glb) {
                        return false;
                    }
                    hcount += 1;
                }
                OpCode::IntOr => {
                    if SubvariableFlow::does_or_set(op, mask, data) != -1 {
                        continue;
                    }
                    let rop = self.create_op_down(OpCode::IntOr, 2, op, rvn, slot);
                    if !self.create_link(Some(rop), mask, -1, outvn_opt.expect("op without output"), data, glb) {
                        return false;
                    }
                    hcount += 1;
                }
                OpCode::IntAnd => {
                    let outvn = outvn_opt.expect("op without output");
                    let in1 = data.op(op).get_in(1);
                    if data.vn(in1).is_constant() && data.vn(in1).get_offset() == mask {
                        if data.vn(outvn).get_size() == self.flowsize && (mask & 1) != 0 {
                            self.add_terminal_patch(op, rvn);
                            hcount += 1;
                            continue;
                        }
                        let consume = data.vn(outvn).get_consume();
                        if !self.aggressive && (consume & mask) != consume {
                            self.add_extension_patch(rvn, op, -1);
                            hcount += 1;
                            continue;
                        }
                    }
                    if SubvariableFlow::does_and_clear(op, mask, data) != -1 {
                        continue;
                    }
                    let rop = self.create_op_down(OpCode::IntAnd, 2, op, rvn, slot);
                    if !self.create_link(Some(rop), mask, -1, outvn, data, glb) {
                        return false;
                    }
                    hcount += 1;
                }
                OpCode::IntZext | OpCode::IntSext => {
                    let rop = self.create_op_down(OpCode::Copy, 1, op, rvn, 0);
                    if !self.create_link(Some(rop), mask, -1, outvn_opt.expect("op without output"), data, glb) {
                        return false;
                    }
                    hcount += 1;
                }
                OpCode::IntMult => {
                    if (mask & 1) == 0 {
                        return false;
                    }
                    let other = data.op(op).get_in(1 - slot);
                    let mut sa = leastsigbit_set(data.vn(other).get_nz_mask());
                    sa &= !7;
                    if self.bitsize + sa > 8 * data.vn(rvn_vn).get_size() {
                        return false;
                    }
                    let rop = self.create_op_down(OpCode::IntMult, 2, op, rvn, slot);
                    if !self.create_link(
                        Some(rop),
                        mask.wrapping_shl(sa as u32),
                        -1,
                        outvn_opt.expect("op without output"),
                        data,
                        glb,
                    ) {
                        return false;
                    }
                    hcount += 1;
                }
                OpCode::IntDiv | OpCode::IntRem => {
                    if (mask & 1) == 0 {
                        return false;
                    }
                    if (self.bitsize & 7) != 0 {
                        return false;
                    }
                    if !data.vn_is_zero_extended(data.op(op).get_in(0), self.flowsize) {
                        return false;
                    }
                    if !data.vn_is_zero_extended(data.op(op).get_in(1), self.flowsize) {
                        return false;
                    }
                    let rop = self.create_op_down(opc, 2, op, rvn, slot);
                    if !self.create_link(Some(rop), mask, -1, outvn_opt.expect("op without output"), data, glb) {
                        return false;
                    }
                    hcount += 1;
                }
                OpCode::IntAdd => {
                    if (mask & 1) == 0 {
                        return false;
                    }
                    let rop = self.create_op_down(OpCode::IntAdd, 2, op, rvn, slot);
                    if !self.create_link(Some(rop), mask, -1, outvn_opt.expect("op without output"), data, glb) {
                        return false;
                    }
                    hcount += 1;
                }
                OpCode::IntLeft => {
                    if slot == 1 {
                        if (mask & 1) == 0 {
                            return false;
                        }
                        if self.bitsize < 8 {
                            return false;
                        }
                        self.add_terminal_patch_same_op(op, rvn, slot);
                        hcount += 1;
                        continue;
                    }
                    let outvn = outvn_opt.expect("op without output");
                    let in1 = data.op(op).get_in(1);
                    if !data.vn(in1).is_constant() {
                        return false;
                    }
                    let sa = data.vn(in1).get_offset() as i32;
                    if sa as u32 >= 64 {
                        return false;
                    }
                    let newmask = (mask << sa) & calc_mask(data.vn(outvn).get_size());
                    if newmask == 0 {
                        continue;
                    }
                    if mask != (newmask >> sa) {
                        return false;
                    }
                    if (mask & 1) != 0
                        && sa + self.bitsize == 8 * data.vn(outvn).get_size()
                        && (data.vn(outvn).get_consume() & !newmask) != 0
                    {
                        self.add_extension_patch(rvn, op, sa);
                        hcount += 1;
                        continue;
                    }
                    let rop = self.create_op_down(OpCode::Copy, 1, op, rvn, 0);
                    if !self.create_link(Some(rop), newmask, -1, outvn, data, glb) {
                        return false;
                    }
                    hcount += 1;
                }
                OpCode::IntRight | OpCode::IntSright => {
                    if slot == 1 {
                        if (mask & 1) == 0 {
                            return false;
                        }
                        if self.bitsize < 8 {
                            return false;
                        }
                        self.add_terminal_patch_same_op(op, rvn, slot);
                        hcount += 1;
                        continue;
                    }
                    let outvn = outvn_opt.expect("op without output");
                    let in1 = data.op(op).get_in(1);
                    if !data.vn(in1).is_constant() {
                        return false;
                    }
                    let sa = data.vn(in1).get_offset() as i32;
                    let newmask = if sa as u32 >= 64 { 0 } else { mask >> sa };
                    if newmask == 0 {
                        if opc == OpCode::IntRight {
                            continue;
                        }
                        return false;
                    }
                    if mask != (newmask << sa) {
                        return false;
                    }
                    if data.vn(outvn).get_size() == self.flowsize
                        && (newmask & 1) == 1
                        && data.vn(data.op(op).get_in(0)).get_nz_mask() == mask
                    {
                        self.add_terminal_patch(op, rvn);
                        hcount += 1;
                        continue;
                    }
                    if (newmask & 1) == 1
                        && sa + self.bitsize == 8 * data.vn(outvn).get_size()
                        && (data.vn(outvn).get_consume() & !newmask) != 0
                    {
                        self.add_extension_patch(rvn, op, 0);
                        hcount += 1;
                        continue;
                    }
                    let rop = self.create_op_down(OpCode::Copy, 1, op, rvn, 0);
                    if !self.create_link(Some(rop), newmask, -1, outvn, data, glb) {
                        return false;
                    }
                    hcount += 1;
                }
                OpCode::Subpiece => {
                    let outvn = outvn_opt.expect("op without output");
                    let sa = (data.vn(data.op(op).get_in(1)).get_offset() as i32).wrapping_mul(8);
                    if sa as u32 >= 64 {
                        continue;
                    }
                    let newmask = (mask >> sa) & calc_mask(data.vn(outvn).get_size());
                    if newmask == 0 {
                        continue;
                    }
                    if mask != (newmask << sa) {
                        if self.flowsize > (sa / 8) + data.vn(outvn).get_size() && (mask & 1) != 0 {
                            self.add_terminal_patch_same_op(op, rvn, 0);
                            hcount += 1;
                            continue;
                        }
                        return false;
                    }
                    if (newmask & 1) != 0
                        && data.vn(outvn).get_size() == self.flowsize
                        && (self.bitsize >= 8 || (!newmask & data.vn(outvn).get_nz_mask()) == 0)
                    {
                        self.add_terminal_patch(op, rvn);
                        hcount += 1;
                        continue;
                    }
                    let rop = self.create_op_down(OpCode::Copy, 1, op, rvn, 0);
                    if !self.create_link(Some(rop), newmask, -1, outvn, data, glb) {
                        return false;
                    }
                    hcount += 1;
                }
                OpCode::Piece => {
                    let newmask = if rvn_vn == data.op(op).get_in(0) {
                        mask.wrapping_shl((8 * data.vn(data.op(op).get_in(1)).get_size()) as u32)
                    } else {
                        mask
                    };
                    let rop = self.create_op_down(OpCode::Copy, 1, op, rvn, 0);
                    if !self.create_link(Some(rop), newmask, -1, outvn_opt.expect("op without output"), data, glb) {
                        return false;
                    }
                    hcount += 1;
                }
                OpCode::IntLess | OpCode::IntLessequal => {
                    let othervn = data.op(op).get_in(1 - slot);
                    if !self.aggressive && (data.vn(rvn_vn).get_nz_mask() | mask) != mask {
                        return false;
                    }
                    if data.vn(othervn).is_constant() {
                        if (mask | data.vn(othervn).get_offset()) != mask {
                            return false;
                        }
                    } else if !self.aggressive && (mask | data.vn(othervn).get_nz_mask()) != mask {
                        return false;
                    }
                    if !self.create_compare_bridge(op, rvn, slot, othervn, data, glb) {
                        return false;
                    }
                    hcount += 1;
                }
                OpCode::IntNotequal | OpCode::IntEqual => {
                    let othervn = data.op(op).get_in(1 - slot);
                    if self.bitsize != 1 {
                        if !self.aggressive && (data.vn(rvn_vn).get_nz_mask() | mask) != mask {
                            return false;
                        }
                        if data.vn(othervn).is_constant() {
                            if (mask | data.vn(othervn).get_offset()) != mask {
                                return false;
                            }
                        } else if !self.aggressive && (mask | data.vn(othervn).get_nz_mask()) != mask {
                            return false;
                        }
                        if !self.create_compare_bridge(op, rvn, slot, othervn, data, glb) {
                            return false;
                        }
                    } else {
                        if !data.vn(othervn).is_constant() {
                            return false;
                        }
                        let newmask = data.vn(rvn_vn).get_nz_mask();
                        if newmask != mask {
                            return false;
                        }
                        let mut booldir = if data.vn(othervn).get_offset() == 0 {
                            true
                        } else if data.vn(othervn).get_offset() == newmask {
                            false
                        } else {
                            return false;
                        };
                        if opc == OpCode::IntEqual {
                            booldir = !booldir;
                        }
                        if booldir {
                            self.add_terminal_patch(op, rvn);
                        } else {
                            let rop = self.create_op_down(OpCode::BoolNegate, 1, op, rvn, 0);
                            self.create_new_out(rop, 1);
                            let output = self.oplist[rop].output.expect("missing negation output");
                            self.add_terminal_patch(op, output);
                        }
                    }
                    hcount += 1;
                }
                OpCode::Call | OpCode::Callind => {
                    callcount += 1;
                    if callcount > 1 {
                        slot = data.op(op).get_repeat_slot(op, rvn_vn, slot, &descend, iter);
                    }
                    if !self.try_call_pull(op, rvn, slot, data, glb) {
                        return false;
                    }
                    hcount += 1;
                }
                OpCode::Return => {
                    if !self.try_return_pull(op, rvn, slot, data, glb) {
                        return false;
                    }
                    hcount += 1;
                }
                OpCode::Branchind => {
                    if !self.try_switch_pull(op, rvn, data) {
                        return false;
                    }
                    hcount += 1;
                }
                OpCode::BoolNegate | OpCode::BoolAnd | OpCode::BoolOr | OpCode::BoolXor => {
                    if self.bitsize != 1 {
                        return false;
                    }
                    if mask != 1 {
                        return false;
                    }
                    self.add_boolean_patch(op, rvn, slot);
                }
                OpCode::FloatInt2float => {
                    if !self.try_int2_float_pull(op, rvn, data) {
                        return false;
                    }
                    hcount += 1;
                }
                OpCode::Cbranch => {
                    if self.bitsize != 1 || slot != 1 {
                        return false;
                    }
                    if mask != 1 {
                        return false;
                    }
                    self.add_boolean_patch(op, rvn, 1);
                    hcount += 1;
                }
                _ => return false,
            }
        }
        if dcount != hcount && data.vn(rvn_vn).is_input() {
            return false;
        }
        true
    }

    fn trace_backward(&mut self, rvn: ReplaceVarnodeRef, data: &mut Funcdata, glb: &Architecture) -> bool {
        let op = match data.vn(self.rvn_vn(rvn)).get_def() {
            None => return true,
            Some(op) => op,
        };
        let mask = self.rvn_mask(rvn);
        let opc = data.op(op).code();
        match opc {
            OpCode::Copy | OpCode::Multiequal | OpCode::IntNegate | OpCode::IntXor => {
                let num_input = data.op(op).num_input();
                let rop = self.create_op(opc, num_input, rvn, data);
                for slot in 0..num_input {
                    let invn = data.op(op).get_in(slot);
                    if !self.create_link(Some(rop), mask, slot, invn, data, glb) {
                        return false;
                    }
                }
                return true;
            }
            OpCode::IntAnd => {
                let sa = SubvariableFlow::does_and_clear(op, mask, data);
                if sa != -1 {
                    let rop = self.create_op(OpCode::Copy, 1, rvn, data);
                    let constvn = data.op(op).get_in(sa);
                    self.add_constant(Some(rop), mask, 0, constvn, data);
                } else {
                    let rop = self.create_op(OpCode::IntAnd, 2, rvn, data);
                    if !self.create_link(Some(rop), mask, 0, data.op(op).get_in(0), data, glb) {
                        return false;
                    }
                    if !self.create_link(Some(rop), mask, 1, data.op(op).get_in(1), data, glb) {
                        return false;
                    }
                }
                return true;
            }
            OpCode::IntOr => {
                let sa = SubvariableFlow::does_or_set(op, mask, data);
                if sa != -1 {
                    let rop = self.create_op(OpCode::Copy, 1, rvn, data);
                    let constvn = data.op(op).get_in(sa);
                    self.add_constant(Some(rop), mask, 0, constvn, data);
                } else {
                    let rop = self.create_op(OpCode::IntOr, 2, rvn, data);
                    if !self.create_link(Some(rop), mask, 0, data.op(op).get_in(0), data, glb) {
                        return false;
                    }
                    if !self.create_link(Some(rop), mask, 1, data.op(op).get_in(1), data, glb) {
                        return false;
                    }
                }
                return true;
            }
            OpCode::IntZext | OpCode::IntSext => {
                let in_size = data.vn(data.op(op).get_in(0)).get_size();
                if (mask & calc_mask(in_size)) != mask {
                    if (mask & 1) != 0 && self.flowsize > in_size {
                        self.add_push(op, rvn);
                        return true;
                    }
                } else {
                    let rop = self.create_op(OpCode::Copy, 1, rvn, data);
                    if !self.create_link(Some(rop), mask, 0, data.op(op).get_in(0), data, glb) {
                        return false;
                    }
                    return true;
                }
            }
            OpCode::IntAdd if (mask & 1) != 0 => {
                let rop = if mask == 1 {
                    self.create_op(OpCode::IntXor, 2, rvn, data)
                } else {
                    self.create_op(OpCode::IntAdd, 2, rvn, data)
                };
                if !self.create_link(Some(rop), mask, 0, data.op(op).get_in(0), data, glb) {
                    return false;
                }
                if !self.create_link(Some(rop), mask, 1, data.op(op).get_in(1), data, glb) {
                    return false;
                }
                return true;
            }
            OpCode::IntLeft => {
                let in1 = data.op(op).get_in(1);
                if data.vn(in1).is_constant() {
                    let sa = data.vn(in1).get_offset() as i32;
                    let newmask = if sa as u32 >= 64 { 0 } else { mask >> sa };
                    if newmask == 0 {
                        let rop = self.create_op(OpCode::Copy, 1, rvn, data);
                        self.add_new_constant(Some(rop), 0, 0);
                        return true;
                    }
                    if (newmask << sa) == mask {
                        let rop = self.create_op(OpCode::Copy, 1, rvn, data);
                        if !self.create_link(Some(rop), newmask, 0, data.op(op).get_in(0), data, glb) {
                            return false;
                        }
                        return true;
                    }
                    if (mask & 1) == 0 {
                        return false;
                    }
                    let rop = self.create_op(OpCode::IntLeft, 2, rvn, data);
                    if !self.create_link(Some(rop), mask, 0, data.op(op).get_in(0), data, glb) {
                        return false;
                    }
                    let shift_mask = calc_mask(data.vn(in1).get_size());
                    self.add_constant(Some(rop), shift_mask, 1, in1, data);
                    return true;
                }
            }
            OpCode::IntRight => {
                let in1 = data.op(op).get_in(1);
                if data.vn(in1).is_constant() {
                    let sa = data.vn(in1).get_offset() as i32;
                    if (sa as u32) < 64 {
                        let newmask = (mask << sa) & calc_mask(data.vn(data.op(op).get_in(0)).get_size());
                        if newmask == 0 {
                            let rop = self.create_op(OpCode::Copy, 1, rvn, data);
                            self.add_new_constant(Some(rop), 0, 0);
                            return true;
                        }
                        if (newmask >> sa) == mask {
                            let rop = self.create_op(OpCode::Copy, 1, rvn, data);
                            if !self.create_link(Some(rop), newmask, 0, data.op(op).get_in(0), data, glb) {
                                return false;
                            }
                            return true;
                        }
                    }
                }
            }
            OpCode::IntSright => {
                let in1 = data.op(op).get_in(1);
                if data.vn(in1).is_constant() {
                    let sa = data.vn(in1).get_offset() as i32;
                    if (sa as u32) < 64 {
                        let newmask = (mask << sa) & calc_mask(data.vn(data.op(op).get_in(0)).get_size());
                        if (newmask >> sa) == mask {
                            let rop = self.create_op(OpCode::Copy, 1, rvn, data);
                            if !self.create_link(Some(rop), newmask, 0, data.op(op).get_in(0), data, glb) {
                                return false;
                            }
                            return true;
                        }
                    }
                }
            }
            OpCode::IntMult => {
                let sa = leastsigbit_set(mask);
                if sa != 0 {
                    let sa2 = leastsigbit_set(data.vn(data.op(op).get_in(1)).get_nz_mask());
                    if sa2 < sa {
                        return false;
                    }
                    let newmask = mask.wrapping_shr(sa as u32);
                    let rop = self.create_op(OpCode::IntMult, 2, rvn, data);
                    if !self.create_link(Some(rop), newmask, 0, data.op(op).get_in(0), data, glb) {
                        return false;
                    }
                    if !self.create_link(Some(rop), mask, 1, data.op(op).get_in(1), data, glb) {
                        return false;
                    }
                } else {
                    let rop = if mask == 1 {
                        self.create_op(OpCode::IntAnd, 2, rvn, data)
                    } else {
                        self.create_op(OpCode::IntMult, 2, rvn, data)
                    };
                    if !self.create_link(Some(rop), mask, 0, data.op(op).get_in(0), data, glb) {
                        return false;
                    }
                    if !self.create_link(Some(rop), mask, 1, data.op(op).get_in(1), data, glb) {
                        return false;
                    }
                }
                return true;
            }
            OpCode::IntDiv | OpCode::IntRem => {
                if (mask & 1) == 0 {
                    return false;
                }
                if (self.bitsize & 7) != 0 {
                    return false;
                }
                if !data.vn_is_zero_extended(data.op(op).get_in(0), self.flowsize) {
                    return false;
                }
                if !data.vn_is_zero_extended(data.op(op).get_in(1), self.flowsize) {
                    return false;
                }
                let rop = self.create_op(opc, 2, rvn, data);
                if !self.create_link(Some(rop), mask, 0, data.op(op).get_in(0), data, glb) {
                    return false;
                }
                if !self.create_link(Some(rop), mask, 1, data.op(op).get_in(1), data, glb) {
                    return false;
                }
                return true;
            }
            OpCode::Subpiece => {
                let sa = (data.vn(data.op(op).get_in(1)).get_offset() as i32).wrapping_mul(8);
                let newmask = mask.wrapping_shl(sa as u32);
                let rop = self.create_op(OpCode::Copy, 1, rvn, data);
                if !self.create_link(Some(rop), newmask, 0, data.op(op).get_in(0), data, glb) {
                    return false;
                }
                return true;
            }
            OpCode::Piece => {
                let low_size = data.vn(data.op(op).get_in(1)).get_size();
                if (mask & calc_mask(low_size)) == mask {
                    let rop = self.create_op(OpCode::Copy, 1, rvn, data);
                    if !self.create_link(Some(rop), mask, 0, data.op(op).get_in(1), data, glb) {
                        return false;
                    }
                    return true;
                }
                let sa = low_size * 8;
                let newmask = mask.wrapping_shr(sa as u32);
                if newmask.wrapping_shl(sa as u32) == mask {
                    let rop = self.create_op(OpCode::Copy, 1, rvn, data);
                    if !self.create_link(Some(rop), newmask, 0, data.op(op).get_in(0), data, glb) {
                        return false;
                    }
                    return true;
                }
            }
            OpCode::Call | OpCode::Callind if self.try_call_return_push(op, rvn, data, glb) => {
                return true;
            }
            OpCode::IntEqual
            | OpCode::IntNotequal
            | OpCode::IntSless
            | OpCode::IntSlessequal
            | OpCode::IntLess
            | OpCode::IntLessequal
            | OpCode::IntCarry
            | OpCode::IntScarry
            | OpCode::IntSborrow
            | OpCode::BoolNegate
            | OpCode::BoolXor
            | OpCode::BoolAnd
            | OpCode::BoolOr
            | OpCode::FloatEqual
            | OpCode::FloatNotequal
            | OpCode::FloatLessequal
            | OpCode::FloatNan
                if (mask & 1) != 1 =>
            {
                let rop = self.create_op(OpCode::Copy, 1, rvn, data);
                self.add_new_constant(Some(rop), 0, 0);
                return true;
            }
            _ => {}
        }
        false
    }

    fn trace_forward_sext(&mut self, rvn: ReplaceVarnodeRef, data: &mut Funcdata, glb: &Architecture) -> bool {
        let mut dcount = 0;
        let mut hcount = 0;
        let mut callcount = 0;

        let rvn_vn = self.rvn_vn(rvn);
        let descend: Vec<OpId> = data.vn(rvn_vn).descend().to_vec();
        for (iter, &op) in descend.iter().enumerate() {
            let mask = self.rvn_mask(rvn);
            let outvn_opt = data.op(op).get_out();
            if let Some(outvn) = outvn_opt
                && data.vn(outvn).is_mark()
                && !data.op(op).is_call()
            {
                continue;
            }
            dcount += 1;
            let mut slot = data.op(op).get_slot(rvn_vn);
            let opc = data.op(op).code();
            match opc {
                OpCode::Copy
                | OpCode::Multiequal
                | OpCode::IntNegate
                | OpCode::IntXor
                | OpCode::IntOr
                | OpCode::IntAnd => {
                    let rop = self.create_op_down(opc, data.op(op).num_input(), op, rvn, slot);
                    if !self.create_link(Some(rop), mask, -1, outvn_opt.expect("op without output"), data, glb) {
                        return false;
                    }
                    hcount += 1;
                }
                OpCode::IntSext => {
                    let rop = self.create_op_down(OpCode::Copy, 1, op, rvn, 0);
                    if !self.create_link(Some(rop), mask, -1, outvn_opt.expect("op without output"), data, glb) {
                        return false;
                    }
                    hcount += 1;
                }
                OpCode::IntSright => {
                    let in1 = data.op(op).get_in(1);
                    if !data.vn(in1).is_constant() {
                        return false;
                    }
                    let rop = self.create_op_down(OpCode::IntSright, 2, op, rvn, 0);
                    if !self.create_link(Some(rop), mask, -1, outvn_opt.expect("op without output"), data, glb) {
                        return false;
                    }
                    let shift_mask = calc_mask(data.vn(in1).get_size());
                    self.add_constant(Some(rop), shift_mask, 1, in1, data);
                    hcount += 1;
                }
                OpCode::Subpiece => {
                    let outvn = outvn_opt.expect("op without output");
                    if data.vn(data.op(op).get_in(1)).get_offset() != 0 {
                        return false;
                    }
                    if data.vn(outvn).get_size() > self.flowsize {
                        return false;
                    }
                    if data.vn(outvn).get_size() == self.flowsize {
                        self.add_terminal_patch(op, rvn);
                    } else {
                        self.add_terminal_patch_same_op(op, rvn, 0);
                    }
                    hcount += 1;
                }
                OpCode::IntLess
                | OpCode::IntLessequal
                | OpCode::IntSless
                | OpCode::IntSlessequal
                | OpCode::IntEqual
                | OpCode::IntNotequal => {
                    let othervn = data.op(op).get_in(1 - slot);
                    if !self.create_compare_bridge(op, rvn, slot, othervn, data, glb) {
                        return false;
                    }
                    hcount += 1;
                }
                OpCode::Call | OpCode::Callind => {
                    callcount += 1;
                    if callcount > 1 {
                        slot = data.op(op).get_repeat_slot(op, rvn_vn, slot, &descend, iter);
                    }
                    if !self.try_call_pull(op, rvn, slot, data, glb) {
                        return false;
                    }
                    hcount += 1;
                }
                OpCode::Return => {
                    if !self.try_return_pull(op, rvn, slot, data, glb) {
                        return false;
                    }
                    hcount += 1;
                }
                OpCode::Branchind => {
                    if !self.try_switch_pull(op, rvn, data) {
                        return false;
                    }
                    hcount += 1;
                }
                _ => return false,
            }
        }
        if dcount != hcount && data.vn(rvn_vn).is_input() {
            return false;
        }
        true
    }

    fn trace_backward_sext(&mut self, rvn: ReplaceVarnodeRef, data: &mut Funcdata, glb: &Architecture) -> bool {
        let op = match data.vn(self.rvn_vn(rvn)).get_def() {
            None => return true,
            Some(op) => op,
        };
        let mask = self.rvn_mask(rvn);
        let opc = data.op(op).code();
        match opc {
            OpCode::Copy | OpCode::Multiequal | OpCode::IntNegate | OpCode::IntXor | OpCode::IntAnd | OpCode::IntOr => {
                let num_input = data.op(op).num_input();
                let rop = self.create_op(opc, num_input, rvn, data);
                for slot in 0..num_input {
                    let invn = data.op(op).get_in(slot);
                    if !self.create_link(Some(rop), mask, slot, invn, data, glb) {
                        return false;
                    }
                }
                return true;
            }
            OpCode::IntZext if data.vn(data.op(op).get_in(0)).get_size() < self.flowsize => {
                self.add_push(op, rvn);
                return true;
            }
            OpCode::IntSext => {
                if self.flowsize != data.vn(data.op(op).get_in(0)).get_size() {
                    return false;
                }
                let rop = self.create_op(OpCode::Copy, 1, rvn, data);
                if !self.create_link(Some(rop), mask, 0, data.op(op).get_in(0), data, glb) {
                    return false;
                }
                return true;
            }
            OpCode::IntSright => {
                let in1 = data.op(op).get_in(1);
                if !data.vn(in1).is_constant() {
                    return false;
                }
                let rop = self.create_op(OpCode::IntSright, 2, rvn, data);
                if !self.create_link(Some(rop), mask, 0, data.op(op).get_in(0), data, glb) {
                    return false;
                }
                if self.oplist[rop].input.len() == 1 {
                    let shift_mask = calc_mask(data.vn(in1).get_size());
                    self.add_constant(Some(rop), shift_mask, 1, in1, data);
                }
                return true;
            }
            OpCode::Call | OpCode::Callind if self.try_call_return_push(op, rvn, data, glb) => {
                return true;
            }
            _ => {}
        }
        false
    }

    fn set_rop_input(&mut self, rop: usize, slot: usize, rep: ReplaceVarnodeRef) {
        let input = &mut self.oplist[rop].input;
        while input.len() <= slot {
            input.push(None);
        }
        input[slot] = Some(rep);
    }

    fn create_link(
        &mut self,
        rop: Option<usize>,
        mask: u64,
        slot: i32,
        vn: VarnodeId,
        data: &mut Funcdata,
        glb: &Architecture,
    ) -> bool {
        let mut inworklist = false;
        let rep = match self.set_replacement(vn, mask, &mut inworklist, data, glb) {
            None => return false,
            Some(rep) => rep,
        };

        if let Some(rop) = rop {
            if slot == -1 {
                self.oplist[rop].output = Some(rep);
                self.replace_varnode_mut(rep).def = Some(rop);
            } else {
                self.set_rop_input(rop, slot as usize, rep);
            }
        }

        if inworklist {
            self.worklist.push(rep);
        }
        true
    }

    fn create_compare_bridge(
        &mut self,
        op: OpId,
        inrvn: ReplaceVarnodeRef,
        slot: i32,
        othervn: VarnodeId,
        data: &mut Funcdata,
        glb: &Architecture,
    ) -> bool {
        let mut inworklist = false;
        let mask = self.rvn_mask(inrvn);
        let rep = match self.set_replacement(othervn, mask, &mut inworklist, data, glb) {
            None => return false,
            Some(rep) => rep,
        };

        if slot == 0 {
            self.add_compare_patch(inrvn, rep, op);
        } else {
            self.add_compare_patch(rep, inrvn, op);
        }

        if inworklist {
            self.worklist.push(rep);
        }
        true
    }

    fn add_push(&mut self, push_op: OpId, rvn: ReplaceVarnodeRef) {
        self.patchlist
            .insert(0, PatchRecord::new(PatchType::PushPatch, push_op, rvn));
    }

    fn add_terminal_patch(&mut self, pullop: OpId, rvn: ReplaceVarnodeRef) {
        self.patchlist.push(PatchRecord::new(PatchType::CopyPatch, pullop, rvn));
        self.pullcount += 1;
    }

    fn add_terminal_patch_same_op(&mut self, pullop: OpId, rvn: ReplaceVarnodeRef, slot: i32) {
        let mut patch = PatchRecord::new(PatchType::ParameterPatch, pullop, rvn);
        patch.slot = slot;
        self.patchlist.push(patch);
        self.pullcount += 1;
    }

    fn add_boolean_patch(&mut self, pullop: OpId, rvn: ReplaceVarnodeRef, slot: i32) {
        let mut patch = PatchRecord::new(PatchType::ParameterPatch, pullop, rvn);
        patch.slot = slot;
        self.patchlist.push(patch);
    }

    fn add_extension_patch(&mut self, rvn: ReplaceVarnodeRef, pushop: OpId, sa: i32) {
        let mut patch = PatchRecord::new(PatchType::ExtensionPatch, pushop, rvn);
        patch.slot = if sa == -1 {
            leastsigbit_set(self.rvn_mask(rvn))
        } else {
            sa
        };
        self.patchlist.push(patch);
    }

    fn add_compare_patch(&mut self, in1: ReplaceVarnodeRef, in2: ReplaceVarnodeRef, op: OpId) {
        let mut patch = PatchRecord::new(PatchType::ComparePatch, op, in1);
        patch.in2 = Some(in2);
        self.patchlist.push(patch);
        self.pullcount += 1;
    }

    fn add_constant(
        &mut self,
        rop: Option<usize>,
        mask: u64,
        slot: u32,
        constvn: VarnodeId,
        data: &Funcdata,
    ) -> ReplaceVarnodeRef {
        let sa = leastsigbit_set(mask);
        let val = (mask & data.vn(constvn).get_offset()).wrapping_shr(sa as u32);
        let index = self.newvarlist.len();
        self.newvarlist.push(ReplaceVarnode {
            vn: Some(constvn),
            replacement: None,
            mask,
            val,
            def: None,
        });
        let res = ReplaceVarnodeRef::New(index);
        if let Some(rop) = rop {
            self.set_rop_input(rop, slot as usize, res);
        }
        res
    }

    fn add_new_constant(&mut self, rop: Option<usize>, slot: u32, val: u64) -> ReplaceVarnodeRef {
        let index = self.newvarlist.len();
        self.newvarlist.push(ReplaceVarnode {
            vn: None,
            replacement: None,
            mask: 0,
            val,
            def: None,
        });
        let res = ReplaceVarnodeRef::New(index);
        if let Some(rop) = rop {
            self.set_rop_input(rop, slot as usize, res);
        }
        res
    }

    fn create_new_out(&mut self, rop: usize, mask: u64) {
        let index = self.newvarlist.len();
        self.newvarlist.push(ReplaceVarnode {
            vn: None,
            replacement: None,
            mask,
            val: 0,
            def: Some(rop),
        });
        self.oplist[rop].output = Some(ReplaceVarnodeRef::New(index));
    }

    fn replace_input(&mut self, rvn: ReplaceVarnodeRef, data: &mut Funcdata, glb: &mut Architecture) -> Result<()> {
        let original = self.rvn_vn(rvn);
        let size = data.vn(original).get_size();
        let mut newvn = data.new_unique(size, None, glb);
        newvn = data.set_input_varnode(newvn, glb)?;
        data.total_replace(original, newvn)?;
        data.delete_varnode(original)?;
        self.replace_varnode_mut(rvn).vn = Some(newvn);
        Ok(())
    }

    fn use_same_address(&self, rvn: ReplaceVarnodeRef, data: &Funcdata) -> bool {
        let original = data.vn(self.rvn_vn(rvn));
        let rvn_mask = self.rvn_mask(rvn);
        if original.is_input() {
            return true;
        }
        if original.is_addr_tied() {
            return false;
        }
        if (rvn_mask & 1) == 0 {
            return false;
        }
        if self.bitsize >= 8 {
            return true;
        }
        if self.aggressive {
            return true;
        }
        let mut bitmask: u32 = 1;
        bitmask = bitmask.wrapping_shl(self.bitsize as u32).wrapping_sub(1);
        let mut mask = original.get_consume();
        mask |= bitmask as u64;
        if mask == rvn_mask {
            return true;
        }
        false
    }

    fn get_replace_varnode(
        &mut self,
        rvn: ReplaceVarnodeRef,
        data: &mut Funcdata,
        glb: &mut Architecture,
    ) -> Result<VarnodeId> {
        let node = self.replace_varnode(rvn).clone();
        if let Some(replacement) = node.replacement {
            return Ok(replacement);
        }
        let original = match node.vn {
            None => {
                if node.def.is_none() {
                    return Ok(data.new_constant(self.flowsize, node.val, glb));
                }
                let replacement = data.new_unique(self.flowsize, None, glb);
                self.replace_varnode_mut(rvn).replacement = Some(replacement);
                return Ok(replacement);
            }
            Some(vn) => vn,
        };
        if data.vn(original).is_constant() {
            let new_vn = data.new_constant(self.flowsize, node.val, glb);
            data.vn_copy_symbol_if_valid(new_vn, original, glb)?;
            return Ok(new_vn);
        }

        let isinput = data.vn(original).is_input();
        let mut replacement = if self.use_same_address(rvn, data) {
            let addr = self.get_replacement_address(rvn, data)?;
            if isinput {
                self.replace_input(rvn, data, glb)?;
            }
            data.new_varnode(self.flowsize, &addr, None, glb)?
        } else {
            data.new_unique(self.flowsize, None, glb)
        };
        self.replace_varnode_mut(rvn).replacement = Some(replacement);
        if isinput {
            replacement = data.set_input_varnode(replacement, glb)?;
            self.replace_varnode_mut(rvn).replacement = Some(replacement);
        }
        Ok(replacement)
    }

    fn process_next_work(&mut self, data: &mut Funcdata, glb: &Architecture) -> bool {
        let rvn = self.worklist.pop().expect("empty subvariable worklist");

        if self.sextrestrictions {
            if !self.trace_backward_sext(rvn, data, glb) {
                return false;
            }
            return self.trace_forward_sext(rvn, data, glb);
        }
        if !self.trace_backward(rvn, data, glb) {
            return false;
        }
        self.trace_forward(rvn, data, glb)
    }

    pub fn do_trace(&mut self, data: &mut Funcdata, glb: &Architecture) -> bool {
        self.pullcount = 0;
        let mut retval = false;
        if self.valid {
            retval = true;
            while !self.worklist.is_empty() {
                if !self.process_next_work(data, glb) {
                    retval = false;
                    break;
                }
            }
        }

        for &vn in self.varmap.keys() {
            data.vn_mut(vn).clear_mark();
        }

        if !retval {
            return false;
        }
        if self.pullcount == 0 {
            return false;
        }
        true
    }

    pub fn do_replacement(&mut self, data: &mut Funcdata, glb: &mut Architecture) -> Result<()> {
        let mut piter = 0;
        while piter < self.patchlist.len() {
            if self.patchlist[piter].patch_type != PatchType::PushPatch {
                break;
            }
            let push_op = self.patchlist[piter].patch_op.expect("patch without op");
            let in1 = self.patchlist[piter].in1.expect("patch without input");
            let new_vn = self.get_replace_varnode(in1, data, glb)?;
            let old_vn = data.op(push_op).get_out().expect("push op without output");
            data.op_set_output(push_op, new_vn, glb)?;

            let addr = data.op(push_op).get_addr().clone();
            let new_zext = data.new_op(1, &addr);
            data.op_set_opcode(new_zext, OpCode::IntZext, glb);
            data.op_set_input(new_zext, new_vn, 0)?;
            data.op_set_output(new_zext, old_vn, glb)?;
            data.op_insert_after(new_zext, push_op);
            piter += 1;
        }

        for index in 0..self.oplist.len() {
            let original = self.oplist[index].op.expect("replace op without original");
            let addr = data.op(original).get_addr().clone();
            let newop = data.new_op(self.oplist[index].numparams, &addr);
            self.oplist[index].replacement = Some(newop);
            data.op_set_opcode(newop, self.oplist[index].opc, glb);
            let rout = self.oplist[index].output.expect("replace op without output");
            let outvn = self.get_replace_varnode(rout, data, glb)?;
            data.op_set_output(newop, outvn, glb)?;
            data.op_insert_after(newop, original);
        }

        for index in 0..self.oplist.len() {
            let newop = self.oplist[index].replacement.expect("missing replacement op");
            for slot in 0..self.oplist[index].input.len() {
                let input = self.oplist[index].input[slot].expect("missing replace op input");
                let invn = self.get_replace_varnode(input, data, glb)?;
                data.op_set_input(newop, invn, slot as i32)?;
            }
        }

        while piter < self.patchlist.len() {
            let patch = self.patchlist[piter].clone();
            piter += 1;
            let pullop = patch.patch_op.expect("patch without op");
            let in1 = patch.in1.expect("patch without input");
            match patch.patch_type {
                PatchType::CopyPatch => {
                    while data.op(pullop).num_input() > 1 {
                        let last = data.op(pullop).num_input() - 1;
                        data.op_remove_input(pullop, last);
                    }
                    let invn = self.get_replace_varnode(in1, data, glb)?;
                    data.op_set_input(pullop, invn, 0)?;
                    data.op_set_opcode(pullop, OpCode::Copy, glb);
                }
                PatchType::ComparePatch => {
                    let invn = self.get_replace_varnode(in1, data, glb)?;
                    data.op_set_input(pullop, invn, 0)?;
                    let in2 = patch.in2.expect("compare patch without second input");
                    let invn2 = self.get_replace_varnode(in2, data, glb)?;
                    data.op_set_input(pullop, invn2, 1)?;
                }
                PatchType::ParameterPatch => {
                    let invn = self.get_replace_varnode(in1, data, glb)?;
                    data.op_set_input(pullop, invn, patch.slot)?;
                }
                PatchType::ExtensionPatch => {
                    let sa = patch.slot;
                    let mut invec: Vec<VarnodeId> = Vec::new();
                    let in_vn = self.get_replace_varnode(in1, data, glb)?;
                    let out_size = data
                        .vn(data.op(pullop).get_out().expect("extension op without output"))
                        .get_size();
                    if sa == 0 {
                        invec.push(in_vn);
                        let opc = if data.vn(in_vn).get_size() == out_size {
                            OpCode::Copy
                        } else {
                            OpCode::IntZext
                        };
                        data.op_set_opcode(pullop, opc, glb);
                        data.op_set_all_input(pullop, &invec)?;
                    } else {
                        if data.vn(in_vn).get_size() != out_size {
                            let addr = data.op(pullop).get_addr().clone();
                            let zextop = data.new_op(1, &addr);
                            data.op_set_opcode(zextop, OpCode::IntZext, glb);
                            let zextout = data.new_unique_out(out_size, zextop, glb)?;
                            data.op_set_input(zextop, in_vn, 0)?;
                            data.op_insert_before(zextop, pullop);
                            invec.push(zextout);
                        } else {
                            invec.push(in_vn);
                        }
                        invec.push(data.new_constant(4, sa as i64 as u64, glb));
                        data.op_set_all_input(pullop, &invec)?;
                        data.op_set_opcode(pullop, OpCode::IntLeft, glb);
                    }
                }
                PatchType::PushPatch => {}
                PatchType::Int2FloatPatch => {
                    let addr = data.op(pullop).get_addr().clone();
                    let zext_op = data.new_op(1, &addr);
                    data.op_set_opcode(zext_op, OpCode::IntZext, glb);
                    let invn = self.get_replace_varnode(in1, data, glb)?;
                    data.op_set_input(zext_op, invn, 0)?;
                    let sizeout = TypeOpFloatInt2Float::preferred_zext_size(data.vn(invn).get_size());
                    let outvn = data.new_unique_out(sizeout, zext_op, glb)?;
                    data.op_insert_before(zext_op, pullop);
                    data.op_set_input(pullop, outvn, 0)?;
                }
            }
        }
        Ok(())
    }
}

fn sign_extend_value(val: u64, sizein: i32, sizeout: i32) -> u64 {
    crate::address::sign_extend_size(val, sizein, sizeout)
}

fn run_subvariable_flow(
    data: &mut Funcdata,
    glb: &mut Architecture,
    root: VarnodeId,
    mask: u64,
    aggr: bool,
    sext: bool,
    big: bool,
) -> Result<i32> {
    let mut subflow = SubvariableFlow::new(data, glb, root, mask, aggr, sext, big);
    if !subflow.do_trace(data, glb) {
        return Ok(0);
    }
    subflow.do_replacement(data, glb)?;
    Ok(1)
}

pub struct RuleSubvarAnd {
    base: RuleBase,
}

impl RuleSubvarAnd {
    pub fn new(group: &str) -> RuleSubvarAnd {
        RuleSubvarAnd {
            base: RuleBase::new(group, 0, "subvar_and"),
        }
    }
}

impl Rule for RuleSubvarAnd {
    fn base(&self) -> &RuleBase {
        &self.base
    }

    fn base_mut(&mut self) -> &mut RuleBase {
        &mut self.base
    }

    fn clone_rule(&self, grouplist: &ActionGroupList) -> Option<Box<dyn Rule>> {
        if !grouplist.contains(self.get_group()) {
            return None;
        }
        Some(Box::new(RuleSubvarAnd::new(self.get_group())))
    }

    fn get_op_list(&self, oplist: &mut Vec<OpCode>) {
        oplist.push(OpCode::IntAnd);
    }

    fn apply_op(&mut self, op: OpId, data: &mut Funcdata, glb: &mut Architecture) -> Result<i32> {
        let in1 = data.op(op).get_in(1);
        if !data.vn(in1).is_constant() {
            return Ok(0);
        }
        let vn = data.op(op).get_in(0);
        let outvn = data.op(op).get_out().expect("and without output");
        let consume = data.vn(outvn).get_consume();
        if consume != data.vn(in1).get_offset() {
            return Ok(0);
        }
        if (consume & 1) == 0 {
            return Ok(0);
        }
        let mut cmask: u64;
        if consume == 1 {
            cmask = 1;
        } else {
            cmask = calc_mask(data.vn(vn).get_size());
            cmask >>= 8;
            while cmask != 0 {
                if cmask == consume {
                    break;
                }
                cmask >>= 8;
            }
        }
        if cmask == 0 {
            return Ok(0);
        }
        if data.vn(outvn).has_no_descend() {
            return Ok(0);
        }
        run_subvariable_flow(data, glb, vn, cmask, false, false, false)
    }
}

pub struct RuleSubvarSubpiece {
    base: RuleBase,
}

impl RuleSubvarSubpiece {
    pub fn new(group: &str) -> RuleSubvarSubpiece {
        RuleSubvarSubpiece {
            base: RuleBase::new(group, 0, "subvar_subpiece"),
        }
    }
}

impl Rule for RuleSubvarSubpiece {
    fn base(&self) -> &RuleBase {
        &self.base
    }

    fn base_mut(&mut self) -> &mut RuleBase {
        &mut self.base
    }

    fn clone_rule(&self, grouplist: &ActionGroupList) -> Option<Box<dyn Rule>> {
        if !grouplist.contains(self.get_group()) {
            return None;
        }
        Some(Box::new(RuleSubvarSubpiece::new(self.get_group())))
    }

    fn get_op_list(&self, oplist: &mut Vec<OpCode>) {
        oplist.push(OpCode::Subpiece);
    }

    fn apply_op(&mut self, op: OpId, data: &mut Funcdata, glb: &mut Architecture) -> Result<i32> {
        let vn = data.op(op).get_in(0);
        let outvn = data.op(op).get_out().expect("subpiece without output");
        let flowsize = data.vn(outvn).get_size();
        let sa = data.vn(data.op(op).get_in(1)).get_offset() as i32;
        if (flowsize + sa) as u32 > 8 {
            return Ok(0);
        }
        let mut mask = calc_mask(flowsize);
        mask = mask.wrapping_shl((8 * sa) as u32);
        let aggressive = data.vn(outvn).is_ptr_flow();
        if !aggressive {
            let consume = data.vn(vn).get_consume();
            if (consume & mask) != consume {
                return Ok(0);
            }
            if data.vn(outvn).has_no_descend() {
                return Ok(0);
            }
        }
        let mut big = false;
        if flowsize >= 8 && data.vn(vn).is_input() && data.vn(vn).lone_descend() == Some(op) {
            big = true;
        }
        run_subvariable_flow(data, glb, vn, mask, aggressive, false, big)
    }
}

pub struct RuleSubvarCompZero {
    base: RuleBase,
}

impl RuleSubvarCompZero {
    pub fn new(group: &str) -> RuleSubvarCompZero {
        RuleSubvarCompZero {
            base: RuleBase::new(group, 0, "subvar_compzero"),
        }
    }
}

impl Rule for RuleSubvarCompZero {
    fn base(&self) -> &RuleBase {
        &self.base
    }

    fn base_mut(&mut self) -> &mut RuleBase {
        &mut self.base
    }

    fn clone_rule(&self, grouplist: &ActionGroupList) -> Option<Box<dyn Rule>> {
        if !grouplist.contains(self.get_group()) {
            return None;
        }
        Some(Box::new(RuleSubvarCompZero::new(self.get_group())))
    }

    fn get_op_list(&self, oplist: &mut Vec<OpCode>) {
        oplist.push(OpCode::IntNotequal);
        oplist.push(OpCode::IntEqual);
    }

    fn apply_op(&mut self, op: OpId, data: &mut Funcdata, glb: &mut Architecture) -> Result<i32> {
        let in1 = data.op(op).get_in(1);
        if !data.vn(in1).is_constant() {
            return Ok(0);
        }
        let vn = data.op(op).get_in(0);
        let mask = data.vn(vn).get_nz_mask();
        let bitnum = leastsigbit_set(mask);
        if bitnum == -1 {
            return Ok(0);
        }
        if (mask >> bitnum) != 1 {
            return Ok(0);
        }

        let constant = data.vn(in1).get_offset();
        if constant != mask && constant != 0 {
            return Ok(0);
        }

        let outvn = data.op(op).get_out().expect("comparison without output");
        if data.vn(outvn).has_no_descend() {
            return Ok(0);
        }
        if data.vn(vn).is_written() {
            let andop = data.vn(vn).get_def().expect("written varnode without defining op");
            if data.op(andop).num_input() == 0 {
                return Ok(0);
            }
            let vn0 = data.op(andop).get_in(0);
            match data.op(andop).code() {
                OpCode::IntAnd | OpCode::IntOr | OpCode::IntRight => {
                    if data.vn(vn0).is_constant() {
                        return Ok(0);
                    }
                    let mask0 = data.vn(vn0).get_consume() & data.vn(vn0).get_nz_mask();
                    let wholemask = calc_mask(data.vn(vn0).get_size()) & mask0;
                    if popcount(wholemask) >= 8 {
                        return Ok(0);
                    }
                }
                _ => {}
            }
        }

        run_subvariable_flow(data, glb, vn, mask, false, false, false)
    }
}

pub struct RuleSubvarShift {
    base: RuleBase,
}

impl RuleSubvarShift {
    pub fn new(group: &str) -> RuleSubvarShift {
        RuleSubvarShift {
            base: RuleBase::new(group, 0, "subvar_shift"),
        }
    }
}

impl Rule for RuleSubvarShift {
    fn base(&self) -> &RuleBase {
        &self.base
    }

    fn base_mut(&mut self) -> &mut RuleBase {
        &mut self.base
    }

    fn clone_rule(&self, grouplist: &ActionGroupList) -> Option<Box<dyn Rule>> {
        if !grouplist.contains(self.get_group()) {
            return None;
        }
        Some(Box::new(RuleSubvarShift::new(self.get_group())))
    }

    fn get_op_list(&self, oplist: &mut Vec<OpCode>) {
        oplist.push(OpCode::IntRight);
    }

    fn apply_op(&mut self, op: OpId, data: &mut Funcdata, glb: &mut Architecture) -> Result<i32> {
        let vn = data.op(op).get_in(0);
        if data.vn(vn).get_size() != 1 {
            return Ok(0);
        }
        let in1 = data.op(op).get_in(1);
        if !data.vn(in1).is_constant() {
            return Ok(0);
        }
        let sa = data.vn(in1).get_offset() as i32;
        let mut mask = data.vn(vn).get_nz_mask();
        if mask.wrapping_shr(sa as u32) != 1 {
            return Ok(0);
        }
        mask = mask.wrapping_shr(sa as u32).wrapping_shl(sa as u32);
        let outvn = data.op(op).get_out().expect("shift without output");
        if data.vn(outvn).has_no_descend() {
            return Ok(0);
        }

        run_subvariable_flow(data, glb, vn, mask, false, false, false)
    }
}

pub struct RuleSubvarZext {
    base: RuleBase,
}

impl RuleSubvarZext {
    pub fn new(group: &str) -> RuleSubvarZext {
        RuleSubvarZext {
            base: RuleBase::new(group, 0, "subvar_zext"),
        }
    }
}

impl Rule for RuleSubvarZext {
    fn base(&self) -> &RuleBase {
        &self.base
    }

    fn base_mut(&mut self) -> &mut RuleBase {
        &mut self.base
    }

    fn clone_rule(&self, grouplist: &ActionGroupList) -> Option<Box<dyn Rule>> {
        if !grouplist.contains(self.get_group()) {
            return None;
        }
        Some(Box::new(RuleSubvarZext::new(self.get_group())))
    }

    fn get_op_list(&self, oplist: &mut Vec<OpCode>) {
        oplist.push(OpCode::IntZext);
    }

    fn apply_op(&mut self, op: OpId, data: &mut Funcdata, glb: &mut Architecture) -> Result<i32> {
        let vn = data.op(op).get_out().expect("extension without output");
        let invn = data.op(op).get_in(0);
        let mask = calc_mask(data.vn(invn).get_size());
        let aggressive = data.vn(invn).is_ptr_flow();
        run_subvariable_flow(data, glb, vn, mask, aggressive, false, false)
    }
}

pub struct RuleSubvarSext {
    base: RuleBase,
    isaggressive: i32,
}

impl RuleSubvarSext {
    pub fn new(group: &str) -> RuleSubvarSext {
        RuleSubvarSext {
            base: RuleBase::new(group, 0, "subvar_sext"),
            isaggressive: 0,
        }
    }
}

impl Rule for RuleSubvarSext {
    fn base(&self) -> &RuleBase {
        &self.base
    }

    fn base_mut(&mut self) -> &mut RuleBase {
        &mut self.base
    }

    fn clone_rule(&self, grouplist: &ActionGroupList) -> Option<Box<dyn Rule>> {
        if !grouplist.contains(self.get_group()) {
            return None;
        }
        Some(Box::new(RuleSubvarSext::new(self.get_group())))
    }

    fn get_op_list(&self, oplist: &mut Vec<OpCode>) {
        oplist.push(OpCode::IntSext);
    }

    fn apply_op(&mut self, op: OpId, data: &mut Funcdata, glb: &mut Architecture) -> Result<i32> {
        let vn = data.op(op).get_out().expect("extension without output");
        let invn = data.op(op).get_in(0);
        let mask = calc_mask(data.vn(invn).get_size());
        run_subvariable_flow(data, glb, vn, mask, self.isaggressive != 0, true, false)
    }

    fn reset(&mut self, _data: &mut Funcdata, glb: &mut Architecture) {
        self.isaggressive = glb.aggressive_ext_trim as i32;
    }
}

#[derive(Clone, Debug)]
pub struct SplitFlow {
    pub manager: TransformManager,
    pub(crate) lane_description: LaneDescription,
    pub(crate) worklist: Vec<usize>,
}

impl SplitFlow {
    pub fn new(data: &mut Funcdata, glb: &Architecture, root: VarnodeId, low_size: i32) -> SplitFlow {
        let whole = data.vn(root).get_size();
        let mut flow = SplitFlow {
            manager: TransformManager::new(),
            lane_description: LaneDescription::new_lo_hi(whole, low_size, whole - low_size),
            worklist: Vec::new(),
        };
        flow.set_replacement(root, data, glb);
        flow
    }

    fn set_replacement(&mut self, vn: VarnodeId, data: &mut Funcdata, glb: &Architecture) -> Option<usize> {
        let original = data.vn(vn);
        if original.is_mark() {
            return Some(self.manager.get_split(vn, &self.lane_description, data));
        }

        if original.is_type_lock() && varnode_metatype(vn, data, glb) != TypeMetatype::PartialStruct {
            return None;
        }
        if original.is_input() {
            return None;
        }
        if original.is_free() && !original.is_constant() {
            return None;
        }

        let is_constant = original.is_constant();
        let res = self.manager.new_split(vn, &self.lane_description, data);
        data.vn_mut(vn).set_mark();
        if !is_constant {
            self.worklist.push(res);
        }
        Some(res)
    }

    fn add_op(&mut self, op: OpId, rvn: usize, slot: i32, data: &mut Funcdata, glb: &Architecture) -> bool {
        let outvn = if slot == -1 {
            rvn
        } else {
            let out = data.op(op).get_out().expect("op without output");
            match self.set_replacement(out, data, glb) {
                None => return false,
                Some(outvn) => outvn,
            }
        };

        if self.manager.var(outvn).get_def().is_some() {
            return true;
        }

        let mut num_param = data.op(op).num_input();
        let lo_op;
        let hi_op;
        if data.op(op).code() == OpCode::Indirect {
            lo_op = self.manager.new_indirect_replace(op, data);
            hi_op = self.manager.new_indirect_replace(op, data);
            num_param = 1;
        } else {
            let opc = data.op(op).code();
            lo_op = self.manager.new_op_replace(num_param, opc, op);
            hi_op = self.manager.new_op_replace(num_param, opc, op);
        }
        for slot_index in 0..num_param {
            let invn = if slot_index == slot {
                rvn
            } else {
                let input = data.op(op).get_in(slot_index);
                match self.set_replacement(input, data, glb) {
                    None => return false,
                    Some(invn) => invn,
                }
            };
            self.manager.op_set_input(lo_op, invn, slot_index);
            self.manager.op_set_input(hi_op, invn + 1, slot_index);
        }
        self.manager.op_set_output(lo_op, outvn);
        self.manager.op_set_output(hi_op, outvn + 1);
        true
    }

    fn trace_forward(&mut self, rvn: usize, data: &mut Funcdata, glb: &Architecture) -> bool {
        let origvn = self
            .manager
            .var(rvn)
            .get_original()
            .expect("placeholder without original varnode");
        let descend: Vec<OpId> = data.vn(origvn).descend().to_vec();
        for op in descend {
            let outvn_opt = data.op(op).get_out();
            if let Some(outvn) = outvn_opt
                && data.vn(outvn).is_mark()
            {
                continue;
            }
            match data.op(op).code() {
                OpCode::Copy
                | OpCode::Multiequal
                | OpCode::Indirect
                | OpCode::IntAnd
                | OpCode::IntOr
                | OpCode::IntXor => {
                    let slot = data.op(op).get_slot(origvn);
                    if !self.add_op(op, rvn, slot, data, glb) {
                        return false;
                    }
                }
                OpCode::Subpiece => {
                    let outvn = outvn_opt.expect("subpiece without output");
                    if data.vn(outvn).is_precis_lo() || data.vn(outvn).is_precis_hi() {
                        return false;
                    }
                    let val = data.vn(data.op(op).get_in(1)).get_offset();
                    let out_size = data.vn(outvn).get_size();
                    if val == 0 && out_size == self.lane_description.get_size(0) {
                        let rop = self.manager.new_preexisting_op(1, OpCode::Copy, op);
                        self.manager.op_set_input(rop, rvn, 0);
                    } else if val == self.lane_description.get_size(0) as i64 as u64
                        && out_size == self.lane_description.get_size(1)
                    {
                        let rop = self.manager.new_preexisting_op(1, OpCode::Copy, op);
                        self.manager.op_set_input(rop, rvn + 1, 0);
                    } else {
                        return false;
                    }
                }
                OpCode::IntLeft => {
                    let tmpvn = data.op(op).get_in(1);
                    if !data.vn(tmpvn).is_constant() {
                        return false;
                    }
                    let val = data.vn(tmpvn).get_offset();
                    if val < (self.lane_description.get_size(1) * 8) as i64 as u64 {
                        return false;
                    }
                    let rop = self.manager.new_preexisting_op(2, OpCode::IntLeft, op);
                    let zextrop = self.manager.new_op(1, OpCode::IntZext, rop);
                    self.manager.op_set_input(zextrop, rvn, 0);
                    let unique = self.manager.new_unique(self.lane_description.get_whole_size());
                    self.manager.op_set_output(zextrop, unique);
                    let zext_out = self.manager.op(zextrop).get_out().expect("missing extension output");
                    self.manager.op_set_input(rop, zext_out, 0);
                    let shift = self
                        .manager
                        .new_constant(data.vn(tmpvn).get_size(), 0, data.vn(tmpvn).get_offset());
                    self.manager.op_set_input(rop, shift, 1);
                }
                OpCode::IntSright | OpCode::IntRight => {
                    let tmpvn = data.op(op).get_in(1);
                    if !data.vn(tmpvn).is_constant() {
                        return false;
                    }
                    let val = data.vn(tmpvn).get_offset();
                    let lo_bits = (self.lane_description.get_size(0) * 8) as i64 as u64;
                    if val < lo_bits {
                        return false;
                    }
                    let opc = data.op(op).code();
                    let ext_op_code = if opc == OpCode::IntRight {
                        OpCode::IntZext
                    } else {
                        OpCode::IntSext
                    };
                    if val == lo_bits {
                        let rop = self.manager.new_preexisting_op(1, ext_op_code, op);
                        self.manager.op_set_input(rop, rvn + 1, 0);
                    } else {
                        let remain_shift = val - lo_bits;
                        let rop = self.manager.new_preexisting_op(2, opc, op);
                        let extrop = self.manager.new_op(1, ext_op_code, rop);
                        self.manager.op_set_input(extrop, rvn + 1, 0);
                        let unique = self.manager.new_unique(self.lane_description.get_whole_size());
                        self.manager.op_set_output(extrop, unique);
                        let ext_out = self.manager.op(extrop).get_out().expect("missing extension output");
                        self.manager.op_set_input(rop, ext_out, 0);
                        let shift = self.manager.new_constant(data.vn(tmpvn).get_size(), 0, remain_shift);
                        self.manager.op_set_input(rop, shift, 1);
                    }
                }
                _ => return false,
            }
        }
        true
    }

    fn trace_backward(&mut self, rvn: usize, data: &mut Funcdata, glb: &Architecture) -> bool {
        let origvn = self
            .manager
            .var(rvn)
            .get_original()
            .expect("placeholder without original varnode");
        let op = match data.vn(origvn).get_def() {
            None => return true,
            Some(op) => op,
        };

        match data.op(op).code() {
            OpCode::Copy | OpCode::Multiequal | OpCode::IntAnd | OpCode::IntOr | OpCode::IntXor | OpCode::Indirect => {
                if !self.add_op(op, rvn, -1, data, glb) {
                    return false;
                }
            }
            OpCode::Piece => {
                let in0 = data.op(op).get_in(0);
                let in1 = data.op(op).get_in(1);
                if data.vn(in0).get_size() != self.lane_description.get_size(1) {
                    return false;
                }
                if data.vn(in1).get_size() != self.lane_description.get_size(0) {
                    return false;
                }
                let lo_op = self.manager.new_op_replace(1, OpCode::Copy, op);
                let hi_op = self.manager.new_op_replace(1, OpCode::Copy, op);
                let lo_in = self.manager.get_preexisting_varnode(in1, data);
                self.manager.op_set_input(lo_op, lo_in, 0);
                self.manager.op_set_output(lo_op, rvn);
                let hi_in = self.manager.get_preexisting_varnode(in0, data);
                self.manager.op_set_input(hi_op, hi_in, 0);
                self.manager.op_set_output(hi_op, rvn + 1);
            }
            OpCode::IntZext => {
                let in0 = data.op(op).get_in(0);
                if data.vn(in0).get_size() != self.lane_description.get_size(0) {
                    return false;
                }
                let out = data.op(op).get_out().expect("extension without output");
                if data.vn(out).get_size() != self.lane_description.get_whole_size() {
                    return false;
                }
                let lo_op = self.manager.new_op_replace(1, OpCode::Copy, op);
                let hi_op = self.manager.new_op_replace(1, OpCode::Copy, op);
                let lo_in = self.manager.get_preexisting_varnode(in0, data);
                self.manager.op_set_input(lo_op, lo_in, 0);
                self.manager.op_set_output(lo_op, rvn);
                let zero = self.manager.new_constant(self.lane_description.get_size(1), 0, 0);
                self.manager.op_set_input(hi_op, zero, 0);
                self.manager.op_set_output(hi_op, rvn + 1);
            }
            OpCode::IntLeft => {
                let cvn = data.op(op).get_in(1);
                if !data.vn(cvn).is_constant() {
                    return false;
                }
                if data.vn(cvn).get_offset() != (self.lane_description.get_size(0) * 8) as i64 as u64 {
                    return false;
                }
                let mut invn = data.op(op).get_in(0);
                if !data.vn(invn).is_written() {
                    return false;
                }
                let zext_op = data.vn(invn).get_def().expect("written varnode without defining op");
                if data.op(zext_op).code() != OpCode::IntZext {
                    return false;
                }
                invn = data.op(zext_op).get_in(0);
                if data.vn(invn).get_size() != self.lane_description.get_size(1) {
                    return false;
                }
                if data.vn(invn).is_free() {
                    return false;
                }
                let lo_op = self.manager.new_op_replace(1, OpCode::Copy, op);
                let hi_op = self.manager.new_op_replace(1, OpCode::Copy, op);
                let zero = self.manager.new_constant(self.lane_description.get_size(0), 0, 0);
                self.manager.op_set_input(lo_op, zero, 0);
                self.manager.op_set_output(lo_op, rvn);
                let hi_in = self.manager.get_preexisting_varnode(invn, data);
                self.manager.op_set_input(hi_op, hi_in, 0);
                self.manager.op_set_output(hi_op, rvn + 1);
            }
            _ => return false,
        }
        true
    }

    fn process_next_work(&mut self, data: &mut Funcdata, glb: &Architecture) -> bool {
        let rvn = self.worklist.pop().expect("empty split worklist");

        if !self.trace_backward(rvn, data, glb) {
            return false;
        }
        self.trace_forward(rvn, data, glb)
    }

    pub fn do_trace(&mut self, data: &mut Funcdata, glb: &Architecture) -> bool {
        if self.worklist.is_empty() {
            return false;
        }
        let mut retval = true;
        while !self.worklist.is_empty() {
            if !self.process_next_work(data, glb) {
                retval = false;
                break;
            }
        }

        self.manager.clear_varnode_marks(data);
        retval
    }
}

pub struct RuleSplitFlow {
    base: RuleBase,
}

impl RuleSplitFlow {
    pub fn new(group: &str) -> RuleSplitFlow {
        RuleSplitFlow {
            base: RuleBase::new(group, 0, "splitflow"),
        }
    }
}

impl Rule for RuleSplitFlow {
    fn base(&self) -> &RuleBase {
        &self.base
    }

    fn base_mut(&mut self) -> &mut RuleBase {
        &mut self.base
    }

    fn clone_rule(&self, grouplist: &ActionGroupList) -> Option<Box<dyn Rule>> {
        if !grouplist.contains(self.get_group()) {
            return None;
        }
        Some(Box::new(RuleSplitFlow::new(self.get_group())))
    }

    fn get_op_list(&self, oplist: &mut Vec<OpCode>) {
        oplist.push(OpCode::Subpiece);
    }

    fn apply_op(&mut self, op: OpId, data: &mut Funcdata, glb: &mut Architecture) -> Result<i32> {
        let lo_size = data.vn(data.op(op).get_in(1)).get_offset() as i32;
        if lo_size == 0 {
            return Ok(0);
        }
        let vn = data.op(op).get_in(0);
        if !data.vn(vn).is_written() {
            return Ok(0);
        }
        if data.vn(vn).is_precis_lo() || data.vn(vn).is_precis_hi() {
            return Ok(0);
        }
        let outvn = data.op(op).get_out().expect("subpiece without output");
        if data.vn(outvn).get_size() + lo_size != data.vn(vn).get_size() {
            return Ok(0);
        }
        let mut concat_op: Option<OpId> = None;
        let vn_def = data.vn(vn).get_def().expect("written varnode without defining op");
        let mut multi_op = vn_def;
        while data.op(multi_op).code() == OpCode::Indirect {
            let tmpvn = data.op(multi_op).get_in(0);
            if !data.vn(tmpvn).is_written() {
                return Ok(0);
            }
            multi_op = data.vn(tmpvn).get_def().expect("written varnode without defining op");
        }
        if data.op(multi_op).code() == OpCode::Piece {
            if vn_def != multi_op {
                concat_op = Some(multi_op);
            }
        } else if data.op(multi_op).code() == OpCode::Multiequal {
            for slot in 0..data.op(multi_op).num_input() {
                let invn = data.op(multi_op).get_in(slot);
                if !data.vn(invn).is_written() {
                    continue;
                }
                let tmp_op = data.vn(invn).get_def().expect("written varnode without defining op");
                if data.op(tmp_op).code() == OpCode::Piece {
                    concat_op = Some(tmp_op);
                    break;
                }
            }
        }
        let concat_op = match concat_op {
            None => return Ok(0),
            Some(concat_op) => concat_op,
        };
        if data.vn(data.op(concat_op).get_in(1)).get_size() != lo_size {
            return Ok(0);
        }
        let mut split_flow = SplitFlow::new(data, glb, vn, lo_size);
        if !split_flow.do_trace(data, glb) {
            return Ok(0);
        }
        split_flow.manager.apply(data, glb)?;
        Ok(1)
    }
}

#[derive(Clone, Copy, Debug)]
pub struct Component {
    pub(crate) in_type: TypeId,
    pub(crate) out_type: TypeId,
    pub(crate) offset: i32,
}

impl Component {
    pub fn new(input: TypeId, out: TypeId, off: i32) -> Component {
        Component {
            in_type: input,
            out_type: out,
            offset: off,
        }
    }
}

#[derive(Clone, Debug, Default)]
pub struct RootPointer {
    pub(crate) load_store: Option<OpId>,
    pub(crate) ptr_type: Option<TypeId>,
    pub(crate) first_pointer: Option<VarnodeId>,
    pub(crate) pointer: Option<VarnodeId>,
    pub(crate) base_offset: i32,
}

impl RootPointer {
    fn get_pointer(&self) -> VarnodeId {
        self.pointer.expect("root pointer is not established")
    }

    fn get_ptr_type(&self) -> TypeId {
        self.ptr_type.expect("root pointer data-type is not established")
    }

    fn back_up_pointer(&mut self, implied_base: Option<TypeId>, data: &Funcdata, glb: &Architecture) -> bool {
        let pointer = self.get_pointer();
        if !data.vn(pointer).is_written() {
            return false;
        }
        let add_op = data.vn(pointer).get_def().expect("written varnode without defining op");
        let opc = data.op(add_op).code();
        let mut off: i32;
        if opc == OpCode::Ptrsub || opc == OpCode::IntAdd || opc == OpCode::Ptradd {
            let cvn = data.op(add_op).get_in(1);
            if !data.vn(cvn).is_constant() {
                return false;
            }
            off = data.vn(cvn).get_offset() as i32;
        } else if opc == OpCode::Copy {
            off = 0;
        } else {
            return false;
        }
        let tmp_pointer = data.op(add_op).get_in(0);
        let ct = data.vn_get_type_read_facing(tmp_pointer, add_op, glb);
        let factory = types(glb);
        let ct_type = factory.get(ct);
        if ct_type.get_metatype() != TypeMetatype::Ptr {
            return false;
        }
        let parent = ct_type.get_ptr_to();
        let meta = factory.get(parent).get_metatype();
        if meta != TypeMetatype::Struct
            && meta != TypeMetatype::Array
            && ((opc != OpCode::Ptradd && opc != OpCode::Copy) || Some(parent) != implied_base)
        {
            return false;
        }
        self.ptr_type = Some(ct);
        if opc == OpCode::Ptradd {
            off = off.wrapping_mul(data.vn(data.op(add_op).get_in(2)).get_offset() as i32);
        }
        off = AddrSpace::address_to_byte_int(off as i64, ct_type.get_word_size()) as i32;
        self.base_offset += off;
        self.pointer = Some(tmp_pointer);
        true
    }

    pub fn find(
        &mut self,
        op: OpId,
        value_type: TypeId,
        resolver: &mut ResolveCache,
        data: &Funcdata,
        glb: &Architecture,
    ) -> bool {
        let factory = types(glb);
        let mut value_type = value_type;
        let mut implied_base: Option<TypeId> = None;
        if factory.get(value_type).get_metatype() == TypeMetatype::PartialStruct {
            value_type = factory.get(value_type).get_parent();
        }
        if factory.get(value_type).get_metatype() == TypeMetatype::Array {
            value_type = factory.get(value_type).get_base();
            implied_base = Some(value_type);
        }
        let key = if data.op(op).code() == OpCode::Load { 0 } else { 1 };
        self.load_store = Some(op);
        self.base_offset = 0;
        let pointer = data.op(op).get_in(1);
        self.first_pointer = Some(pointer);
        self.pointer = Some(pointer);
        let ct = data.vn_get_type_read_facing(pointer, op, glb);
        if factory.get(ct).get_metatype() != TypeMetatype::Ptr {
            return false;
        }
        resolver.add_resolution(key, data.vn(pointer).get_type(), op, 1, data, glb);
        self.ptr_type = Some(ct);
        if factory.get(ct).get_ptr_to() != value_type {
            if implied_base.is_some() {
                return false;
            }
            if !self.back_up_pointer(implied_base, data, glb) {
                return false;
            }
            if factory.get(self.get_ptr_type()).get_ptr_to() != value_type {
                return false;
            }
        }
        for _ in 0..3 {
            let pointer = self.get_pointer();
            if data.vn(pointer).is_addr_tied() || data.vn(pointer).lone_descend().is_none() {
                break;
            }
            let last_vn = pointer;
            if !self.back_up_pointer(implied_base, data, glb) {
                break;
            }
            let last_def = data.vn(last_vn).get_def().expect("written varnode without defining op");
            resolver.add_resolution(key, data.vn(self.get_pointer()).get_type(), last_def, 0, data, glb);
        }
        true
    }

    pub fn duplicate_to_temp(&mut self, data: &mut Funcdata, glb: &mut Architecture, follow_op: OpId) -> Result<()> {
        let new_root = data.build_copy_temp(self.get_pointer(), follow_op, glb)?;
        data.vn_update_type(new_root, self.get_ptr_type());
        self.pointer = Some(new_root);
        Ok(())
    }

    pub fn free_pointer_chain(&mut self, data: &mut Funcdata) -> Result<()> {
        loop {
            let first_pointer = self.first_pointer.expect("root pointer chain is not established");
            if Some(first_pointer) == self.pointer
                || data.vn(first_pointer).is_addr_tied()
                || !data.vn(first_pointer).has_no_descend()
            {
                break;
            }
            let tmp_op = data.vn(first_pointer).get_def().expect("pointer without defining op");
            self.first_pointer = Some(data.op(tmp_op).get_in(0));
            data.op_destroy(tmp_op)?;
        }
        Ok(())
    }
}

pub struct SplitDatatype {
    pub(crate) data_type_pieces: Vec<Component>,
    pub(crate) resolver: ResolveCache,
    pub(crate) split_structures: bool,
    pub(crate) split_arrays: bool,
    pub(crate) is_load_store: bool,
}

impl SplitDatatype {
    pub fn new(_data: &Funcdata, glb: &Architecture) -> SplitDatatype {
        SplitDatatype {
            data_type_pieces: Vec::new(),
            resolver: ResolveCache::new(),
            split_structures: (glb.split_datatype_config & OptionSplitDatatypes::OPTION_STRUCT) != 0,
            split_arrays: (glb.split_datatype_config & OptionSplitDatatypes::OPTION_ARRAY) != 0,
            is_load_store: false,
        }
    }

    fn get_component(
        &mut self,
        ct: TypeId,
        offset: i32,
        is_hole: &mut bool,
        glb: &mut Architecture,
    ) -> Result<Option<TypeId>> {
        *is_hole = false;
        let mut cur_type = ct;
        let mut cur_off = offset as i64;
        loop {
            let mut new_off = cur_off;
            let next = types(glb).get(cur_type).get_sub_type(cur_off, &mut new_off, glb);
            cur_off = new_off;
            cur_type = match next {
                Some(next) => next,
                None => {
                    let factory = types(glb);
                    let mut hole = factory.get(ct).get_hole_size(offset, factory);
                    if hole > 0 {
                        if hole > 8 {
                            hole = 8;
                        }
                        *is_hole = true;
                        return Ok(Some(types_mut(glb).get_base(hole, TypeMetatype::Unknown)?));
                    }
                    return Ok(None);
                }
            };
            if !(cur_off != 0 || types(glb).get(cur_type).get_metatype() == TypeMetatype::Array) {
                break;
            }
        }
        Ok(Some(cur_type))
    }

    fn categorize_datatype(&mut self, ct: TypeId, glb: &Architecture) -> i32 {
        let factory = types(glb);
        let dt = factory.get(ct);
        match dt.get_metatype() {
            TypeMetatype::Array if self.split_arrays => {
                let sub_type = factory.get(dt.get_base());
                if sub_type.get_metatype() != TypeMetatype::Unknown || sub_type.get_size() != 1 {
                    return 1;
                }
                return 2;
            }
            TypeMetatype::PartialStruct => {
                let sub_type = factory.get(dt.get_parent());
                if sub_type.get_metatype() == TypeMetatype::Array {
                    if self.split_arrays {
                        let base = factory.get(sub_type.get_base());
                        if base.get_metatype() != TypeMetatype::Unknown || base.get_size() != 1 {
                            return 1;
                        }
                        return 2;
                    }
                } else if sub_type.get_metatype() == TypeMetatype::Struct && self.split_structures {
                    return 0;
                }
            }
            TypeMetatype::Struct if self.split_structures && dt.num_depend(factory) > 1 => {
                return 0;
            }
            TypeMetatype::Int | TypeMetatype::Uint | TypeMetatype::Unknown => return 2,
            _ => {}
        }
        -1
    }

    fn test_datatype_compatibility(
        &mut self,
        in_base: TypeId,
        out_base: TypeId,
        in_constant: bool,
        glb: &mut Architecture,
    ) -> Result<bool> {
        let in_category = self.categorize_datatype(in_base, glb);
        if in_category < 0 {
            return Ok(false);
        }
        let out_category = self.categorize_datatype(out_base, glb);
        if out_category < 0 {
            return Ok(false);
        }
        if out_category == 2 && in_category == 2 {
            return Ok(false);
        }
        if !in_constant && in_base == out_base && types(glb).get(in_base).get_metatype() == TypeMetatype::Struct {
            return Ok(false);
        }
        if self.is_load_store && out_category == 2 && in_category == 1 {
            return Ok(false);
        }
        if self.is_load_store && in_category == 2 && !in_constant && out_category == 1 {
            return Ok(false);
        }
        if self.is_load_store && in_category == 1 && out_category == 1 && !in_constant {
            return Ok(false);
        }
        let mut in_hole = false;
        let mut out_hole = false;
        let mut cur_off = 0;
        let mut size_left = types(glb).get(in_base).get_size();
        if in_category == 2 {
            while size_left > 0 {
                let cur_out = match self.get_component(out_base, cur_off, &mut out_hole, glb)? {
                    None => return Ok(false),
                    Some(cur_out) => cur_out,
                };
                let out_size = types(glb).get(cur_out).get_size();
                let cur_in = if in_constant {
                    cur_out
                } else {
                    types_mut(glb).get_base(out_size, TypeMetatype::Unknown)?
                };
                self.data_type_pieces.push(Component::new(cur_in, cur_out, cur_off));
                size_left -= out_size;
                cur_off += out_size;
                if out_hole {
                    if self.data_type_pieces.len() == 1 {
                        return Ok(false);
                    }
                    if size_left == 0 && self.data_type_pieces.len() == 2 {
                        return Ok(false);
                    }
                }
            }
        } else if out_category == 2 {
            while size_left > 0 {
                let cur_in = match self.get_component(in_base, cur_off, &mut in_hole, glb)? {
                    None => return Ok(false),
                    Some(cur_in) => cur_in,
                };
                let in_size = types(glb).get(cur_in).get_size();
                let cur_out = types_mut(glb).get_base(in_size, TypeMetatype::Unknown)?;
                self.data_type_pieces.push(Component::new(cur_in, cur_out, cur_off));
                size_left -= in_size;
                cur_off += in_size;
                if in_hole {
                    if self.data_type_pieces.len() == 1 {
                        return Ok(false);
                    }
                    if size_left == 0 && self.data_type_pieces.len() == 2 {
                        return Ok(false);
                    }
                }
            }
        } else {
            while size_left > 0 {
                let mut cur_in = match self.get_component(in_base, cur_off, &mut in_hole, glb)? {
                    None => return Ok(false),
                    Some(cur_in) => cur_in,
                };
                let mut cur_out = match self.get_component(out_base, cur_off, &mut out_hole, glb)? {
                    None => return Ok(false),
                    Some(cur_out) => cur_out,
                };
                loop {
                    let in_size = types(glb).get(cur_in).get_size();
                    let out_size = types(glb).get(cur_out).get_size();
                    if in_size == out_size {
                        break;
                    }
                    if in_size > out_size {
                        let next = if in_hole {
                            Some(types_mut(glb).get_base(out_size, TypeMetatype::Unknown)?)
                        } else {
                            self.get_component(cur_in, 0, &mut in_hole, glb)?
                        };
                        cur_in = match next {
                            None => return Ok(false),
                            Some(next) => next,
                        };
                    } else {
                        let next = if out_hole {
                            Some(types_mut(glb).get_base(in_size, TypeMetatype::Unknown)?)
                        } else {
                            self.get_component(cur_out, 0, &mut out_hole, glb)?
                        };
                        cur_out = match next {
                            None => return Ok(false),
                            Some(next) => next,
                        };
                    }
                }
                self.data_type_pieces.push(Component::new(cur_in, cur_out, cur_off));
                let in_size = types(glb).get(cur_in).get_size();
                size_left -= in_size;
                cur_off += in_size;
            }
        }
        Ok(self.data_type_pieces.len() > 1)
    }

    fn test_copy_constraints(&mut self, copy_op: OpId, data: &Funcdata) -> bool {
        let in_vn = data.op(copy_op).get_in(0);
        let input = data.vn(in_vn);
        if input.is_input() {
            return false;
        }
        if input.is_addr_tied() {
            let out_vn = data.op(copy_op).get_out().expect("copy without output");
            let output = data.vn(out_vn);
            if output.is_addr_tied() && output.get_addr() == input.get_addr() {
                return false;
            }
        } else if input.is_written() {
            let def = input.get_def().expect("written varnode without defining op");
            if data.op(def).code() == OpCode::Load && input.lone_descend() == Some(copy_op) {
                return false;
            }
        }
        true
    }

    fn generate_constants(
        &mut self,
        vn: VarnodeId,
        in_varnodes: &mut Vec<VarnodeId>,
        data: &mut Funcdata,
        glb: &mut Architecture,
    ) -> Result<bool> {
        if data.vn(vn).lone_descend().is_none() {
            return Ok(false);
        }
        if !data.vn(vn).is_written() {
            return Ok(false);
        }
        let op = data.vn(vn).get_def().expect("written varnode without defining op");
        let opc = data.op(op).code();
        if opc == OpCode::IntZext {
            if !data.vn(data.op(op).get_in(0)).is_constant() {
                return Ok(false);
            }
        } else if opc == OpCode::Piece {
            if !data.vn(data.op(op).get_in(0)).is_constant() || !data.vn(data.op(op).get_in(1)).is_constant() {
                return Ok(false);
            }
        } else {
            return Ok(false);
        }
        let fullsize = data.vn(vn).get_size();
        let is_big_endian = data.vn(vn).get_space().expect("varnode without space").is_big_endian();
        let (lo, hi, losize) = if opc == OpCode::IntZext {
            let in0 = data.vn(data.op(op).get_in(0));
            (in0.get_offset(), 0u64, in0.get_size())
        } else {
            let in0 = data.vn(data.op(op).get_in(0));
            let in1 = data.vn(data.op(op).get_in(1));
            (in1.get_offset(), in0.get_offset(), in1.get_size())
        };
        for index in 0..self.data_type_pieces.len() {
            let dt = self.data_type_pieces[index].in_type;
            let dt_size = types(glb).get(dt).get_size();
            if dt_size > 8 {
                in_varnodes.clear();
                return Ok(false);
            }
            let sa = if is_big_endian {
                fullsize - (self.data_type_pieces[index].offset + dt_size)
            } else {
                self.data_type_pieces[index].offset
            };
            let mut val: u64;
            if sa >= losize {
                val = hi.wrapping_shr((sa - losize) as u32);
            } else {
                val = lo.wrapping_shr((sa * 8) as u32);
                if sa + dt_size > losize {
                    val |= hi.wrapping_shl(((losize - sa) * 8) as u32);
                }
            }
            val &= calc_mask(dt_size);
            let out_vn = data.new_constant(dt_size, val, glb);
            in_varnodes.push(out_vn);
            data.vn_update_type(out_vn, dt);
        }
        data.op_destroy(op)?;
        Ok(true)
    }

    fn build_in_constants(
        &mut self,
        root_vn: VarnodeId,
        in_varnodes: &mut Vec<VarnodeId>,
        big_endian: bool,
        data: &mut Funcdata,
        glb: &mut Architecture,
    ) {
        let base_val = data.vn(root_vn).get_offset();
        let root_size = data.vn(root_vn).get_size();
        for index in 0..self.data_type_pieces.len() {
            let dt = self.data_type_pieces[index].in_type;
            let dt_size = types(glb).get(dt).get_size();
            let mut off = self.data_type_pieces[index].offset;
            if big_endian {
                off = root_size - off - dt_size;
            }
            let val = base_val.wrapping_shr((8 * off) as u32) & calc_mask(dt_size);
            let out_vn = data.new_constant(dt_size, val, glb);
            in_varnodes.push(out_vn);
            data.vn_update_type(out_vn, dt);
        }
    }

    fn build_in_subpieces(
        &mut self,
        root_vn: VarnodeId,
        follow_op: OpId,
        in_varnodes: &mut Vec<VarnodeId>,
        data: &mut Funcdata,
        glb: &mut Architecture,
    ) -> Result<()> {
        if self.generate_constants(root_vn, in_varnodes, data, glb)? {
            return Ok(());
        }
        let base_addr = data.vn(root_vn).get_addr().clone();
        let root_size = data.vn(root_vn).get_size();
        for index in 0..self.data_type_pieces.len() {
            let dt = self.data_type_pieces[index].in_type;
            let dt_size = types(glb).get(dt).get_size();
            let mut off = self.data_type_pieces[index].offset;
            let mut addr = base_addr.add(off as i64);
            addr.renormalize(dt_size)?;
            if addr.is_big_endian() {
                off = root_size - off - dt_size;
            }
            let follow_addr = data.op(follow_op).get_addr().clone();
            let subpiece = data.new_op(2, &follow_addr);
            data.op_set_opcode(subpiece, OpCode::Subpiece, glb);
            data.op_set_input(subpiece, root_vn, 0)?;
            let offset_vn = data.new_constant(4, off as i64 as u64, glb);
            data.op_set_input(subpiece, offset_vn, 1)?;
            let out_vn = data.new_varnode_out(dt_size, &addr, subpiece, glb)?;
            in_varnodes.push(out_vn);
            data.vn_update_type(out_vn, dt);
            data.op_insert_before(subpiece, follow_op);
        }
        Ok(())
    }

    fn build_out_varnodes(
        &mut self,
        root_vn: VarnodeId,
        out_varnodes: &mut Vec<VarnodeId>,
        data: &mut Funcdata,
        glb: &mut Architecture,
    ) -> Result<()> {
        let base_addr = data.vn(root_vn).get_addr().clone();
        for index in 0..self.data_type_pieces.len() {
            let dt = self.data_type_pieces[index].out_type;
            let dt_size = types(glb).get(dt).get_size();
            let off = self.data_type_pieces[index].offset;
            let mut addr = base_addr.add(off as i64);
            addr.renormalize(dt_size)?;
            let out_vn = data.new_varnode(dt_size, &addr, Some(dt), glb)?;
            out_varnodes.push(out_vn);
        }
        Ok(())
    }

    fn build_out_concats(
        &mut self,
        root_vn: VarnodeId,
        previous_op: OpId,
        out_varnodes: &mut [VarnodeId],
        data: &mut Funcdata,
        glb: &mut Architecture,
    ) -> Result<()> {
        if data.vn(root_vn).has_no_descend() {
            return Ok(());
        }
        let base_addr = data.vn(root_vn).get_addr().clone();
        let mut pre_op = previous_op;
        let address_tied = data.vn(root_vn).is_addr_tied();
        for &vn in out_varnodes.iter() {
            if !address_tied {
                data.vn_mut(vn).set_proto_partial();
            }
        }
        let previous_addr = data.op(previous_op).get_addr().clone();
        let mut concat_op;
        if base_addr.is_big_endian() {
            let mut vn = out_varnodes[0];
            let mut index = 1usize;
            loop {
                concat_op = data.new_op(2, &previous_addr);
                data.op_set_opcode(concat_op, OpCode::Piece, glb);
                data.op_set_input(concat_op, vn, 0)?;
                data.op_set_input(concat_op, out_varnodes[index], 1)?;
                data.op_insert_after(concat_op, pre_op);
                if index + 1 >= out_varnodes.len() {
                    break;
                }
                pre_op = concat_op;
                let size = data.vn(vn).get_size() + data.vn(out_varnodes[index]).get_size();
                let mut addr = base_addr.clone();
                addr.renormalize(size)?;
                vn = data.new_varnode_out(size, &addr, concat_op, glb)?;
                if !address_tied {
                    data.vn_mut(vn).set_proto_partial();
                }
                index += 1;
            }
        } else {
            let mut vn = out_varnodes[out_varnodes.len() - 1];
            let mut index = out_varnodes.len() as i32 - 2;
            loop {
                concat_op = data.new_op(2, &previous_addr);
                data.op_set_opcode(concat_op, OpCode::Piece, glb);
                data.op_set_input(concat_op, vn, 0)?;
                data.op_set_input(concat_op, out_varnodes[index as usize], 1)?;
                data.op_insert_after(concat_op, pre_op);
                if index <= 0 {
                    break;
                }
                pre_op = concat_op;
                let size = data.vn(vn).get_size() + data.vn(out_varnodes[index as usize]).get_size();
                let mut addr = data.vn(out_varnodes[index as usize]).get_addr().clone();
                addr.renormalize(size)?;
                vn = data.new_varnode_out(size, &addr, concat_op, glb)?;
                if !address_tied {
                    data.vn_mut(vn).set_proto_partial();
                }
                index -= 1;
            }
        }
        data.op_mut(concat_op).set_partial_root();
        data.op_set_output(concat_op, root_vn, glb)?;
        if !address_tied {
            Merge::register_proto_partial_root(data, root_vn);
        }
        Ok(())
    }

    fn build_pointers(
        &mut self,
        root_vn: VarnodeId,
        ptr_type: TypeId,
        base_offset: i32,
        follow_op: OpId,
        ptr_varnodes: &mut Vec<VarnodeId>,
        is_input: bool,
        data: &mut Funcdata,
        glb: &mut Architecture,
    ) -> Result<()> {
        let (base_type, word_size, ptr_size) = {
            let pointer = types(glb).get(ptr_type);
            (pointer.get_ptr_to(), pointer.get_word_size(), pointer.get_size())
        };
        let key = if is_input { 0 } else { 1 };
        for index in 0..self.data_type_pieces.len() {
            let match_type = if is_input {
                self.data_type_pieces[index].in_type
            } else {
                self.data_type_pieces[index].out_type
            };
            let match_size = types(glb).get(match_type).get_size();
            let mut cur_off: i64 = base_offset as i64 + self.data_type_pieces[index].offset as i64;
            let mut tmp_type = base_type;
            let mut in_ptr = root_vn;
            loop {
                let mut new_off: i64;
                let new_type: TypeId;
                let tmp_size = types(glb).get(tmp_type).get_size() as i64;
                if cur_off < 0 || cur_off >= tmp_size {
                    new_type = tmp_type;
                    new_off = cur_off % tmp_size;
                    new_off = if new_off < 0 { new_off + tmp_size } else { new_off };
                } else {
                    new_off = cur_off;
                    let sub = types(glb).get(tmp_type).get_sub_type(cur_off, &mut new_off, glb);
                    new_type = match sub {
                        Some(sub) => sub,
                        None => {
                            new_off = 0;
                            match_type
                        }
                    };
                }
                let res_type = if types(glb).get(new_type).needs_resolution() {
                    self.resolver.resolve(key, new_type, types(glb))
                } else {
                    new_type
                };

                let follow_addr = data.op(follow_op).get_addr().clone();
                let in_ptr_size = data.vn(in_ptr).get_size();
                let new_op;
                if tmp_type == res_type || types(glb).get(tmp_type).get_metatype() == TypeMetatype::Array {
                    let mut final_offset = cur_off - new_off;
                    let mut size = types(glb).get(res_type).get_size();
                    final_offset /= size as i64;
                    size = AddrSpace::byte_to_address_int(size as i64, word_size) as i32;
                    new_op = data.new_op(3, &follow_addr);
                    data.op_set_opcode(new_op, OpCode::Ptradd, glb);
                    data.op_set_input(new_op, in_ptr, 0)?;
                    let index_vn = data.new_constant(in_ptr_size, final_offset as u64, glb);
                    data.op_set_input(new_op, index_vn, 1)?;
                    let size_vn = data.new_constant(in_ptr_size, size as i64 as u64, glb);
                    data.op_set_input(new_op, size_vn, 2)?;
                    let index_size = data.vn(index_vn).get_size();
                    let index_type = types_mut(glb).get_base(index_size, TypeMetatype::Int)?;
                    data.vn_update_type(index_vn, index_type);
                } else {
                    let final_offset = AddrSpace::byte_to_address_int(cur_off - new_off, word_size);
                    new_op = data.new_op(2, &follow_addr);
                    data.op_set_opcode(new_op, OpCode::Ptrsub, glb);
                    data.op_set_input(new_op, in_ptr, 0)?;
                    let offset_vn = data.new_constant(in_ptr_size, final_offset as u64, glb);
                    data.op_set_input(new_op, offset_vn, 1)?;
                }
                self.resolver
                    .inherit_resolution_varnode(key, in_ptr, new_op, 0, data, glb)?;
                in_ptr = data.new_unique_out(in_ptr_size, new_op, glb)?;
                let tmp_ptr = types_mut(glb).get_type_pointer_strip_array(ptr_size, new_type, word_size)?;
                data.vn_update_type(in_ptr, tmp_ptr);
                data.op_insert_before(new_op, follow_op);
                tmp_type = res_type;
                cur_off = new_off;
                if types(glb).get(tmp_type).get_size() <= match_size {
                    break;
                }
            }
            ptr_varnodes.push(in_ptr);
        }
        Ok(())
    }

    fn is_arithmetic_input(vn: VarnodeId, data: &Funcdata, glb: &Architecture) -> bool {
        for &op in data.vn(vn).descend() {
            if data.op(op).get_opcode(glb).is_arithmetic_op() {
                return true;
            }
        }
        false
    }

    fn is_arithmetic_output(vn: VarnodeId, data: &Funcdata, glb: &Architecture) -> bool {
        if !data.vn(vn).is_written() {
            return false;
        }
        let def = data.vn(vn).get_def().expect("written varnode without defining op");
        data.op(def).get_opcode(glb).is_arithmetic_op()
    }

    pub fn split_copy(
        &mut self,
        copy_op: OpId,
        in_type: TypeId,
        out_type: TypeId,
        data: &mut Funcdata,
        glb: &mut Architecture,
    ) -> Result<bool> {
        if !self.test_copy_constraints(copy_op, data) {
            return Ok(false);
        }
        let in_vn = data.op(copy_op).get_in(0);
        if !self.test_datatype_compatibility(in_type, out_type, data.vn(in_vn).is_constant(), glb)? {
            return Ok(false);
        }
        if SplitDatatype::is_arithmetic_output(in_vn, data, glb) {
            return Ok(false);
        }
        let out_vn = data.op(copy_op).get_out().expect("copy without output");
        if SplitDatatype::is_arithmetic_input(out_vn, data, glb) {
            return Ok(false);
        }
        let mut in_varnodes: Vec<VarnodeId> = Vec::new();
        let mut out_varnodes: Vec<VarnodeId> = Vec::new();
        let unres_out_type = data.vn(out_vn).get_type();
        self.resolver.add_resolution(0, unres_out_type, copy_op, -1, data, glb);
        if data.vn(in_vn).is_constant() {
            let big_endian = data
                .vn(out_vn)
                .get_space()
                .expect("varnode without space")
                .is_big_endian();
            self.build_in_constants(in_vn, &mut in_varnodes, big_endian, data, glb);
        } else {
            self.build_in_subpieces(in_vn, copy_op, &mut in_varnodes, data, glb)?;
        }
        self.build_out_varnodes(out_vn, &mut out_varnodes, data, glb)?;
        self.build_out_concats(out_vn, copy_op, &mut out_varnodes, data, glb)?;
        for index in 0..in_varnodes.len() {
            let addr = data.op(copy_op).get_addr().clone();
            let new_copy_op = data.new_op(1, &addr);
            data.op_set_opcode(new_copy_op, OpCode::Copy, glb);
            data.op_set_input(new_copy_op, in_varnodes[index], 0)?;
            data.op_set_output(new_copy_op, out_varnodes[index], glb)?;
            data.op_insert_before(new_copy_op, copy_op);
            let offset = self.data_type_pieces[index].offset;
            self.resolver.inherit_resolution(
                0,
                unres_out_type,
                offset,
                out_varnodes[index],
                new_copy_op,
                -1,
                data,
                glb,
            )?;
        }
        data.op_destroy(copy_op)?;
        Ok(true)
    }

    pub fn split_load(
        &mut self,
        load_op: OpId,
        in_type: TypeId,
        data: &mut Funcdata,
        glb: &mut Architecture,
    ) -> Result<bool> {
        self.is_load_store = true;
        let mut out_vn = data.op(load_op).get_out().expect("load without output");
        let mut copy_op: Option<OpId> = None;
        if !data.vn(out_vn).is_addr_tied() {
            copy_op = data.vn(out_vn).lone_descend();
        }
        if let Some(copy) = copy_op {
            let opc = data.op(copy).code();
            if opc == OpCode::Store {
                return Ok(false);
            }
            if opc == OpCode::Zpull || opc == OpCode::Spull {
                return Ok(false);
            }
            if opc != OpCode::Copy {
                copy_op = None;
            }
        }
        if let Some(copy) = copy_op {
            out_vn = data.op(copy).get_out().expect("copy without output");
        }
        let out_type = data.vn_get_type_def_facing(out_vn, glb);
        if !self.test_datatype_compatibility(in_type, out_type, false, glb)? {
            return Ok(false);
        }
        if SplitDatatype::is_arithmetic_input(out_vn, data, glb) {
            return Ok(false);
        }
        let mut root = RootPointer::default();
        if !root.find(load_op, in_type, &mut self.resolver, data, glb) {
            return Ok(false);
        }
        let mut ptr_varnodes: Vec<VarnodeId> = Vec::new();
        let mut out_varnodes: Vec<VarnodeId> = Vec::new();
        let insert_point = copy_op.unwrap_or(load_op);
        self.build_pointers(
            root.get_pointer(),
            root.get_ptr_type(),
            root.base_offset,
            load_op,
            &mut ptr_varnodes,
            true,
            data,
            glb,
        )?;
        self.build_out_varnodes(out_vn, &mut out_varnodes, data, glb)?;
        self.build_out_concats(out_vn, insert_point, &mut out_varnodes, data, glb)?;
        let spc = space_from_const(data.op(load_op).get_in(0), data, glb);
        for index in 0..ptr_varnodes.len() {
            let addr = data.op(insert_point).get_addr().clone();
            let new_load_op = data.new_op(2, &addr);
            data.op_set_opcode(new_load_op, OpCode::Load, glb);
            let space_vn = data.new_varnode_space(&spc, glb);
            data.op_set_input(new_load_op, space_vn, 0)?;
            data.op_set_input(new_load_op, ptr_varnodes[index], 1)?;
            data.op_set_output(new_load_op, out_varnodes[index], glb)?;
            data.op_insert_before(new_load_op, insert_point);
        }
        if let Some(copy) = copy_op {
            data.op_destroy(copy)?;
        }
        data.op_destroy(load_op)?;
        root.free_pointer_chain(data)?;
        Ok(true)
    }

    pub fn split_store(
        &mut self,
        store_op: OpId,
        out_type: TypeId,
        data: &mut Funcdata,
        glb: &mut Architecture,
    ) -> Result<bool> {
        self.is_load_store = true;
        let in_vn = data.op(store_op).get_in(2);
        let mut load_op: Option<OpId> = None;
        let mut in_type: Option<TypeId> = None;
        if data.vn(in_vn).is_written() {
            let def = data.vn(in_vn).get_def().expect("written varnode without defining op");
            if data.op(def).code() == OpCode::Load && data.vn(in_vn).lone_descend() == Some(store_op) {
                load_op = Some(def);
                let size = data.vn(in_vn).get_size();
                in_type = SplitDatatype::get_value_datatype(def, size, data, glb)?;
                if in_type.is_none() {
                    load_op = None;
                }
            }
        }
        let mut in_type = match in_type {
            Some(in_type) => in_type,
            None => data.vn_get_type_read_facing(in_vn, store_op, glb),
        };
        let in_constant = data.vn(in_vn).is_constant();
        if !self.test_datatype_compatibility(in_type, out_type, in_constant, glb)? {
            if load_op.is_some() {
                load_op = None;
                in_type = data.vn_get_type_read_facing(in_vn, store_op, glb);
                self.data_type_pieces.clear();
                if !self.test_datatype_compatibility(in_type, out_type, in_constant, glb)? {
                    return Ok(false);
                }
            } else {
                return Ok(false);
            }
        }

        if SplitDatatype::is_arithmetic_output(in_vn, data, glb) {
            return Ok(false);
        }

        let mut store_root = RootPointer::default();
        if !store_root.find(store_op, out_type, &mut self.resolver, data, glb) {
            return Ok(false);
        }

        let mut load_root = RootPointer::default();
        if let Some(load) = load_op
            && !load_root.find(load, in_type, &mut self.resolver, data, glb)
        {
            return Ok(false);
        }

        let store_space = space_from_const(data.op(store_op).get_in(0), data, glb);
        let mut in_varnodes: Vec<VarnodeId> = Vec::new();
        if in_constant {
            self.build_in_constants(in_vn, &mut in_varnodes, store_space.is_big_endian(), data, glb);
        } else if let Some(load) = load_op {
            let mut load_ptrs: Vec<VarnodeId> = Vec::new();
            self.build_pointers(
                load_root.get_pointer(),
                load_root.get_ptr_type(),
                load_root.base_offset,
                load,
                &mut load_ptrs,
                true,
                data,
                glb,
            )?;
            let load_space = space_from_const(data.op(load).get_in(0), data, glb);
            for index in 0..load_ptrs.len() {
                let addr = data.op(load).get_addr().clone();
                let new_load_op = data.new_op(2, &addr);
                data.op_set_opcode(new_load_op, OpCode::Load, glb);
                let space_vn = data.new_varnode_space(&load_space, glb);
                data.op_set_input(new_load_op, space_vn, 0)?;
                data.op_set_input(new_load_op, load_ptrs[index], 1)?;
                let dt = self.data_type_pieces[index].in_type;
                let dt_size = types(glb).get(dt).get_size();
                let vn = data.new_unique_out(dt_size, new_load_op, glb)?;
                data.vn_update_type(vn, dt);
                in_varnodes.push(vn);
                data.op_insert_before(new_load_op, load);
            }
        } else {
            self.build_in_subpieces(in_vn, store_op, &mut in_varnodes, data, glb)?;
        }

        let mut store_ptrs: Vec<VarnodeId> = Vec::new();
        if data.vn(store_root.get_pointer()).is_addr_tied() {
            store_root.duplicate_to_temp(data, glb, store_op)?;
        }
        self.build_pointers(
            store_root.get_pointer(),
            store_root.get_ptr_type(),
            store_root.base_offset,
            store_op,
            &mut store_ptrs,
            false,
            data,
            glb,
        )?;
        data.op_set_input(store_op, store_ptrs[0], 1)?;
        data.op_set_input(store_op, in_varnodes[0], 2)?;
        let mut last_store = store_op;
        for index in 1..store_ptrs.len() {
            let addr = data.op(store_op).get_addr().clone();
            let new_store_op = data.new_op(3, &addr);
            data.op_set_opcode(new_store_op, OpCode::Store, glb);
            let space_vn = data.new_varnode_space(&store_space, glb);
            data.op_set_input(new_store_op, space_vn, 0)?;
            data.op_set_input(new_store_op, store_ptrs[index], 1)?;
            data.op_set_input(new_store_op, in_varnodes[index], 2)?;
            data.op_insert_after(new_store_op, last_store);
            last_store = new_store_op;
        }

        if let Some(load) = load_op {
            data.op_destroy(load)?;
            load_root.free_pointer_chain(data)?;
        }
        store_root.free_pointer_chain(data)?;
        Ok(true)
    }

    pub fn get_value_datatype(
        load_store: OpId,
        size: i32,
        data: &Funcdata,
        glb: &mut Architecture,
    ) -> Result<Option<TypeId>> {
        let ptr_type = data.vn_get_type_read_facing(data.op(load_store).get_in(1), load_store, glb);
        let factory = types(glb);
        let pointer = factory.get(ptr_type);
        if pointer.get_metatype() != TypeMetatype::Ptr {
            return Ok(None);
        }
        let (res_type, base_offset) = if pointer.is_pointer_rel() {
            (pointer.get_parent(), pointer.get_byte_offset())
        } else {
            (pointer.get_ptr_to(), 0)
        };
        let res = factory.get(res_type);
        let metain = res.get_metatype();
        let align_size = res.get_align_size();
        if align_size < size {
            if matches!(
                metain,
                TypeMetatype::Int | TypeMetatype::Uint | TypeMetatype::Bool | TypeMetatype::Float | TypeMetatype::Ptr
            ) && (size % align_size) == 0
            {
                let num_el = size / align_size;
                return Ok(Some(types_mut(glb).get_type_array(num_el, res_type)?));
            }
        } else if metain == TypeMetatype::Struct || metain == TypeMetatype::Array {
            return types_mut(glb).get_exact_piece(res_type, base_offset, size);
        }
        Ok(None)
    }
}

pub struct RuleSplitCopy {
    base: RuleBase,
}

impl RuleSplitCopy {
    pub fn new(group: &str) -> RuleSplitCopy {
        RuleSplitCopy {
            base: RuleBase::new(group, 0, "splitcopy"),
        }
    }
}

impl Rule for RuleSplitCopy {
    fn base(&self) -> &RuleBase {
        &self.base
    }

    fn base_mut(&mut self) -> &mut RuleBase {
        &mut self.base
    }

    fn clone_rule(&self, grouplist: &ActionGroupList) -> Option<Box<dyn Rule>> {
        if !grouplist.contains(self.get_group()) {
            return None;
        }
        Some(Box::new(RuleSplitCopy::new(self.get_group())))
    }

    fn get_op_list(&self, oplist: &mut Vec<OpCode>) {
        oplist.push(OpCode::Copy);
    }

    fn apply_op(&mut self, op: OpId, data: &mut Funcdata, glb: &mut Architecture) -> Result<i32> {
        let in_type = data.vn_get_type_read_facing(data.op(op).get_in(0), op, glb);
        let out_vn = data.op(op).get_out().expect("copy without output");
        let out_type = data.vn_get_type_def_facing(out_vn, glb);
        let metain = types(glb).get(in_type).get_metatype();
        let metaout = types(glb).get(out_type).get_metatype();
        if metain != TypeMetatype::PartialStruct
            && metaout != TypeMetatype::PartialStruct
            && metain != TypeMetatype::Array
            && metaout != TypeMetatype::Array
            && metain != TypeMetatype::Struct
            && metaout != TypeMetatype::Struct
        {
            return Ok(0);
        }
        let mut splitter = SplitDatatype::new(data, glb);
        if splitter.split_copy(op, in_type, out_type, data, glb)? {
            return Ok(1);
        }
        Ok(0)
    }
}

pub struct RuleSplitLoad {
    base: RuleBase,
}

impl RuleSplitLoad {
    pub fn new(group: &str) -> RuleSplitLoad {
        RuleSplitLoad {
            base: RuleBase::new(group, 0, "splitload"),
        }
    }
}

impl Rule for RuleSplitLoad {
    fn base(&self) -> &RuleBase {
        &self.base
    }

    fn base_mut(&mut self) -> &mut RuleBase {
        &mut self.base
    }

    fn clone_rule(&self, grouplist: &ActionGroupList) -> Option<Box<dyn Rule>> {
        if !grouplist.contains(self.get_group()) {
            return None;
        }
        Some(Box::new(RuleSplitLoad::new(self.get_group())))
    }

    fn get_op_list(&self, oplist: &mut Vec<OpCode>) {
        oplist.push(OpCode::Load);
    }

    fn apply_op(&mut self, op: OpId, data: &mut Funcdata, glb: &mut Architecture) -> Result<i32> {
        let out_vn = data.op(op).get_out().expect("load without output");
        let size = data.vn(out_vn).get_size();
        let in_type = match SplitDatatype::get_value_datatype(op, size, data, glb)? {
            None => return Ok(0),
            Some(in_type) => in_type,
        };
        let metain = types(glb).get(in_type).get_metatype();
        if metain != TypeMetatype::Struct && metain != TypeMetatype::Array && metain != TypeMetatype::PartialStruct {
            return Ok(0);
        }
        let mut splitter = SplitDatatype::new(data, glb);
        if splitter.split_load(op, in_type, data, glb)? {
            return Ok(1);
        }
        Ok(0)
    }
}

pub struct RuleSplitStore {
    base: RuleBase,
}

impl RuleSplitStore {
    pub fn new(group: &str) -> RuleSplitStore {
        RuleSplitStore {
            base: RuleBase::new(group, 0, "splitstore"),
        }
    }
}

impl Rule for RuleSplitStore {
    fn base(&self) -> &RuleBase {
        &self.base
    }

    fn base_mut(&mut self) -> &mut RuleBase {
        &mut self.base
    }

    fn clone_rule(&self, grouplist: &ActionGroupList) -> Option<Box<dyn Rule>> {
        if !grouplist.contains(self.get_group()) {
            return None;
        }
        Some(Box::new(RuleSplitStore::new(self.get_group())))
    }

    fn get_op_list(&self, oplist: &mut Vec<OpCode>) {
        oplist.push(OpCode::Store);
    }

    fn apply_op(&mut self, op: OpId, data: &mut Funcdata, glb: &mut Architecture) -> Result<i32> {
        let size = data.vn(data.op(op).get_in(2)).get_size();
        let out_type = match SplitDatatype::get_value_datatype(op, size, data, glb)? {
            None => return Ok(0),
            Some(out_type) => out_type,
        };
        let metain = types(glb).get(out_type).get_metatype();
        if metain != TypeMetatype::Struct && metain != TypeMetatype::Array && metain != TypeMetatype::PartialStruct {
            return Ok(0);
        }
        let mut splitter = SplitDatatype::new(data, glb);
        if splitter.split_store(op, out_type, data, glb)? {
            return Ok(1);
        }
        Ok(0)
    }
}

pub struct RuleDumptyHumpLate {
    base: RuleBase,
}

impl RuleDumptyHumpLate {
    pub fn new(group: &str) -> RuleDumptyHumpLate {
        RuleDumptyHumpLate {
            base: RuleBase::new(group, 0, "dumptyhumplate"),
        }
    }
}

impl Rule for RuleDumptyHumpLate {
    fn base(&self) -> &RuleBase {
        &self.base
    }

    fn base_mut(&mut self) -> &mut RuleBase {
        &mut self.base
    }

    fn clone_rule(&self, grouplist: &ActionGroupList) -> Option<Box<dyn Rule>> {
        if !grouplist.contains(self.get_group()) {
            return None;
        }
        Some(Box::new(RuleDumptyHumpLate::new(self.get_group())))
    }

    fn get_op_list(&self, oplist: &mut Vec<OpCode>) {
        oplist.push(OpCode::Subpiece);
    }

    fn apply_op(&mut self, op: OpId, data: &mut Funcdata, glb: &mut Architecture) -> Result<i32> {
        let mut vn = data.op(op).get_in(0);
        if !data.vn(vn).is_written() {
            return Ok(0);
        }
        let mut piece_op = data.vn(vn).get_def().expect("written varnode without defining op");
        let opc = data.op(piece_op).code();
        if opc == OpCode::Subpiece {
            let base = data.op(piece_op).get_in(0);
            data.op_set_input(op, base, 0)?;
            let op_offset = data.vn(data.op(op).get_in(1)).get_offset();
            let trunc = op_offset.wrapping_add(data.vn(data.op(piece_op).get_in(1)).get_offset());
            if trunc != op_offset {
                let trunc_vn = data.new_constant(4, trunc, glb);
                data.op_set_input(op, trunc_vn, 1)?;
            }
            if data.vn(vn).has_no_descend() && !data.vn(vn).is_auto_live() {
                let mut scratch: Vec<OpId> = Vec::new();
                data.op_destroy_recursive(piece_op, &mut scratch)?;
            }
            return Ok(1);
        } else if opc != OpCode::Piece {
            return Ok(0);
        }
        let out = data.op(op).get_out().expect("subpiece without output");
        let out_size = data.vn(out).get_size();
        let mut trunc = data.vn(data.op(op).get_in(1)).get_offset() as i32;
        loop {
            let mut trial_vn = data.op(piece_op).get_in(1);
            let mut trial_trunc = trunc;
            if trunc >= data.vn(trial_vn).get_size() {
                trial_trunc -= data.vn(trial_vn).get_size();
                trial_vn = data.op(piece_op).get_in(0);
            }
            if out_size + trial_trunc > data.vn(trial_vn).get_size() {
                break;
            }
            vn = trial_vn;
            trunc = trial_trunc;
            if data.vn(vn).get_size() == out_size {
                break;
            }
            if !data.vn(vn).is_written() {
                break;
            }
            piece_op = data.vn(vn).get_def().expect("written varnode without defining op");
            if data.op(piece_op).code() != OpCode::Piece {
                break;
            }
        }
        if vn == data.op(op).get_in(0) {
            return Ok(0);
        }
        if data.vn(vn).is_written() {
            let def = data.vn(vn).get_def().expect("written varnode without defining op");
            if data.op(def).code() == OpCode::Copy {
                vn = data.op(def).get_in(0);
            }
        }
        let remove_op;
        if out_size != data.vn(vn).get_size() {
            remove_op = data
                .vn(data.op(op).get_in(0))
                .get_def()
                .expect("written varnode without defining op");
            if data.vn(data.op(op).get_in(1)).get_offset() != trunc as i64 as u64 {
                let trunc_vn = data.new_constant(4, trunc as i64 as u64, glb);
                data.op_set_input(op, trunc_vn, 1)?;
            }
            data.op_set_input(op, vn, 0)?;
        } else if data.vn(out).is_auto_live() {
            remove_op = data
                .vn(data.op(op).get_in(0))
                .get_def()
                .expect("written varnode without defining op");
            data.op_remove_input(op, 1);
            data.op_set_opcode(op, OpCode::Copy, glb);
            data.op_set_input(op, vn, 0)?;
        } else {
            remove_op = op;
            data.total_replace(out, vn)?;
        }
        let remove_out = data.op(remove_op).get_out().expect("removed op without output");
        if data.vn(remove_out).has_no_descend() && !data.vn(remove_out).is_auto_live() {
            let mut scratch: Vec<OpId> = Vec::new();
            data.op_destroy_recursive(remove_op, &mut scratch)?;
        }
        Ok(1)
    }
}

#[derive(Clone, Copy, Debug)]
pub struct State {
    pub op: OpId,
    pub slot: i32,
    pub max_precision: i32,
}

impl State {
    pub fn new(start_op: OpId) -> State {
        State {
            op: start_op,
            slot: 0,
            max_precision: 0,
        }
    }

    pub fn incorporate_input_size(&mut self, sz: i32) {
        self.max_precision = if self.max_precision < sz {
            sz
        } else {
            self.max_precision
        };
    }
}

fn precision_passes_through(opc: OpCode) -> bool {
    matches!(
        opc,
        OpCode::Multiequal
            | OpCode::FloatNeg
            | OpCode::FloatAbs
            | OpCode::FloatSqrt
            | OpCode::FloatCeil
            | OpCode::FloatFloor
            | OpCode::FloatRound
            | OpCode::Copy
    )
}

#[derive(Clone, Debug)]
pub struct SubfloatFlow {
    pub manager: TransformManager,
    pub(crate) precision: i32,
    pub(crate) terminator_count: i32,
    pub(crate) format: Option<FloatFormat>,
    pub(crate) worklist: Vec<usize>,
    pub(crate) max_precision_map: BTreeMap<OpId, i32>,
}

impl SubfloatFlow {
    pub fn new(data: &mut Funcdata, glb: &Architecture, root: VarnodeId, prec: i32) -> Result<SubfloatFlow> {
        let format = glb
            .translate
            .as_deref()
            .expect("translator is not initialized")
            .translate_base()
            .get_float_format(prec)
            .cloned();
        let mut flow = SubfloatFlow {
            manager: TransformManager::with_flavor(TransformFlavor::Subfloat),
            precision: prec,
            terminator_count: 0,
            format,
            worklist: Vec::new(),
            max_precision_map: BTreeMap::new(),
        };
        if flow.format.is_none() {
            return Ok(flow);
        }
        flow.set_replacement(root, data, glb)?;
        Ok(flow)
    }

    pub fn preserve_address(&self, vn: VarnodeId, bit_size: i32, lsb_offset: i32, data: &Funcdata) -> bool {
        self.manager.preserve_address(vn, bit_size, lsb_offset, data)
    }

    fn max_precision(&mut self, vn: VarnodeId, data: &mut Funcdata) -> i32 {
        if !data.vn(vn).is_written() {
            return data.vn(vn).get_size();
        }
        let op = data.vn(vn).get_def().expect("written varnode without defining op");
        match data.op(op).code() {
            OpCode::Multiequal
            | OpCode::FloatNeg
            | OpCode::FloatAbs
            | OpCode::FloatSqrt
            | OpCode::FloatCeil
            | OpCode::FloatFloor
            | OpCode::FloatRound
            | OpCode::Copy => {}
            OpCode::FloatAdd | OpCode::FloatSub | OpCode::FloatMult | OpCode::FloatDiv => return 0,
            OpCode::FloatFloat2float | OpCode::FloatInt2float => {
                let in_size = data.vn(data.op(op).get_in(0)).get_size();
                if in_size > data.vn(vn).get_size() {
                    return data.vn(vn).get_size();
                }
                return in_size;
            }
            _ => return data.vn(vn).get_size(),
        }

        if let Some(&res) = self.max_precision_map.get(&op) {
            return res;
        }
        let mut op_stack: Vec<State> = vec![State::new(op)];
        data.op_mut(op).set_mark();
        let mut max = 0;
        while let Some(state) = op_stack.last_mut() {
            if state.slot >= data.op(state.op).num_input() {
                max = state.max_precision;
                let finished = state.op;
                data.op_mut(finished).clear_mark();
                self.max_precision_map.insert(finished, max);
                op_stack.pop();
                if let Some(parent) = op_stack.last_mut() {
                    parent.incorporate_input_size(max);
                }
                continue;
            }
            let next_vn = data.op(state.op).get_in(state.slot);
            state.slot += 1;
            if !data.vn(next_vn).is_written() {
                state.incorporate_input_size(data.vn(next_vn).get_size());
                continue;
            }
            let next_op = data.vn(next_vn).get_def().expect("written varnode without defining op");
            if data.op(next_op).is_mark() {
                continue;
            }
            let next_code = data.op(next_op).code();
            if precision_passes_through(next_code) {
                if let Some(&cached) = self.max_precision_map.get(&next_op) {
                    state.incorporate_input_size(cached);
                    continue;
                }
                data.op_mut(next_op).set_mark();
                op_stack.push(State::new(next_op));
                continue;
            }
            match next_code {
                OpCode::FloatAdd | OpCode::FloatSub | OpCode::FloatMult | OpCode::FloatDiv => {}
                OpCode::FloatFloat2float | OpCode::FloatInt2float => {
                    let in_size = data.vn(data.op(next_op).get_in(0)).get_size();
                    let next_size = data.vn(next_vn).get_size();
                    if in_size > next_size {
                        state.incorporate_input_size(next_size);
                    } else {
                        state.incorporate_input_size(in_size);
                    }
                }
                _ => state.incorporate_input_size(data.vn(next_vn).get_size()),
            }
        }
        max
    }

    fn exceeds_precision(&mut self, op: OpId, data: &mut Funcdata) -> bool {
        let val1 = self.max_precision(data.op(op).get_in(0), data);
        let val2 = self.max_precision(data.op(op).get_in(1), data);
        let min = if val1 < val2 { val1 } else { val2 };
        min > self.precision
    }

    fn set_replacement(&mut self, vn: VarnodeId, data: &mut Funcdata, glb: &Architecture) -> Result<Option<usize>> {
        let original = data.vn(vn);
        if original.is_mark() {
            return Ok(Some(self.manager.get_piece(vn, self.precision * 8, 0, data)?));
        }

        if original.is_constant() {
            let form2 = glb
                .translate
                .as_deref()
                .expect("translator is not initialized")
                .translate_base()
                .get_float_format(original.get_size());
            let form2 = match form2 {
                None => return Ok(None),
                Some(form2) => form2,
            };
            let format = self.format.as_ref().expect("missing float format");
            let converted = format.convert_encoding(original.get_offset(), form2);
            return Ok(Some(self.manager.new_constant(self.precision, 0, converted)));
        }

        if original.is_free() {
            return Ok(None);
        }

        if original.is_addr_force() && original.get_size() != self.precision {
            return Ok(None);
        }

        if original.is_type_lock()
            && varnode_metatype(vn, data, glb) != TypeMetatype::PartialStruct
            && varnode_type_size(vn, data, glb) != self.precision
        {
            return Ok(None);
        }

        if original.is_input() && original.get_size() != self.precision {
            return Ok(None);
        }

        let same_size = original.get_size() == self.precision;
        data.vn_mut(vn).set_mark();
        let res = if same_size {
            self.manager.new_preexisting_varnode(vn, data)
        } else {
            let res = self.manager.new_piece(vn, self.precision * 8, 0, data);
            self.worklist.push(res);
            res
        };
        Ok(Some(res))
    }

    fn trace_forward(&mut self, rvn: usize, data: &mut Funcdata, glb: &Architecture) -> Result<bool> {
        let vn = self
            .manager
            .var(rvn)
            .get_original()
            .expect("placeholder without original varnode");
        let descend: Vec<OpId> = data.vn(vn).descend().to_vec();
        for (iter, &op) in descend.iter().enumerate() {
            let outvn_opt = data.op(op).get_out();
            if let Some(outvn) = outvn_opt
                && data.vn(outvn).is_mark()
            {
                continue;
            }
            let opc = data.op(op).code();
            match opc {
                OpCode::FloatAdd
                | OpCode::FloatSub
                | OpCode::FloatMult
                | OpCode::FloatDiv
                | OpCode::Multiequal
                | OpCode::Copy
                | OpCode::FloatCeil
                | OpCode::FloatFloor
                | OpCode::FloatRound
                | OpCode::FloatNeg
                | OpCode::FloatAbs
                | OpCode::FloatSqrt => {
                    if matches!(
                        opc,
                        OpCode::FloatAdd | OpCode::FloatSub | OpCode::FloatMult | OpCode::FloatDiv
                    ) && self.exceeds_precision(op, data)
                    {
                        return Ok(false);
                    }
                    let rop = self.manager.new_op_replace(data.op(op).num_input(), opc, op);
                    let outvn = outvn_opt.expect("op without output");
                    let outrvn = match self.set_replacement(outvn, data, glb)? {
                        None => return Ok(false),
                        Some(outrvn) => outrvn,
                    };
                    let slot = data.op(op).get_slot(vn);
                    self.manager.op_set_input(rop, rvn, slot);
                    self.manager.op_set_output(rop, outrvn);
                }
                OpCode::FloatFloat2float => {
                    let out_size = data.vn(outvn_opt.expect("op without output")).get_size();
                    if out_size < self.precision {
                        return Ok(false);
                    }
                    let new_code = if out_size == self.precision {
                        OpCode::Copy
                    } else {
                        OpCode::FloatFloat2float
                    };
                    let rop = self.manager.new_preexisting_op(1, new_code, op);
                    self.manager.op_set_input(rop, rvn, 0);
                    self.terminator_count += 1;
                }
                OpCode::FloatEqual | OpCode::FloatNotequal | OpCode::FloatLess | OpCode::FloatLessequal => {
                    if self.exceeds_precision(op, data) {
                        return Ok(false);
                    }
                    let mut slot = data.op(op).get_slot(vn);
                    let other = data.op(op).get_in(1 - slot);
                    let rvn2 = match self.set_replacement(other, data, glb)? {
                        None => return Ok(false),
                        Some(rvn2) => rvn2,
                    };
                    if rvn == rvn2 {
                        slot = data.op(op).get_repeat_slot(op, vn, slot, &descend, iter);
                    }
                    if TransformManager::preexisting_guard(slot, self.manager.var(rvn2)) {
                        let rop = self.manager.new_preexisting_op(2, opc, op);
                        self.manager.op_set_input(rop, rvn, slot);
                        self.manager.op_set_input(rop, rvn2, 1 - slot);
                        self.terminator_count += 1;
                    }
                }
                OpCode::FloatTrunc | OpCode::FloatNan => {
                    let rop = self.manager.new_preexisting_op(1, opc, op);
                    self.manager.op_set_input(rop, rvn, 0);
                    self.terminator_count += 1;
                }
                _ => return Ok(false),
            }
        }
        Ok(true)
    }

    fn trace_backward(&mut self, rvn: usize, data: &mut Funcdata, glb: &Architecture) -> Result<bool> {
        let original = self
            .manager
            .var(rvn)
            .get_original()
            .expect("placeholder without original varnode");
        let op = match data.vn(original).get_def() {
            None => return Ok(true),
            Some(op) => op,
        };

        let opc = data.op(op).code();
        match opc {
            OpCode::FloatAdd
            | OpCode::FloatSub
            | OpCode::FloatMult
            | OpCode::FloatDiv
            | OpCode::Copy
            | OpCode::FloatCeil
            | OpCode::FloatFloor
            | OpCode::FloatRound
            | OpCode::FloatNeg
            | OpCode::FloatAbs
            | OpCode::FloatSqrt
            | OpCode::Multiequal => {
                if matches!(
                    opc,
                    OpCode::FloatAdd | OpCode::FloatSub | OpCode::FloatMult | OpCode::FloatDiv
                ) && self.exceeds_precision(op, data)
                {
                    return Ok(false);
                }
                let rop = match self.manager.var(rvn).get_def() {
                    Some(rop) => rop,
                    None => {
                        let rop = self.manager.new_op_replace(data.op(op).num_input(), opc, op);
                        self.manager.op_set_output(rop, rvn);
                        rop
                    }
                };
                for slot in 0..data.op(op).num_input() {
                    if self.manager.op(rop).get_in(slot).is_none() {
                        let input = data.op(op).get_in(slot);
                        let newvar = match self.set_replacement(input, data, glb)? {
                            None => return Ok(false),
                            Some(newvar) => newvar,
                        };
                        self.manager.op_set_input(rop, newvar, slot);
                    }
                }
                Ok(true)
            }
            OpCode::FloatInt2float => {
                let vn = data.op(op).get_in(0);
                if !data.vn(vn).is_constant() && data.vn(vn).is_free() {
                    return Ok(false);
                }
                let rop = self.manager.new_op_replace(1, OpCode::FloatInt2float, op);
                self.manager.op_set_output(rop, rvn);
                let newvar = self.manager.get_preexisting_varnode(vn, data);
                self.manager.op_set_input(rop, newvar, 0);
                Ok(true)
            }
            OpCode::FloatFloat2float => {
                let vn = data.op(op).get_in(0);
                let newvar;
                let new_code;
                if data.vn(vn).is_constant() {
                    new_code = OpCode::Copy;
                    if data.vn(vn).get_size() == self.precision {
                        newvar = self.manager.new_constant(self.precision, 0, data.vn(vn).get_offset());
                    } else {
                        newvar = match self.set_replacement(vn, data, glb)? {
                            None => return Ok(false),
                            Some(newvar) => newvar,
                        };
                    }
                } else {
                    if data.vn(vn).is_free() {
                        return Ok(false);
                    }
                    new_code = if data.vn(vn).get_size() == self.precision {
                        OpCode::Copy
                    } else {
                        OpCode::FloatFloat2float
                    };
                    newvar = self.manager.get_preexisting_varnode(vn, data);
                }
                let rop = self.manager.new_op_replace(1, new_code, op);
                self.manager.op_set_output(rop, rvn);
                self.manager.op_set_input(rop, newvar, 0);
                Ok(true)
            }
            _ => Ok(false),
        }
    }

    fn process_next_work(&mut self, data: &mut Funcdata, glb: &Architecture) -> Result<bool> {
        let rvn = self.worklist.pop().expect("empty subfloat worklist");

        if !self.trace_backward(rvn, data, glb)? {
            return Ok(false);
        }
        self.trace_forward(rvn, data, glb)
    }

    pub fn do_trace(&mut self, data: &mut Funcdata, glb: &Architecture) -> Result<bool> {
        if self.format.is_none() {
            return Ok(false);
        }
        self.terminator_count = 0;
        let mut retval = true;
        while !self.worklist.is_empty() {
            if !self.process_next_work(data, glb)? {
                retval = false;
                break;
            }
        }

        self.manager.clear_varnode_marks(data);

        if !retval {
            return Ok(false);
        }
        if self.terminator_count == 0 {
            return Ok(false);
        }
        Ok(true)
    }
}

pub struct RuleSubfloatConvert {
    base: RuleBase,
}

impl RuleSubfloatConvert {
    pub fn new(group: &str) -> RuleSubfloatConvert {
        RuleSubfloatConvert {
            base: RuleBase::new(group, 0, "subfloat_convert"),
        }
    }
}

impl Rule for RuleSubfloatConvert {
    fn base(&self) -> &RuleBase {
        &self.base
    }

    fn base_mut(&mut self) -> &mut RuleBase {
        &mut self.base
    }

    fn clone_rule(&self, grouplist: &ActionGroupList) -> Option<Box<dyn Rule>> {
        if !grouplist.contains(self.get_group()) {
            return None;
        }
        Some(Box::new(RuleSubfloatConvert::new(self.get_group())))
    }

    fn get_op_list(&self, oplist: &mut Vec<OpCode>) {
        oplist.push(OpCode::FloatFloat2float);
    }

    fn apply_op(&mut self, op: OpId, data: &mut Funcdata, glb: &mut Architecture) -> Result<i32> {
        let invn = data.op(op).get_in(0);
        let outvn = data.op(op).get_out().expect("conversion without output");
        let insize = data.vn(invn).get_size();
        let outsize = data.vn(outvn).get_size();
        let mut subflow = if outsize > insize {
            SubfloatFlow::new(data, glb, outvn, insize)?
        } else {
            SubfloatFlow::new(data, glb, invn, outsize)?
        };
        if !subflow.do_trace(data, glb)? {
            return Ok(0);
        }
        subflow.manager.apply(data, glb)?;
        Ok(1)
    }
}

#[derive(Clone, Copy, Debug)]
pub struct WorkNode {
    pub(crate) lanes: usize,
    pub(crate) num_lanes: i32,
    pub(crate) skip_lanes: i32,
}

#[derive(Clone, Debug)]
pub struct LaneDivide {
    pub manager: TransformManager,
    pub(crate) description: LaneDescription,
    pub(crate) work_list: Vec<WorkNode>,
    pub(crate) allow_subpiece_terminator: bool,
}

impl LaneDivide {
    pub fn new(
        data: &mut Funcdata,
        glb: &Architecture,
        root: VarnodeId,
        desc: &LaneDescription,
        allow_downcast: bool,
    ) -> LaneDivide {
        let mut divide = LaneDivide {
            manager: TransformManager::new(),
            description: desc.clone(),
            work_list: Vec::new(),
            allow_subpiece_terminator: allow_downcast,
        };
        divide.set_replacement(root, desc.get_num_lanes(), 0, data, glb);
        divide
    }

    fn set_replacement(
        &mut self,
        vn: VarnodeId,
        num_lanes: i32,
        skip_lanes: i32,
        data: &mut Funcdata,
        glb: &Architecture,
    ) -> Option<usize> {
        let original = data.vn(vn);
        if original.is_mark() {
            return Some(
                self.manager
                    .get_split_lanes(vn, &self.description, num_lanes, skip_lanes, data),
            );
        }

        if original.is_constant() {
            return Some(
                self.manager
                    .new_split_lanes(vn, &self.description, num_lanes, skip_lanes, data),
            );
        }

        if original.is_type_lock() {
            let meta = varnode_metatype(vn, data, glb);
            if meta > TypeMetatype::Array {
                return None;
            }
            if meta == TypeMetatype::Struct || meta == TypeMetatype::Union {
                return None;
            }
        }

        let is_free = original.is_free();
        data.vn_mut(vn).set_mark();
        let res = self
            .manager
            .new_split_lanes(vn, &self.description, num_lanes, skip_lanes, data);
        if !is_free {
            self.work_list.push(WorkNode {
                lanes: res,
                num_lanes,
                skip_lanes,
            });
        }
        Some(res)
    }

    fn build_unary_op(&mut self, opc: OpCode, op: OpId, in_vars: usize, out_vars: usize, num_lanes: i32) {
        for index in 0..num_lanes {
            let rop = self.manager.new_op_replace(1, opc, op);
            self.manager.op_set_output(rop, out_vars + index as usize);
            self.manager.op_set_input(rop, in_vars + index as usize, 0);
        }
    }

    fn build_binary_op(
        &mut self,
        opc: OpCode,
        op: OpId,
        in0_vars: usize,
        in1_vars: usize,
        out_vars: usize,
        num_lanes: i32,
    ) {
        for index in 0..num_lanes {
            let rop = self.manager.new_op_replace(2, opc, op);
            self.manager.op_set_output(rop, out_vars + index as usize);
            self.manager.op_set_input(rop, in0_vars + index as usize, 0);
            self.manager.op_set_input(rop, in1_vars + index as usize, 1);
        }
    }

    fn build_piece(
        &mut self,
        op: OpId,
        out_vars: usize,
        num_lanes: i32,
        skip_lanes: i32,
        data: &mut Funcdata,
        glb: &Architecture,
    ) -> bool {
        let mut high_lanes = 0;
        let mut high_skip = 0;
        let mut low_lanes = 0;
        let mut low_skip = 0;
        let high_vn = data.op(op).get_in(0);
        let low_vn = data.op(op).get_in(1);
        let high_size = data.vn(high_vn).get_size();
        let low_size = data.vn(low_vn).get_size();

        if !self.description.restriction(
            num_lanes,
            skip_lanes,
            low_size,
            high_size,
            &mut high_lanes,
            &mut high_skip,
        ) {
            return false;
        }
        if !self
            .description
            .restriction(num_lanes, skip_lanes, 0, low_size, &mut low_lanes, &mut low_skip)
        {
            return false;
        }
        if high_lanes == 1 {
            let high_rvn = self.manager.get_preexisting_varnode(high_vn, data);
            let rop = self.manager.new_op_replace(1, OpCode::Copy, op);
            self.manager.op_set_input(rop, high_rvn, 0);
            self.manager.op_set_output(rop, out_vars + (num_lanes - 1) as usize);
        } else {
            let high_rvn = match self.set_replacement(high_vn, high_lanes, high_skip, data, glb) {
                None => return false,
                Some(high_rvn) => high_rvn,
            };
            let out_high_start = num_lanes - high_lanes;
            for index in 0..high_lanes {
                let rop = self.manager.new_op_replace(1, OpCode::Copy, op);
                self.manager.op_set_input(rop, high_rvn + index as usize, 0);
                self.manager
                    .op_set_output(rop, out_vars + (out_high_start + index) as usize);
            }
        }
        if low_lanes == 1 {
            let low_rvn = self.manager.get_preexisting_varnode(low_vn, data);
            let rop = self.manager.new_op_replace(1, OpCode::Copy, op);
            self.manager.op_set_input(rop, low_rvn, 0);
            self.manager.op_set_output(rop, out_vars);
        } else {
            let low_rvn = match self.set_replacement(low_vn, low_lanes, low_skip, data, glb) {
                None => return false,
                Some(low_rvn) => low_rvn,
            };
            for index in 0..low_lanes {
                let rop = self.manager.new_op_replace(1, OpCode::Copy, op);
                self.manager.op_set_input(rop, low_rvn + index as usize, 0);
                self.manager.op_set_output(rop, out_vars + index as usize);
            }
        }
        true
    }

    fn build_multiequal(
        &mut self,
        op: OpId,
        out_vars: usize,
        num_lanes: i32,
        skip_lanes: i32,
        data: &mut Funcdata,
        glb: &Architecture,
    ) -> bool {
        let mut in_var_sets: Vec<usize> = Vec::new();
        let num_input = data.op(op).num_input();
        for slot in 0..num_input {
            let input = data.op(op).get_in(slot);
            let in_vn = match self.set_replacement(input, num_lanes, skip_lanes, data, glb) {
                None => return false,
                Some(in_vn) => in_vn,
            };
            in_var_sets.push(in_vn);
        }
        for index in 0..num_lanes {
            let rop = self.manager.new_op_replace(num_input, OpCode::Multiequal, op);
            self.manager.op_set_output(rop, out_vars + index as usize);
            for slot in 0..num_input {
                self.manager
                    .op_set_input(rop, in_var_sets[slot as usize] + index as usize, slot);
            }
        }
        true
    }

    fn build_indirect(
        &mut self,
        op: OpId,
        out_vars: usize,
        num_lanes: i32,
        skip_lanes: i32,
        data: &mut Funcdata,
        glb: &Architecture,
    ) -> bool {
        let input = data.op(op).get_in(0);
        let in_vn = match self.set_replacement(input, num_lanes, skip_lanes, data, glb) {
            None => return false,
            Some(in_vn) => in_vn,
        };
        for index in 0..num_lanes {
            let rop = self.manager.new_indirect_replace(op, data);
            self.manager.op_set_output(rop, out_vars + index as usize);
            self.manager.op_set_input(rop, in_vn + index as usize, 0);
        }
        true
    }

    fn build_store(
        &mut self,
        op: OpId,
        num_lanes: i32,
        skip_lanes: i32,
        data: &mut Funcdata,
        glb: &Architecture,
    ) -> bool {
        let stored = data.op(op).get_in(2);
        let in_vars = match self.set_replacement(stored, num_lanes, skip_lanes, data, glb) {
            None => return false,
            Some(in_vars) => in_vars,
        };
        let space_vn = data.op(op).get_in(0);
        let space_const = data.vn(space_vn).get_offset();
        let space_const_size = data.vn(space_vn).get_size();
        let spc = space_from_const(space_vn, data, glb);
        let orig_ptr = data.op(op).get_in(1);
        if data.vn(orig_ptr).is_free() && !data.vn(orig_ptr).is_constant() {
            return false;
        }
        let base_ptr = self.manager.get_preexisting_varnode(orig_ptr, data);
        let ptr_size = data.vn(orig_ptr).get_size();
        let mut byte_pos: i64 = 0;
        for count in 0..num_lanes {
            let index = if spc.is_big_endian() {
                num_lanes - 1 - count
            } else {
                count
            };
            let rop_store = self.manager.new_op_replace(3, OpCode::Store, op);

            let ptr_vn = if byte_pos == 0 {
                base_ptr
            } else {
                let ptr_vn = self.manager.new_unique(ptr_size);
                let add_op = self.manager.new_op(2, OpCode::IntAdd, rop_store);
                self.manager.op_set_output(add_op, ptr_vn);
                self.manager.op_set_input(add_op, base_ptr, 0);
                let offset = self.manager.new_constant(ptr_size, 0, byte_pos as u64);
                self.manager.op_set_input(add_op, offset, 1);
                ptr_vn
            };

            let space_rvn = self.manager.new_constant(space_const_size, 0, space_const);
            self.manager.op_set_input(rop_store, space_rvn, 0);
            self.manager.op_set_input(rop_store, ptr_vn, 1);
            self.manager.op_set_input(rop_store, in_vars + index as usize, 2);
            byte_pos += self.description.get_size(skip_lanes + index) as i64;
        }
        true
    }

    fn build_load(
        &mut self,
        op: OpId,
        out_vars: usize,
        num_lanes: i32,
        skip_lanes: i32,
        data: &mut Funcdata,
        glb: &Architecture,
    ) -> bool {
        let space_vn = data.op(op).get_in(0);
        let space_const = data.vn(space_vn).get_offset();
        let space_const_size = data.vn(space_vn).get_size();
        let spc = space_from_const(space_vn, data, glb);
        let orig_ptr = data.op(op).get_in(1);
        if data.vn(orig_ptr).is_free() && !data.vn(orig_ptr).is_constant() {
            return false;
        }
        let base_ptr = self.manager.get_preexisting_varnode(orig_ptr, data);
        let ptr_size = data.vn(orig_ptr).get_size();
        let mut byte_pos: i64 = 0;
        for count in 0..num_lanes {
            let rop_load = self.manager.new_op_replace(2, OpCode::Load, op);
            let index = if spc.is_big_endian() {
                num_lanes - 1 - count
            } else {
                count
            };

            let ptr_vn = if byte_pos == 0 {
                base_ptr
            } else {
                let ptr_vn = self.manager.new_unique(ptr_size);
                let add_op = self.manager.new_op(2, OpCode::IntAdd, rop_load);
                self.manager.op_set_output(add_op, ptr_vn);
                self.manager.op_set_input(add_op, base_ptr, 0);
                let offset = self.manager.new_constant(ptr_size, 0, byte_pos as u64);
                self.manager.op_set_input(add_op, offset, 1);
                ptr_vn
            };

            let space_rvn = self.manager.new_constant(space_const_size, 0, space_const);
            self.manager.op_set_input(rop_load, space_rvn, 0);
            self.manager.op_set_input(rop_load, ptr_vn, 1);
            self.manager.op_set_output(rop_load, out_vars + index as usize);
            byte_pos += self.description.get_size(skip_lanes + index) as i64;
        }
        true
    }

    fn build_right_shift(
        &mut self,
        op: OpId,
        out_vars: usize,
        num_lanes: i32,
        skip_lanes: i32,
        data: &mut Funcdata,
        glb: &Architecture,
    ) -> bool {
        let shift_vn = data.op(op).get_in(1);
        if !data.vn(shift_vn).is_constant() {
            return false;
        }
        let mut shift_size = data.vn(shift_vn).get_offset() as i32;
        if (shift_size & 7) != 0 {
            return false;
        }
        shift_size /= 8;
        let start_pos = shift_size + self.description.get_position(skip_lanes);
        let start_lane = self.description.get_boundary(start_pos);
        if start_lane < 0 {
            return false;
        }
        let mut src_lane = start_lane;
        let mut dest_lane = skip_lanes;
        while src_lane - skip_lanes < num_lanes {
            if self.description.get_size(src_lane) != self.description.get_size(dest_lane) {
                return false;
            }
            src_lane += 1;
            dest_lane += 1;
        }
        let input = data.op(op).get_in(0);
        let in_vars = match self.set_replacement(input, num_lanes, skip_lanes, data, glb) {
            None => return false,
            Some(in_vars) => in_vars,
        };
        let moved = start_lane - skip_lanes;
        self.build_unary_op(OpCode::Copy, op, in_vars + moved as usize, out_vars, num_lanes - moved);
        for zero_lane in (num_lanes - moved)..num_lanes {
            let rop = self.manager.new_op_replace(1, OpCode::Copy, op);
            self.manager.op_set_output(rop, out_vars + zero_lane as usize);
            let zero = self.manager.new_constant(self.description.get_size(zero_lane), 0, 0);
            self.manager.op_set_input(rop, zero, 0);
        }
        true
    }

    fn build_left_shift(
        &mut self,
        op: OpId,
        out_vars: usize,
        num_lanes: i32,
        skip_lanes: i32,
        data: &mut Funcdata,
        glb: &Architecture,
    ) -> bool {
        let shift_vn = data.op(op).get_in(1);
        if !data.vn(shift_vn).is_constant() {
            return false;
        }
        let mut shift_size = data.vn(shift_vn).get_offset() as i32;
        if (shift_size & 7) != 0 {
            return false;
        }
        shift_size /= 8;
        let start_pos = shift_size + self.description.get_position(skip_lanes);
        let start_lane = self.description.get_boundary(start_pos);
        if start_lane < 0 {
            return false;
        }
        let mut dest_lane = start_lane;
        let mut src_lane = skip_lanes;
        while dest_lane - skip_lanes < num_lanes {
            if self.description.get_size(src_lane) != self.description.get_size(dest_lane) {
                return false;
            }
            src_lane += 1;
            dest_lane += 1;
        }
        let input = data.op(op).get_in(0);
        let in_vars = match self.set_replacement(input, num_lanes, skip_lanes, data, glb) {
            None => return false,
            Some(in_vars) => in_vars,
        };
        let moved = start_lane - skip_lanes;
        for zero_lane in 0..moved {
            let rop = self.manager.new_op_replace(1, OpCode::Copy, op);
            self.manager.op_set_output(rop, out_vars + zero_lane as usize);
            let zero = self.manager.new_constant(self.description.get_size(zero_lane), 0, 0);
            self.manager.op_set_input(rop, zero, 0);
        }
        self.build_unary_op(OpCode::Copy, op, in_vars, out_vars + moved as usize, num_lanes - moved);
        true
    }

    fn build_zext(
        &mut self,
        op: OpId,
        out_vars: usize,
        num_lanes: i32,
        skip_lanes: i32,
        data: &mut Funcdata,
        glb: &Architecture,
    ) -> bool {
        let mut in_lanes = 0;
        let mut in_skip = 0;
        let invn = data.op(op).get_in(0);
        if !data.vn(invn).is_constant() || data.vn(invn).get_offset() != 0 {
            let in_size = data.vn(invn).get_size();
            if !self
                .description
                .restriction(num_lanes, skip_lanes, 0, in_size, &mut in_lanes, &mut in_skip)
            {
                return false;
            }
            if in_lanes == 1 {
                let rop = self.manager.new_op_replace(1, OpCode::Copy, op);
                let in_var = self.manager.get_preexisting_varnode(invn, data);
                self.manager.op_set_input(rop, in_var, 0);
                self.manager.op_set_output(rop, out_vars);
            } else {
                let in_rvn = match self.set_replacement(invn, in_lanes, in_skip, data, glb) {
                    None => return false,
                    Some(in_rvn) => in_rvn,
                };
                for index in 0..in_lanes {
                    let rop = self.manager.new_op_replace(1, OpCode::Copy, op);
                    self.manager.op_set_input(rop, in_rvn + index as usize, 0);
                    self.manager.op_set_output(rop, out_vars + index as usize);
                }
            }
        } else {
            in_lanes = 0;
        }
        for index in 0..(num_lanes - in_lanes) {
            let rop = self.manager.new_op_replace(1, OpCode::Copy, op);
            let zero = self
                .manager
                .new_constant(self.description.get_size(skip_lanes + in_lanes + index), 0, 0);
            self.manager.op_set_input(rop, zero, 0);
            self.manager.op_set_output(rop, out_vars + (in_lanes + index) as usize);
        }
        true
    }

    fn trace_forward(
        &mut self,
        rvn: usize,
        num_lanes: i32,
        skip_lanes: i32,
        data: &mut Funcdata,
        glb: &Architecture,
    ) -> bool {
        let origvn = self
            .manager
            .var(rvn)
            .get_original()
            .expect("placeholder without original varnode");
        let descend: Vec<OpId> = data.vn(origvn).descend().to_vec();
        for op in descend {
            let outvn_opt = data.op(op).get_out();
            if let Some(outvn) = outvn_opt
                && data.vn(outvn).is_mark()
            {
                continue;
            }
            match data.op(op).code() {
                OpCode::Subpiece => {
                    let outvn = outvn_opt.expect("subpiece without output");
                    let byte_pos = data.vn(data.op(op).get_in(1)).get_offset() as i32;
                    let mut out_lanes = 0;
                    let mut out_skip = 0;
                    let out_size = data.vn(outvn).get_size();
                    if !self.description.restriction(
                        num_lanes,
                        skip_lanes,
                        byte_pos,
                        out_size,
                        &mut out_lanes,
                        &mut out_skip,
                    ) {
                        if self.allow_subpiece_terminator {
                            let lane_index = self.description.get_boundary(byte_pos);
                            if lane_index < 0 || lane_index >= self.description.get_num_lanes() {
                                return false;
                            }
                            if self.description.get_size(lane_index) <= out_size {
                                return false;
                            }
                            let rop = self.manager.new_preexisting_op(2, OpCode::Subpiece, op);
                            self.manager
                                .op_set_input(rop, (rvn as i64 + (lane_index - skip_lanes) as i64) as usize, 0);
                            let zero = self.manager.new_constant(4, 0, 0);
                            self.manager.op_set_input(rop, zero, 1);
                            continue;
                        }
                        return false;
                    }
                    if out_lanes == 1 {
                        let rop = self.manager.new_preexisting_op(1, OpCode::Copy, op);
                        self.manager
                            .op_set_input(rop, (rvn as i64 + (out_skip - skip_lanes) as i64) as usize, 0);
                    } else if self.set_replacement(outvn, out_lanes, out_skip, data, glb).is_none() {
                        return false;
                    }
                }
                OpCode::Piece => {
                    let outvn = outvn_opt.expect("piece without output");
                    let mut out_lanes = 0;
                    let mut out_skip = 0;
                    let byte_pos = if data.op(op).get_in(0) == origvn {
                        data.vn(data.op(op).get_in(1)).get_size()
                    } else {
                        0
                    };
                    let out_size = data.vn(outvn).get_size();
                    if !self.description.extension(
                        num_lanes,
                        skip_lanes,
                        byte_pos,
                        out_size,
                        &mut out_lanes,
                        &mut out_skip,
                    ) {
                        return false;
                    }
                    if self.set_replacement(outvn, out_lanes, out_skip, data, glb).is_none() {
                        return false;
                    }
                }
                OpCode::Copy
                | OpCode::IntNegate
                | OpCode::IntAnd
                | OpCode::IntOr
                | OpCode::IntXor
                | OpCode::Multiequal
                | OpCode::Indirect => {
                    let outvn = outvn_opt.expect("op without output");
                    if self.set_replacement(outvn, num_lanes, skip_lanes, data, glb).is_none() {
                        return false;
                    }
                }
                OpCode::IntRight => {
                    if !data.vn(data.op(op).get_in(1)).is_constant() {
                        return false;
                    }
                    let outvn = outvn_opt.expect("shift without output");
                    if self.set_replacement(outvn, num_lanes, skip_lanes, data, glb).is_none() {
                        return false;
                    }
                }
                OpCode::Store => {
                    if data.op(op).get_in(2) != origvn {
                        return false;
                    }
                    if !self.build_store(op, num_lanes, skip_lanes, data, glb) {
                        return false;
                    }
                }
                _ => return false,
            }
        }
        true
    }

    fn trace_backward(
        &mut self,
        rvn: usize,
        num_lanes: i32,
        skip_lanes: i32,
        data: &mut Funcdata,
        glb: &Architecture,
    ) -> bool {
        let original = self
            .manager
            .var(rvn)
            .get_original()
            .expect("placeholder without original varnode");
        let op = match data.vn(original).get_def() {
            None => return true,
            Some(op) => op,
        };

        let opc = data.op(op).code();
        match opc {
            OpCode::IntNegate | OpCode::Copy => {
                let input = data.op(op).get_in(0);
                let in_vars = match self.set_replacement(input, num_lanes, skip_lanes, data, glb) {
                    None => return false,
                    Some(in_vars) => in_vars,
                };
                self.build_unary_op(opc, op, in_vars, rvn, num_lanes);
            }
            OpCode::IntAnd | OpCode::IntOr | OpCode::IntXor => {
                let input0 = data.op(op).get_in(0);
                let in0_vars = match self.set_replacement(input0, num_lanes, skip_lanes, data, glb) {
                    None => return false,
                    Some(in0_vars) => in0_vars,
                };
                let input1 = data.op(op).get_in(1);
                let in1_vars = match self.set_replacement(input1, num_lanes, skip_lanes, data, glb) {
                    None => return false,
                    Some(in1_vars) => in1_vars,
                };
                self.build_binary_op(opc, op, in0_vars, in1_vars, rvn, num_lanes);
            }
            OpCode::Multiequal => {
                if !self.build_multiequal(op, rvn, num_lanes, skip_lanes, data, glb) {
                    return false;
                }
            }
            OpCode::Indirect => {
                if !self.build_indirect(op, rvn, num_lanes, skip_lanes, data, glb) {
                    return false;
                }
            }
            OpCode::Subpiece => {
                let in_vn = data.op(op).get_in(0);
                let byte_pos = data.vn(data.op(op).get_in(1)).get_offset() as i32;
                let mut in_lanes = 0;
                let mut in_skip = 0;
                let in_size = data.vn(in_vn).get_size();
                if !self
                    .description
                    .extension(num_lanes, skip_lanes, byte_pos, in_size, &mut in_lanes, &mut in_skip)
                {
                    return false;
                }
                let in_vars = match self.set_replacement(in_vn, in_lanes, in_skip, data, glb) {
                    None => return false,
                    Some(in_vars) => in_vars,
                };
                self.build_unary_op(
                    OpCode::Copy,
                    op,
                    (in_vars as i64 + (skip_lanes - in_skip) as i64) as usize,
                    rvn,
                    num_lanes,
                );
            }
            OpCode::Piece => {
                if !self.build_piece(op, rvn, num_lanes, skip_lanes, data, glb) {
                    return false;
                }
            }
            OpCode::Load => {
                if !self.build_load(op, rvn, num_lanes, skip_lanes, data, glb) {
                    return false;
                }
            }
            OpCode::IntRight => {
                if !self.build_right_shift(op, rvn, num_lanes, skip_lanes, data, glb) {
                    return false;
                }
            }
            OpCode::IntLeft => {
                if !self.build_left_shift(op, rvn, num_lanes, skip_lanes, data, glb) {
                    return false;
                }
            }
            OpCode::IntZext => {
                if !self.build_zext(op, rvn, num_lanes, skip_lanes, data, glb) {
                    return false;
                }
            }
            _ => return false,
        }
        true
    }

    fn process_next_work(&mut self, data: &mut Funcdata, glb: &Architecture) -> bool {
        let node = self.work_list.pop().expect("empty lane work list");

        if !self.trace_backward(node.lanes, node.num_lanes, node.skip_lanes, data, glb) {
            return false;
        }
        self.trace_forward(node.lanes, node.num_lanes, node.skip_lanes, data, glb)
    }

    pub fn do_trace(&mut self, data: &mut Funcdata, glb: &Architecture) -> bool {
        if self.work_list.is_empty() {
            return false;
        }
        let mut retval = true;
        while !self.work_list.is_empty() {
            if !self.process_next_work(data, glb) {
                retval = false;
                break;
            }
        }

        self.manager.clear_varnode_marks(data);
        retval
    }
}
