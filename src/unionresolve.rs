use std::cmp::Ordering;
use std::collections::BTreeSet;

use crate::address::{Address, bit_transitions, sign_extend};
use crate::architecture::Architecture;
use crate::error::Result;
use crate::float::FloatClass;
use crate::fspec::FuncProto;
use crate::funcdata::Funcdata;
use crate::op::OpId;
use crate::opcodes::OpCode;
use crate::typeop::TypeOpSubpiece;
use crate::types::{Datatype, TypeFactory, TypeId, TypeMetatype, types_of, types_of_mut};
use crate::varnode::VarnodeId;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ResolvedUnion {
    pub(crate) resolve: TypeId,
    pub(crate) base_type: TypeId,
    pub(crate) field_num: i32,
    pub(crate) lock: bool,
}

impl ResolvedUnion {
    pub fn new(unres_type: TypeId, types: &TypeFactory) -> ResolvedUnion {
        let dt = types.get(unres_type);
        let mut base_type = unres_type;
        if dt.get_metatype() == TypeMetatype::Ptr {
            base_type = dt.get_ptr_to();
        } else if dt.get_metatype() == TypeMetatype::PartialUnion {
            base_type = dt.get_parent_union();
        }
        ResolvedUnion {
            resolve: unres_type,
            base_type,
            field_num: -1,
            lock: false,
        }
    }

    pub fn new_field(unres_type: TypeId, fld_num: i32, types: &mut TypeFactory) -> Result<ResolvedUnion> {
        let dt = types.get(unres_type);
        let meta = dt.get_metatype();
        let base_type;
        let resolve;
        if meta == TypeMetatype::PartialUnion {
            let parent_union = dt.get_parent_union();
            base_type = parent_union;
            if fld_num < 0 {
                resolve = dt.get_stripped().expect("partial union without stripped data-type");
            } else {
                let field_type = types.get(parent_union).get_field(fld_num).tp;
                let offset = dt.get_offset();
                let size = dt.get_size();
                let stripped = dt.get_stripped().expect("partial union without stripped data-type");
                resolve = match types.get_exact_piece(field_type, offset, size)? {
                    Some(piece) => piece,
                    None => stripped,
                };
            }
        } else if meta == TypeMetatype::Ptr {
            let ptrto = dt.get_ptr_to();
            base_type = ptrto;
            if fld_num < 0 {
                resolve = unres_type;
            } else {
                let size = dt.get_size();
                let wordsize = dt.get_word_size();
                let field = types
                    .get(ptrto)
                    .get_depend(fld_num, types)
                    .expect("union field data-type");
                resolve = types.get_type_pointer_strip_array(size, field, wordsize)?;
            }
        } else {
            base_type = unres_type;
            if fld_num < 0 {
                resolve = unres_type;
            } else {
                resolve = dt.get_depend(fld_num, types).expect("union field data-type");
            }
        }
        Ok(ResolvedUnion {
            resolve,
            base_type,
            field_num: fld_num,
            lock: false,
        })
    }

    pub fn new_resolved(op: &ResolvedUnion, res: TypeId) -> ResolvedUnion {
        ResolvedUnion {
            resolve: res,
            base_type: op.base_type,
            field_num: op.field_num,
            lock: op.lock,
        }
    }

    pub fn get_datatype(&self) -> TypeId {
        self.resolve
    }

    pub fn get_base(&self) -> TypeId {
        self.base_type
    }

    pub fn get_field_num(&self) -> i32 {
        self.field_num
    }

    pub fn is_locked(&self) -> bool {
        self.lock
    }

    pub fn update(&mut self, op: &ResolvedUnion) -> bool {
        if self.lock && self.field_num != op.field_num {
            return false;
        }
        if self.field_num == op.field_num && self.resolve == op.resolve {
            return false;
        }
        self.field_num = op.field_num;
        self.resolve = op.resolve;
        true
    }

    pub fn set_resolve(&mut self, res: TypeId) {
        self.resolve = res;
    }

    pub fn set_lock(&mut self, val: bool) {
        self.lock = val;
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ResolveEdge {
    type_id: u64,
    op_time: u32,
    encoding: i32,
}

impl ResolveEdge {
    fn stripped_type_id(unres_type: TypeId, types: &TypeFactory) -> u64 {
        let dt = types.get(unres_type);
        if dt.get_metatype() == TypeMetatype::Ptr {
            types.get(dt.get_ptr_to()).get_id()
        } else if dt.get_metatype() == TypeMetatype::PartialUnion {
            types.get(dt.get_parent_union()).get_id()
        } else {
            dt.get_id()
        }
    }

    pub fn new(unres_type: TypeId, op: OpId, slot: i32, data: &Funcdata, types: &TypeFactory) -> ResolveEdge {
        let mut encoding = slot;
        if types.get(unres_type).get_metatype() == TypeMetatype::Ptr {
            encoding += 0x1000;
        }
        ResolveEdge {
            type_id: ResolveEdge::stripped_type_id(unres_type, types),
            op_time: data.op(op).get_time(),
            encoding,
        }
    }

    pub fn new_address(unres_type: TypeId, addr: &Address, _slot: i32, types: &TypeFactory) -> ResolveEdge {
        ResolveEdge {
            type_id: ResolveEdge::stripped_type_id(unres_type, types),
            op_time: addr.get_offset() as u32,
            encoding: 0x2000,
        }
    }
}

impl Ord for ResolveEdge {
    fn cmp(&self, op2: &ResolveEdge) -> Ordering {
        if self.type_id != op2.type_id {
            return self.type_id.cmp(&op2.type_id);
        }
        if self.encoding != op2.encoding {
            return self.encoding.cmp(&op2.encoding);
        }
        self.op_time.cmp(&op2.op_time)
    }
}

impl PartialOrd for ResolveEdge {
    fn partial_cmp(&self, op2: &ResolveEdge) -> Option<Ordering> {
        Some(self.cmp(op2))
    }
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum TrialDirection {
    FitDown,
    FitUp,
}

#[derive(Clone, Debug)]
pub struct Trial {
    pub vn: VarnodeId,
    pub op: Option<OpId>,
    pub inslot: i32,
    pub direction: TrialDirection,
    pub max_length: i32,
    pub fit_type: TypeId,
    pub score_index: i32,
}

impl Trial {
    pub fn new_down(op: OpId, slot: i32, ct: TypeId, index: i32, max: i32, data: &Funcdata) -> Trial {
        Trial {
            vn: data.op(op).get_in(slot),
            op: Some(op),
            inslot: slot,
            direction: TrialDirection::FitDown,
            fit_type: ct,
            score_index: index,
            max_length: max,
        }
    }

    pub fn new_up(vn: VarnodeId, ct: TypeId, index: i32, max: i32) -> Trial {
        Trial {
            vn,
            op: None,
            inslot: -1,
            direction: TrialDirection::FitUp,
            fit_type: ct,
            score_index: index,
            max_length: max,
        }
    }
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct VisitMark {
    vn: VarnodeId,
    index: i32,
}

impl VisitMark {
    pub fn new(vn: VarnodeId, index: i32) -> VisitMark {
        VisitMark { vn, index }
    }
}

fn is_aggregate_meta(meta: TypeMetatype) -> bool {
    meta == TypeMetatype::Array
        || meta == TypeMetatype::Struct
        || meta == TypeMetatype::Union
        || meta == TypeMetatype::Code
        || meta == TypeMetatype::Float
}

enum ProtoSource {
    Call(OpId),
    Function,
}

pub struct ScoreUnionFields {
    scores: Vec<i32>,
    fields: Vec<Option<TypeId>>,
    visited: BTreeSet<VisitMark>,
    trial_current: Vec<Trial>,
    trial_next: Vec<Trial>,
    result: ResolvedUnion,
    trial_count: i32,
}

impl ScoreUnionFields {
    pub const MAX_PASSES: i32 = 6;
    pub const THRESHOLD: i32 = 256;
    pub const MAX_TRIALS: i32 = 1024;

    fn with_result(result: ResolvedUnion) -> ScoreUnionFields {
        ScoreUnionFields {
            scores: Vec::new(),
            fields: Vec::new(),
            visited: BTreeSet::new(),
            trial_current: Vec::new(),
            trial_next: Vec::new(),
            result,
            trial_count: 0,
        }
    }

    fn test_array_arithmetic(&self, op: OpId, inslot: i32, data: &Funcdata, types: &TypeFactory) -> bool {
        let base_size = types.get(self.result.base_type).get_size() as i64 as u64;
        let op_data = data.op(op);
        if op_data.code() == OpCode::IntAdd {
            let vn = data.vn(op_data.get_in(1 - inslot));
            if vn.is_constant() {
                if vn.get_offset() >= base_size {
                    return true;
                }
            } else if vn.is_written() {
                let mult_op = data.op(vn.get_def().expect("written varnode without definition"));
                if mult_op.code() == OpCode::IntMult {
                    let vn2 = data.vn(mult_op.get_in(1));
                    if vn2.is_constant() && vn2.get_offset() >= base_size {
                        return true;
                    }
                }
            }
        } else if op_data.code() == OpCode::Ptradd {
            let vn = data.vn(op_data.get_in(2));
            if vn.get_offset() >= base_size {
                return true;
            }
        }
        false
    }

    fn test_simple_cases(&self, op: OpId, inslot: i32, parent: TypeId, data: &Funcdata, types: &TypeFactory) -> bool {
        if data.op(op).is_marker() && inslot < 0 {
            return true;
        }
        if types.get(parent).get_metatype() == TypeMetatype::Ptr {
            if inslot < 0 {
                return true;
            }
            if self.test_array_arithmetic(op, inslot, data, types) {
                return true;
            }
        }
        false
    }

    fn score_locked_type(ct: TypeId, lock_type: TypeId, types: &TypeFactory) -> i32 {
        let mut score = 0;
        let mut ct = ct;
        let mut lock_type = lock_type;
        if lock_type == ct {
            score += 5;
        }
        while types.get(ct).get_metatype() == TypeMetatype::Ptr {
            if types.get(lock_type).get_metatype() != TypeMetatype::Ptr {
                break;
            }
            score += 5;
            ct = types.get(ct).get_ptr_to();
            lock_type = types.get(lock_type).get_ptr_to();
        }
        let ct_meta = types.get(ct).get_metatype();
        let vn_meta = types.get(lock_type).get_metatype();
        if ct_meta == vn_meta {
            if ct_meta == TypeMetatype::Struct
                || ct_meta == TypeMetatype::Union
                || ct_meta == TypeMetatype::Array
                || ct_meta == TypeMetatype::Code
            {
                score += 10;
            } else {
                score += 3;
            }
        } else {
            if (ct_meta == TypeMetatype::Int && vn_meta == TypeMetatype::Uint)
                || (ct_meta == TypeMetatype::Uint && vn_meta == TypeMetatype::Int)
            {
                score -= 1;
            } else {
                score -= 5;
            }
            if types.get(ct).get_size() != types.get(lock_type).get_size() {
                score -= 2;
            }
        }
        score
    }

    fn proto_for<'a>(source: &ProtoSource, data: &'a mut Funcdata) -> Option<&'a mut FuncProto> {
        match source {
            ProtoSource::Call(op) => {
                let fc = data.get_call_specs_op(*op)?;
                Some(&mut **data.call_spec_mut(fc))
            }
            ProtoSource::Function => Some(data.get_func_proto_mut()),
        }
    }

    fn score_parameter(ct: TypeId, proto: Option<&mut FuncProto>, param_slot: i32, glb: &Architecture) -> i32 {
        if let Some(proto) = proto
            && proto.is_input_locked(glb)
            && proto.num_params(glb) > param_slot
        {
            let param_type = proto
                .get_param(param_slot, glb)
                .expect("prototype parameter")
                .get_type(glb);
            return ScoreUnionFields::score_locked_type(ct, param_type, types_of(glb));
        }
        let meta = types_of(glb).get(ct).get_metatype();
        if meta == TypeMetatype::Array
            || meta == TypeMetatype::Struct
            || meta == TypeMetatype::Union
            || meta == TypeMetatype::Code
        {
            return -1;
        }
        0
    }

    fn score_return_type(ct: TypeId, proto: Option<&mut FuncProto>, glb: &Architecture) -> i32 {
        if let Some(proto) = proto
            && proto.is_output_locked(glb)
        {
            let output_type = proto.get_output_type(glb);
            return ScoreUnionFields::score_locked_type(ct, output_type, types_of(glb));
        }
        let meta = types_of(glb).get(ct).get_metatype();
        if meta == TypeMetatype::Array
            || meta == TypeMetatype::Struct
            || meta == TypeMetatype::Union
            || meta == TypeMetatype::Code
        {
            return -1;
        }
        0
    }

    fn deref_pointer(
        &mut self,
        trial: &Trial,
        vn: VarnodeId,
        score: &mut i32,
        data: &Funcdata,
        glb: &mut Architecture,
    ) -> Result<Option<TypeId>> {
        *score = 0;
        let vn_size = data.vn(vn).get_size();
        let types = types_of(glb);
        if types.get(trial.fit_type).get_metatype() == TypeMetatype::Ptr {
            let ptrto = types.get(trial.fit_type).get_ptr_to();
            let mut sub_type = Some(ptrto);
            while let Some(sub) = sub_type {
                if types.get(sub).get_size() <= vn_size {
                    break;
                }
                let mut newoff = 0i64;
                sub_type = types.get(sub).get_sub_type(0, &mut newoff, glb);
            }
            if let Some(sub) = sub_type
                && types.get(sub).get_size() == vn_size
            {
                *score = 10;
                return Ok(Some(sub));
            }
            let ptrto_size = types.get(ptrto).get_size();
            if trial.max_length != 0 && (vn_size % ptrto_size) == 0 {
                *score = -4;
                return Ok(Some(types_of_mut(glb).get_type_array(vn_size / ptrto_size, ptrto)?));
            }
            *score = -5;
        } else {
            *score = -10;
        }
        Ok(None)
    }

    fn new_trials_down(
        &mut self,
        vn: VarnodeId,
        ct: TypeId,
        score_index: i32,
        max: i32,
        data: &Funcdata,
        glb: &Architecture,
    ) {
        let mark = VisitMark::new(vn, score_index);
        if !self.visited.insert(mark) {
            return;
        }
        if data.vn(vn).is_type_lock() {
            let lock_type = data.vn_get_type_def_facing(vn, glb);
            let types = types_of(glb);
            if !types.get(lock_type).needs_resolution() {
                self.scores[score_index as usize] += ScoreUnionFields::score_locked_type(ct, lock_type, types);
                return;
            }
        }
        for op in data.vn(vn).descend().iter() {
            let slot = data.op(*op).get_slot(vn);
            self.trial_next
                .push(Trial::new_down(*op, slot, ct, score_index, max, data));
        }
    }

    fn new_trials(
        &mut self,
        op: OpId,
        slot: i32,
        ct: TypeId,
        score_index: i32,
        max: i32,
        data: &Funcdata,
        glb: &Architecture,
    ) {
        let vn = data.op(op).get_in(slot);
        let mark = VisitMark::new(vn, score_index);
        if !self.visited.insert(mark) {
            return;
        }
        if data.vn(vn).is_type_lock() {
            let lock_type = data.vn_get_type_read_facing(vn, op, glb);
            let types = types_of(glb);
            if !types.get(lock_type).needs_resolution() {
                self.scores[score_index as usize] += ScoreUnionFields::score_locked_type(ct, lock_type, types);
                return;
            }
        }
        self.trial_next.push(Trial::new_up(vn, ct, score_index, max));
        for read_op in data.vn(vn).descend().iter() {
            let inslot = data.op(*read_op).get_slot(vn);
            if *read_op == op && inslot == slot {
                continue;
            }
            self.trial_next
                .push(Trial::new_down(*read_op, inslot, ct, score_index, max, data));
        }
    }

    fn score_trial_down(
        &mut self,
        trial: &Trial,
        last_level: bool,
        data: &mut Funcdata,
        glb: &mut Architecture,
    ) -> Result<()> {
        if trial.direction == TrialDirection::FitUp {
            return Ok(());
        }
        let trial_op = trial.op.expect("downward trial without p-code op");
        let mut res_type: Option<TypeId> = None;
        let mut max_length = 0;
        let fit_dt = types_of(glb).get(trial.fit_type);
        let meta = fit_dt.get_metatype();
        let mut score = 0;
        match data.op(trial_op).code() {
            OpCode::Copy | OpCode::Multiequal | OpCode::Indirect => {
                res_type = Some(trial.fit_type);
                max_length = trial.max_length;
            }
            OpCode::Load => {
                let out = data.op(trial_op).get_out().expect("LOAD without output");
                res_type = self.deref_pointer(trial, out, &mut score, data, glb)?;
            }
            OpCode::Store => {
                if trial.inslot == 1 {
                    let value = data.op(trial_op).get_in(2);
                    let ptrto = self.deref_pointer(trial, value, &mut score, data, glb)?;
                    if let Some(ptrto) = ptrto
                        && !last_level
                    {
                        self.new_trials(trial_op, 2, ptrto, trial.score_index, 0, data, glb);
                    }
                } else if trial.inslot == 2 {
                    if meta == TypeMetatype::Code {
                        score = -5;
                    } else {
                        let store_vn = data.op(trial_op).get_in(1);
                        let store_ptr = data.vn_get_type_read_facing(store_vn, trial_op, glb);
                        let store_dt = types_of(glb).get(store_ptr);
                        if !last_level && store_dt.get_metatype() == TypeMetatype::Ptr {
                            let store_size = store_dt.get_size();
                            let wordsize = store_dt.get_word_size();
                            let fit_size = types_of(glb).get(trial.fit_type).get_size();
                            let ptr =
                                types_of_mut(glb).get_type_pointer_strip_array(store_size, trial.fit_type, wordsize)?;
                            self.new_trials(trial_op, 1, ptr, trial.score_index, fit_size, data, glb);
                        }
                        score = 1;
                    }
                }
            }
            OpCode::Cbranch => {
                score = if meta == TypeMetatype::Bool { 10 } else { -10 };
            }
            OpCode::Branchind => {
                if meta == TypeMetatype::Ptr || is_aggregate_meta(meta) {
                    score = -5;
                } else {
                    score = 1;
                }
            }
            OpCode::Call | OpCode::Callother => {
                if trial.inslot > 0 {
                    let proto = ScoreUnionFields::proto_for(&ProtoSource::Call(trial_op), data);
                    score = ScoreUnionFields::score_parameter(trial.fit_type, proto, trial.inslot - 1, glb);
                }
            }
            OpCode::Callind => {
                if trial.inslot == 0 {
                    if meta == TypeMetatype::Ptr {
                        let types = types_of(glb);
                        let ptrto = types.get(trial.fit_type).get_ptr_to();
                        if types.get(ptrto).get_metatype() == TypeMetatype::Code {
                            score = 10;
                        } else {
                            score = -10;
                        }
                    }
                } else {
                    let proto = ScoreUnionFields::proto_for(&ProtoSource::Call(trial_op), data);
                    score = ScoreUnionFields::score_parameter(trial.fit_type, proto, trial.inslot - 1, glb);
                }
            }
            OpCode::Return => {
                let proto = ScoreUnionFields::proto_for(&ProtoSource::Function, data);
                score = ScoreUnionFields::score_return_type(trial.fit_type, proto, glb);
            }
            OpCode::IntEqual | OpCode::IntNotequal => {
                score = if is_aggregate_meta(meta) { -1 } else { 1 };
            }
            OpCode::IntSless | OpCode::IntSlessequal | OpCode::IntScarry | OpCode::IntSborrow => {
                if is_aggregate_meta(meta) {
                    score = -5;
                } else if meta == TypeMetatype::Ptr
                    || meta == TypeMetatype::Unknown
                    || meta == TypeMetatype::Uint
                    || meta == TypeMetatype::Bool
                {
                    score = -1;
                } else {
                    score = 5;
                }
            }
            OpCode::IntLess | OpCode::IntLessequal | OpCode::IntCarry => {
                if is_aggregate_meta(meta) {
                    score = -5;
                } else if meta == TypeMetatype::Ptr || meta == TypeMetatype::Unknown || meta == TypeMetatype::Uint {
                    score = 5;
                } else if meta == TypeMetatype::Int {
                    score = -5;
                }
            }
            OpCode::IntZext => {
                if meta == TypeMetatype::Uint {
                    score = 2;
                } else if meta == TypeMetatype::Int || meta == TypeMetatype::Bool {
                    score = 1;
                } else if meta == TypeMetatype::Unknown {
                    score = 0;
                } else {
                    score = -5;
                }
            }
            OpCode::IntSext => {
                if meta == TypeMetatype::Int {
                    score = 2;
                } else if meta == TypeMetatype::Uint || meta == TypeMetatype::Bool {
                    score = 1;
                } else if meta == TypeMetatype::Unknown {
                    score = 0;
                } else {
                    score = -5;
                }
            }
            OpCode::IntAdd | OpCode::IntSub | OpCode::Ptrsub => {
                if meta == TypeMetatype::Ptr {
                    if trial.inslot >= 0 {
                        let vn = data.op(trial_op).get_in(1 - trial.inslot);
                        if data.vn(vn).is_constant() {
                            let mut base_type = Some(trial.fit_type);
                            let vn_data = data.vn(vn);
                            let mut off = sign_extend(vn_data.get_offset() as i64, vn_data.get_size() * 8 - 1);
                            if trial.max_length != 0 {
                                if off < 0 || off >= trial.max_length as i64 {
                                    base_type = None;
                                    score = -1;
                                } else {
                                    max_length = trial.max_length;
                                }
                            }
                            while off != 0 {
                                let Some(current) = base_type else {
                                    break;
                                };
                                let mut par_off = 0i64;
                                let mut par = None;
                                base_type = Datatype::down_chain(current, &mut off, &mut par, &mut par_off, true, glb)?;
                            }
                            if let Some(base) = base_type {
                                res_type = Some(base);
                                let types = types_of(glb);
                                max_length = types.get(types.get(base).get_ptr_to()).get_size();
                                score = 5;
                            }
                        } else if trial.max_length != 0 {
                            score = 1;
                            let mut el_size = 1;
                            let vn_data = data.vn(vn);
                            if vn_data.is_written() {
                                let mult_op = data.op(vn_data.get_def().expect("written varnode without definition"));
                                if mult_op.code() == OpCode::IntMult {
                                    let mult_vn = data.vn(mult_op.get_in(1));
                                    if mult_vn.is_constant() {
                                        el_size = mult_vn.get_offset() as i32;
                                    }
                                }
                            }
                            let types = types_of(glb);
                            let base_ptrto = types.get(trial.fit_type).get_ptr_to();
                            if types.get(base_ptrto).get_align_size() == el_size {
                                if el_size == trial.max_length {
                                    score = 2;
                                } else {
                                    score = 5;
                                }
                                res_type = Some(trial.fit_type);
                                max_length = trial.max_length;
                            }
                        } else {
                            score = 5;
                        }
                    }
                } else if meta == TypeMetatype::Int || meta == TypeMetatype::Uint || meta == TypeMetatype::Unknown {
                    score = 1;
                    res_type = Some(trial.fit_type);
                } else if meta == TypeMetatype::Bool {
                    score = -3;
                } else {
                    score = -5;
                }
            }
            OpCode::Int2comp => {
                if is_aggregate_meta(meta) {
                    score = -5;
                } else if meta == TypeMetatype::Ptr || meta == TypeMetatype::Unknown || meta == TypeMetatype::Bool {
                    score = -1;
                } else if meta == TypeMetatype::Int {
                    score = 5;
                }
            }
            OpCode::IntNegate
            | OpCode::IntXor
            | OpCode::IntAnd
            | OpCode::IntOr
            | OpCode::Popcount
            | OpCode::Lzcount => {
                if is_aggregate_meta(meta) {
                    score = -5;
                } else if meta == TypeMetatype::Ptr || meta == TypeMetatype::Bool {
                    score = -1;
                } else if meta == TypeMetatype::Uint || meta == TypeMetatype::Unknown {
                    score = 2;
                }
            }
            OpCode::IntLeft | OpCode::IntRight => {
                if trial.inslot == 0 {
                    if is_aggregate_meta(meta) {
                        score = -5;
                    } else if meta == TypeMetatype::Ptr || meta == TypeMetatype::Bool {
                        score = -1;
                    } else if meta == TypeMetatype::Uint || meta == TypeMetatype::Unknown {
                        score = 2;
                    }
                } else if is_aggregate_meta(meta) || meta == TypeMetatype::Ptr {
                    score = -5;
                } else {
                    score = 1;
                }
            }
            OpCode::IntSright => {
                if trial.inslot == 0 {
                    if is_aggregate_meta(meta) {
                        score = -5;
                    } else if meta == TypeMetatype::Ptr
                        || meta == TypeMetatype::Bool
                        || meta == TypeMetatype::Uint
                        || meta == TypeMetatype::Unknown
                    {
                        score = -1;
                    } else {
                        score = 2;
                    }
                } else if is_aggregate_meta(meta) || meta == TypeMetatype::Ptr {
                    score = -5;
                } else {
                    score = 1;
                }
            }
            OpCode::IntMult => {
                if is_aggregate_meta(meta) {
                    score = -10;
                } else if meta == TypeMetatype::Ptr || meta == TypeMetatype::Bool {
                    score = -2;
                } else {
                    score = 5;
                }
            }
            OpCode::IntDiv | OpCode::IntRem => {
                if is_aggregate_meta(meta) {
                    score = -10;
                } else if meta == TypeMetatype::Ptr || meta == TypeMetatype::Bool {
                    score = -2;
                } else if meta == TypeMetatype::Uint || meta == TypeMetatype::Unknown {
                    score = 5;
                }
            }
            OpCode::IntSdiv | OpCode::IntSrem => {
                if is_aggregate_meta(meta) {
                    score = -10;
                } else if meta == TypeMetatype::Ptr || meta == TypeMetatype::Bool {
                    score = -2;
                } else if meta == TypeMetatype::Int {
                    score = 5;
                }
            }
            OpCode::BoolNegate | OpCode::BoolAnd | OpCode::BoolXor | OpCode::BoolOr => {
                if meta == TypeMetatype::Bool {
                    score = 10;
                } else if meta == TypeMetatype::Int || meta == TypeMetatype::Uint || meta == TypeMetatype::Unknown {
                    score = -1;
                } else {
                    score = -10;
                }
            }
            OpCode::FloatEqual
            | OpCode::FloatNotequal
            | OpCode::FloatLess
            | OpCode::FloatLessequal
            | OpCode::FloatNan
            | OpCode::FloatAdd
            | OpCode::FloatDiv
            | OpCode::FloatMult
            | OpCode::FloatSub
            | OpCode::FloatNeg
            | OpCode::FloatAbs
            | OpCode::FloatSqrt
            | OpCode::FloatFloat2float
            | OpCode::FloatTrunc
            | OpCode::FloatCeil
            | OpCode::FloatFloor
            | OpCode::FloatRound => {
                score = if meta == TypeMetatype::Float { 10 } else { -10 };
            }
            OpCode::FloatInt2float => {
                if is_aggregate_meta(meta) {
                    score = -10;
                } else if meta == TypeMetatype::Ptr {
                    score = -5;
                } else if meta == TypeMetatype::Int {
                    score = 5;
                }
            }
            OpCode::Piece => {
                if is_aggregate_meta(meta) {
                    score = -5;
                }
            }
            OpCode::Subpiece => {
                let offset = TypeOpSubpiece::compute_byte_offset_for_composite(trial_op, data);
                let out = data.op(trial_op).get_out().expect("SUBPIECE without output");
                res_type = self.score_truncation(trial.fit_type, out, offset, trial.score_index, data, glb);
            }
            OpCode::Ptradd => {
                if meta == TypeMetatype::Ptr {
                    if trial.inslot == 0 {
                        let types = types_of(glb);
                        let ptrto = types.get(trial.fit_type).get_ptr_to();
                        let elsize_vn = data.op(trial_op).get_in(2);
                        if types.get(ptrto).get_align_size() as i64 as u64 == data.vn(elsize_vn).get_offset() {
                            score = 10;
                            res_type = Some(trial.fit_type);
                        }
                    } else {
                        score = -10;
                    }
                } else if is_aggregate_meta(meta) {
                    score = -5;
                } else {
                    score = 1;
                }
            }
            OpCode::Segmentop => {
                if trial.inslot == 2 {
                    if meta == TypeMetatype::Ptr {
                        score = 5;
                    } else if is_aggregate_meta(meta) {
                        score = -5;
                    } else {
                        score = -1;
                    }
                } else if is_aggregate_meta(meta) || meta == TypeMetatype::Ptr {
                    score = -2;
                }
            }
            _ => {
                score = -10;
            }
        }
        self.scores[trial.score_index as usize] += score;
        if let Some(res_type) = res_type
            && !last_level
        {
            let out = data.op(trial_op).get_out().expect("p-code op without output");
            self.new_trials_down(out, res_type, trial.score_index, max_length, data, glb);
        }
        Ok(())
    }

    fn score_trial_up(
        &mut self,
        trial: &Trial,
        last_level: bool,
        data: &mut Funcdata,
        glb: &mut Architecture,
    ) -> Result<()> {
        if trial.direction == TrialDirection::FitDown {
            return Ok(());
        }
        let mut score = 0;
        if !data.vn(trial.vn).is_written() {
            if data.vn(trial.vn).is_constant() {
                self.score_constant_fit(trial, data, glb);
            }
            return Ok(());
        }
        let mut res_type: Option<TypeId> = None;
        let mut max_length = 0;
        let mut newslot = 0;
        let fit_dt = types_of(glb).get(trial.fit_type);
        let meta = fit_dt.get_metatype();
        let fit_size = fit_dt.get_size();
        let def = data.vn(trial.vn).get_def().expect("written varnode without definition");
        match data.op(def).code() {
            OpCode::Copy | OpCode::Multiequal | OpCode::Indirect => {
                res_type = Some(trial.fit_type);
                max_length = trial.max_length;
                newslot = 0;
            }
            OpCode::Load => {
                let ptr_size = data.vn(data.op(def).get_in(1)).get_size();
                res_type = Some(types_of_mut(glb).get_type_pointer_strip_array(ptr_size, trial.fit_type, 1)?);
                max_length = fit_size;
                newslot = 1;
            }
            OpCode::Call | OpCode::Callother | OpCode::Callind => {
                let proto = ScoreUnionFields::proto_for(&ProtoSource::Call(def), data);
                score = ScoreUnionFields::score_return_type(trial.fit_type, proto, glb);
            }
            OpCode::IntEqual
            | OpCode::IntNotequal
            | OpCode::IntSless
            | OpCode::IntSlessequal
            | OpCode::IntScarry
            | OpCode::IntSborrow
            | OpCode::IntLess
            | OpCode::IntLessequal
            | OpCode::IntCarry
            | OpCode::BoolNegate
            | OpCode::BoolAnd
            | OpCode::BoolXor
            | OpCode::BoolOr
            | OpCode::FloatEqual
            | OpCode::FloatNotequal
            | OpCode::FloatLess
            | OpCode::FloatLessequal
            | OpCode::FloatNan => {
                if meta == TypeMetatype::Bool {
                    score = 10;
                } else if fit_size == 1 {
                    score = 1;
                } else {
                    score = -10;
                }
            }
            OpCode::IntAdd | OpCode::IntSub | OpCode::Ptrsub => {
                if meta == TypeMetatype::Ptr {
                    score = 5;
                    let in1 = data.vn(data.op(def).get_in(1));
                    if trial.max_length == 0 && in1.is_constant() {
                        let types = types_of(glb);
                        let ptrto = types.get(trial.fit_type).get_ptr_to();
                        if types.get(ptrto).get_align_size() == in1.get_offset() as i32 {
                            score += 1;
                        }
                    }
                } else if meta == TypeMetatype::Int || meta == TypeMetatype::Uint {
                    score = 5;
                } else if is_aggregate_meta(meta) {
                    score = -5;
                } else {
                    score = 1;
                }
            }
            OpCode::Int2comp => {
                if is_aggregate_meta(meta) {
                    score = -5;
                } else if meta == TypeMetatype::Ptr || meta == TypeMetatype::Unknown || meta == TypeMetatype::Bool {
                    score = -1;
                } else if meta == TypeMetatype::Int {
                    score = 5;
                }
            }
            OpCode::IntNegate
            | OpCode::IntXor
            | OpCode::IntAnd
            | OpCode::IntOr
            | OpCode::Popcount
            | OpCode::Lzcount => {
                if is_aggregate_meta(meta) {
                    score = -5;
                } else if meta == TypeMetatype::Ptr || meta == TypeMetatype::Bool {
                    score = -1;
                } else if meta == TypeMetatype::Uint || meta == TypeMetatype::Unknown {
                    score = 2;
                }
            }
            OpCode::IntLeft | OpCode::IntRight => {
                if is_aggregate_meta(meta) {
                    score = -5;
                } else if meta == TypeMetatype::Ptr || meta == TypeMetatype::Bool {
                    score = -1;
                } else if meta == TypeMetatype::Uint || meta == TypeMetatype::Unknown {
                    score = 2;
                }
            }
            OpCode::IntSright => {
                if is_aggregate_meta(meta) {
                    score = -5;
                } else if meta == TypeMetatype::Ptr
                    || meta == TypeMetatype::Bool
                    || meta == TypeMetatype::Uint
                    || meta == TypeMetatype::Unknown
                {
                    score = -1;
                } else {
                    score = 2;
                }
            }
            OpCode::IntMult => {
                if is_aggregate_meta(meta) {
                    score = -10;
                } else if meta == TypeMetatype::Ptr || meta == TypeMetatype::Bool {
                    score = -2;
                } else {
                    score = 5;
                }
            }
            OpCode::IntDiv | OpCode::IntRem => {
                if is_aggregate_meta(meta) {
                    score = -10;
                } else if meta == TypeMetatype::Ptr || meta == TypeMetatype::Bool {
                    score = -2;
                } else if meta == TypeMetatype::Uint || meta == TypeMetatype::Unknown {
                    score = 5;
                }
            }
            OpCode::IntSdiv | OpCode::IntSrem => {
                if is_aggregate_meta(meta) {
                    score = -10;
                } else if meta == TypeMetatype::Ptr || meta == TypeMetatype::Bool {
                    score = -2;
                } else if meta == TypeMetatype::Int {
                    score = 5;
                }
            }
            OpCode::FloatAdd
            | OpCode::FloatDiv
            | OpCode::FloatMult
            | OpCode::FloatSub
            | OpCode::FloatNeg
            | OpCode::FloatAbs
            | OpCode::FloatSqrt
            | OpCode::FloatFloat2float
            | OpCode::FloatCeil
            | OpCode::FloatFloor
            | OpCode::FloatRound
            | OpCode::FloatInt2float => {
                score = if meta == TypeMetatype::Float { 10 } else { -10 };
            }
            OpCode::FloatTrunc => {
                score = if meta == TypeMetatype::Int || meta == TypeMetatype::Uint {
                    2
                } else {
                    -2
                };
            }
            OpCode::Piece => {
                if meta == TypeMetatype::Float || meta == TypeMetatype::Bool {
                    score = -5;
                } else if meta == TypeMetatype::Code || meta == TypeMetatype::Ptr {
                    score = -2;
                }
            }
            OpCode::Subpiece => {
                if meta == TypeMetatype::Int || meta == TypeMetatype::Uint || meta == TypeMetatype::Bool {
                    if data.vn(data.op(def).get_in(1)).get_offset() == 0 {
                        score = 3;
                    } else {
                        score = 1;
                    }
                } else {
                    score = -5;
                }
            }
            OpCode::Ptradd => {
                if meta == TypeMetatype::Ptr {
                    let types = types_of(glb);
                    let ptrto = types.get(trial.fit_type).get_ptr_to();
                    if types.get(ptrto).get_align_size() as i64 as u64 == data.vn(data.op(def).get_in(2)).get_offset() {
                        score = 10;
                    } else {
                        score = 2;
                    }
                } else if is_aggregate_meta(meta) {
                    score = -5;
                } else {
                    score = 1;
                }
            }
            _ => {
                score = -10;
            }
        }
        self.scores[trial.score_index as usize] += score;
        if let Some(res_type) = res_type
            && !last_level
        {
            self.new_trials(def, newslot, res_type, trial.score_index, max_length, data, glb);
        }
        Ok(())
    }

    fn score_truncation(
        &mut self,
        ct: TypeId,
        vn: VarnodeId,
        offset: i32,
        score_index: i32,
        data: &Funcdata,
        glb: &Architecture,
    ) -> Option<TypeId> {
        let types = types_of(glb);
        let vn_size = data.vn(vn).get_size();
        let mut score;
        let mut ct = Some(ct);
        let union_dt = types.get(ct.expect("truncated data-type"));
        if union_dt.get_metatype() == TypeMetatype::Union {
            let union_id = ct.expect("truncated data-type");
            ct = None;
            score = -10;
            let num = union_dt.num_depend(types);
            for index in 0..num {
                let field = union_dt.get_field(index);
                if field.offset == offset && types.get(field.tp).get_size() == vn_size {
                    score = 10;
                    if self.result.get_base() == union_id {
                        score += 5;
                    }
                    break;
                }
            }
        } else {
            score = 10;
            let mut cur_off = offset as i64;
            while let Some(cur) = ct {
                let cur_dt = types.get(cur);
                if cur_off == 0 && cur_dt.get_size() == vn_size {
                    break;
                }
                let cur_meta = cur_dt.get_metatype();
                if cur_meta == TypeMetatype::Int || cur_meta == TypeMetatype::Uint {
                    if cur_dt.get_size() as i64 >= vn_size as i64 + cur_off {
                        score = 1;
                        break;
                    }
                } else if cur_meta == TypeMetatype::Array {
                    let el_type = types.get(cur_dt.get_depend(0, types).expect("array element data-type"));
                    if el_type.get_align_size() < vn_size {
                        if (cur_off + vn_size as i64) % el_type.get_align_size() as i64 != 0 {
                            score = -5;
                        } else {
                            score = 1;
                        }
                        break;
                    }
                }
                let mut newoff = cur_off;
                ct = cur_dt.get_sub_type(cur_off, &mut newoff, glb);
                cur_off = newoff;
            }
            if ct.is_none() {
                score = -10;
            }
        }
        self.scores[score_index as usize] += score;
        ct
    }

    fn score_constant_fit(&mut self, trial: &Trial, data: &Funcdata, glb: &Architecture) {
        let vn_data = data.vn(trial.vn);
        let size = vn_data.get_size();
        let val = vn_data.get_offset();
        let meta = types_of(glb).get(trial.fit_type).get_metatype();
        let mut score: i32;
        if meta == TypeMetatype::Bool {
            score = if size == 1 && val < 2 { 2 } else { -2 };
        } else if meta == TypeMetatype::Float {
            score = -1;
            let format = glb.translate.as_deref().and_then(|trans| trans.get_float_format(size));
            if let Some(format) = format {
                let f_class = format.get_class(val);
                if f_class == FloatClass::Zero {
                    score = 2;
                } else if f_class == FloatClass::Normalized {
                    let exp = format.get_exponent(val);
                    if exp < 7 && exp > -4 {
                        score = 2;
                    }
                }
            }
        } else if meta == TypeMetatype::Int || meta == TypeMetatype::Uint || meta == TypeMetatype::Ptr {
            if val == 0 {
                score = 2;
            } else {
                let spc = glb
                    .manager
                    .get_default_data_space()
                    .expect("default data space is not set");
                let mut looks_like_pointer = false;
                if val >= spc.get_pointer_lower_bound()
                    && val <= spc.get_pointer_upper_bound()
                    && bit_transitions(val, size) >= 3
                {
                    looks_like_pointer = true;
                }
                if meta == TypeMetatype::Ptr {
                    score = if looks_like_pointer { 2 } else { -2 };
                } else {
                    score = if looks_like_pointer { 1 } else { 2 };
                }
            }
        } else if meta == TypeMetatype::Array {
            score = 0;
        } else {
            score = -2;
        }
        self.scores[trial.score_index as usize] += score;
    }

    fn run_one_level(&mut self, last_pass: bool, data: &mut Funcdata, glb: &mut Architecture) -> Result<()> {
        let current = std::mem::take(&mut self.trial_current);
        let mut outcome = Ok(());
        for trial in current.iter() {
            self.trial_count += 1;
            if self.trial_count > ScoreUnionFields::MAX_TRIALS {
                break;
            }
            if let Err(err) = self.score_trial_down(trial, last_pass, data, glb) {
                outcome = Err(err);
                break;
            }
            if let Err(err) = self.score_trial_up(trial, last_pass, data, glb) {
                outcome = Err(err);
                break;
            }
        }
        self.trial_current = current;
        outcome
    }

    fn compute_best_index(&mut self) {
        let mut best_score = self.scores[0];
        let mut best_index = 0;
        for index in 1..self.scores.len() {
            if self.scores[index] > best_score {
                best_score = self.scores[index];
                best_index = index;
            }
        }
        self.result.field_num = best_index as i32 - 1;
        self.result.resolve = self.fields[best_index].expect("scored field data-type");
    }

    fn run(&mut self, data: &mut Funcdata, glb: &mut Architecture) -> Result<()> {
        self.trial_count = 0;
        for pass in 0..ScoreUnionFields::MAX_PASSES {
            if self.trial_current.is_empty() {
                break;
            }
            if self.trial_count > ScoreUnionFields::THRESHOLD {
                break;
            }
            if pass + 1 == ScoreUnionFields::MAX_PASSES {
                self.run_one_level(true, data, glb)?;
            } else {
                self.run_one_level(false, data, glb)?;
                std::mem::swap(&mut self.trial_current, &mut self.trial_next);
                self.trial_next.clear();
            }
        }
        Ok(())
    }

    pub fn new(
        data: &mut Funcdata,
        glb: &mut Architecture,
        parent_type: TypeId,
        op: OpId,
        slot: i32,
    ) -> Result<ScoreUnionFields> {
        let mut res = ScoreUnionFields::with_result(ResolvedUnion::new(parent_type, types_of(glb)));
        if res.test_simple_cases(op, slot, parent_type, data, types_of(glb)) {
            return Ok(res);
        }
        let parent_dt = types_of(glb).get(parent_type);
        let word_size = if parent_dt.get_metatype() == TypeMetatype::Ptr {
            parent_dt.get_word_size() as i32
        } else {
            0
        };
        let parent_size = parent_dt.get_size();
        let base_type = res.result.base_type;
        let num_fields = types_of(glb).get(base_type).num_depend(types_of(glb));
        res.scores.resize((num_fields + 1) as usize, 0);
        res.fields.resize((num_fields + 1) as usize, None);
        let vn;
        if slot < 0 {
            vn = data.op(op).get_out().expect("p-code op without output");
            if data.vn(vn).get_size() != parent_size {
                res.scores[0] -= 10;
            } else {
                res.trial_current.push(Trial::new_up(vn, parent_type, 0, 0));
            }
        } else {
            vn = data.op(op).get_in(slot);
            if data.vn(vn).get_size() != parent_size {
                res.scores[0] -= 10;
            } else {
                res.trial_current
                    .push(Trial::new_down(op, slot, parent_type, 0, 0, data));
            }
        }
        res.fields[0] = Some(parent_type);
        let opc = data.op(op).code();
        if word_size == 0
            || opc == OpCode::IntAdd
            || opc == OpCode::Ptradd
            || opc == OpCode::Ptrsub
            || opc == OpCode::Store
            || opc == OpCode::Load
        {
            res.scores[0] -= 1;
        }
        res.visited.insert(VisitMark::new(vn, 0));
        let vn_size = data.vn(vn).get_size();
        for index in 0..num_fields {
            let types = types_of(glb);
            let base_dt = types.get(base_type);
            let mut field_type = base_dt.get_depend(index, types).expect("union field data-type");
            let mut max_length = 0;
            if word_size != 0 {
                let field_dt = types.get(field_type);
                if field_dt.get_metatype() == TypeMetatype::Array {
                    max_length = field_dt.get_size();
                } else if field_dt.get_size() < base_dt.get_size() {
                    max_length = field_dt.get_size();
                }
                field_type =
                    types_of_mut(glb).get_type_pointer_strip_array(parent_size, field_type, word_size as u32)?;
            }
            let score_index = (index + 1) as usize;
            if vn_size != types_of(glb).get(field_type).get_size() {
                res.scores[score_index] -= 10;
            } else if slot < 0 {
                res.trial_current
                    .push(Trial::new_up(vn, field_type, index + 1, max_length));
            } else {
                res.trial_current
                    .push(Trial::new_down(op, slot, field_type, index + 1, max_length, data));
            }
            res.fields[score_index] = Some(field_type);
            res.visited.insert(VisitMark::new(vn, index + 1));
        }
        res.run(data, glb)?;
        res.compute_best_index();
        Ok(res)
    }

    pub fn new_offset(
        data: &mut Funcdata,
        glb: &mut Architecture,
        union_type: TypeId,
        offset: i32,
        op: OpId,
    ) -> Result<ScoreUnionFields> {
        let mut res = ScoreUnionFields::with_result(ResolvedUnion::new(union_type, types_of(glb)));
        let vn = data.op(op).get_out().expect("p-code op without output");
        let vn_size = data.vn(vn).get_size();
        let types = types_of(glb);
        let num_fields = types.get(union_type).num_depend(types);
        res.scores.resize((num_fields + 1) as usize, 0);
        res.fields.resize((num_fields + 1) as usize, None);
        res.fields[0] = Some(union_type);
        res.scores[0] = -10;
        for index in 0..num_fields {
            let types = types_of(glb);
            let union_field = types.get(union_type).get_field(index);
            let field_type = union_field.tp;
            let field_offset = union_field.offset;
            res.fields[(index + 1) as usize] = Some(field_type);
            if types.get(field_type).get_size() != vn_size || field_offset != offset {
                res.scores[(index + 1) as usize] = -10;
                continue;
            }
            res.new_trials_down(vn, field_type, index + 1, 0, data, glb);
        }
        std::mem::swap(&mut res.trial_current, &mut res.trial_next);
        if res.trial_current.len() > 1 {
            res.run(data, glb)?;
        }
        res.compute_best_index();
        if let Some(piece) = types_of_mut(glb).get_exact_piece(res.result.resolve, offset, vn_size)? {
            res.result.resolve = piece;
        }
        Ok(res)
    }

    pub fn new_offset_slot(
        data: &mut Funcdata,
        glb: &mut Architecture,
        union_type: TypeId,
        offset: i32,
        op: OpId,
        slot: i32,
    ) -> Result<ScoreUnionFields> {
        let mut res = ScoreUnionFields::with_result(ResolvedUnion::new(union_type, types_of(glb)));
        if res.test_simple_cases(op, slot, union_type, data, types_of(glb)) {
            return Ok(res);
        }
        let vn = if slot < 0 {
            data.op(op).get_out().expect("p-code op without output")
        } else {
            data.op(op).get_in(slot)
        };
        let vn_size = data.vn(vn).get_size();
        let types = types_of(glb);
        let num_fields = types.get(union_type).num_depend(types);
        res.scores.resize((num_fields + 1) as usize, 0);
        res.fields.resize((num_fields + 1) as usize, None);
        res.fields[0] = Some(union_type);
        res.scores[0] = -10;
        for index in 0..num_fields {
            let types = types_of(glb);
            let union_field = types.get(union_type).get_field(index);
            let field_type = union_field.tp;
            let field_offset = union_field.offset;
            res.fields[(index + 1) as usize] = Some(field_type);
            let ct = res.score_truncation(field_type, vn, offset - field_offset, index + 1, data, glb);
            if let Some(ct) = ct {
                if slot < 0 {
                    res.trial_current.push(Trial::new_up(vn, ct, index + 1, 0));
                } else {
                    res.trial_current
                        .push(Trial::new_down(op, slot, ct, index + 1, 0, data));
                }
                res.visited.insert(VisitMark::new(vn, index + 1));
            }
        }
        if res.trial_current.len() > 1 {
            res.run(data, glb)?;
        }
        res.compute_best_index();
        if let Some(piece) = types_of_mut(glb).get_exact_piece(res.result.resolve, offset, vn_size)? {
            res.result.resolve = piece;
        }
        Ok(res)
    }

    pub fn get_result(&self) -> &ResolvedUnion {
        &self.result
    }
}

#[derive(Clone, Debug)]
pub struct ResolveCacheRecord {
    pub base_type: TypeId,
    pub field_num: i32,
    pub key: i32,
}

impl ResolveCacheRecord {
    pub fn new(key: i32, dt: TypeId, fld_num: i32) -> ResolveCacheRecord {
        ResolveCacheRecord {
            base_type: dt,
            field_num: fld_num,
            key,
        }
    }

    pub fn matches(&self, key: i32, dt: TypeId) -> bool {
        self.key == key && self.base_type == dt
    }
}

#[derive(Clone, Debug, Default)]
pub struct ResolveCache {
    resolve_list: Vec<ResolveCacheRecord>,
}

impl ResolveCache {
    pub fn new() -> ResolveCache {
        ResolveCache {
            resolve_list: Vec::new(),
        }
    }

    pub fn add_resolution(&mut self, key: i32, dt: TypeId, op: OpId, slot: i32, data: &Funcdata, glb: &Architecture) {
        if !types_of(glb).get(dt).needs_resolution() {
            return;
        }
        let Some(res) = data.get_union_resolution(dt, op, slot, glb) else {
            return;
        };
        let parent = res.get_base();
        self.resolve_list
            .push(ResolveCacheRecord::new(key, parent, res.get_field_num()));
    }

    pub fn resolve(&self, key: i32, dt: TypeId, types: &TypeFactory) -> TypeId {
        for record in self.resolve_list.iter() {
            if record.matches(key, dt) {
                if record.field_num < 0 {
                    return dt;
                }
                return types
                    .get(dt)
                    .get_depend(record.field_num, types)
                    .expect("resolved field data-type");
            }
        }
        dt
    }

    pub fn inherit_resolution(
        &self,
        key: i32,
        dt: TypeId,
        off: i32,
        vn: VarnodeId,
        op: OpId,
        slot: i32,
        data: &mut Funcdata,
        glb: &mut Architecture,
    ) -> Result<()> {
        let types = types_of(glb);
        let dt_data = types.get(dt);
        if !dt_data.needs_resolution() {
            return Ok(());
        }
        let mut parent = dt;
        if dt_data.get_metatype() == TypeMetatype::PartialUnion {
            parent = dt_data.get_parent_union();
        } else if dt_data.get_metatype() == TypeMetatype::Ptr {
            parent = dt_data.get_ptr_to();
        }
        for record in self.resolve_list.iter() {
            if record.matches(key, parent) {
                let vn_size = data.vn(vn).get_size();
                let piece = types_of_mut(glb).get_exact_piece(dt, off, vn_size)?;
                if let Some(piece) = piece {
                    let new_res = ResolvedUnion::new_field(piece, record.field_num, types_of_mut(glb))?;
                    data.set_union_field(piece, op, slot, &new_res, glb);
                    data.vn_update_type(vn, piece);
                }
                return Ok(());
            }
        }
        Ok(())
    }

    pub fn inherit_resolution_varnode(
        &self,
        key: i32,
        vn: VarnodeId,
        op: OpId,
        slot: i32,
        data: &mut Funcdata,
        glb: &mut Architecture,
    ) -> Result<()> {
        let dt = data.vn(vn).get_type();
        self.inherit_resolution(key, dt, 0, vn, op, slot, data, glb)
    }
}
