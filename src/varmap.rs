use std::collections::BTreeSet;

use crate::address::{Address, Range, RangeList, calc_mask, sign_extend};
use crate::architecture::Architecture;
use crate::database::{
    Database, EntryId, EntryMap, Scope, ScopeId, ScopeKind, Symbol, SymbolEntry, SymbolId, SymbolNameKey,
};
use crate::dynamic::DynamicHash;
use crate::error::{Error, Result};
use crate::fspec::FuncProto;
use crate::funcdata::Funcdata;
use crate::heritage::LoadGuard;
use crate::marshal::{AttributeId, Decoder, ElementId, Encoder};
use crate::op::PcodeOp;
use crate::opcodes::OpCode;
use crate::space::{AddrSpace, SpaceRef};
use crate::types::{TypeFactory, TypeId, TypeMetatype};
use crate::varnode::{Varnode, VarnodeId};

pub const ATTRIB_LOCK: AttributeId = AttributeId::new("lock", 133);
pub const ATTRIB_MAIN: AttributeId = AttributeId::new("main", 134);
pub const ELEM_LOCALDB: ElementId = ElementId::new("localdb", 228);

fn db_ref(glb: &Architecture) -> &Database {
    glb.symboltab.as_deref().expect("architecture has no symbol table")
}

fn db_mut(glb: &mut Architecture) -> &mut Database {
    glb.symboltab.as_deref_mut().expect("architecture has no symbol table")
}

fn types_ref(glb: &Architecture) -> &TypeFactory {
    glb.types.as_deref().expect("architecture has no type factory")
}

fn types_mut(glb: &mut Architecture) -> &mut TypeFactory {
    glb.types.as_deref_mut().expect("architecture has no type factory")
}

fn db_and_types(glb: &mut Architecture) -> (&mut Database, &mut TypeFactory) {
    (
        glb.symboltab.as_deref_mut().expect("architecture has no symbol table"),
        glb.types.as_deref_mut().expect("architecture has no type factory"),
    )
}

fn same_space_ref(first: Option<&SpaceRef>, second: &SpaceRef) -> bool {
    first.is_some_and(|spc| spc.get_index() == second.get_index())
}

#[derive(Clone, Debug)]
pub struct NameRecommend {
    addr: Address,
    useaddr: Address,
    size: i32,
    name: String,
    symbol_id: u64,
}

impl NameRecommend {
    pub fn new(ad: &Address, usepoint: &Address, sz: i32, nm: &str, id: u64) -> NameRecommend {
        NameRecommend {
            addr: ad.clone(),
            useaddr: usepoint.clone(),
            size: sz,
            name: nm.to_string(),
            symbol_id: id,
        }
    }

    pub fn get_addr(&self) -> &Address {
        &self.addr
    }

    pub fn get_use_addr(&self) -> &Address {
        &self.useaddr
    }

    pub fn get_size(&self) -> i32 {
        self.size
    }

    pub fn get_name(&self) -> String {
        self.name.clone()
    }

    pub fn get_symbol_id(&self) -> u64 {
        self.symbol_id
    }
}

#[derive(Clone, Debug)]
pub struct DynamicRecommend {
    use_point: Address,
    hash: u64,
    name: String,
    symbol_id: u64,
}

impl DynamicRecommend {
    pub fn new(addr: &Address, hash: u64, nm: &str, id: u64) -> DynamicRecommend {
        DynamicRecommend {
            use_point: addr.clone(),
            hash,
            name: nm.to_string(),
            symbol_id: id,
        }
    }

    pub fn get_address(&self) -> &Address {
        &self.use_point
    }

    pub fn get_hash(&self) -> u64 {
        self.hash
    }

    pub fn get_name(&self) -> String {
        self.name.clone()
    }

    pub fn get_symbol_id(&self) -> u64 {
        self.symbol_id
    }
}

#[derive(Clone, Debug)]
pub struct TypeRecommend {
    addr: Address,
    data_type: TypeId,
}

impl TypeRecommend {
    pub fn new(ad: &Address, dt: TypeId) -> TypeRecommend {
        TypeRecommend {
            addr: ad.clone(),
            data_type: dt,
        }
    }

    pub fn get_address(&self) -> &Address {
        &self.addr
    }

    pub fn get_type(&self) -> TypeId {
        self.data_type
    }
}

#[repr(i32)]
#[derive(Copy, Clone, Debug, Default, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum RangeType {
    #[default]
    Fixed = 0,
    Open = 1,
    Endpoint = 2,
}

#[derive(Clone, Debug, Default)]
pub struct RangeHint {
    pub start: u64,
    pub size: i32,
    pub sstart: i64,
    pub tp: Option<TypeId>,
    pub flags: u32,
    pub range_type: RangeType,
    pub highind: i32,
}

impl RangeHint {
    pub const TYPELOCK: u32 = 1;
    pub const COPY_CONSTANT: u32 = 2;
    pub const BACKFILL: u32 = 4;

    pub fn new(st: u64, sz: i32, sst: i64, ct: Option<TypeId>, fl: u32, rt: RangeType, hi: i32) -> RangeHint {
        RangeHint {
            start: st,
            size: sz,
            sstart: sst,
            tp: ct,
            flags: fl,
            range_type: rt,
            highind: hi,
        }
    }

    fn type_id(&self) -> TypeId {
        self.tp.expect("range hint has no data-type")
    }

    fn align_size(&self, types: &TypeFactory) -> i32 {
        types.get(self.type_id()).get_align_size()
    }

    fn metatype(&self, types: &TypeFactory) -> TypeMetatype {
        types.get(self.type_id()).get_metatype()
    }

    pub fn backfill_to_point(&mut self, point: i64, types: &TypeFactory) {
        let align = self.align_size(types) as i64;
        let diff = self.sstart.wrapping_sub(point);
        let num = diff / align;
        let amount = num.wrapping_mul(align);
        self.sstart = self.sstart.wrapping_sub(amount);
        self.start = self.start.wrapping_sub(amount as u64);
    }

    pub fn is_type_lock(&self) -> bool {
        (self.flags & RangeHint::TYPELOCK) != 0
    }

    pub fn is_backfill(&self) -> bool {
        (self.flags & RangeHint::BACKFILL) != 0
    }

    pub fn is_const_absorbable(&self, other: &RangeHint, types: &TypeFactory) -> bool {
        if (other.flags & RangeHint::COPY_CONSTANT) == 0 {
            return false;
        }
        if other.is_type_lock() {
            return false;
        }
        if other.size < self.size {
            return false;
        }
        let meta = self.metatype(types);
        if meta != TypeMetatype::Int
            && meta != TypeMetatype::Uint
            && meta != TypeMetatype::Bool
            && meta != TypeMetatype::Float
        {
            return false;
        }
        let b_meta = other.metatype(types);
        if b_meta != TypeMetatype::Unknown && b_meta != TypeMetatype::Int && b_meta != TypeMetatype::Uint {
            return false;
        }
        let mut end = self.sstart;
        if self.highind > 0 {
            end = end.wrapping_add((self.highind as i64).wrapping_mul(self.align_size(types) as i64));
        } else {
            end = end.wrapping_add(self.size as i64);
        }
        if other.sstart > end {
            return false;
        }
        true
    }

    pub fn reconcile(&self, other: &RangeHint, glb: &Architecture) -> bool {
        let types = types_ref(glb);
        let (hint, other) = if self.align_size(types) < other.align_size(types) {
            (other, self)
        } else {
            (self, other)
        };
        if other.is_type_lock() {
            return false;
        }
        let a_align = hint.align_size(types) as i64;
        let mut modulus = other.sstart.wrapping_sub(hint.sstart) % a_align;
        if modulus < 0 {
            modulus += a_align;
        }
        let b_align = other.align_size(types);
        let mut sub = Some(hint.type_id());
        while let Some(current) = sub {
            if types.get(current).get_align_size() <= b_align {
                break;
            }
            let mut newoff = modulus;
            sub = types.get(current).get_sub_type(modulus, &mut newoff, glb);
            modulus = newoff;
        }
        if let Some(current) = sub
            && types.get(current).get_align_size() == b_align
        {
            return true;
        }
        if other.range_type == RangeType::Open && other.is_const_absorbable(hint, types) {
            return true;
        }
        let meta = hint.metatype(types);
        if meta != TypeMetatype::Struct
            && meta != TypeMetatype::Union
            && (meta != TypeMetatype::Array
                || types.get(types.get(hint.type_id()).get_base()).get_metatype() != TypeMetatype::Unknown)
        {
            return false;
        }
        let meta = other.metatype(types);
        if meta == TypeMetatype::Unknown || meta == TypeMetatype::Int || meta == TypeMetatype::Uint {
            return true;
        }
        if meta == TypeMetatype::Array
            && types.get(types.get(other.type_id()).get_base()).get_metatype() == TypeMetatype::Unknown
        {
            return true;
        }
        false
    }

    pub fn contain(&self, other: &RangeHint) -> bool {
        if self.sstart == other.sstart {
            return true;
        }
        if other.sstart.wrapping_add(other.size as i64).wrapping_sub(1)
            <= self.sstart.wrapping_add(self.size as i64).wrapping_sub(1)
        {
            return true;
        }
        false
    }

    pub fn preferred(&self, other: &RangeHint, reconcile: bool, types: &TypeFactory) -> bool {
        if self.start != other.start {
            return true;
        }
        if other.is_type_lock() {
            if !self.is_type_lock() {
                return false;
            }
        } else if self.is_type_lock() {
            return true;
        }
        if self.range_type == RangeType::Open && other.range_type != RangeType::Open {
            if !reconcile {
                return false;
            }
            if self.is_const_absorbable(other, types) {
                return true;
            }
        } else if other.range_type == RangeType::Open && self.range_type != RangeType::Open {
            if !reconcile {
                return true;
            }
            if other.is_const_absorbable(self, types) {
                return false;
            }
        } else if self.range_type == RangeType::Fixed
            && other.range_type == RangeType::Fixed
            && self.size != other.size
            && !reconcile
        {
            return self.size > other.size;
        }
        types.get(self.type_id()).type_order(types.get(other.type_id()), types) < 0
    }

    pub fn attempt_join(&mut self, other: &mut RangeHint, types: &TypeFactory) -> bool {
        if other.is_backfill() && self.attempt_backfill(other, types) {
            return true;
        }
        if self.range_type != RangeType::Open {
            return false;
        }
        if other.range_type == RangeType::Endpoint {
            return false;
        }
        if self.is_const_absorbable(other, types) {
            self.absorb(other, types);
            return true;
        }
        if self.highind < 0 {
            return false;
        }
        let mut settype = self.type_id();
        if types.get(settype).get_align_size() != other.align_size(types) {
            return false;
        }
        if settype != other.type_id() {
            let mut a_test_type = self.type_id();
            let mut b_test_type = other.type_id();
            while types.get(a_test_type).get_metatype() == TypeMetatype::Ptr {
                if types.get(b_test_type).get_metatype() != TypeMetatype::Ptr {
                    break;
                }
                a_test_type = types.get(a_test_type).get_ptr_to();
                b_test_type = types.get(b_test_type).get_ptr_to();
            }
            let a_meta = types.get(a_test_type).get_metatype();
            let b_meta = types.get(b_test_type).get_metatype();
            if a_meta == TypeMetatype::Unknown {
                settype = other.type_id();
            } else if b_meta == TypeMetatype::Unknown
                || (a_meta == TypeMetatype::Int && b_meta == TypeMetatype::Uint)
                || (a_meta == TypeMetatype::Uint && b_meta == TypeMetatype::Int)
            {
            } else if a_test_type != b_test_type {
                return false;
            }
        }
        if self.is_type_lock() {
            return false;
        }
        if other.is_type_lock() {
            return false;
        }
        let set_align = types.get(settype).get_align_size() as i64;
        let mut diffsz = other.sstart.wrapping_sub(self.sstart);
        if diffsz % set_align != 0 {
            return false;
        }
        diffsz /= set_align;
        if diffsz > self.highind as i64 {
            return false;
        }
        self.tp = Some(settype);
        self.absorb(other, types);
        true
    }

    pub fn attempt_backfill(&mut self, other: &mut RangeHint, types: &TypeFactory) -> bool {
        let rightedge = self.sstart.wrapping_add(self.size as i64);
        if other.sstart < rightedge {
            return true;
        }
        if self.range_type != RangeType::Open {
            other.backfill_to_point(rightedge, types);
            return false;
        }
        if self.is_backfill() {
            return true;
        }
        other.backfill_to_point(other.sstart.wrapping_sub(rightedge) / 2, types);
        true
    }

    pub fn backfill_open(&mut self, range: &Range, max_elements: i32, types: &TypeFactory) {
        if self.start < range.get_first() {
            return;
        }
        let align = self.align_size(types) as i64 as u64;
        let diff = self.start - range.get_first();
        let mut num = diff / align;
        if num > max_elements as i64 as u64 {
            num = max_elements as i64 as u64;
        }
        let amount = num.wrapping_mul(align);
        let tmp_start = self.start.wrapping_sub(amount);
        if !range.contains(&Address::new(range.get_space().clone(), tmp_start)) {
            return;
        }
        self.start = tmp_start;
        self.sstart = self.sstart.wrapping_sub(amount as i64);
    }

    pub fn absorb(&mut self, other: &RangeHint, types: &TypeFactory) {
        if other.range_type == RangeType::Open {
            if self.align_size(types) == other.align_size(types) {
                self.range_type = RangeType::Open;
                if 0 <= other.highind {
                    let mut diffsz = other.sstart.wrapping_sub(self.sstart);
                    diffsz /= self.align_size(types) as i64;
                    let trialhi = (other.highind as i64).wrapping_add(diffsz) as i32;
                    if self.highind < trialhi {
                        self.highind = trialhi;
                    }
                }
            } else if self.start == other.start {
                let meta = self.metatype(types);
                if meta != TypeMetatype::Struct && meta != TypeMetatype::Union {
                    self.range_type = RangeType::Open;
                }
            }
        } else if (other.flags & RangeHint::COPY_CONSTANT) != 0 && self.range_type == RangeType::Open {
            let diffsz = other.sstart.wrapping_sub(self.sstart).wrapping_add(other.size as i64);
            if diffsz > self.size as i64 {
                let trialhi = (diffsz / self.align_size(types) as i64) as i32;
                if self.highind < trialhi {
                    self.highind = trialhi;
                }
            }
        }
        if (self.flags & RangeHint::COPY_CONSTANT) != 0 && (other.flags & RangeHint::COPY_CONSTANT) == 0 {
            self.flags ^= RangeHint::COPY_CONSTANT;
        }
    }

    pub fn merge(&mut self, other: &RangeHint, _space: &SpaceRef, glb: &mut Architecture) -> Result<bool> {
        let did_reconcile;
        let res_type;
        if other.range_type == RangeType::Endpoint {
            return Err(Error::Lowlevel("RangeHint overlaps endpoint".to_string()));
        }
        if self.contain(other) {
            did_reconcile = self.reconcile(other, glb);
            if !did_reconcile && self.start != other.start {
                res_type = 2;
            } else {
                res_type = if self.preferred(other, did_reconcile, types_ref(glb)) {
                    0
                } else {
                    1
                };
            }
        } else {
            did_reconcile = false;
            res_type = if self.is_type_lock() { 0 } else { 2 };
        }
        if !did_reconcile && self.is_type_lock() {
            if other.is_type_lock() {
                let types = types_ref(glb);
                return Err(Error::Lowlevel(format!(
                    "Overlapping forced variable types : {}   {}",
                    types.get(self.type_id()).get_name(),
                    types.get(other.type_id()).get_name()
                )));
            }
            if self.start != other.start {
                return Ok(false);
            }
        }
        if res_type == 0 {
            self.absorb(other, types_ref(glb));
        } else if res_type == 1 {
            let copy_range = self.clone();
            self.tp = other.tp;
            self.flags = other.flags;
            self.range_type = other.range_type;
            self.highind = other.highind;
            self.size = other.size;
            self.absorb(&copy_range, types_ref(glb));
        } else if res_type == 2 {
            self.flags = 0;
            self.range_type = RangeType::Fixed;
            let diff = other.sstart.wrapping_sub(self.sstart) as i32;
            if diff.wrapping_add(other.size) > self.size {
                self.size = diff.wrapping_add(other.size);
            }
            if self.size != 1 && self.size != 2 && self.size != 4 && self.size != 8 {
                self.size = 1;
                self.range_type = RangeType::Open;
            }
            self.tp = Some(types_mut(glb).get_base(self.size, TypeMetatype::Unknown)?);
            self.flags = 0;
            self.highind = -1;
            return Ok(false);
        }
        Ok(false)
    }

    pub fn compare(&self, op2: &RangeHint) -> i32 {
        if self.sstart != op2.sstart {
            return if self.sstart < op2.sstart { -1 } else { 1 };
        }
        if self.size != op2.size {
            return if self.size < op2.size { -1 } else { 1 };
        }
        if self.range_type != op2.range_type {
            return if self.range_type < op2.range_type { -1 } else { 1 };
        }
        if self.flags != op2.flags {
            return if self.flags < op2.flags { -1 } else { 1 };
        }
        if self.highind != op2.highind {
            return if self.highind < op2.highind { -1 } else { 1 };
        }
        0
    }

    pub fn compare_ranges(first: &RangeHint, second: &RangeHint) -> bool {
        first.compare(second) < 0
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct AddBase {
    pub base: VarnodeId,
    pub index: Option<VarnodeId>,
}

impl AddBase {
    pub fn new(base_2: VarnodeId, input: Option<VarnodeId>) -> AddBase {
        AddBase {
            base: base_2,
            index: input,
        }
    }
}

#[derive(Clone, Debug, Default)]
pub struct AliasChecker {
    space: Option<SpaceRef>,
    add_base: Vec<AddBase>,
    alias: Vec<u64>,
    calculated: bool,
    local_extreme: u64,
    local_boundary: u64,
    alias_boundary: u64,
    direction: i32,
}

impl AliasChecker {
    pub fn new() -> AliasChecker {
        AliasChecker {
            space: None,
            add_base: Vec::new(),
            alias: Vec::new(),
            calculated: false,
            local_extreme: 0,
            local_boundary: 0,
            alias_boundary: 0,
            direction: 0,
        }
    }

    fn derive_boundaries(&mut self, proto: &FuncProto, glb: &Architecture) {
        self.local_extreme = !0u64;
        self.local_boundary = 0x1000000;
        if self.direction == -1 {
            self.local_extreme = self.local_boundary;
        }
        if proto.has_model() {
            let localrange = proto.get_local_range(glb);
            let paramrange = proto.get_param_range(glb);
            let local = localrange.get_first_range();
            let param = paramrange.get_last_range();
            if let (Some(_), Some(param)) = (local, param) {
                self.local_boundary = param.get_last();
                if self.direction == -1 {
                    self.local_boundary = paramrange
                        .get_first_range()
                        .expect("parameter range is not empty")
                        .get_first();
                    self.local_extreme = self.local_boundary;
                }
            }
        }
    }

    fn gather_internal(&mut self, data: &Funcdata) {
        self.calculated = true;
        self.alias_boundary = self.local_extreme;
        let space = self.space.clone().expect("alias checker has no address space");
        let spacebase = data.find_spacebase_input(&space).ok().flatten();
        let Some(spacebase) = spacebase else {
            return;
        };
        let mut addbase = std::mem::take(&mut self.add_base);
        AliasChecker::gather_additive_base(data, spacebase, &mut addbase);
        for base in addbase.iter() {
            let mut offset = AliasChecker::gather_offset(data, base.base);
            offset = AddrSpace::address_to_byte(offset, space.get_word_size());
            self.alias.push(offset);
            if self.direction == 1 {
                if offset < self.local_boundary {
                    continue;
                }
            } else if offset > self.local_boundary {
                continue;
            }
            if offset < self.alias_boundary {
                self.alias_boundary = offset;
            }
        }
        self.add_base = addbase;
    }

    pub fn gather(&mut self, data: &Funcdata, spc: &SpaceRef, defer: bool, glb: &Architecture) {
        self.space = Some(spc.clone());
        self.calculated = false;
        self.add_base.clear();
        self.alias.clear();
        self.direction = if spc.stack_grows_negative() { 1 } else { -1 };
        self.derive_boundaries(data.get_func_proto(), glb);
        if !defer {
            self.gather_internal(data);
        }
    }

    pub fn has_local_alias(&mut self, data: &Funcdata, vn: VarnodeId) -> bool {
        if !self.calculated {
            self.gather_internal(data);
        }
        let space = self.space.as_ref().expect("alias checker has no address space");
        if !same_space_ref(data.vn(vn).get_space(), space) {
            return false;
        }
        if self.direction == -1 {
            return false;
        }
        data.vn(vn).get_offset() >= self.alias_boundary
    }

    pub fn sort_alias(&mut self) {
        self.alias.sort();
    }

    pub fn get_add_base(&self) -> &Vec<AddBase> {
        &self.add_base
    }

    pub fn get_alias(&self) -> &Vec<u64> {
        &self.alias
    }

    pub fn gather_additive_base(data: &Funcdata, startvn: VarnodeId, addbase: &mut Vec<AddBase>) {
        let mut vnqueue: Vec<AddBase> = Vec::new();
        let mut marked: BTreeSet<VarnodeId> = BTreeSet::new();
        marked.insert(startvn);
        vnqueue.push(AddBase::new(startvn, None));
        let mut pos = 0;
        while pos < vnqueue.len() {
            let vn = vnqueue[pos].base;
            let mut indexvn = vnqueue[pos].index;
            pos += 1;
            let mut nonadduse = false;
            for &op in data.vn(vn).descend() {
                let pcode = data.op(op);
                match pcode.code() {
                    OpCode::Copy => {
                        nonadduse = true;
                        let subvn = pcode.get_out().expect("COPY has an output");
                        if marked.insert(subvn) {
                            vnqueue.push(AddBase::new(subvn, indexvn));
                        }
                    }
                    OpCode::IntSub => {
                        if vn == pcode.get_in(1) {
                            nonadduse = true;
                            continue;
                        }
                        let othervn = pcode.get_in(1);
                        if !data.vn(othervn).is_constant() {
                            indexvn = Some(othervn);
                        }
                        let subvn = pcode.get_out().expect("INT_SUB has an output");
                        if marked.insert(subvn) {
                            vnqueue.push(AddBase::new(subvn, indexvn));
                        }
                    }
                    OpCode::IntAdd | OpCode::Ptradd | OpCode::Ptrsub | OpCode::Segmentop => {
                        if matches!(pcode.code(), OpCode::IntAdd | OpCode::Ptradd) {
                            let mut othervn = pcode.get_in(1);
                            if othervn == vn {
                                othervn = pcode.get_in(0);
                            }
                            if !data.vn(othervn).is_constant() {
                                indexvn = Some(othervn);
                            }
                        }
                        let subvn = pcode.get_out().expect("additive op has an output");
                        if marked.insert(subvn) {
                            vnqueue.push(AddBase::new(subvn, indexvn));
                        }
                    }
                    _ => {
                        nonadduse = true;
                    }
                }
            }
            if nonadduse {
                addbase.push(AddBase::new(vn, indexvn));
            }
        }
    }

    pub fn gather_offset(data: &Funcdata, vn: VarnodeId) -> u64 {
        let varnode = data.vn(vn);
        if varnode.is_constant() {
            return varnode.get_offset();
        }
        let Some(def) = varnode.get_def() else {
            return 0;
        };
        let def_op = data.op(def);
        let retval = match def_op.code() {
            OpCode::Copy => AliasChecker::gather_offset(data, def_op.get_in(0)),
            OpCode::Ptrsub | OpCode::IntAdd => AliasChecker::gather_offset(data, def_op.get_in(0))
                .wrapping_add(AliasChecker::gather_offset(data, def_op.get_in(1))),
            OpCode::IntSub => AliasChecker::gather_offset(data, def_op.get_in(0))
                .wrapping_sub(AliasChecker::gather_offset(data, def_op.get_in(1))),
            OpCode::Ptradd => {
                let othervn = def_op.get_in(2);
                let mut retval = AliasChecker::gather_offset(data, def_op.get_in(0));
                let in1 = def_op.get_in(1);
                if data.vn(in1).is_constant() {
                    retval = retval.wrapping_add(data.vn(in1).get_offset().wrapping_mul(data.vn(othervn).get_offset()));
                } else if data.vn(othervn).get_offset() == 1 {
                    retval = retval.wrapping_add(AliasChecker::gather_offset(data, in1));
                }
                retval
            }
            OpCode::Segmentop => AliasChecker::gather_offset(data, def_op.get_in(2)),
            _ => 0,
        };
        retval & calc_mask(varnode.get_size())
    }
}

pub struct MapState {
    spaceid: SpaceRef,
    range: RangeList,
    param_range: RangeList,
    maplist: Vec<RangeHint>,
    iter: usize,
    default_type: Option<TypeId>,
    checker: AliasChecker,
    param_range_hit: bool,
    pub debugon: bool,
}

impl MapState {
    pub fn new(spc: &SpaceRef, rn: &RangeList, pm: &RangeList, dt: Option<TypeId>) -> MapState {
        let mut range = rn.clone();
        for rng in pm.iter() {
            range.remove_range(rng.get_space(), rng.get_first(), rng.get_last());
        }
        MapState {
            spaceid: spc.clone(),
            range,
            param_range: pm.clone(),
            maplist: Vec::new(),
            iter: 0,
            default_type: dt,
            checker: AliasChecker::new(),
            param_range_hit: false,
            debugon: false,
        }
    }

    fn default_type_id(&self) -> TypeId {
        self.default_type.expect("map state has no default data-type")
    }

    fn add_guard(&mut self, guard: &LoadGuard, opc: OpCode, data: &Funcdata, glb: &mut Architecture) -> Result<()> {
        if !guard.is_valid(opc, data) {
            return Ok(());
        }
        let mut step = guard.get_step();
        if step == 0 {
            return Ok(());
        }
        let op = guard.get_op().expect("valid load guard has an op");
        let in1 = data.op(op).get_in(1);
        let mut ct = data.vn_get_type_read_facing(in1, op, glb);
        let types = types_ref(glb);
        if types.get(ct).get_metatype() == TypeMetatype::Ptr {
            ct = types.get(ct).get_ptr_to();
            while types.get(ct).get_metatype() == TypeMetatype::Array {
                ct = types.get(ct).get_base();
            }
        }
        let out_size = if opc == OpCode::Store {
            data.vn(data.op(op).get_in(2)).get_size()
        } else {
            data.vn(data.op(op).get_out().expect("LOAD has an output")).get_size()
        };
        if out_size != step {
            if out_size > step || (step % out_size) != 0 {
                return Ok(());
            }
            step = out_size;
        }
        if types.get(ct).get_align_size() != step {
            if step > 8 {
                return Ok(());
            }
            ct = types_mut(glb).get_base(step, TypeMetatype::Unknown)?;
        }
        let types = types_ref(glb);
        if guard.is_range_locked() {
            let span = guard.get_maximum().wrapping_sub(guard.get_minimum()).wrapping_add(1);
            let min_items = (span / (step as i64 as u64)) as i32;
            self.add_range(
                guard.get_minimum(),
                Some(ct),
                0,
                RangeType::Open,
                min_items.wrapping_sub(1),
                types,
            );
        } else {
            self.add_range(guard.get_minimum(), Some(ct), 0, RangeType::Open, 3, types);
        }
        Ok(())
    }

    fn adjust_out_of_range(&mut self, st: &mut u64, ct: &mut TypeId, fl: &mut u32, types: &TypeFactory) -> bool {
        let ct_size = types.get(*ct).get_size();
        if self
            .param_range
            .in_range(&Address::new(self.spaceid.clone(), *st), ct_size as u64)
        {
            self.param_range_hit = true;
            return false;
        }
        let default_type = self.default_type_id();
        let default_size = types.get(default_type).get_size();
        if default_size < ct_size
            && self
                .range
                .in_range(&Address::new(self.spaceid.clone(), *st), default_size as u64)
        {
            *ct = default_type;
            return true;
        }
        if *st == 0 {
            return false;
        }
        let Some(near) = self.range.get_nearest_range(&self.spaceid, *st) else {
            return false;
        };
        let align = types.get(*ct).get_align_size() as i64 as u64;
        let ct_size = types.get(*ct).get_size() as i64 as u64;
        if near.get_last() < *st {
            let num = (*st - near.get_last() - 1) / align;
            *st = st.wrapping_sub(align.wrapping_mul(num + 1));
            if !near.contains(&Address::new(
                self.spaceid.clone(),
                st.wrapping_add(ct_size).wrapping_sub(1),
            )) {
                *st = st.wrapping_sub(align);
            }
            if !near.contains(&Address::new(self.spaceid.clone(), *st)) {
                return false;
            }
            *fl |= RangeHint::BACKFILL;
        } else {
            let num = near.get_first().wrapping_sub(*st).wrapping_add(1) / align;
            *st = st.wrapping_add(align.wrapping_mul(num + 1));
            if !near.contains(&Address::new(self.spaceid.clone(), *st)) {
                return false;
            }
            if !near.contains(&Address::new(
                self.spaceid.clone(),
                st.wrapping_add(ct_size).wrapping_sub(1),
            )) {
                return false;
            }
        }
        true
    }

    fn add_range(&mut self, st: u64, ct: Option<TypeId>, fl: u32, rt: RangeType, hi: i32, types: &TypeFactory) {
        let mut st = st;
        let mut fl = fl;
        let mut ct = match ct {
            Some(tp) if types.get(tp).get_size() != 0 => tp,
            _ => self.default_type_id(),
        };
        if !self
            .range
            .in_range(&Address::new(self.spaceid.clone(), st), types.get(ct).get_size() as u64)
        {
            if rt != RangeType::Open {
                return;
            }
            if !self.adjust_out_of_range(&mut st, &mut ct, &mut fl, types) {
                return;
            }
        }
        let word_size = self.spaceid.get_word_size();
        let mut sst = AddrSpace::byte_to_address(st, word_size) as i64;
        sst = sign_extend(sst, (self.spaceid.get_addr_size() * 8) as i32 - 1);
        sst = AddrSpace::address_to_byte(sst as u64, word_size) as i64;
        let new_range = RangeHint::new(st, types.get(ct).get_size(), sst, Some(ct), fl, rt, hi);
        self.maplist.push(new_range);
    }

    fn add_fixed_type(&mut self, start: u64, ct: TypeId, flags: u32, types: &mut TypeFactory) -> Result<()> {
        let meta = types.get(ct).get_metatype();
        if meta == TypeMetatype::PartialStruct {
            let tps = ct;
            let mut ct = types.get(tps).get_parent();
            let tps_offset = types.get(tps).get_offset();
            if types.get(ct).get_metatype() == TypeMetatype::Struct && tps_offset == 0 {
                self.add_range(start, Some(ct), 0, RangeType::Open, -1, types);
            } else if types.get(ct).get_metatype() == TypeMetatype::Array {
                ct = types.get(ct).get_base();
                if types.get(ct).get_metatype() != TypeMetatype::Unknown {
                    self.add_range(start, Some(ct), 0, RangeType::Open, -1, types);
                }
            }
            if flags != 0 {
                let tps_size = types.get(tps).get_size();
                let ct = types.get_base(tps_size, TypeMetatype::Unknown)?;
                self.add_range(start, Some(ct), flags, RangeType::Fixed, -1, types);
            }
        } else if meta == TypeMetatype::PartialUnion {
            if types.get(ct).get_offset() == 0 {
                let parent = types.get(ct).get_parent_union();
                self.add_range(start, Some(parent), 0, RangeType::Open, -1, types);
            }
        } else {
            self.add_range(start, Some(ct), flags, RangeType::Fixed, -1, types);
        }
        Ok(())
    }

    fn reconcile_datatypes(&mut self, types: &TypeFactory) {
        let maplist = std::mem::take(&mut self.maplist);
        let mut new_list: Vec<RangeHint> = Vec::with_capacity(maplist.len());
        let mut hints = maplist.into_iter();
        let Some(first) = hints.next() else {
            return;
        };
        let mut start_pos = 0;
        let mut start_hint = first.clone();
        let mut start_datatype = first.type_id();
        new_list.push(first);
        for cur_hint in hints {
            if cur_hint.start == start_hint.start
                && cur_hint.size == start_hint.size
                && cur_hint.flags == start_hint.flags
            {
                let cur_datatype = cur_hint.type_id();
                if types.get(cur_datatype).type_order(types.get(start_datatype), types) < 0 {
                    start_datatype = cur_datatype;
                }
                if cur_hint.compare(new_list.last().expect("list is not empty")) != 0 {
                    new_list.push(cur_hint);
                }
            } else {
                while start_pos < new_list.len() {
                    new_list[start_pos].tp = Some(start_datatype);
                    start_pos += 1;
                }
                start_hint = cur_hint.clone();
                start_datatype = cur_hint.type_id();
                new_list.push(cur_hint);
            }
        }
        while start_pos < new_list.len() {
            new_list[start_pos].tp = Some(start_datatype);
            start_pos += 1;
        }
        self.maplist = new_list;
    }

    fn is_read_active(data: &Funcdata, vn: VarnodeId) -> bool {
        let varnode = data.vn(vn);
        for &op in varnode.descend() {
            let pcode = data.op(op);
            if pcode.is_marker() {
                let out = pcode.get_out().expect("marker op has an output");
                if varnode.get_addr() != data.vn(out).get_addr() {
                    return true;
                }
            } else {
                let opc = pcode.code();
                if opc == OpCode::Piece {
                    let out = pcode.get_out().expect("PIECE has an output");
                    let mut addr = data.vn(out).get_addr().clone();
                    let slot = if addr.is_big_endian() { 0 } else { 1 };
                    if pcode.get_in(slot) != vn {
                        addr = addr.add(data.vn(pcode.get_in(slot)).get_size() as i64);
                    }
                    if *varnode.get_addr() != addr {
                        return true;
                    }
                } else if opc == OpCode::Subpiece {
                } else {
                    return true;
                }
            }
        }
        false
    }

    pub fn turn_on_debug(&mut self) {
        self.debugon = true;
    }

    pub fn turn_off_debug(&mut self) {
        self.debugon = false;
    }

    pub fn initialize(&mut self, types: &TypeFactory) -> bool {
        let Some(lastrange) = self.range.get_last_signed_range(&self.spaceid) else {
            return false;
        };
        if self.maplist.is_empty() {
            return false;
        }
        let high = self.spaceid.wrap_offset(lastrange.get_last().wrapping_add(1));
        let word_size = self.spaceid.get_word_size();
        let mut sst = AddrSpace::byte_to_address(high, word_size) as i64;
        sst = sign_extend(sst, (self.spaceid.get_addr_size() * 8) as i32 - 1);
        sst = AddrSpace::address_to_byte(sst as u64, word_size) as i64;
        let term_range = RangeHint::new(high, 1, sst, self.default_type, 0, RangeType::Endpoint, -2);
        self.maplist.push(term_range);
        self.maplist.sort_by(|first, second| first.compare(second).cmp(&0));
        self.reconcile_datatypes(types);
        self.iter = 0;
        if self.maplist[0].is_backfill() {
            let start = self.maplist[0].start;
            if let Some(sub) = self.range.get_range(&self.spaceid, start) {
                let sub = sub.clone();
                self.maplist[0].backfill_open(&sub, 127, types);
            }
        }
        true
    }

    pub fn has_param_range_hit(&self) -> bool {
        self.param_range_hit
    }

    pub fn sort_alias(&mut self) {
        self.checker.sort_alias();
    }

    pub fn get_alias(&self) -> &Vec<u64> {
        self.checker.get_alias()
    }

    pub fn gather_symbols(&mut self, db: &Database, rangemap: Option<&EntryMap>, types: &TypeFactory) {
        let Some(rangemap) = rangemap else {
            return;
        };
        for (_, record) in rangemap.list_iter() {
            let entry = db.entry(record.entry);
            let sym = db.symbol(entry.get_symbol());
            let start = entry.get_addr().get_offset();
            let ct = sym.get_type();
            let flags = if sym.is_type_locked() { RangeHint::TYPELOCK } else { 0 };
            self.add_range(start, ct, flags, RangeType::Fixed, -1, types);
        }
    }

    pub fn gather_varnodes(&mut self, glb: &mut Architecture, data: &Funcdata) -> Result<()> {
        let begin = data.begin_loc_space(&self.spaceid);
        let end = data.end_loc_space(&self.spaceid, glb);
        let varnodes = data.vbank.loc_range(&begin, &end);
        let types = types_mut(glb);
        for vn in varnodes {
            let varnode = data.vn(vn);
            if varnode.is_free() {
                continue;
            }
            if !varnode.is_written() {
                if MapState::is_read_active(data, vn) {
                    self.add_fixed_type(varnode.get_offset(), varnode.get_type(), 0, types)?;
                }
                continue;
            }
            let op = data.op(varnode.get_def().expect("written varnode has a defining op"));
            match op.code() {
                OpCode::Indirect => {
                    let invn = op.get_in(0);
                    if varnode.get_addr() != data.vn(invn).get_addr() || MapState::is_read_active(data, vn) {
                        self.add_fixed_type(varnode.get_offset(), varnode.get_type(), 0, types)?;
                    }
                }
                OpCode::Multiequal => {
                    let mut slot = 0;
                    while slot < op.num_input() {
                        let invn = op.get_in(slot);
                        if varnode.get_addr() != data.vn(invn).get_addr() {
                            break;
                        }
                        slot += 1;
                    }
                    if slot != op.num_input() || MapState::is_read_active(data, vn) {
                        self.add_fixed_type(varnode.get_offset(), varnode.get_type(), 0, types)?;
                    }
                }
                OpCode::Piece => {
                    let mut addr = varnode.get_addr().clone();
                    let slot = if addr.is_big_endian() { 0 } else { 1 };
                    let in_first = data.vn(op.get_in(slot));
                    if *in_first.get_addr() != addr {
                        self.add_fixed_type(addr.get_offset(), in_first.get_type(), 0, types)?;
                    }
                    addr = addr.add(in_first.get_size() as i64);
                    let in_second = data.vn(op.get_in(1 - slot));
                    if *in_second.get_addr() != addr {
                        self.add_fixed_type(addr.get_offset(), in_second.get_type(), 0, types)?;
                    }
                    if MapState::is_read_active(data, vn) {
                        self.add_fixed_type(varnode.get_offset(), varnode.get_type(), 0, types)?;
                    }
                }
                OpCode::Subpiece => {
                    let in0 = data.vn(op.get_in(0));
                    let mut addr = in0.get_addr().clone();
                    let trunc = if addr.is_big_endian() {
                        in0.get_size() - varnode.get_size() - data.vn(op.get_in(1)).get_offset() as i32
                    } else {
                        data.vn(op.get_in(1)).get_offset() as i32
                    };
                    addr = addr.add(trunc as i64);
                    if addr != *varnode.get_addr() || MapState::is_read_active(data, vn) {
                        self.add_fixed_type(varnode.get_offset(), varnode.get_type(), 0, types)?;
                    }
                }
                OpCode::Copy => {
                    let flags = if data.vn(op.get_in(0)).is_constant() {
                        RangeHint::COPY_CONSTANT
                    } else {
                        0
                    };
                    self.add_fixed_type(varnode.get_offset(), varnode.get_type(), flags, types)?;
                }
                _ => {
                    self.add_fixed_type(varnode.get_offset(), varnode.get_type(), 0, types)?;
                }
            }
        }
        Ok(())
    }

    pub fn gather_open(&mut self, glb: &mut Architecture, data: &Funcdata) -> Result<()> {
        let spaceid = self.spaceid.clone();
        self.checker.gather(data, &spaceid, false, glb);
        let addbase = self.checker.get_add_base().clone();
        let alias = self.checker.get_alias().clone();
        {
            let types = types_ref(glb);
            for (index, base) in addbase.iter().enumerate() {
                let offset = alias[index];
                let mut ct = Some(data.vn(base.base).get_type());
                let tp = ct.expect("varnode has a data-type");
                if types.get(tp).get_metatype() == TypeMetatype::Ptr {
                    let mut pointed = types.get(tp).get_ptr_to();
                    while types.get(pointed).get_metatype() == TypeMetatype::Array {
                        pointed = types.get(pointed).get_base();
                    }
                    ct = Some(pointed);
                } else {
                    ct = None;
                }
                let min_items = if base.index.is_some() { 3 } else { -1 };
                self.add_range(offset, ct, 0, RangeType::Open, min_items, types);
            }
        }
        for guard in data.get_load_guards() {
            self.add_guard(guard, OpCode::Load, data, glb)?;
        }
        for guard in data.get_store_guards() {
            self.add_guard(guard, OpCode::Store, data, glb)?;
        }
        Ok(())
    }

    pub fn next(&mut self) -> &mut RangeHint {
        &mut self.maplist[self.iter]
    }

    pub fn get_next(&mut self) -> bool {
        self.iter += 1;
        if self.iter == self.maplist.len() {
            return false;
        }
        true
    }
}

pub struct ScopeLocalData {
    pub space: SpaceRef,
    pub name_recommend: Vec<NameRecommend>,
    pub dyn_recommend: Vec<DynamicRecommend>,
    pub type_recommend: Vec<TypeRecommend>,
    pub min_param_offset: u64,
    pub max_param_offset: u64,
    pub stack_grows_negative: bool,
    pub range_locked: bool,
    pub overlap_problems: bool,
    pub open_param_refs: bool,
}

impl ScopeLocalData {
    pub fn get_space_id(&self) -> &SpaceRef {
        &self.space
    }

    pub fn has_overlap_probems(&self) -> bool {
        self.overlap_problems
    }

    pub fn is_unaffected_storage(&self, data: &Funcdata, vn: VarnodeId) -> bool {
        data.vn(vn)
            .get_space()
            .is_some_and(|spc| spc.get_index() == self.space.get_index())
    }

    pub fn has_open_param_refs(&self) -> bool {
        self.open_param_refs
    }

    pub fn has_type_recommendations(&self) -> bool {
        !self.type_recommend.is_empty()
    }

    pub fn add_type_recommendation(&mut self, addr: &Address, dt: TypeId) {
        self.type_recommend.push(TypeRecommend::new(addr, dt));
    }
}

impl Scope {
    pub fn new_local(glb: &Architecture, id: u64, spc: &SpaceRef, fd: &Address, name: &str) -> Scope {
        let mut scope = Scope::new_internal(id, name, glb.manager.num_spaces());
        scope.kind = ScopeKind::Local(Box::new(ScopeLocalData {
            space: spc.clone(),
            name_recommend: Vec::new(),
            dyn_recommend: Vec::new(),
            type_recommend: Vec::new(),
            min_param_offset: !0u64,
            max_param_offset: 0,
            stack_grows_negative: true,
            range_locked: false,
            overlap_problems: false,
            open_param_refs: false,
        }));
        scope.restrict_scope(fd.clone());
        scope
    }
}

impl Database {
    fn local_space(&self, scope: ScopeId) -> SpaceRef {
        self.scope(scope).local_data().space.clone()
    }

    pub fn local_adjust_fit(&self, scope: ScopeId, hint: &mut RangeHint, types: &TypeFactory) -> bool {
        if hint.size == 0 {
            return false;
        }
        if hint.is_type_lock() {
            return false;
        }
        let space = self.local_space(scope);
        let addr = Address::new(space, hint.start);
        let mut maxsize = self
            .scope(scope)
            .get_range_tree()
            .longest_fit(&addr, hint.size as i64 as u64);
        if maxsize == 0 {
            return false;
        }
        let type_size = types.get(hint.type_id()).get_size() as i64 as u64;
        if maxsize < hint.size as i64 as u64 {
            if maxsize < type_size {
                return false;
            }
            hint.size = maxsize as i32;
        }
        let Some(entry) = self.scope_find_overlap(scope, &addr, hint.size) else {
            return true;
        };
        if *self.entry(entry).get_addr() <= addr {
            return false;
        }
        maxsize = self.entry(entry).get_addr().get_offset().wrapping_sub(hint.start);
        if maxsize < type_size {
            return false;
        }
        hint.size = maxsize as i32;
        true
    }

    pub fn local_create_entry(glb: &mut Architecture, scope: ScopeId, hint: &RangeHint) -> Result<()> {
        let space = db_ref(glb).local_space(scope);
        let addr = Address::new(space, hint.start);
        let usepoint = Address::invalid();
        let types = types_mut(glb);
        let mut ct = types.concretize(hint.type_id())?;
        let num = hint.size / types.get(ct).get_align_size();
        if num > 1 {
            ct = types.get_type_array(num, ct)?;
        }
        Database::scope_add_symbol_at(glb, scope, "", Some(ct), &addr, &usepoint)?;
        Ok(())
    }

    pub fn local_restructure(glb: &mut Architecture, scope: ScopeId, state: &mut MapState) -> Result<bool> {
        let space = db_ref(glb).local_space(scope);
        let mut overlap_problems = false;
        if !state.initialize(types_ref(glb)) {
            return Ok(overlap_problems);
        }
        let mut cur = state.next().clone();
        while state.get_next() {
            let next = state.next();
            if next.sstart < cur.sstart.wrapping_add(cur.size as i64) {
                let next = next.clone();
                if cur.merge(&next, &space, glb)? {
                    overlap_problems = true;
                }
            } else if !cur.attempt_join(next, types_ref(glb)) {
                if cur.range_type == RangeType::Open {
                    cur.size = next.sstart.wrapping_sub(cur.sstart) as i32;
                    if cur.size < 0 {
                        cur.size = 0x7fffffff;
                    }
                }
                let next = next.clone();
                if db_ref(glb).local_adjust_fit(scope, &mut cur, types_ref(glb)) {
                    Database::local_create_entry(glb, scope, &cur)?;
                }
                cur = next;
            }
        }
        Ok(overlap_problems)
    }

    pub fn local_mark_unaliased(glb: &mut Architecture, scope: ScopeId, alias: &[u64]) {
        let alias_block_level = glb.alias_block_level;
        let (db, types) = db_and_types(glb);
        let space = db.local_space(scope);
        let entries: Vec<EntryId> = match db.scope(scope).maptable.get(space.get_index() as usize) {
            Some(Some(rangemap)) => rangemap.list_iter().map(|(_, record)| record.entry).collect(),
            _ => return,
        };
        let ranges: Vec<Range> = db.scope(scope).get_range_tree().iter().cloned().collect();
        let mut range_pos = 0;
        let mut aliason = false;
        let mut curalias: u64 = 0;
        let mut alias_pos = 0;
        for entry in entries {
            let record = db.entry(entry);
            let curoff = record
                .get_addr()
                .get_offset()
                .wrapping_add(record.get_size() as i64 as u64)
                .wrapping_sub(1);
            while alias_pos < alias.len() && alias[alias_pos] <= curoff {
                aliason = true;
                curalias = alias[alias_pos];
                alias_pos += 1;
            }
            while range_pos < ranges.len() {
                let rng = &ranges[range_pos];
                if rng.get_space().get_index() == space.get_index() {
                    if rng.get_first() > curalias && curoff >= rng.get_first() {
                        aliason = false;
                    }
                    if rng.get_last() >= curoff {
                        break;
                    }
                    if rng.get_last() > curalias {
                        aliason = false;
                    }
                }
                range_pos += 1;
            }
            let symbol = record.get_symbol();
            if aliason && curoff.wrapping_sub(curalias) > 0xffff {
                aliason = false;
            }
            if !aliason {
                let symscope = db.symbol(symbol).get_scope();
                db.scope_set_attribute(types, symscope, symbol, Varnode::NOLOCALALIAS);
            }
            if db.symbol(symbol).is_type_locked() && alias_block_level != 0 {
                if alias_block_level == 3 {
                    aliason = false;
                } else {
                    let meta = types
                        .get(db.symbol(symbol).get_type().expect("symbol has a data-type"))
                        .get_metatype();
                    if meta == TypeMetatype::Struct || (meta == TypeMetatype::Array && alias_block_level > 1) {
                        aliason = false;
                    }
                }
            }
        }
    }

    pub fn local_fake_input_symbols(glb: &mut Architecture, data: &mut Funcdata, scope: ScopeId) -> Result<()> {
        let db = db_ref(glb);
        let space = db.local_space(scope);
        let lockedinputs = db.scope_get_category_size(scope, Symbol::FUNCTION_PARAMETER as i32);
        let begin = data.begin_def_flags(Varnode::INPUT)?;
        let end = data.end_def_flags(Varnode::INPUT)?;
        let inputs = data.vbank.def_range(&begin, &end);
        let mut pos = 0;
        while pos < inputs.len() {
            let mut vn = inputs[pos];
            pos += 1;
            let mut locked = data.vn(vn).is_type_lock();
            let addr = data.vn(vn).get_addr().clone();
            if !same_space_ref(addr.get_space(), &space) {
                continue;
            }
            if !data.get_func_proto().get_param_range(glb).in_range(&addr, 1) {
                continue;
            }
            let mut endpoint = addr
                .get_offset()
                .wrapping_add(data.vn(vn).get_size() as i64 as u64)
                .wrapping_sub(1);
            while pos < inputs.len() {
                vn = inputs[pos];
                let varnode = data.vn(vn);
                if !same_space_ref(varnode.get_space(), &space) {
                    break;
                }
                if endpoint < varnode.get_offset() {
                    break;
                }
                let newendpoint = varnode
                    .get_offset()
                    .wrapping_add(varnode.get_size() as i64 as u64)
                    .wrapping_sub(1);
                if endpoint < newendpoint {
                    endpoint = newendpoint;
                }
                if varnode.is_type_lock() {
                    locked = true;
                }
                pos += 1;
            }
            if !locked {
                let usepoint = Address::invalid();
                if lockedinputs != 0 {
                    let mut vflags = 0;
                    let varnode = data.vn(vn);
                    let entry = db_ref(glb).scope_query_properties(
                        scope,
                        varnode.get_addr(),
                        varnode.get_size(),
                        &usepoint,
                        &mut vflags,
                    );
                    if let Some(entry) = entry {
                        let db = db_ref(glb);
                        if db.symbol(db.entry(entry).get_symbol()).get_category() == Symbol::FUNCTION_PARAMETER {
                            continue;
                        }
                    }
                }
                let size = endpoint.wrapping_sub(addr.get_offset()).wrapping_add(1) as i32;
                let ct = types_mut(glb).get_base(size, TypeMetatype::Unknown)?;
                match Database::scope_add_symbol_at(glb, scope, "", Some(ct), &addr, &usepoint) {
                    Ok(entry) => {
                        let db = db_mut(glb);
                        let sym = db.entry(entry).get_symbol();
                        db.scope_set_category(scope, sym, Symbol::FAKE_INPUT as i32, -1);
                    }
                    Err(err) if err.is_lowlevel() => {
                        data.warning_header(err.explain(), glb);
                    }
                    Err(err) => return Err(err),
                }
            }
        }
        Ok(())
    }

    pub fn local_add_recommend_name(&mut self, scope: ScopeId, sym: SymbolId) -> Result<()> {
        let entry = self.symbol_get_first_whole_map(sym)?;
        let record = self.entry(entry);
        let symbol = self.symbol(sym);
        if record.is_dynamic() {
            let rec = DynamicRecommend::new(
                &record.get_first_use_address(),
                record.get_hash(),
                symbol.get_name(),
                symbol.get_id(),
            );
            self.scope_mut(scope).local_data_mut().dyn_recommend.push(rec);
        } else {
            let mut usepoint = Address::invalid();
            if !record.get_use_limit().empty() {
                let range = record
                    .get_use_limit()
                    .get_first_range()
                    .expect("use limit is not empty");
                usepoint = Address::new(range.get_space().clone(), range.get_first());
            }
            let rec = NameRecommend::new(
                record.get_addr(),
                &usepoint,
                record.get_size(),
                symbol.get_name(),
                symbol.get_id(),
            );
            self.scope_mut(scope).local_data_mut().name_recommend.push(rec);
        }
        if self.symbol(sym).get_category() < 0 {
            self.scope_remove_symbol(scope, sym);
        }
        Ok(())
    }

    pub fn local_collect_name_recs(&mut self, scope: ScopeId, types: &TypeFactory) -> Result<()> {
        {
            let local = self.scope_mut(scope).local_data_mut();
            local.name_recommend.clear();
            local.dyn_recommend.clear();
        }
        let mut iter: Option<SymbolNameKey> = self.scope(scope).nametree.keys().next().cloned();
        while let Some(key) = iter {
            let sym = self.scope(scope).nametree[&key];
            iter = self
                .scope(scope)
                .nametree
                .range((std::ops::Bound::Excluded(&key), std::ops::Bound::Unbounded))
                .next()
                .map(|(next, _)| next.clone());
            let symbol = self.symbol(sym);
            if symbol.is_name_locked() && !symbol.is_type_locked() {
                if symbol.is_this_pointer() {
                    let dt = symbol.get_type().expect("symbol has a data-type");
                    if types.get(dt).get_metatype() == TypeMetatype::Ptr
                        && types.get(types.get(dt).get_ptr_to()).get_metatype() == TypeMetatype::Struct
                    {
                        let entry = self.symbol_get_first_whole_map(sym)?;
                        if !self.entry(entry).is_dynamic() {
                            let addr = self.entry(entry).get_addr().clone();
                            self.scope_mut(scope)
                                .local_data_mut()
                                .add_type_recommendation(&addr, dt);
                        }
                    }
                }
                self.local_add_recommend_name(scope, sym)?;
            }
        }
        Ok(())
    }

    pub fn local_annotate_raw_stack_ptr(glb: &mut Architecture, data: &mut Funcdata, scope: ScopeId) -> Result<()> {
        if !data.has_type_recovery_started() {
            return Ok(());
        }
        let space = db_ref(glb).local_space(scope);
        let Some(sp_vn) = data.find_spacebase_input(&space)? else {
            return Ok(());
        };
        let mut ref_ops = Vec::new();
        let mut saw_raw = false;
        for &op in data.vn(sp_vn).descend() {
            let pcode = data.op(op);
            if pcode.get_eval_type() == PcodeOp::SPECIAL && !pcode.is_call() {
                continue;
            }
            let opc = pcode.code();
            if opc == OpCode::Ptrsub {
                if data.vn(pcode.get_in(1)).get_offset() == 0 {
                    saw_raw = true;
                }
                continue;
            }
            if opc == OpCode::IntAdd || opc == OpCode::Ptradd {
                continue;
            }
            ref_ops.push(op);
            saw_raw = true;
        }
        if saw_raw {
            let zeroaddr = Address::new(space, 0);
            if db_ref(glb)
                .scope_query_container(scope, &zeroaddr, 1, &Address::invalid())
                .is_none()
            {
                let ct = types_mut(glb).get_base(1, TypeMetatype::Unknown)?;
                Database::scope_add_symbol_at(glb, scope, "", Some(ct), &zeroaddr, &Address::invalid())?;
            }
        }
        for op in ref_ops {
            let slot = data.op(op).get_slot(sp_vn);
            let size = data.vn(sp_vn).get_size();
            let constant = data.new_constant(size, 0, glb);
            let ptrsub = data.new_op_before(op, OpCode::Ptrsub, sp_vn, constant, None, glb)?;
            let out = data.op(ptrsub).get_out().expect("PTRSUB has an output");
            data.op_set_input(op, out, slot)?;
        }
        Ok(())
    }

    pub fn local_check_unaliased_return(glb: &mut Architecture, data: &mut Funcdata, scope: ScopeId, alias: &[u64]) {
        let Some(ret_op) = data.get_first_return_op() else {
            return;
        };
        if data.op(ret_op).num_input() < 2 {
            return;
        }
        let vn = data.op(ret_op).get_in(1);
        let space = db_ref(glb).local_space(scope);
        if !same_space_ref(data.vn(vn).get_space(), &space) {
            return;
        }
        let offset = data.vn(vn).get_offset();
        let size = data.vn(vn).get_size();
        let pos = alias.partition_point(|&val| val < offset);
        if pos < alias.len() && alias[pos] <= offset.wrapping_add(size as i64 as u64).wrapping_sub(1) {
            return;
        }
        Database::local_mark_not_mapped(glb, data, scope, &space, offset, size, false);
    }

    pub fn local_is_unmapped_unaliased(&self, data: &Funcdata, scope: ScopeId, vn: VarnodeId) -> bool {
        let local = self.scope(scope).local_data();
        if !same_space_ref(data.vn(vn).get_space(), &local.space) {
            return false;
        }
        if local.max_param_offset < local.min_param_offset {
            return true;
        }
        let offset = data.vn(vn).get_offset();
        offset < local.min_param_offset || offset > local.max_param_offset
    }

    pub fn local_mark_not_mapped(
        glb: &mut Architecture,
        data: &mut Funcdata,
        scope: ScopeId,
        spc: &SpaceRef,
        first: u64,
        sz: i32,
        param: bool,
    ) {
        let space = db_ref(glb).local_space(scope);
        if space.get_index() != spc.get_index() {
            return;
        }
        let mut last = first.wrapping_add(sz as i64 as u64).wrapping_sub(1);
        if last < first || last > spc.get_highest() {
            last = spc.get_highest();
        }
        if param {
            let local = db_mut(glb).scope_mut(scope).local_data_mut();
            if first < local.min_param_offset {
                local.min_param_offset = first;
            }
            if last > local.max_param_offset {
                local.max_param_offset = last;
            }
        }
        let addr = Address::new(space.clone(), first);
        let mut overlap = db_ref(glb).scope_find_overlap(scope, &addr, sz);
        while let Some(entry) = overlap {
            let db = db_ref(glb);
            let sym = db.entry(entry).get_symbol();
            let symbol = db.symbol(sym);
            if (symbol.get_flags() & Varnode::TYPELOCK) != 0 {
                if !param || symbol.get_category() != Symbol::FUNCTION_PARAMETER {
                    let message = format!("Variable defined which should be unmapped: {}", symbol.get_name());
                    data.warning_header(&message, glb);
                }
                return;
            } else if symbol.get_category() == Symbol::FAKE_INPUT {
                return;
            }
            let db = db_mut(glb);
            db.scope_remove_symbol(scope, sym);
            overlap = db.scope_find_overlap(scope, &addr, sz);
        }
        db_mut(glb).remove_range(scope, &space, first, last);
    }

    pub fn local_encode(glb: &Architecture, scope: ScopeId, encoder: &mut dyn Encoder) -> Result<()> {
        let local = db_ref(glb).scope(scope).local_data();
        encoder.open_element(ELEM_LOCALDB);
        encoder.write_space(ATTRIB_MAIN, &local.space);
        encoder.write_bool(ATTRIB_LOCK, local.range_locked);
        Database::scope_encode_internal(glb, scope, encoder)?;
        encoder.close_element(ELEM_LOCALDB);
        Ok(())
    }

    pub fn local_decode(glb: &mut Architecture, scope: ScopeId, decoder: &mut dyn Decoder) -> Result<()> {
        Database::scope_decode_internal(glb, scope, decoder)?;
        let (db, types) = db_and_types(glb);
        db.local_collect_name_recs(scope, types)
    }

    pub fn local_decode_wrapping_attributes(
        glb: &mut Architecture,
        scope: ScopeId,
        decoder: &mut dyn Decoder,
    ) -> Result<()> {
        let local = db_mut(glb).scope_mut(scope).local_data_mut();
        local.range_locked = false;
        if decoder.read_bool_attr(ATTRIB_LOCK)? {
            local.range_locked = true;
        }
        local.space = decoder.read_space_attr(ATTRIB_MAIN)?;
        Ok(())
    }

    #[allow(clippy::too_many_arguments)]
    pub fn local_build_variable_name(
        glb: &Architecture,
        data: Option<&Funcdata>,
        scope: ScopeId,
        addr: &Address,
        pc: &Address,
        ct: Option<TypeId>,
        index: &mut i32,
        flags: u32,
    ) -> Result<String> {
        let db = db_ref(glb);
        let local = db.scope(scope).local_data();
        let space = &local.space;
        if (flags & (Varnode::ADDRTIED | Varnode::PERSIST)) == Varnode::ADDRTIED
            && same_space_ref(addr.get_space(), space)
        {
            let data =
                data.ok_or_else(|| Error::Lowlevel("local scope variable naming requires its function".to_string()))?;
            if data.get_func_proto().get_local_range(glb).in_range(addr, 1) {
                let mut start = AddrSpace::byte_to_address(addr.get_offset(), space.get_word_size()) as i64;
                start = sign_extend(start, addr.get_addr_size() * 8 - 1);
                if local.stack_grows_negative {
                    start = start.wrapping_neg();
                }
                let mut text = String::new();
                if let Some(ct) = ct {
                    let types = types_ref(glb);
                    types.get(ct).print_name_base(&mut text, types);
                }
                let spacename = addr.get_space().expect("address has a space").get_name();
                let mut capitalized = spacename.to_string();
                if let Some(first) = capitalized.get_mut(0..1) {
                    first.make_ascii_uppercase();
                }
                text.push_str(&capitalized);
                if start <= 0 {
                    text.push('X');
                    start = start.wrapping_neg();
                } else if local.min_param_offset < local.max_param_offset
                    && (if local.stack_grows_negative {
                        addr.get_offset() < local.min_param_offset
                    } else {
                        addr.get_offset() > local.max_param_offset
                    })
                {
                    text.push('Y');
                }
                text.push_str(&format!("_{:x}", start));
                return db.scope_make_name_unique(scope, &text);
            }
        }
        let _ = pc;
        Database::scope_build_variable_name_internal(glb, scope, addr, ct, index, flags)
    }

    pub fn local_reset_local_window(glb: &mut Architecture, data: &mut Funcdata, scope: ScopeId) {
        let proto = data.get_func_proto();
        let stack_grows_negative = proto.is_stack_grows_negative(glb);
        let mut newrange = RangeList::new();
        for rng in proto.get_local_range(glb).iter() {
            newrange.insert_range(rng.get_space(), rng.get_first(), rng.get_last());
        }
        for rng in proto.get_param_range(glb).iter() {
            newrange.insert_range(rng.get_space(), rng.get_first(), rng.get_last());
        }
        let db = db_mut(glb);
        let local = db.scope_mut(scope).local_data_mut();
        local.stack_grows_negative = stack_grows_negative;
        local.min_param_offset = !0u64;
        local.max_param_offset = 0;
        if local.range_locked {
            return;
        }
        db.set_range(scope, &newrange);
    }

    pub fn local_restructure_varnode(
        glb: &mut Architecture,
        data: &mut Funcdata,
        scope: ScopeId,
        aliasyes: bool,
    ) -> Result<()> {
        {
            let (db, types) = db_and_types(glb);
            db.scope_clear_unlocked_category(scope, -1, types)?;
        }
        let space = db_ref(glb).local_space(scope);
        let rangetree = db_ref(glb).scope(scope).get_range_tree().clone();
        let param_range = data.get_func_proto().get_param_range(glb).clone();
        let default_type = types_mut(glb).get_base(1, TypeMetatype::Unknown)?;
        let mut state = MapState::new(&space, &rangetree, &param_range, Some(default_type));
        if db_ref(glb).scope(scope).debugon {
            state.turn_on_debug();
        }
        state.gather_varnodes(glb, data)?;
        state.gather_open(glb, data)?;
        {
            let db = db_ref(glb);
            let rangemap = db
                .scope(scope)
                .maptable
                .get(space.get_index() as usize)
                .and_then(|slot| slot.as_deref());
            state.gather_symbols(db, rangemap, types_ref(glb));
        }
        let open_param_refs = state.has_param_range_hit();
        db_mut(glb).scope_mut(scope).local_data_mut().open_param_refs = open_param_refs;
        let overlap_problems = Database::local_restructure(glb, scope, &mut state)?;
        db_mut(glb).scope_mut(scope).local_data_mut().overlap_problems = overlap_problems;
        {
            let (db, types) = db_and_types(glb);
            db.scope_clear_unlocked_category(scope, Symbol::FUNCTION_PARAMETER as i32, types)?;
            db.scope_clear_category(scope, Symbol::FAKE_INPUT as i32);
        }
        Database::local_fake_input_symbols(glb, data, scope)?;
        state.sort_alias();
        let alias = state.get_alias().clone();
        if aliasyes {
            Database::local_mark_unaliased(glb, scope, &alias);
            Database::local_check_unaliased_return(glb, data, scope, &alias);
        }
        if !alias.is_empty() && alias[0] == 0 {
            Database::local_annotate_raw_stack_ptr(glb, data, scope)?;
        }
        Ok(())
    }

    pub fn local_remap_symbol(
        &mut self,
        scope: ScopeId,
        sym: SymbolId,
        addr: &Address,
        usepoint: &Address,
        types: &TypeFactory,
    ) -> Result<EntryId> {
        let entry = self.symbol_get_first_whole_map(sym)?;
        let record = self.entry(entry);
        let size = record.get_size();
        if !record.is_dynamic() && record.get_addr() == addr {
            if usepoint.is_invalid() && record.get_first_use_address().is_invalid() {
                return Ok(entry);
            }
            if record.get_first_use_address() == *usepoint {
                return Ok(entry);
            }
        }
        self.scope_remove_symbol_mappings(scope, sym);
        let rnglist = Database::usepoint_range_list(usepoint);
        let res = self
            .entries
            .alloc(SymbolEntry::new_map(sym, Varnode::MAPPED, addr, size, 0, &rnglist));
        self.scope_add_map_internal(scope, sym, res, types)?;
        Ok(res)
    }

    fn usepoint_range_list(usepoint: &Address) -> RangeList {
        let mut rnglist = RangeList::new();
        if !usepoint.is_invalid() {
            let spc = usepoint.get_space().expect("valid usepoint has a space");
            rnglist.insert_range(spc, usepoint.get_offset(), usepoint.get_offset());
        }
        rnglist
    }

    pub fn local_remap_symbol_dynamic(
        &mut self,
        scope: ScopeId,
        sym: SymbolId,
        hash: u64,
        usepoint: &Address,
        types: &TypeFactory,
    ) -> Result<EntryId> {
        let entry = self.symbol_get_first_whole_map(sym)?;
        let record = self.entry(entry);
        let size = record.get_size();
        if record.is_dynamic() && record.get_hash() == hash && record.get_first_use_address() == *usepoint {
            return Ok(entry);
        }
        self.scope_remove_symbol_mappings(scope, sym);
        let rnglist = Database::usepoint_range_list(usepoint);
        let new_entry = self
            .entries
            .alloc(SymbolEntry::new_dynamic(sym, Varnode::MAPPED, hash, 0, size, &rnglist));
        self.scope_add_dynamic_map_internal(scope, sym, new_entry, types);
        Ok(new_entry)
    }

    fn local_apply_name_recommendation(
        glb: &mut Architecture,
        scope: ScopeId,
        sym: SymbolId,
        name: &str,
        symbol_id: u64,
    ) -> Result<()> {
        let (db, types) = db_and_types(glb);
        let newname = db.scope_make_name_unique(scope, name)?;
        db.scope_rename_symbol(scope, sym, &newname)?;
        db.scope_set_symbol_id(sym, symbol_id);
        db.scope_set_attribute(types, scope, sym, Varnode::NAMELOCK);
        Ok(())
    }

    pub fn local_recover_name_recommendations_for_symbols(
        glb: &mut Architecture,
        data: &mut Funcdata,
        scope: ScopeId,
    ) -> Result<()> {
        let param_usepoint = data.get_address().sub(1);
        let name_recommend = db_ref(glb).scope(scope).local_data().name_recommend.clone();
        for rec in name_recommend.iter() {
            let addr = rec.get_addr();
            let usepoint = rec.get_use_addr();
            let size = rec.get_size();
            let sym: SymbolId;
            let vn: Option<VarnodeId>;
            if usepoint.is_invalid() {
                let db = db_ref(glb);
                let Some(entry) = db.scope_find_overlap(scope, addr, size) else {
                    continue;
                };
                if db.entry(entry).get_addr() != addr {
                    continue;
                }
                sym = db.entry(entry).get_symbol();
                if (db.symbol(sym).get_flags() & Varnode::ADDRTIED) == 0 {
                    continue;
                }
                vn = data.find_linked_varnode(entry, glb);
            } else {
                vn = if *usepoint == param_usepoint {
                    data.find_varnode_input(size, addr)
                } else {
                    data.find_varnode_written(size, addr, usepoint, u32::MAX)
                };
                let Some(found) = vn else {
                    continue;
                };
                let high = data.vn(found).get_high()?;
                let Some(found_sym) = data.high_get_symbol(high, glb) else {
                    continue;
                };
                sym = found_sym;
                let db = db_ref(glb);
                if (db.symbol(sym).get_flags() & Varnode::ADDRTIED) != 0 {
                    continue;
                }
                let entry = db.symbol_get_first_whole_map(sym)?;
                if db.entry(entry).get_size() != size {
                    continue;
                }
            }
            if !db_ref(glb).symbol(sym).is_name_undefined() {
                continue;
            }
            Database::local_apply_name_recommendation(glb, scope, sym, &rec.get_name(), rec.get_symbol_id())?;
            if let Some(vn) = vn {
                data.remap_varnode(vn, sym, usepoint, glb)?;
            }
        }
        let dyn_recommend = db_ref(glb).scope(scope).local_data().dyn_recommend.clone();
        if dyn_recommend.is_empty() {
            return Ok(());
        }
        let mut dhash = DynamicHash::new();
        for dyn_entry in dyn_recommend.iter() {
            dhash.clear();
            let Some(vn) = dhash.find_varnode(data, dyn_entry.get_address(), dyn_entry.get_hash()) else {
                continue;
            };
            if data.vn(vn).is_annotation() {
                continue;
            }
            let high = data.vn(vn).get_high()?;
            let Some(sym) = data.high_get_symbol(high, glb) else {
                continue;
            };
            let db = db_ref(glb);
            if db.symbol(sym).get_scope() != scope {
                continue;
            }
            if !db.symbol(sym).is_name_undefined() {
                continue;
            }
            let (db, types) = db_and_types(glb);
            let newname = db.scope_make_name_unique(scope, &dyn_entry.get_name())?;
            db.scope_rename_symbol(scope, sym, &newname)?;
            db.scope_set_attribute(types, scope, sym, Varnode::NAMELOCK);
            db.scope_set_symbol_id(sym, dyn_entry.get_symbol_id());
            data.remap_dynamic_varnode(vn, sym, dyn_entry.get_address(), dyn_entry.get_hash(), glb)?;
        }
        Ok(())
    }

    pub fn local_apply_type_recommendations(glb: &mut Architecture, data: &mut Funcdata, scope: ScopeId) -> Result<()> {
        let recommendations = db_ref(glb).scope(scope).local_data().type_recommend.clone();
        for rec in recommendations.iter() {
            let dt = rec.get_type();
            let size = types_ref(glb).get(dt).get_size();
            if let Some(vn) = data.find_varnode_input(size, rec.get_address()) {
                data.vn_update_type_locked(vn, dt, true, false, glb);
            }
        }
        Ok(())
    }
}
