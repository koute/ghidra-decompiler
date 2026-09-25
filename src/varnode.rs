use std::fmt::Write;
use std::ops::Bound;

use crate::address::{
    Address, AddressKey, ELEM_ADDR, MachExtreme, SeqKey, SeqNum, calc_mask, sign_extend_size, signbit_negative,
};
use crate::architecture::Architecture;
use crate::arena::Arena;
use crate::cover::Cover;
use crate::database::{ATTRIB_VOLATILE, Database, EntryId, SymbolKind};
use crate::define_id;
use crate::error::{Error, Result};
use crate::fspec::{CallSpecId, FspecSpace, FuncCallSpecs};
use crate::funcdata::Funcdata;
use crate::marshal::{ATTRIB_REF, AttributeId, Encoder};
use crate::op::{OpId, PcodeOp, iop_space_encode_attributes_size, iop_space_print_raw};
use crate::opcodes::OpCode;
use crate::orderedindex::OrderedIndex;
use crate::space::{SpaceRef, SpaceType};
use crate::translate::{AddrSpaceManager, Translate, UniqueLayout};
use crate::types::{Datatype, TypeFactory, TypeId, TypeMetatype};
use crate::variable::{HighId, HighVariable};

pub const ATTRIB_ADDRTIED: AttributeId = AttributeId::new("addrtied", 30);
pub const ATTRIB_GRP: AttributeId = AttributeId::new("grp", 31);
pub const ATTRIB_INPUT: AttributeId = AttributeId::new("input", 32);
pub const ATTRIB_PERSISTS: AttributeId = AttributeId::new("persists", 33);
pub const ATTRIB_UNAFF: AttributeId = AttributeId::new("unaff", 34);

define_id!(VarnodeId);

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct LocKey {
    pub addr: AddressKey,
    pub size: i32,
    pub class: u32,
    pub seq: Option<SeqKey>,
    pub create_index: u32,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct DefKey {
    pub class: u32,
    pub seq: Option<SeqKey>,
    pub addr: AddressKey,
    pub size: i32,
    pub create_index: u32,
}

pub type LocIter = Option<LocKey>;

pub type DefIter = Option<DefKey>;

pub fn flag_class(flags: u32) -> u32 {
    (flags & (Varnode::INPUT | Varnode::WRITTEN)).wrapping_sub(1)
}

const INPUT_CLASS: u32 = Varnode::INPUT - 1;
const WRITTEN_CLASS: u32 = Varnode::WRITTEN - 1;
const FREE_CLASS: u32 = u32::MAX;

fn loc_search(addr: &Address, size: i32, class: u32, seq: Option<SeqNum>) -> LocKey {
    LocKey {
        addr: addr.ordering_key(),
        size,
        class,
        seq: seq.map(|seq| seq.ordering_key()),
        create_index: 0,
    }
}

fn def_search(class: u32, seq: Option<SeqNum>, addr: &Address, size: i32) -> DefKey {
    DefKey {
        class,
        seq: seq.map(|seq| seq.ordering_key()),
        addr: addr.ordering_key(),
        size,
        create_index: 0,
    }
}

fn same_space(first: &Address, second: &Address) -> bool {
    match (first.get_space(), second.get_space()) {
        (None, None) => true,
        (Some(spc), Some(other)) => spc.get_index() == other.get_index(),
        _ => false,
    }
}

fn is_constant_space(addr: &Address) -> bool {
    addr.get_space()
        .map(|spc| spc.get_type() == SpaceType::Constant)
        .unwrap_or(false)
}

fn type_factory(glb: &Architecture) -> &TypeFactory {
    glb.types.as_deref().expect("architecture has no type factory")
}

fn symbol_table(glb: &Architecture) -> &Database {
    glb.symboltab.as_deref().expect("architecture has no symbol table")
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Default)]
pub enum VarnodeTemp {
    #[default]
    Empty,
    DataType(TypeId),
    ValueSet(usize),
}

pub struct Varnode {
    pub(crate) flags: u32,
    pub(crate) size: i32,
    pub(crate) create_index: u32,
    pub(crate) mergegroup: i16,
    pub(crate) addlflags: u16,
    pub(crate) loc: Address,
    pub(crate) def: Option<OpId>,
    pub(crate) high: Option<HighId>,
    pub(crate) mapentry: Option<EntryId>,
    pub(crate) tp: TypeId,
    pub(crate) lociter: Option<LocKey>,
    pub(crate) defiter: Option<DefKey>,
    pub(crate) descend: Vec<OpId>,
    pub(crate) cover: Option<Box<Cover>>,
    pub(crate) temp: VarnodeTemp,
    pub(crate) consumed: u64,
    pub(crate) nzm: u64,
}

impl Varnode {
    pub const MARK: u32 = 0x01;
    pub const CONSTANT: u32 = 0x02;
    pub const ANNOTATION: u32 = 0x04;
    pub const INPUT: u32 = 0x08;
    pub const WRITTEN: u32 = 0x10;
    pub const INSERT: u32 = 0x20;
    pub const IMPLIED: u32 = 0x40;
    pub const EXPLICT: u32 = 0x80;
    pub const TYPELOCK: u32 = 0x100;
    pub const NAMELOCK: u32 = 0x200;
    pub const NOLOCALALIAS: u32 = 0x400;
    pub const VOLATIL: u32 = 0x800;
    pub const EXTERNREF: u32 = 0x1000;
    pub const READONLY: u32 = 0x2000;
    pub const PERSIST: u32 = 0x4000;
    pub const ADDRTIED: u32 = 0x8000;
    pub const UNAFFECTED: u32 = 0x10000;
    pub const SPACEBASE: u32 = 0x20000;
    pub const INDIRECTONLY: u32 = 0x40000;
    pub const DIRECTWRITE: u32 = 0x80000;
    pub const ADDRFORCE: u32 = 0x100000;
    pub const MAPPED: u32 = 0x200000;
    pub const INDIRECT_CREATION: u32 = 0x400000;
    pub const RETURN_ADDRESS: u32 = 0x800000;
    pub const COVERDIRTY: u32 = 0x1000000;
    pub const PRECISLO: u32 = 0x2000000;
    pub const PRECISHI: u32 = 0x4000000;
    pub const INDIRECTSTORAGE: u32 = 0x8000000;
    pub const HIDDENRETPARM: u32 = 0x10000000;
    pub const INCIDENTAL_COPY: u32 = 0x20000000;
    pub const AUTOLIVE_HOLD: u32 = 0x40000000;
    pub const PROTO_PARTIAL: u32 = 0x80000000;

    pub const ACTIVEHERITAGE: u16 = 0x01;
    pub const WRITEMASK: u16 = 0x02;
    pub const VACCONSUME: u16 = 0x04;
    pub const LISCONSUME: u16 = 0x08;
    pub const SYMCHECK_INCOMPLETE: u16 = 0x20;
    pub const SYMCHECK_COMPLETE: u16 = 0x30;
    pub const PTRFLOW: u16 = 0x40;
    pub const UNSIGNEDPRINT: u16 = 0x80;
    pub const LONGPRINT: u16 = 0x100;
    pub const STACK_STORE: u16 = 0x200;
    pub const LOCKED_INPUT: u16 = 0x400;
    pub const SPACEBASE_PLACEHOLDER: u16 = 0x800;
    pub const STOP_UPPROPAGATION: u16 = 0x1000;
    pub const HAS_IMPLIED_FIELD: u16 = 0x2000;

    pub fn new(size: i32, addr: &Address, dt: TypeId) -> Varnode {
        let (flags, nzm) = match addr.get_space() {
            None => (0, u64::MAX),
            Some(spc) => match spc.get_type() {
                SpaceType::Constant => (Varnode::CONSTANT, addr.get_offset()),
                SpaceType::Fspec | SpaceType::Iop => (Varnode::ANNOTATION | Varnode::COVERDIRTY, u64::MAX),
                _ => (Varnode::COVERDIRTY, u64::MAX),
            },
        };
        Varnode {
            flags,
            size,
            create_index: 0,
            mergegroup: 0,
            addlflags: 0,
            loc: addr.clone(),
            def: None,
            high: None,
            mapentry: None,
            tp: dt,
            lociter: None,
            defiter: None,
            descend: Vec::new(),
            cover: None,
            temp: VarnodeTemp::Empty,
            consumed: u64::MAX,
            nzm,
        }
    }

    pub fn loc_key(&self, ops: &Arena<OpId, PcodeOp>) -> LocKey {
        let class = flag_class(self.flags);
        let seq = if (self.flags & (Varnode::INPUT | Varnode::WRITTEN)) == Varnode::WRITTEN {
            self.def.map(|op| ops.get(op).get_seq_num().ordering_key())
        } else {
            None
        };
        let create_index = if (self.flags & (Varnode::INPUT | Varnode::WRITTEN)) == 0 {
            self.create_index
        } else {
            0
        };
        LocKey {
            addr: self.loc.ordering_key(),
            size: self.size,
            class,
            seq,
            create_index,
        }
    }

    pub fn def_key(&self, ops: &Arena<OpId, PcodeOp>) -> DefKey {
        let LocKey {
            addr,
            size,
            class,
            seq,
            create_index,
        } = self.loc_key(ops);
        DefKey {
            class,
            seq,
            addr,
            size,
            create_index,
        }
    }

    pub fn set_high(&mut self, tv: Option<HighId>, mg: i16) {
        self.high = tv;
        self.mergegroup = mg;
    }

    pub fn get_addr(&self) -> &Address {
        &self.loc
    }

    pub fn get_space(&self) -> Option<&SpaceRef> {
        self.loc.get_space()
    }

    pub fn get_space_from_const(&self, manager: &AddrSpaceManager) -> Option<SpaceRef> {
        manager.get_space(self.loc.get_offset() as i32)
    }

    pub fn get_offset(&self) -> u64 {
        self.loc.get_offset()
    }

    pub fn get_size(&self) -> i32 {
        self.size
    }

    pub fn get_merge_group(&self) -> i16 {
        self.mergegroup
    }

    pub fn get_def(&self) -> Option<OpId> {
        self.def
    }

    pub fn get_high(&self) -> Result<HighId> {
        self.high
            .ok_or_else(|| Error::Lowlevel("Requesting non-existent high-level".to_string()))
    }

    pub fn get_high_option(&self) -> Option<HighId> {
        self.high
    }

    pub fn get_symbol_entry(&self) -> Option<EntryId> {
        self.mapentry
    }

    pub fn get_flags(&self) -> u32 {
        self.flags
    }

    pub fn get_type(&self) -> TypeId {
        self.tp
    }

    pub fn set_temp_type(&mut self, tp: Option<TypeId>) {
        self.temp = match tp {
            Some(tp) => VarnodeTemp::DataType(tp),
            None => VarnodeTemp::Empty,
        };
    }

    pub fn get_temp_type(&self) -> Option<TypeId> {
        match self.temp {
            VarnodeTemp::DataType(tp) => Some(tp),
            _ => None,
        }
    }

    pub fn set_value_set(&mut self, value_set: Option<usize>) {
        self.temp = match value_set {
            Some(index) => VarnodeTemp::ValueSet(index),
            None => VarnodeTemp::Empty,
        };
    }

    pub fn get_value_set(&self) -> Option<usize> {
        match self.temp {
            VarnodeTemp::ValueSet(index) => Some(index),
            _ => None,
        }
    }

    pub fn get_create_index(&self) -> u32 {
        self.create_index
    }

    pub fn get_cover_raw(&self) -> Option<&Cover> {
        self.cover.as_deref()
    }

    pub fn descend(&self) -> &[OpId] {
        &self.descend
    }

    pub fn get_consume(&self) -> u64 {
        self.consumed
    }

    pub fn set_consume(&mut self, val: u64) {
        self.consumed = val;
    }

    pub fn is_consume_list(&self) -> bool {
        (self.addlflags & Varnode::LISCONSUME) != 0
    }

    pub fn is_consume_vacuous(&self) -> bool {
        (self.addlflags & Varnode::VACCONSUME) != 0
    }

    pub fn set_consume_list(&mut self) {
        self.addlflags |= Varnode::LISCONSUME;
    }

    pub fn set_consume_vacuous(&mut self) {
        self.addlflags |= Varnode::VACCONSUME;
    }

    pub fn clear_consume_list(&mut self) {
        self.addlflags &= !Varnode::LISCONSUME;
    }

    pub fn clear_consume_vacuous(&mut self) {
        self.addlflags &= !Varnode::VACCONSUME;
    }

    pub fn lone_descend(&self) -> Option<OpId> {
        if self.descend.len() == 1 {
            return Some(self.descend[0]);
        }
        None
    }

    pub fn print_raw_no_markup(&self, out: &mut String, trans: &dyn Translate, data: &Funcdata) -> i32 {
        self.print_raw_no_markup_radix(out, trans, data).0
    }

    fn print_raw_no_markup_radix(&self, out: &mut String, trans: &dyn Translate, data: &Funcdata) -> (i32, bool) {
        let spc = self.loc.get_space().expect("varnode has no address space");
        let name = trans.get_register_name(spc, self.loc.get_offset(), self.size);
        if !name.is_empty() {
            let point = trans.get_register(&name).expect("register name without register");
            let off = self.loc.get_offset().wrapping_sub(point.offset);
            out.push_str(&name);
            if off != 0 {
                let _ = write!(out, "+{}", off);
            }
            return (point.size as i32, false);
        }
        out.push(self.loc.get_shortcut());
        let expect = trans.manager().get_default_size();
        data.print_address_raw(&self.loc, out);
        let leaves_hex = self.loc.print_raw_leaves_hex().unwrap_or(false);
        (expect, leaves_hex)
    }

    pub fn intersects(&self, op: &Varnode) -> bool {
        self.intersects_addr(&op.loc, op.size)
    }

    pub fn intersects_addr(&self, op2loc: &Address, op2size: i32) -> bool {
        if !same_space(&self.loc, op2loc) {
            return false;
        }
        if is_constant_space(&self.loc) {
            return false;
        }
        let first = self.loc.get_offset();
        let second = op2loc.get_offset();
        if second < first {
            if first >= second.wrapping_add(op2size as u64) {
                return false;
            }
            return true;
        }
        if second >= first.wrapping_add(self.size as u64) {
            return false;
        }
        true
    }

    pub fn contains(&self, op: &Varnode) -> i32 {
        if !same_space(&self.loc, &op.loc) {
            return 3;
        }
        if is_constant_space(&self.loc) {
            return 3;
        }
        let first = self.loc.get_offset();
        let second = op.loc.get_offset();
        if second < first {
            return -1;
        }
        if second >= first.wrapping_add(self.size as u64) {
            return 2;
        }
        if second.wrapping_add(op.size as u64) > first.wrapping_add(self.size as u64) {
            return 1;
        }
        0
    }

    pub fn characterize_overlap(&self, op: &Varnode) -> i32 {
        if !same_space(&self.loc, &op.loc) {
            return 0;
        }
        if self.loc.get_offset() == op.loc.get_offset() {
            return if self.size == op.size { 2 } else { 1 };
        } else if self.loc.get_offset() < op.loc.get_offset() {
            let thisright = self.loc.get_offset().wrapping_add((self.size - 1) as u64);
            return if thisright < op.loc.get_offset() { 0 } else { 1 };
        }
        let opright = op.loc.get_offset().wrapping_add((op.size - 1) as u64);
        if opright < self.loc.get_offset() { 0 } else { 1 }
    }

    pub fn overlap(&self, op: &Varnode) -> i32 {
        self.overlap_addr(&op.loc, op.size)
    }

    pub fn overlap_join(&self, op: &Varnode) -> Result<i32> {
        if !self.loc.is_big_endian() {
            return self.loc.overlap_join(0, &op.loc, op.size);
        }
        let over = self.loc.overlap_join(self.size - 1, &op.loc, op.size)?;
        if over != -1 {
            return Ok(op.size - 1 - over);
        }
        Ok(-1)
    }

    pub fn overlap_addr(&self, op2loc: &Address, op2size: i32) -> i32 {
        if !self.loc.is_big_endian() {
            return self.loc.overlap(0, op2loc, op2size);
        }
        let over = self.loc.overlap(self.size - 1, op2loc, op2size);
        if over != -1 {
            return op2size - 1 - over;
        }
        -1
    }

    pub fn get_nz_mask(&self) -> u64 {
        self.nzm
    }

    pub fn is_annotation(&self) -> bool {
        (self.flags & Varnode::ANNOTATION) != 0
    }

    pub fn is_implied(&self) -> bool {
        (self.flags & Varnode::IMPLIED) != 0
    }

    pub fn is_explicit(&self) -> bool {
        (self.flags & Varnode::EXPLICT) != 0
    }

    pub fn is_constant(&self) -> bool {
        (self.flags & Varnode::CONSTANT) != 0
    }

    pub fn is_free(&self) -> bool {
        (self.flags & (Varnode::WRITTEN | Varnode::INPUT)) == 0
    }

    pub fn is_input(&self) -> bool {
        (self.flags & Varnode::INPUT) != 0
    }

    pub fn is_illegal_input(&self) -> bool {
        (self.flags & (Varnode::INPUT | Varnode::DIRECTWRITE)) == Varnode::INPUT
    }

    pub fn is_indirect_only(&self) -> bool {
        (self.flags & Varnode::INDIRECTONLY) != 0
    }

    pub fn is_external_ref(&self) -> bool {
        (self.flags & Varnode::EXTERNREF) != 0
    }

    pub fn has_action_property(&self) -> bool {
        (self.flags & (Varnode::READONLY | Varnode::VOLATIL)) != 0
    }

    pub fn is_read_only(&self) -> bool {
        (self.flags & Varnode::READONLY) != 0
    }

    pub fn is_volatile(&self) -> bool {
        (self.flags & Varnode::VOLATIL) != 0
    }

    pub fn is_persist(&self) -> bool {
        (self.flags & Varnode::PERSIST) != 0
    }

    pub fn is_direct_write(&self) -> bool {
        (self.flags & Varnode::DIRECTWRITE) != 0
    }

    pub fn is_addr_tied(&self) -> bool {
        (self.flags & (Varnode::ADDRTIED | Varnode::INSERT)) == (Varnode::ADDRTIED | Varnode::INSERT)
    }

    pub fn is_addr_force(&self) -> bool {
        (self.flags & Varnode::ADDRFORCE) != 0
    }

    pub fn is_auto_live(&self) -> bool {
        (self.flags & (Varnode::ADDRFORCE | Varnode::AUTOLIVE_HOLD)) != 0
    }

    pub fn is_auto_live_hold(&self) -> bool {
        (self.flags & Varnode::AUTOLIVE_HOLD) != 0
    }

    pub fn is_mapped(&self) -> bool {
        (self.flags & Varnode::MAPPED) != 0
    }

    pub fn is_unaffected(&self) -> bool {
        (self.flags & Varnode::UNAFFECTED) != 0
    }

    pub fn is_spacebase(&self) -> bool {
        (self.flags & Varnode::SPACEBASE) != 0
    }

    pub fn is_return_address(&self) -> bool {
        (self.flags & Varnode::RETURN_ADDRESS) != 0
    }

    pub fn is_proto_partial(&self) -> bool {
        (self.flags & Varnode::PROTO_PARTIAL) != 0
    }

    pub fn get_symbol_check(&self) -> u32 {
        (self.addlflags & Varnode::SYMCHECK_COMPLETE) as u32
    }

    pub fn is_ptr_flow(&self) -> bool {
        (self.addlflags & Varnode::PTRFLOW) != 0
    }

    pub fn is_spacebase_placeholder(&self) -> bool {
        (self.addlflags & Varnode::SPACEBASE_PLACEHOLDER) != 0
    }

    pub fn has_no_local_alias(&self) -> bool {
        (self.flags & Varnode::NOLOCALALIAS) != 0
    }

    pub fn is_mark(&self) -> bool {
        (self.flags & Varnode::MARK) != 0
    }

    pub fn is_active_heritage(&self) -> bool {
        (self.addlflags & Varnode::ACTIVEHERITAGE) != 0
    }

    pub fn is_stack_store(&self) -> bool {
        (self.addlflags & Varnode::STACK_STORE) != 0
    }

    pub fn is_locked_input(&self) -> bool {
        (self.addlflags & Varnode::LOCKED_INPUT) != 0
    }

    pub fn stops_up_propagation(&self) -> bool {
        (self.addlflags & Varnode::STOP_UPPROPAGATION) != 0
    }

    pub fn has_implied_field(&self) -> bool {
        (self.addlflags & Varnode::HAS_IMPLIED_FIELD) != 0
    }

    pub fn is_indirect_zero(&self) -> bool {
        (self.flags & (Varnode::INDIRECT_CREATION | Varnode::CONSTANT))
            == (Varnode::INDIRECT_CREATION | Varnode::CONSTANT)
    }

    pub fn is_extra_out(&self) -> bool {
        (self.flags & (Varnode::INDIRECT_CREATION | Varnode::ADDRTIED)) == Varnode::INDIRECT_CREATION
    }

    pub fn is_precis_lo(&self) -> bool {
        (self.flags & Varnode::PRECISLO) != 0
    }

    pub fn is_precis_hi(&self) -> bool {
        (self.flags & Varnode::PRECISHI) != 0
    }

    pub fn is_incidental_copy(&self) -> bool {
        (self.flags & Varnode::INCIDENTAL_COPY) != 0
    }

    pub fn is_write_mask(&self) -> bool {
        (self.addlflags & Varnode::WRITEMASK) != 0
    }

    pub fn is_unsigned_print(&self) -> bool {
        (self.addlflags & Varnode::UNSIGNEDPRINT) != 0
    }

    pub fn is_long_print(&self) -> bool {
        (self.addlflags & Varnode::LONGPRINT) != 0
    }

    pub fn is_written(&self) -> bool {
        (self.flags & Varnode::WRITTEN) != 0
    }

    pub fn has_cover(&self) -> bool {
        (self.flags & (Varnode::CONSTANT | Varnode::ANNOTATION | Varnode::INSERT)) == Varnode::INSERT
    }

    pub fn has_no_descend(&self) -> bool {
        self.descend.is_empty()
    }

    pub fn constant_match(&self, val: u64) -> bool {
        if !self.is_constant() {
            return false;
        }
        self.loc.get_offset() == val
    }

    pub fn is_heritage_known(&self) -> bool {
        (self.flags & (Varnode::INSERT | Varnode::CONSTANT | Varnode::ANNOTATION)) != 0
    }

    pub fn is_type_lock(&self) -> bool {
        (self.flags & Varnode::TYPELOCK) != 0
    }

    pub fn is_name_lock(&self) -> bool {
        (self.flags & Varnode::NAMELOCK) != 0
    }

    pub fn set_active_heritage(&mut self) {
        self.addlflags |= Varnode::ACTIVEHERITAGE;
    }

    pub fn clear_active_heritage(&mut self) {
        self.addlflags &= !Varnode::ACTIVEHERITAGE;
    }

    pub fn set_mark(&mut self) {
        self.flags |= Varnode::MARK;
    }

    pub fn clear_mark(&mut self) {
        self.flags &= !Varnode::MARK;
    }

    pub fn set_direct_write(&mut self) {
        self.flags |= Varnode::DIRECTWRITE;
    }

    pub fn clear_direct_write(&mut self) {
        self.flags &= !Varnode::DIRECTWRITE;
    }

    pub fn set_flags(&mut self, fl: u32, highs: &mut Arena<HighId, HighVariable>) {
        self.flags |= fl;
        self.mark_high_dirty(fl, highs);
    }

    pub fn clear_flags(&mut self, fl: u32, highs: &mut Arena<HighId, HighVariable>) {
        self.flags &= !fl;
        self.mark_high_dirty(fl, highs);
    }

    fn mark_high_dirty(&self, fl: u32, highs: &mut Arena<HighId, HighVariable>) {
        if let Some(high) = self.high {
            highs.get_mut(high).flags_dirty();
            if (fl & Varnode::COVERDIRTY) != 0 {
                HighVariable::cover_dirty(highs, high);
            }
        }
    }

    pub fn set_unaffected(&mut self, highs: &mut Arena<HighId, HighVariable>) {
        self.set_flags(Varnode::UNAFFECTED, highs);
    }

    pub fn set_input(&mut self, highs: &mut Arena<HighId, HighVariable>) {
        self.set_flags(Varnode::INPUT | Varnode::COVERDIRTY, highs);
    }

    pub fn set_def(&mut self, op: Option<OpId>, highs: &mut Arena<HighId, HighVariable>) {
        self.def = op;
        if op.is_none() {
            self.set_flags(Varnode::COVERDIRTY, highs);
            self.clear_flags(Varnode::WRITTEN, highs);
        } else {
            self.set_flags(Varnode::COVERDIRTY | Varnode::WRITTEN, highs);
        }
    }

    pub fn add_descend(&mut self, op: OpId, highs: &mut Arena<HighId, HighVariable>) -> Result<()> {
        if self.is_free() && !self.is_spacebase() && !self.descend.is_empty() {
            return Err(Error::Lowlevel("Free varnode has multiple descendants".to_string()));
        }
        self.descend.push(op);
        self.set_flags(Varnode::COVERDIRTY, highs);
        Ok(())
    }

    pub fn erase_descend(&mut self, op: OpId, highs: &mut Arena<HighId, HighVariable>) {
        let position = self
            .descend
            .iter()
            .position(|reader| *reader == op)
            .expect("op is not a descendant of varnode");
        self.descend.remove(position);
        self.set_flags(Varnode::COVERDIRTY, highs);
    }

    pub fn destroy_descend(&mut self) {
        self.descend.clear();
    }

    pub fn clear_cover(&mut self) {
        self.cover = None;
    }

    pub fn calc_cover(&mut self, highs: &mut Arena<HighId, HighVariable>) {
        if self.has_cover() {
            self.cover = Some(Box::new(Cover::new()));
            self.set_flags(Varnode::COVERDIRTY, highs);
        }
    }

    pub fn set_addr_force(&mut self, highs: &mut Arena<HighId, HighVariable>) {
        self.set_flags(Varnode::ADDRFORCE, highs);
    }

    pub fn clear_addr_force(&mut self, highs: &mut Arena<HighId, HighVariable>) {
        self.clear_flags(Varnode::ADDRFORCE, highs);
    }

    pub fn set_implied(&mut self, highs: &mut Arena<HighId, HighVariable>) {
        self.set_flags(Varnode::IMPLIED, highs);
    }

    pub fn clear_implied(&mut self, highs: &mut Arena<HighId, HighVariable>) {
        self.clear_flags(Varnode::IMPLIED, highs);
    }

    pub fn set_explicit(&mut self, highs: &mut Arena<HighId, HighVariable>) {
        self.set_flags(Varnode::EXPLICT, highs);
    }

    pub fn clear_explicit(&mut self, highs: &mut Arena<HighId, HighVariable>) {
        self.clear_flags(Varnode::EXPLICT, highs);
    }

    pub fn set_return_address(&mut self) {
        self.flags |= Varnode::RETURN_ADDRESS;
    }

    pub fn clear_return_address(&mut self) {
        self.flags &= !Varnode::RETURN_ADDRESS;
    }

    pub fn set_symbol_check(&mut self, val: u32) {
        self.addlflags = (self.addlflags & !Varnode::SYMCHECK_COMPLETE) | ((val as u16) & Varnode::SYMCHECK_COMPLETE);
    }

    pub fn set_ptr_flow(&mut self) {
        self.addlflags |= Varnode::PTRFLOW;
    }

    pub fn clear_ptr_flow(&mut self) {
        self.addlflags &= !Varnode::PTRFLOW;
    }

    pub fn set_spacebase_placeholder(&mut self) {
        self.addlflags |= Varnode::SPACEBASE_PLACEHOLDER;
    }

    pub fn clear_spacebase_placeholder(&mut self) {
        self.addlflags &= !Varnode::SPACEBASE_PLACEHOLDER;
    }

    pub fn set_precis_lo(&mut self, highs: &mut Arena<HighId, HighVariable>) {
        self.set_flags(Varnode::PRECISLO, highs);
    }

    pub fn clear_precis_lo(&mut self, highs: &mut Arena<HighId, HighVariable>) {
        self.clear_flags(Varnode::PRECISLO, highs);
    }

    pub fn set_precis_hi(&mut self, highs: &mut Arena<HighId, HighVariable>) {
        self.set_flags(Varnode::PRECISHI, highs);
    }

    pub fn clear_precis_hi(&mut self, highs: &mut Arena<HighId, HighVariable>) {
        self.clear_flags(Varnode::PRECISHI, highs);
    }

    pub fn set_write_mask(&mut self) {
        self.addlflags |= Varnode::WRITEMASK;
    }

    pub fn clear_write_mask(&mut self) {
        self.addlflags &= !Varnode::WRITEMASK;
    }

    pub fn set_auto_live_hold(&mut self) {
        self.flags |= Varnode::AUTOLIVE_HOLD;
    }

    pub fn clear_auto_live_hold(&mut self) {
        self.flags &= !Varnode::AUTOLIVE_HOLD;
    }

    pub fn set_proto_partial(&mut self) {
        self.flags |= Varnode::PROTO_PARTIAL;
    }

    pub fn clear_proto_partial(&mut self) {
        self.flags &= !Varnode::PROTO_PARTIAL;
    }

    pub fn set_unsigned_print(&mut self) {
        self.addlflags |= Varnode::UNSIGNEDPRINT;
    }

    pub fn set_long_print(&mut self) {
        self.addlflags |= Varnode::LONGPRINT;
    }

    pub fn set_stop_up_propagation(&mut self) {
        self.addlflags |= Varnode::STOP_UPPROPAGATION;
    }

    pub fn clear_stop_up_propagation(&mut self) {
        self.addlflags &= !Varnode::STOP_UPPROPAGATION;
    }

    pub fn set_implied_field(&mut self) {
        self.addlflags |= Varnode::HAS_IMPLIED_FIELD;
    }

    pub fn set_stack_store(&mut self) {
        self.addlflags |= Varnode::STACK_STORE;
    }

    pub fn set_locked_input(&mut self) {
        self.addlflags |= Varnode::LOCKED_INPUT;
    }

    pub fn encode(&self, encoder: &mut dyn Encoder, data: &Funcdata) -> Result<()> {
        encoder.open_element(ELEM_ADDR);
        let spc = self.loc.get_space().expect("varnode has no address space");
        match spc.get_type() {
            SpaceType::Iop => iop_space_encode_attributes_size(encoder, self.loc.get_offset(), self.size)?,
            SpaceType::Fspec => {
                let fc = data.call_spec(FuncCallSpecs::get_fspec_from_const(&self.loc));
                FspecSpace::encode_attributes_size(fc, encoder, self.size)?
            }
            _ => spc.encode_attributes_size(encoder, self.loc.get_offset(), self.size)?,
        }
        encoder.write_unsigned_integer(ATTRIB_REF, self.get_create_index() as u64);
        if self.mergegroup != 0 {
            encoder.write_signed_integer(ATTRIB_GRP, self.get_merge_group() as i64);
        }
        if self.is_persist() {
            encoder.write_bool(ATTRIB_PERSISTS, true);
        }
        if self.is_addr_tied() {
            encoder.write_bool(ATTRIB_ADDRTIED, true);
        }
        if self.is_unaffected() {
            encoder.write_bool(ATTRIB_UNAFF, true);
        }
        if self.is_input() {
            encoder.write_bool(ATTRIB_INPUT, true);
        }
        if self.is_volatile() {
            encoder.write_bool(ATTRIB_VOLATILE, true);
        }
        encoder.close_element(ELEM_ADDR);
        Ok(())
    }
}

impl Funcdata {
    pub fn vn_less(&self, vn: VarnodeId, op2: VarnodeId) -> bool {
        let first = self.vn(vn);
        let second = self.vn(op2);
        if first.loc != second.loc {
            return first.loc < second.loc;
        }
        if first.size != second.size {
            return first.size < second.size;
        }
        let f1 = first.flags & (Varnode::INPUT | Varnode::WRITTEN);
        let f2 = second.flags & (Varnode::INPUT | Varnode::WRITTEN);
        if f1 != f2 {
            return f1.wrapping_sub(1) < f2.wrapping_sub(1);
        }
        if f1 == Varnode::WRITTEN {
            let first_seq = self.op(first.def.expect("written varnode has no def")).get_seq_num();
            let second_seq = self.op(second.def.expect("written varnode has no def")).get_seq_num();
            if first_seq != second_seq {
                return first_seq < second_seq;
            }
        }
        false
    }

    pub fn vn_equal(&self, vn: VarnodeId, op2: VarnodeId) -> bool {
        let first = self.vn(vn);
        let second = self.vn(op2);
        if first.loc != second.loc {
            return false;
        }
        if first.size != second.size {
            return false;
        }
        let f1 = first.flags & (Varnode::INPUT | Varnode::WRITTEN);
        let f2 = second.flags & (Varnode::INPUT | Varnode::WRITTEN);
        if f1 != f2 {
            return false;
        }
        if f1 == Varnode::WRITTEN {
            let first_seq = self.op(first.def.expect("written varnode has no def")).get_seq_num();
            let second_seq = self.op(second.def.expect("written varnode has no def")).get_seq_num();
            if first_seq != second_seq {
                return false;
            }
        }
        true
    }

    pub fn vn_not_equal(&self, vn: VarnodeId, op2: VarnodeId) -> bool {
        !self.vn_equal(vn, op2)
    }

    pub fn vn_compare_pointers(&self, first: VarnodeId, second: VarnodeId) -> bool {
        self.vn_less(first, second)
    }

    pub fn vn_set_flags(&mut self, vn: VarnodeId, fl: u32) {
        self.vbank.varnodes.get_mut(vn).set_flags(fl, &mut self.highs);
    }

    pub fn vn_clear_flags(&mut self, vn: VarnodeId, fl: u32) {
        self.vbank.varnodes.get_mut(vn).clear_flags(fl, &mut self.highs);
    }

    pub fn print_address_raw(&self, addr: &Address, out: &mut String) {
        match addr.get_space().map(|spc| spc.get_type()) {
            Some(SpaceType::Iop) => iop_space_print_raw(self, out, addr.get_offset()),
            Some(SpaceType::Fspec) => {
                let fc = self.call_spec(CallSpecId(addr.get_offset() as u32));
                FspecSpace::print_raw(fc, out);
            }
            _ => addr.print_raw(out),
        }
    }

    pub fn vn_update_cover(&mut self, vn: VarnodeId) {
        if (self.vn(vn).flags & Varnode::COVERDIRTY) != 0 {
            if self.vn(vn).has_cover()
                && let Some(mut cover) = self.vn_mut(vn).cover.take()
            {
                cover.rebuild(vn, self);
                self.vn_mut(vn).cover = Some(cover);
            }
            self.vn_clear_flags(vn, Varnode::COVERDIRTY);
        }
    }

    pub fn vn_get_cover(&mut self, vn: VarnodeId) -> Option<&Cover> {
        self.vn_update_cover(vn);
        self.vn(vn).cover.as_deref()
    }

    pub fn vn_print_cover(&self, vn: VarnodeId, out: &mut String) -> Result<()> {
        let varnode = self.vn(vn);
        let Some(cover) = varnode.cover.as_deref() else {
            return Err(Error::Lowlevel("No cover to print".to_string()));
        };
        if (varnode.flags & Varnode::COVERDIRTY) != 0 {
            out.push_str("Cover is dirty\n");
        } else {
            cover.print(out, self);
        }
        Ok(())
    }

    pub fn vn_print_info(&self, vn: VarnodeId, out: &mut String, glb: &Architecture) {
        let types = type_factory(glb);
        let varnode = self.vn(vn);
        types.get(varnode.tp).print_raw(out, types);
        out.push_str(" = ");
        self.vn_print_raw(vn, out, glb);
        if varnode.is_addr_tied() {
            out.push_str(" tied");
        }
        if varnode.is_mapped() {
            out.push_str(" mapped");
        }
        if varnode.is_persist() {
            out.push_str(" persistent");
        }
        if varnode.is_type_lock() {
            out.push_str(" tlock");
        }
        if varnode.is_name_lock() {
            out.push_str(" nlock");
        }
        if varnode.is_spacebase() {
            out.push_str(" base");
        }
        if varnode.is_unaffected() {
            out.push_str(" unaff");
        }
        if varnode.is_implied() {
            out.push_str(" implied");
        }
        if varnode.is_addr_force() {
            out.push_str(" addrforce");
        }
        if varnode.is_read_only() {
            out.push_str(" readonly");
        }
        let _ = write!(out, " (consumed=0x{:x})", varnode.consumed);
        let _ = write!(out, " (internal={:x})", vn.0);
        let _ = writeln!(out, " (create=0x{:x})", varnode.create_index);
    }

    pub fn vn_clear_symbol_links(&mut self, vn: VarnodeId) {
        let Some(high) = self.vn(vn).high else {
            self.vn_mut(vn).mapentry = None;
            self.vn_clear_flags(vn, Varnode::NAMELOCK | Varnode::TYPELOCK | Varnode::MAPPED);
            return;
        };
        let mut found_entry = false;
        for index in 0..self.high(high).num_instances() {
            let instance = self.high(high).get_instance(index);
            found_entry = found_entry || self.vn(instance).mapentry.is_some();
            self.vn_mut(instance).mapentry = None;
            self.vn_clear_flags(instance, Varnode::NAMELOCK | Varnode::TYPELOCK | Varnode::MAPPED);
        }
        if found_entry {
            self.high_mut(high).symbol_dirty();
        }
    }

    pub fn vn_set_symbol_properties(&mut self, vn: VarnodeId, entry: EntryId, glb: &mut Architecture) -> Result<bool> {
        let mut res = Database::entry_update_type(glb, entry, self, vn)?;
        let symtab = glb.symboltab.as_deref().expect("architecture has no symbol table");
        let sym = symtab.entry(entry).get_symbol();
        if symtab.symbol(sym).is_type_locked() && self.vn(vn).mapentry != Some(entry) {
            self.vn_mut(vn).mapentry = Some(entry);
            if let Some(high) = self.vn(vn).high {
                self.high_set_symbol(high, vn, glb)?;
            }
            res = true;
        }
        let all_flags = symbol_table(glb).entry_get_all_flags(entry);
        self.vn_set_flags(vn, all_flags & !Varnode::TYPELOCK);
        Ok(res)
    }

    pub fn vn_set_symbol_entry(&mut self, vn: VarnodeId, entry: EntryId, glb: &mut Architecture) -> Result<()> {
        self.vn_mut(vn).mapentry = Some(entry);
        let mut fl = Varnode::MAPPED;
        let symtab = symbol_table(glb);
        if symtab.symbol(symtab.entry(entry).get_symbol()).is_name_locked() {
            fl |= Varnode::NAMELOCK;
        }
        self.vn_set_flags(vn, fl);
        if let Some(high) = self.vn(vn).high {
            self.high_set_symbol(high, vn, glb)?;
        }
        Ok(())
    }

    pub fn vn_set_symbol_reference(&mut self, vn: VarnodeId, entry: EntryId, off: i32, glb: &mut Architecture) {
        if let Some(high) = self.vn(vn).high {
            let sym = symbol_table(glb).entry(entry).get_symbol();
            self.high_mut(high).set_symbol_reference(sym, off);
        }
    }

    pub fn vn_replace_in_high(&mut self, vn: VarnodeId, replacevn: VarnodeId) -> Result<()> {
        let high = self.vn(vn).high.expect("varnode has no high variable");
        self.high_remove(high, vn);
        let replace_high = self
            .vn(replacevn)
            .high
            .expect("replacement varnode has no high variable");
        self.vn_mut(replacevn).high = None;
        self.high_mut(replace_high).inst[0] = vn;
        let mergegroup = self.vn(vn).mergegroup;
        self.high_insert(high, replacevn, mergegroup);
        let varnode = self.vn_mut(vn);
        varnode.high = Some(replace_high);
        varnode.mergegroup = 0;
        Ok(())
    }

    pub fn vn_get_type_def_facing(&self, vn: VarnodeId, glb: &Architecture) -> TypeId {
        let types = type_factory(glb);
        let varnode = self.vn(vn);
        if !types.get(varnode.tp).needs_resolution() {
            return varnode.tp;
        }
        match varnode.def {
            Some(def) => Datatype::find_resolve(varnode.tp, def, -1, self, glb),
            None => varnode.tp,
        }
    }

    pub fn vn_get_type_read_facing(&self, vn: VarnodeId, op: OpId, glb: &Architecture) -> TypeId {
        let types = type_factory(glb);
        let varnode = self.vn(vn);
        if !types.get(varnode.tp).needs_resolution() {
            return varnode.tp;
        }
        Datatype::find_resolve(varnode.tp, op, self.op(op).get_slot(vn), self, glb)
    }

    pub fn vn_get_high_type_def_facing(&mut self, vn: VarnodeId, glb: &Architecture) -> Result<TypeId> {
        let high = self.vn(vn).get_high()?;
        let ct = self.high_get_type(high, glb);
        let types = type_factory(glb);
        if !types.get(ct).needs_resolution() {
            return Ok(ct);
        }
        match self.vn(vn).def {
            Some(def) => Ok(Datatype::find_resolve(ct, def, -1, self, glb)),
            None => Ok(ct),
        }
    }

    pub fn vn_get_high_type_read_facing(&mut self, vn: VarnodeId, op: OpId, glb: &Architecture) -> Result<TypeId> {
        let high = self.vn(vn).get_high()?;
        let ct = self.high_get_type(high, glb);
        let types = type_factory(glb);
        if !types.get(ct).needs_resolution() {
            return Ok(ct);
        }
        Ok(Datatype::find_resolve(ct, op, self.op(op).get_slot(vn), self, glb))
    }

    pub fn vn_get_use_point(&self, vn: VarnodeId) -> Address {
        let varnode = self.vn(vn);
        if varnode.is_written() {
            return self
                .op(varnode.def.expect("written varnode has no def"))
                .get_addr()
                .clone();
        }
        self.get_address().add(-1)
    }

    pub fn vn_print_raw(&self, vn: VarnodeId, out: &mut String, glb: &Architecture) {
        let varnode = self.vn(vn);
        let trans = glb.translate.as_deref().expect("architecture has no translator");
        let (expect, leaves_hex) = varnode.print_raw_no_markup_radix(out, trans, self);
        if expect != varnode.size {
            if leaves_hex {
                let _ = write!(out, ":{:x}", varnode.size);
            } else {
                let _ = write!(out, ":{}", varnode.size);
            }
        }
        if (varnode.flags & Varnode::INPUT) != 0 {
            out.push_str("(i)");
        }
        if varnode.is_written() {
            let _ = write!(
                out,
                "({})",
                self.op(varnode.def.expect("written varnode has no def")).get_seq_num()
            );
        }
        if (varnode.flags & (Varnode::INSERT | Varnode::CONSTANT)) == 0 {
            out.push_str("(free)");
        }
    }

    pub fn vn_print_raw_option(&self, vn: Option<VarnodeId>, out: &mut String, glb: &Architecture) {
        match vn {
            None => out.push_str("<null>"),
            Some(vn) => self.vn_print_raw(vn, out, glb),
        }
    }

    pub fn vn_term_order(&self, vn: VarnodeId, op: VarnodeId) -> i32 {
        if self.vn(vn).is_constant() {
            if !self.vn(op).is_constant() {
                return 1;
            }
        } else {
            if self.vn(op).is_constant() {
                return -1;
            }
            let strip_mult = |id: VarnodeId| -> VarnodeId {
                let varnode = self.vn(id);
                if varnode.is_written() {
                    let def = self.op(varnode.def.expect("written varnode has no def"));
                    if def.code() == OpCode::IntMult && self.vn(def.get_in(1)).is_constant() {
                        return def.get_in(0);
                    }
                }
                id
            };
            let first = strip_mult(vn);
            let second = strip_mult(op);
            if self.vn(first).get_addr() < self.vn(second).get_addr() {
                return -1;
            }
            if self.vn(second).get_addr() < self.vn(first).get_addr() {
                return 1;
            }
        }
        0
    }

    pub fn vn_print_raw_heritage(&self, vn: VarnodeId, out: &mut String, depth: i32, glb: &mut Architecture) {
        for _ in 0..depth {
            out.push(' ');
        }
        let varnode = self.vn(vn);
        if varnode.is_constant() {
            self.vn_print_raw(vn, out, glb);
            out.push('\n');
            return;
        }
        self.vn_print_raw(vn, out, glb);
        out.push(' ');
        match varnode.def {
            Some(def) => self.op_print_raw(def, out, glb),
            None => self.vn_print_raw(vn, out, glb),
        }
        let varnode = self.vn(vn);
        if (varnode.flags & Varnode::INPUT) != 0 {
            out.push_str(" Input");
        }
        if (varnode.flags & Varnode::CONSTANT) != 0 {
            out.push_str(" Constant");
        }
        if (varnode.flags & Varnode::ANNOTATION) != 0 {
            out.push_str(" Code");
        }
        match varnode.def {
            Some(def) => {
                let _ = writeln!(out, "\t\t{}", self.op(def).get_seq_num());
                for slot in 0..self.op(def).num_input() {
                    let input = self.op(def).get_in(slot);
                    self.vn_print_raw_heritage(input, out, depth + 5, glb);
                }
            }
            None => out.push('\n'),
        }
    }

    pub fn vn_is_constant_extended(&self, vn: VarnodeId, val: &mut [u64; 2]) -> bool {
        let varnode = self.vn(vn);
        if varnode.is_constant() {
            val[0] = varnode.get_offset();
            val[1] = 0;
            return true;
        }
        if !varnode.is_written() || varnode.size <= 8 {
            return false;
        }
        if varnode.size > 16 {
            return false;
        }
        let def = self.op(varnode.def.expect("written varnode has no def"));
        match def.code() {
            OpCode::IntZext => {
                let vn0 = self.vn(def.get_in(0));
                if vn0.is_constant() {
                    val[0] = vn0.get_offset();
                    val[1] = 0;
                    return true;
                }
            }
            OpCode::IntSext => {
                let vn0 = self.vn(def.get_in(0));
                if vn0.is_constant() {
                    val[0] = vn0.get_offset();
                    if vn0.get_size() < 8 {
                        val[0] = sign_extend_size(val[0], vn0.get_size(), varnode.size);
                    }
                    val[1] = if signbit_negative(val[0], 8) { u64::MAX } else { 0 };
                    return true;
                }
            }
            OpCode::Piece => {
                let vnlo = self.vn(def.get_in(1));
                if vnlo.is_constant() {
                    val[0] = vnlo.get_offset();
                    let vnhi = self.vn(def.get_in(0));
                    if vnhi.is_constant() {
                        val[1] = vnhi.get_offset();
                        if vnlo.get_size() == 8 {
                            return true;
                        }
                        val[0] |= val[1].wrapping_shl((8 * vnlo.get_size()) as u32);
                        val[1] = val[1].wrapping_shr((8 * (8 - vnlo.get_size())) as u32);
                        return true;
                    }
                }
            }
            _ => {}
        }
        false
    }

    pub fn vn_is_eventual_constant(&self, vn: VarnodeId, max_binary: i32, max_load: i32) -> bool {
        let mut cur_vn = vn;
        let mut max_load = max_load;
        while !self.vn(cur_vn).is_constant() {
            if !self.vn(cur_vn).is_written() {
                return false;
            }
            let op = self.op(self.vn(cur_vn).def.expect("written varnode has no def"));
            match op.code() {
                OpCode::Load => {
                    if max_load == 0 {
                        return false;
                    }
                    max_load -= 1;
                    cur_vn = op.get_in(1);
                }
                OpCode::IntAdd | OpCode::IntSub | OpCode::IntXor | OpCode::IntOr | OpCode::IntAnd => {
                    if max_binary == 0 {
                        return false;
                    }
                    if !self.vn_is_eventual_constant(op.get_in(0), max_binary - 1, max_load) {
                        return false;
                    }
                    return self.vn_is_eventual_constant(op.get_in(1), max_binary - 1, max_load);
                }
                OpCode::IntZext | OpCode::IntSext | OpCode::Copy => {
                    cur_vn = op.get_in(0);
                }
                OpCode::IntLeft | OpCode::IntRight | OpCode::IntSright | OpCode::IntMult => {
                    if !self.vn(op.get_in(1)).is_constant() {
                        return false;
                    }
                    cur_vn = op.get_in(0);
                }
                _ => return false,
            }
        }
        true
    }

    pub fn vn_update_type(&mut self, vn: VarnodeId, ct: TypeId) -> bool {
        let varnode = self.vn_mut(vn);
        if varnode.tp == ct || varnode.is_type_lock() {
            return false;
        }
        varnode.tp = ct;
        if let Some(high) = varnode.high {
            self.high_mut(high).type_dirty();
        }
        true
    }

    pub fn vn_update_type_locked(
        &mut self,
        vn: VarnodeId,
        ct: TypeId,
        lock: bool,
        over: bool,
        glb: &Architecture,
    ) -> bool {
        let mut lock = lock;
        if type_factory(glb).get(ct).get_metatype() == TypeMetatype::Unknown {
            lock = false;
        }
        let varnode = self.vn_mut(vn);
        if varnode.is_type_lock() && !over {
            return false;
        }
        if varnode.tp == ct && varnode.is_type_lock() == lock {
            return false;
        }
        varnode.flags &= !Varnode::TYPELOCK;
        if lock {
            varnode.flags |= Varnode::TYPELOCK;
        }
        varnode.tp = ct;
        if let Some(high) = varnode.high {
            self.high_mut(high).type_dirty();
        }
        true
    }

    pub fn vn_copy_symbol(&mut self, vn: VarnodeId, source: VarnodeId, glb: &Architecture) -> Result<()> {
        let (source_type, source_entry, source_flags) = {
            let src = self.vn(source);
            (src.tp, src.mapentry, src.flags)
        };
        let varnode = self.vn_mut(vn);
        varnode.tp = source_type;
        varnode.mapentry = source_entry;
        varnode.flags &= !(Varnode::TYPELOCK | Varnode::NAMELOCK);
        varnode.flags |= (Varnode::TYPELOCK | Varnode::NAMELOCK) & source_flags;
        if let Some(high) = varnode.high {
            self.high_mut(high).type_dirty();
            if self.vn(vn).mapentry.is_some() {
                self.high_set_symbol(high, vn, glb)?;
            }
        }
        Ok(())
    }

    pub fn vn_copy_symbol_if_valid(&mut self, vn: VarnodeId, source: VarnodeId, glb: &Architecture) -> Result<()> {
        let Some(map_entry) = self.vn(source).get_symbol_entry() else {
            return Ok(());
        };
        let symtab = symbol_table(glb);
        let sym = symtab.symbol(symtab.entry(map_entry).get_symbol());
        if !matches!(sym.kind, SymbolKind::Equate { .. }) {
            return Ok(());
        }
        let varnode = self.vn(vn);
        if sym.is_value_close(varnode.loc.get_offset(), varnode.size) {
            self.vn_copy_symbol(vn, source, glb)?;
        }
        Ok(())
    }

    pub fn vn_get_local_type(&mut self, vn: VarnodeId, blockup: &mut bool, glb: &mut Architecture) -> Result<TypeId> {
        if self.vn(vn).is_type_lock() {
            return Ok(self.vn(vn).tp);
        }
        let mut ct: Option<TypeId> = None;
        if let Some(def) = self.vn(vn).def {
            let outct = self.op_output_type_local(def, glb);
            ct = Some(outct);
            if self.op(def).stops_type_propagation() {
                *blockup = true;
                return Ok(outct);
            }
        }
        let descend = self.vn(vn).descend.clone();
        for op in descend {
            let slot = self.op(op).get_slot(vn);
            let newct = self.op_input_type_local(op, slot, glb);
            match ct {
                None => ct = Some(newct),
                Some(current) => {
                    let types = type_factory(glb);
                    if 0 > types.get(newct).type_order(types.get(current), types) {
                        ct = Some(newct);
                    }
                }
            }
        }
        ct.ok_or_else(|| Error::Lowlevel("NULL local type".to_string()))
    }

    pub fn vn_is_boolean_value(&self, vn: VarnodeId, use_annotation: bool, glb: &Architecture) -> bool {
        let varnode = self.vn(vn);
        if varnode.is_written() {
            return self
                .op(varnode.def.expect("written varnode has no def"))
                .is_calculated_bool();
        }
        if !use_annotation {
            return false;
        }
        if (varnode.flags & (Varnode::INPUT | Varnode::TYPELOCK)) == (Varnode::INPUT | Varnode::TYPELOCK)
            && varnode.size == 1
            && type_factory(glb).get(varnode.tp).get_metatype() == TypeMetatype::Bool
        {
            return true;
        }
        false
    }

    pub fn vn_is_zero_extended(&self, vn: VarnodeId, base_size: i32) -> bool {
        let varnode = self.vn(vn);
        if base_size >= varnode.size {
            return false;
        }
        if varnode.size > 8 {
            if !varnode.is_written() {
                return false;
            }
            let def = self.op(varnode.def.expect("written varnode has no def"));
            if def.code() != OpCode::IntZext {
                return false;
            }
            if self.vn(def.get_in(0)).get_size() > base_size {
                return false;
            }
            return true;
        }
        let mask = varnode.nzm.wrapping_shr((8 * base_size) as u32);
        mask == 0
    }

    fn vn_copy_source(&self, vn: VarnodeId) -> Option<VarnodeId> {
        let varnode = self.vn(vn);
        if varnode.is_written() {
            let def = self.op(varnode.def.expect("written varnode has no def"));
            if def.code() == OpCode::Copy {
                return Some(def.get_in(0));
            }
        }
        None
    }

    pub fn vn_copy_shadow(&self, vn: VarnodeId, op2: VarnodeId) -> bool {
        if vn == op2 {
            return true;
        }
        let mut cur = vn;
        while let Some(source) = self.vn_copy_source(cur) {
            cur = source;
            if cur == op2 {
                return true;
            }
        }
        let mut other = op2;
        while let Some(source) = self.vn_copy_source(other) {
            other = source;
            if cur == other {
                return true;
            }
        }
        false
    }

    pub fn vn_find_subpiece_shadow(&self, vn: VarnodeId, least_byte: i32, whole: VarnodeId, recurse: i32) -> bool {
        let mut cur = vn;
        while let Some(source) = self.vn_copy_source(cur) {
            cur = source;
        }
        let mut whole = whole;
        let mut recurse = recurse;
        if !self.vn(cur).is_written() {
            if self.vn(cur).is_constant() {
                while let Some(source) = self.vn_copy_source(whole) {
                    whole = source;
                }
                if !self.vn(whole).is_constant() {
                    return false;
                }
                let mut off = self.vn(whole).get_offset().wrapping_shr((least_byte * 8) as u32);
                off &= calc_mask(self.vn(cur).get_size());
                return off == self.vn(cur).get_offset();
            }
            return false;
        }
        let def = self.op(self.vn(cur).def.expect("written varnode has no def"));
        match def.code() {
            OpCode::Subpiece => {
                let mut tmpvn = def.get_in(0);
                let off = self.vn(def.get_in(1)).get_offset() as i32;
                if off != least_byte || self.vn(tmpvn).get_size() != self.vn(whole).get_size() {
                    return false;
                }
                if tmpvn == whole {
                    return true;
                }
                while let Some(source) = self.vn_copy_source(tmpvn) {
                    tmpvn = source;
                    if tmpvn == whole {
                        return true;
                    }
                }
            }
            OpCode::Multiequal => {
                recurse += 1;
                if recurse > 1 {
                    return false;
                }
                while let Some(source) = self.vn_copy_source(whole) {
                    whole = source;
                }
                if !self.vn(whole).is_written() {
                    return false;
                }
                let big_op = self.op(self.vn(whole).def.expect("written varnode has no def"));
                if big_op.code() != OpCode::Multiequal {
                    return false;
                }
                let small_op = def;
                if big_op.get_parent() != small_op.get_parent() {
                    return false;
                }
                for slot in 0..small_op.num_input() {
                    if !self.vn_find_subpiece_shadow(small_op.get_in(slot), least_byte, big_op.get_in(slot), recurse) {
                        return false;
                    }
                }
                return true;
            }
            _ => {}
        }
        false
    }

    pub fn vn_find_piece_shadow(&self, vn: VarnodeId, least_byte: i32, piece: VarnodeId) -> bool {
        let mut cur = vn;
        while let Some(source) = self.vn_copy_source(cur) {
            cur = source;
        }
        if !self.vn(cur).is_written() {
            return false;
        }
        let def = self.op(self.vn(cur).def.expect("written varnode has no def"));
        if def.code() == OpCode::Piece {
            let mut least_byte = least_byte;
            let mut tmpvn = def.get_in(1);
            if least_byte >= self.vn(tmpvn).get_size() {
                least_byte -= self.vn(tmpvn).get_size();
                tmpvn = def.get_in(0);
            } else if self.vn(piece).get_size() + least_byte > self.vn(tmpvn).get_size() {
                return false;
            }
            if least_byte == 0 && self.vn(tmpvn).get_size() == self.vn(piece).get_size() {
                if tmpvn == piece {
                    return true;
                }
                while let Some(source) = self.vn_copy_source(tmpvn) {
                    tmpvn = source;
                    if tmpvn == piece {
                        return true;
                    }
                }
                return false;
            }
            return self.vn_find_piece_shadow(tmpvn, least_byte, piece);
        }
        false
    }

    pub fn vn_partial_copy_shadow(&self, vn: VarnodeId, op2: VarnodeId, rel_off: i32) -> bool {
        let this_size = self.vn(vn).get_size();
        let other_size = self.vn(op2).get_size();
        let (small, big, rel_off) = if this_size < other_size {
            (vn, op2, rel_off)
        } else if this_size > other_size {
            (op2, vn, -rel_off)
        } else {
            return false;
        };
        if rel_off < 0 {
            return false;
        }
        if rel_off + self.vn(small).get_size() > self.vn(big).get_size() {
            return false;
        }
        let big_endian = self.vn(vn).get_addr().is_big_endian();
        let least_byte = if big_endian {
            (self.vn(big).get_size() - self.vn(small).get_size()) - rel_off
        } else {
            rel_off
        };
        if self.vn_find_subpiece_shadow(small, least_byte, big, 0) {
            return true;
        }
        if self.vn_find_piece_shadow(big, least_byte, small) {
            return true;
        }
        false
    }

    pub fn vn_get_structured_type(&self, vn: VarnodeId, glb: &Architecture) -> Option<TypeId> {
        let varnode = self.vn(vn);
        let ct = match varnode.mapentry {
            Some(entry) => {
                let symtab = symbol_table(glb);
                symtab.symbol(symtab.entry(entry).get_symbol()).get_type()?
            }
            None => varnode.tp,
        };
        if type_factory(glb).get(ct).is_piece_structured() {
            return Some(ct);
        }
        None
    }

    pub fn vn_destroy(&mut self, vn: VarnodeId) {
        self.vn_mut(vn).cover = None;
        if let Some(high) = self.vn(vn).high {
            self.high_remove(high, vn);
            if self.high(high).is_unattached() {
                self.high_destroy(high);
            }
        }
    }
}

pub struct VarnodeBank {
    pub(crate) varnodes: Arena<VarnodeId, Varnode>,
    pub(crate) uniq_space: Option<SpaceRef>,
    pub(crate) uniqbase: u32,
    pub(crate) uniqid: u32,
    pub(crate) create_index: u32,
    pub(crate) loc_tree: OrderedIndex<LocKey, VarnodeId>,
    pub(crate) def_tree: OrderedIndex<DefKey, VarnodeId>,
}

impl VarnodeBank {
    pub fn new(manager: &AddrSpaceManager, trans: &dyn Translate) -> VarnodeBank {
        let uniqbase = trans.get_unique_start(UniqueLayout::Analysis);
        VarnodeBank {
            varnodes: Arena::new(),
            uniq_space: manager.get_unique_space(),
            uniqbase,
            uniqid: uniqbase,
            create_index: 0,
            loc_tree: OrderedIndex::default(),
            def_tree: OrderedIndex::default(),
        }
    }

    pub fn get(&self, vn: VarnodeId) -> &Varnode {
        self.varnodes.get(vn)
    }

    pub fn get_mut(&mut self, vn: VarnodeId) -> &mut Varnode {
        self.varnodes.get_mut(vn)
    }

    fn erase_keys(&mut self, vn: VarnodeId) {
        let varnode = self.varnodes.get_mut(vn);
        if let Some(key) = varnode.lociter.take() {
            self.loc_tree.remove(&key);
        }
        if let Some(key) = varnode.defiter.take() {
            self.def_tree.remove(&key);
        }
    }

    fn insert_keys(&mut self, vn: VarnodeId, ops: &Arena<OpId, PcodeOp>) {
        let loc_key = self.varnodes.get(vn).loc_key(ops);
        let def_key = self.varnodes.get(vn).def_key(ops);
        self.loc_tree.insert(loc_key, vn);
        self.def_tree.insert(def_key, vn);
        let varnode = self.varnodes.get_mut(vn);
        varnode.lociter = Some(loc_key);
        varnode.defiter = Some(def_key);
    }

    pub fn xref(
        &mut self,
        vn: VarnodeId,
        ops: &mut Arena<OpId, PcodeOp>,
        highs: &mut Arena<HighId, HighVariable>,
    ) -> Result<VarnodeId> {
        let loc_key = self.varnodes.get(vn).loc_key(ops);
        if let Some(othervn) = self.loc_tree.get(&loc_key).copied() {
            self.replace(vn, othervn, ops, highs)?;
            self.varnodes.remove(vn);
            return Ok(othervn);
        }
        self.loc_tree.insert(loc_key, vn);
        self.varnodes.get_mut(vn).lociter = Some(loc_key);
        self.varnodes.get_mut(vn).set_flags(Varnode::INSERT, highs);
        let def_key = self.varnodes.get(vn).def_key(ops);
        self.def_tree.insert(def_key, vn);
        self.varnodes.get_mut(vn).defiter = Some(def_key);
        Ok(vn)
    }

    pub fn clear(&mut self) {
        self.varnodes.clear();
        self.loc_tree.clear();
        self.def_tree.clear();
        self.uniqid = self.uniqbase;
        self.create_index = 0;
    }

    pub fn num_varnodes(&self) -> i32 {
        self.loc_tree.len() as i32
    }

    pub fn create(&mut self, size: i32, addr: &Address, ct: TypeId) -> VarnodeId {
        let mut varnode = Varnode::new(size, addr, ct);
        varnode.create_index = self.create_index;
        self.create_index = self.create_index.wrapping_add(1);
        let loc_key = varnode.loc_key(&Arena::new());
        let def_key = varnode.def_key(&Arena::new());
        varnode.lociter = Some(loc_key);
        varnode.defiter = Some(def_key);
        let vn = self.varnodes.alloc(varnode);
        self.loc_tree.insert(loc_key, vn);
        self.def_tree.insert(def_key, vn);
        vn
    }

    pub fn create_def(
        &mut self,
        size: i32,
        addr: &Address,
        ct: TypeId,
        op: OpId,
        ops: &mut Arena<OpId, PcodeOp>,
        highs: &mut Arena<HighId, HighVariable>,
    ) -> Result<VarnodeId> {
        let mut varnode = Varnode::new(size, addr, ct);
        varnode.create_index = self.create_index;
        self.create_index = self.create_index.wrapping_add(1);
        varnode.set_def(Some(op), highs);
        let vn = self.varnodes.alloc(varnode);
        self.xref(vn, ops, highs)
    }

    fn next_unique_address(&mut self, size: i32) -> Address {
        let spc = self.uniq_space.clone().expect("no unique space");
        let addr = Address::new(spc, self.uniqid as u64);
        self.uniqid = self.uniqid.wrapping_add(size as u32);
        addr
    }

    pub fn create_unique(&mut self, size: i32, ct: TypeId) -> VarnodeId {
        let addr = self.next_unique_address(size);
        self.create(size, &addr, ct)
    }

    pub fn create_def_unique(
        &mut self,
        size: i32,
        ct: TypeId,
        op: OpId,
        ops: &mut Arena<OpId, PcodeOp>,
        highs: &mut Arena<HighId, HighVariable>,
    ) -> Result<VarnodeId> {
        let addr = self.next_unique_address(size);
        self.create_def(size, &addr, ct, op, ops, highs)
    }

    pub fn check_destroy(&self, vn: VarnodeId) -> Result<()> {
        let varnode = self.varnodes.get(vn);
        if varnode.def.is_some() || !varnode.has_no_descend() {
            return Err(Error::Lowlevel("Deleting integrated varnode".to_string()));
        }
        Ok(())
    }

    pub fn destroy(&mut self, vn: VarnodeId) -> Result<()> {
        self.check_destroy(vn)?;
        self.erase_keys(vn);
        self.varnodes.remove(vn);
        Ok(())
    }

    pub fn set_input(
        &mut self,
        vn: VarnodeId,
        ops: &mut Arena<OpId, PcodeOp>,
        highs: &mut Arena<HighId, HighVariable>,
    ) -> Result<VarnodeId> {
        if !self.varnodes.get(vn).is_free() {
            return Err(Error::Lowlevel(
                "Making input out of varnode which is not free".to_string(),
            ));
        }
        if self.varnodes.get(vn).is_constant() {
            return Err(Error::Lowlevel("Making input out of constant varnode".to_string()));
        }
        self.erase_keys(vn);
        self.varnodes.get_mut(vn).set_input(highs);
        self.xref(vn, ops, highs)
    }

    pub fn set_def(
        &mut self,
        vn: VarnodeId,
        op: OpId,
        ops: &mut Arena<OpId, PcodeOp>,
        highs: &mut Arena<HighId, HighVariable>,
    ) -> Result<VarnodeId> {
        if !self.varnodes.get(vn).is_free() {
            let addr = ops.get(op).get_addr();
            let mut msg = format!("Defining varnode which is not free at {}", addr.get_shortcut());
            addr.print_raw(&mut msg);
            return Err(Error::Lowlevel(msg));
        }
        if self.varnodes.get(vn).is_constant() {
            let addr = ops.get(op).get_addr();
            let mut msg = format!("Assignment to constant at {}", addr.get_shortcut());
            addr.print_raw(&mut msg);
            return Err(Error::Lowlevel(msg));
        }
        self.erase_keys(vn);
        self.varnodes.get_mut(vn).set_def(Some(op), highs);
        self.xref(vn, ops, highs)
    }

    pub fn make_free(&mut self, vn: VarnodeId, ops: &Arena<OpId, PcodeOp>, highs: &mut Arena<HighId, HighVariable>) {
        self.erase_keys(vn);
        let varnode = self.varnodes.get_mut(vn);
        varnode.set_def(None, highs);
        varnode.clear_flags(Varnode::INSERT | Varnode::INPUT | Varnode::INDIRECT_CREATION, highs);
        self.insert_keys(vn, ops);
    }

    pub fn replace(
        &mut self,
        oldvn: VarnodeId,
        newvn: VarnodeId,
        ops: &mut Arena<OpId, PcodeOp>,
        highs: &mut Arena<HighId, HighVariable>,
    ) -> Result<()> {
        let mut index = 0;
        while index < self.varnodes.get(oldvn).descend.len() {
            let op = self.varnodes.get(oldvn).descend[index];
            if ops.get(op).output == Some(newvn) {
                index += 1;
                continue;
            }
            let slot = ops.get(op).get_slot(oldvn);
            self.varnodes.get_mut(oldvn).descend.remove(index);
            ops.get_mut(op).clear_input(slot);
            self.varnodes.get_mut(newvn).add_descend(op, highs)?;
            ops.get_mut(op).set_input(Some(newvn), slot);
        }
        self.varnodes.get_mut(oldvn).set_flags(Varnode::COVERDIRTY, highs);
        self.varnodes.get_mut(newvn).set_flags(Varnode::COVERDIRTY, highs);
        Ok(())
    }

    pub fn find(
        &self,
        size: i32,
        loc: &Address,
        pc: &Address,
        uniq: u32,
        ops: &Arena<OpId, PcodeOp>,
    ) -> Option<VarnodeId> {
        let start = self.begin_loc_pc(size, loc, pc, uniq)?;
        for (_, vn) in self.loc_tree.range(start..) {
            let varnode = self.varnodes.get(*vn);
            if varnode.get_size() != size {
                break;
            }
            if varnode.get_addr() != loc {
                break;
            }
            if let Some(op) = varnode.def {
                let pcode_op = ops.get(op);
                if pcode_op.get_addr() == pc && (uniq == u32::MAX || pcode_op.get_time() == uniq) {
                    return Some(*vn);
                }
            }
        }
        None
    }

    pub fn find_input(&self, size: i32, loc: &Address) -> Option<VarnodeId> {
        let vn = self.loc_at(&self.begin_loc_flags(size, loc, Varnode::INPUT))?;
        let varnode = self.varnodes.get(vn);
        if varnode.is_input() && varnode.get_size() == size && varnode.get_addr() == loc {
            return Some(vn);
        }
        None
    }

    pub fn find_covered_input(&self, size: i32, loc: &Address) -> Option<VarnodeId> {
        let spc = loc.get_space().expect("address has no space");
        let highest = spc.get_highest();
        let end = loc.get_offset().wrapping_add(size as u64).wrapping_sub(1);
        let iter = self.def_input_lower_bound(loc);
        let enditer = if end == highest {
            let tmp = Address::new(spc.clone(), highest);
            self.def_input_end(&tmp)
        } else {
            self.def_input_lower_bound(&loc.add(size as i64))
        };
        for vn in self.def_range(&iter, &enditer) {
            let varnode = self.varnodes.get(vn);
            if varnode
                .get_offset()
                .wrapping_add(varnode.get_size() as u64)
                .wrapping_sub(1)
                <= end
            {
                return Some(vn);
            }
        }
        None
    }

    pub fn find_covering_input(&self, size: i32, loc: &Address) -> Option<VarnodeId> {
        let iter = self.def_input_lower_bound(loc);
        let key = iter.as_ref()?;
        let mut vn = self.def_tree[key];
        if self.varnodes.get(vn).get_addr() != loc
            && let Some((_, previous)) = self.def_tree.range(..key).next_back()
        {
            vn = *previous;
        }
        let varnode = self.varnodes.get(vn);
        if varnode.is_input()
            && same_space(varnode.get_addr(), loc)
            && varnode.get_offset() <= loc.get_offset()
            && varnode
                .get_offset()
                .wrapping_add(varnode.get_size() as u64)
                .wrapping_sub(1)
                >= loc.get_offset().wrapping_add(size as u64).wrapping_sub(1)
        {
            return Some(vn);
        }
        None
    }

    pub fn has_input_intersection(&self, size: i32, loc: &Address) -> bool {
        let iter = self.def_input_lower_bound(loc);
        if let Some(key) = iter.as_ref() {
            let varnode = self.varnodes.get(self.def_tree[key]);
            if varnode.is_input() && varnode.intersects_addr(loc, size) {
                return true;
            }
        }
        let previous = match iter.as_ref() {
            Some(key) => self.def_tree.range(..key).next_back(),
            None => self.def_tree.iter().next_back(),
        };
        if let Some((_, vn)) = previous {
            let varnode = self.varnodes.get(*vn);
            if varnode.is_input() && varnode.intersects_addr(loc, size) {
                return true;
            }
        }
        false
    }

    fn def_input_lower_bound(&self, addr: &Address) -> DefIter {
        self.def_lower_bound(&def_search(INPUT_CLASS, None, addr, 0))
    }

    fn def_input_end(&self, addr: &Address) -> DefIter {
        self.def_lower_bound(&def_search(INPUT_CLASS, None, addr, 1000000))
    }

    pub fn get_create_index(&self) -> u32 {
        self.create_index
    }

    pub fn loc_at(&self, iter: &LocIter) -> Option<VarnodeId> {
        iter.as_ref().and_then(|key| self.loc_tree.get(key).copied())
    }

    pub fn loc_entry_from(&self, key: &LocKey) -> Option<(LocKey, VarnodeId, LocIter)> {
        self.loc_tree.entry_from(key)
    }

    pub fn def_entry_from(&self, key: &DefKey) -> Option<(DefKey, VarnodeId, DefIter)> {
        self.def_tree.entry_from(key)
    }

    pub fn loc_lower_bound(&self, key: &LocKey) -> LocIter {
        self.loc_tree
            .range((Bound::Included(key), Bound::Unbounded))
            .next()
            .map(|(found, _)| *found)
    }

    pub fn loc_upper_bound(&self, key: &LocKey) -> LocIter {
        self.loc_tree
            .range((Bound::Excluded(key), Bound::Unbounded))
            .next()
            .map(|(found, _)| *found)
    }

    pub fn loc_next(&self, iter: &LocIter) -> LocIter {
        match iter {
            Some(key) => self.loc_upper_bound(key),
            None => None,
        }
    }

    pub fn loc_prev(&self, iter: &LocIter) -> LocIter {
        match iter {
            Some(key) => self
                .loc_tree
                .range((Bound::Unbounded, Bound::Excluded(key)))
                .next_back()
                .map(|(found, _)| *found),
            None => self.loc_tree.keys().next_back().cloned(),
        }
    }

    pub fn loc_range(&self, begin: &LocIter, end: &LocIter) -> Vec<VarnodeId> {
        let Some(start) = begin else {
            return Vec::new();
        };
        let upper = match end {
            Some(key) => Bound::Excluded(key),
            None => Bound::Unbounded,
        };
        if let Some(key) = end
            && key < start
        {
            return Vec::new();
        }
        self.loc_tree
            .range((Bound::Included(start), upper))
            .map(|(_, id)| *id)
            .collect()
    }

    pub fn begin_loc(&self) -> LocIter {
        self.loc_tree.keys().next().cloned()
    }

    pub fn end_loc(&self) -> LocIter {
        None
    }

    pub fn begin_loc_space(&self, spaceid: &SpaceRef) -> LocIter {
        self.loc_lower_bound(&loc_search(&Address::new(spaceid.clone(), 0), 0, INPUT_CLASS, None))
    }

    pub fn end_loc_space(&self, spaceid: &SpaceRef, manager: &AddrSpaceManager) -> LocIter {
        let next = manager.get_next_space_in_order(Some(spaceid));
        self.loc_lower_bound(&loc_search(&Address::from_parts(next, 0), 0, INPUT_CLASS, None))
    }

    pub fn begin_loc_addr(&self, addr: &Address) -> LocIter {
        self.loc_lower_bound(&loc_search(addr, 0, INPUT_CLASS, None))
    }

    pub fn end_loc_addr(&self, addr: &Address, manager: &AddrSpaceManager) -> LocIter {
        let spc = addr.get_space().expect("address has no space");
        let search = if addr.get_offset() == spc.get_highest() {
            Address::from_parts(manager.get_next_space_in_order(Some(spc)), 0)
        } else {
            addr.add(1)
        };
        self.loc_lower_bound(&loc_search(&search, 0, INPUT_CLASS, None))
    }

    pub fn begin_loc_size(&self, size: i32, addr: &Address) -> LocIter {
        self.loc_lower_bound(&loc_search(addr, size, INPUT_CLASS, None))
    }

    pub fn end_loc_size(&self, size: i32, addr: &Address) -> LocIter {
        self.loc_lower_bound(&loc_search(addr, size + 1, INPUT_CLASS, None))
    }

    pub fn begin_loc_flags(&self, size: i32, addr: &Address, fl: u32) -> LocIter {
        if fl == Varnode::INPUT {
            return self.loc_lower_bound(&loc_search(addr, size, INPUT_CLASS, None));
        }
        if fl == Varnode::WRITTEN {
            let seq = SeqNum::extreme(MachExtreme::Minimal);
            return self.loc_lower_bound(&loc_search(addr, size, WRITTEN_CLASS, Some(seq)));
        }
        let seq = SeqNum::extreme(MachExtreme::Maximal);
        self.loc_upper_bound(&loc_search(addr, size, WRITTEN_CLASS, Some(seq)))
    }

    pub fn end_loc_flags(&self, size: i32, addr: &Address, fl: u32) -> LocIter {
        if fl == Varnode::WRITTEN {
            let seq = SeqNum::extreme(MachExtreme::Maximal);
            return self.loc_upper_bound(&loc_search(addr, size, WRITTEN_CLASS, Some(seq)));
        } else if fl == Varnode::INPUT {
            return self.loc_upper_bound(&loc_search(addr, size, INPUT_CLASS, None));
        }
        self.loc_lower_bound(&loc_search(addr, size + 1, INPUT_CLASS, None))
    }

    pub fn begin_loc_pc(&self, size: i32, addr: &Address, pc: &Address, uniq: u32) -> LocIter {
        let uniq = if uniq == u32::MAX { 0 } else { uniq };
        let seq = SeqNum::new(pc.clone(), uniq);
        self.loc_lower_bound(&loc_search(addr, size, WRITTEN_CLASS, Some(seq)))
    }

    pub fn end_loc_pc(&self, size: i32, addr: &Address, pc: &Address, uniq: u32) -> LocIter {
        let seq = SeqNum::new(pc.clone(), uniq);
        self.loc_upper_bound(&loc_search(addr, size, WRITTEN_CLASS, Some(seq)))
    }

    pub fn overlap_loc(&self, iter: &LocIter, bounds: &mut Vec<LocIter>) -> u32 {
        let first = self.loc_at(iter).expect("overlap_loc called at end of tree");
        let varnode = self.varnodes.get(first);
        let spc = varnode.get_addr().clone();
        let off = varnode.get_offset();
        let mut max_off = off.wrapping_add((varnode.get_size() - 1) as u64);
        let mut flags = varnode.get_flags();
        bounds.push(*iter);
        let mut iter = self.end_loc_flags(varnode.get_size(), varnode.get_addr(), Varnode::WRITTEN);
        bounds.push(iter);
        while let Some(vn) = self.loc_at(&iter) {
            let varnode = self.varnodes.get(vn);
            if !same_space(varnode.get_addr(), &spc) || varnode.get_offset() > max_off {
                break;
            }
            if varnode.is_free() {
                iter = self.end_loc_flags(varnode.get_size(), varnode.get_addr(), 0);
                continue;
            }
            let end_off = varnode.get_offset().wrapping_add((varnode.get_size() - 1) as u64);
            if end_off > max_off {
                max_off = end_off;
            }
            flags |= varnode.get_flags();
            bounds.push(iter);
            iter = self.end_loc_flags(varnode.get_size(), varnode.get_addr(), Varnode::WRITTEN);
            bounds.push(iter);
        }
        bounds.push(iter);
        flags
    }

    pub fn def_at(&self, iter: &DefIter) -> Option<VarnodeId> {
        iter.as_ref().and_then(|key| self.def_tree.get(key).copied())
    }

    fn def_lower_bound(&self, key: &DefKey) -> DefIter {
        self.def_tree
            .range((Bound::Included(key), Bound::Unbounded))
            .next()
            .map(|(found, _)| *found)
    }

    fn def_upper_bound(&self, key: &DefKey) -> DefIter {
        self.def_tree
            .range((Bound::Excluded(key), Bound::Unbounded))
            .next()
            .map(|(found, _)| *found)
    }

    pub fn def_next(&self, iter: &DefIter) -> DefIter {
        match iter {
            Some(key) => self.def_upper_bound(key),
            None => None,
        }
    }

    pub fn def_range(&self, begin: &DefIter, end: &DefIter) -> Vec<VarnodeId> {
        let Some(start) = begin else {
            return Vec::new();
        };
        let upper = match end {
            Some(key) => Bound::Excluded(key),
            None => Bound::Unbounded,
        };
        if let Some(key) = end
            && key < start
        {
            return Vec::new();
        }
        self.def_tree
            .range((Bound::Included(start), upper))
            .map(|(_, id)| *id)
            .collect()
    }

    pub fn begin_def(&self) -> DefIter {
        self.def_tree.keys().next().cloned()
    }

    pub fn end_def(&self) -> DefIter {
        None
    }

    fn written_extreme(ex: MachExtreme) -> DefKey {
        def_search(WRITTEN_CLASS, Some(SeqNum::extreme(ex)), &Address::extreme(ex), 0)
    }

    pub fn begin_def_flags(&self, fl: u32) -> Result<DefIter> {
        if fl == Varnode::INPUT {
            return Ok(self.begin_def());
        } else if fl == Varnode::WRITTEN {
            return Ok(self.def_lower_bound(&VarnodeBank::written_extreme(MachExtreme::Minimal)));
        }
        Ok(self.def_upper_bound(&VarnodeBank::written_extreme(MachExtreme::Maximal)))
    }

    pub fn end_def_flags(&self, fl: u32) -> Result<DefIter> {
        if fl == Varnode::INPUT {
            return Ok(self.def_lower_bound(&VarnodeBank::written_extreme(MachExtreme::Minimal)));
        } else if fl == Varnode::WRITTEN {
            return Ok(self.def_upper_bound(&VarnodeBank::written_extreme(MachExtreme::Maximal)));
        }
        Ok(None)
    }

    pub fn begin_def_addr(&self, fl: u32, addr: &Address) -> Result<DefIter> {
        if fl == Varnode::WRITTEN {
            return Err(Error::Lowlevel(
                "Cannot get contiguous written AND addressed".to_string(),
            ));
        } else if fl == Varnode::INPUT {
            return Ok(self.def_input_lower_bound(addr));
        }
        Ok(self.def_upper_bound(&def_search(FREE_CLASS, None, addr, 0)))
    }

    pub fn end_def_addr(&self, fl: u32, addr: &Address) -> Result<DefIter> {
        if fl == Varnode::WRITTEN {
            return Err(Error::Lowlevel(
                "Cannot get contiguous written AND addressed".to_string(),
            ));
        } else if fl == Varnode::INPUT {
            return Ok(self.def_input_end(addr));
        }
        Ok(self.def_lower_bound(&def_search(FREE_CLASS, None, addr, 1000000)))
    }

    pub fn verify_integrity(&self) -> Result<()> {
        for vn in self.loc_tree.values() {
            let key = self.varnodes.get(*vn).defiter.as_ref();
            if key.and_then(|key| self.def_tree.get(key)) != Some(vn) {
                return Err(Error::Lowlevel("Varbank loc missing in def".to_string()));
            }
        }
        for vn in self.def_tree.values() {
            let key = self.varnodes.get(*vn).lociter.as_ref();
            if key.and_then(|key| self.loc_tree.get(key)) != Some(vn) {
                return Err(Error::Lowlevel("Varbank def missing in loc".to_string()));
            }
        }
        Ok(())
    }
}

pub fn contiguous_test(data: &Funcdata, vn1: VarnodeId, vn2: VarnodeId) -> bool {
    let first = data.vn(vn1);
    let second = data.vn(vn2);
    if first.is_input() || second.is_input() {
        return false;
    }
    if !first.is_written() || !second.is_written() {
        return false;
    }
    let op1 = data.op(first.get_def().expect("written varnode has no def"));
    let op2 = data.op(second.get_def().expect("written varnode has no def"));
    match op1.code() {
        OpCode::Subpiece => {
            if op2.code() != OpCode::Subpiece {
                return false;
            }
            let vnwhole = op1.get_in(0);
            if op2.get_in(0) != vnwhole {
                return false;
            }
            if data.vn(op2.get_in(1)).get_offset() != 0 {
                return false;
            }
            if data.vn(op1.get_in(1)).get_offset() != second.get_size() as u64 {
                return false;
            }
            true
        }
        _ => false,
    }
}

pub fn find_contiguous_whole(data: &mut Funcdata, vn1: VarnodeId, _vn2: VarnodeId) -> Option<VarnodeId> {
    let first = data.vn(vn1);
    if first.is_written() {
        let def = data.op(first.get_def().expect("written varnode has no def"));
        if def.code() == OpCode::Subpiece {
            return Some(def.get_in(0));
        }
    }
    None
}

#[cfg(test)]
mod tests {
    use std::sync::Arc;

    use super::*;
    use crate::space::AddrSpace;

    fn ram() -> SpaceRef {
        Arc::new(AddrSpace::new_processor("ram", false, 4, 1, 3, 0, 0, 0))
    }

    fn empty_bank() -> VarnodeBank {
        VarnodeBank {
            varnodes: Arena::new(),
            uniq_space: None,
            uniqbase: 0x10000000,
            uniqid: 0x10000000,
            create_index: 0,
            loc_tree: OrderedIndex::default(),
            def_tree: OrderedIndex::default(),
        }
    }

    #[test]
    fn overlap_tests() {
        let spc = ram();
        let big = Varnode::new(4, &Address::new(spc.clone(), 0x10), TypeId(0));
        let small = Varnode::new(2, &Address::new(spc.clone(), 0x12), TypeId(0));
        let outside = Varnode::new(2, &Address::new(spc, 0x13), TypeId(0));
        assert_eq!(big.contains(&small), 0);
        assert_eq!(big.contains(&outside), 1);
        assert_eq!(small.contains(&big), -1);
        assert_eq!(small.overlap(&big), 2);
        assert_eq!(big.overlap(&small), -1);
        assert_eq!(big.characterize_overlap(&small), 1);
        assert!(big.intersects(&outside));
        assert!(!small.intersects_addr(&Address::new(ram(), 0x14), 4));
    }

    #[test]
    fn bank_trees_and_inputs() {
        let spc = ram();
        let mut bank = empty_bank();
        let mut ops: Arena<OpId, PcodeOp> = Arena::new();
        let mut highs: Arena<HighId, HighVariable> = Arena::new();
        let free_first = bank.create(4, &Address::new(spc.clone(), 0x10), TypeId(0));
        let free_second = bank.create(4, &Address::new(spc.clone(), 0x10), TypeId(0));
        let small = bank.create(2, &Address::new(spc.clone(), 0x12), TypeId(0));
        assert_eq!(bank.num_varnodes(), 3);
        let input = bank
            .set_input(free_second, &mut ops, &mut highs)
            .expect("set input failed");
        assert_eq!(input, free_second);
        assert!(bank.get(input).is_input());
        let loc_order = bank.loc_range(&bank.begin_loc(), &bank.end_loc());
        assert_eq!(loc_order, vec![free_second, free_first, small]);
        let addr = Address::new(spc.clone(), 0x10);
        assert_eq!(bank.find_input(4, &addr), Some(free_second));
        assert_eq!(bank.find_input(2, &addr), None);
        assert_eq!(
            bank.find_covering_input(2, &Address::new(spc.clone(), 0x11)),
            Some(free_second)
        );
        assert_eq!(
            bank.find_covered_input(8, &Address::new(spc.clone(), 0xe)),
            Some(free_second)
        );
        assert!(bank.has_input_intersection(4, &Address::new(spc.clone(), 0x12)));
        assert!(!bank.has_input_intersection(4, &Address::new(spc.clone(), 0x14)));
        let frees = bank.loc_range(&bank.begin_loc_flags(4, &addr, 0), &bank.end_loc_flags(4, &addr, 0));
        assert_eq!(frees, vec![free_first]);
        let inputs = bank.def_range(
            &bank.begin_def_flags(Varnode::INPUT).expect("begin def failed"),
            &bank.end_def_flags(Varnode::INPUT).expect("end def failed"),
        );
        assert_eq!(inputs, vec![free_second]);
        let second_input = bank.create(4, &addr, TypeId(0));
        let merged = bank
            .set_input(second_input, &mut ops, &mut highs)
            .expect("set input failed");
        assert_eq!(merged, free_second);
        assert!(!bank.varnodes.contains(second_input));
        bank.verify_integrity().expect("bank trees are inconsistent");
        assert!(bank.destroy(small).is_ok());
        assert_eq!(bank.num_varnodes(), 2);
        bank.make_free(free_second, &ops, &mut highs);
        assert!(bank.get(free_second).is_free());
        bank.verify_integrity().expect("bank trees are inconsistent");
    }
}
