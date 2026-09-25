use crate::stdsort::std_sort;
use std::cmp::Ordering;
use std::ops::{Deref, DerefMut};
use std::sync::Arc;

use crate::address::{ATTRIB_FIRST, ELEM_ADDR};
use crate::address::{Address, Range, RangeList};
use crate::architecture::Architecture;
use crate::architecture::ELEM_RULE;
use crate::arena::Arena;
use crate::database::{Database, ScopeId, Symbol, SymbolId};
use crate::define_id;
use crate::error::{Error, Result};
use crate::funcdata::{AncestorRealistic, Funcdata};
use crate::marshal::{
    ATTRIB_ALIGN, ATTRIB_CONSTRUCTOR, ATTRIB_CONTENT, ATTRIB_DESTRUCTOR, ATTRIB_EXTRAPOP, ATTRIB_HIDDENRETPARM,
    ATTRIB_INDIRECTSTORAGE, ATTRIB_METATYPE, ATTRIB_MODEL, ATTRIB_NAME, ATTRIB_NAMELOCK, ATTRIB_OFFSET, ATTRIB_SIZE,
    ATTRIB_SPACE, ATTRIB_STORAGE, ATTRIB_THISPTR, ATTRIB_TYPELOCK, AttributeId, Decoder, ELEM_INPUT, ELEM_OUTPUT,
    ELEM_RETURNADDRESS, ELEM_VOID, ElementId, Encoder,
};
use crate::modelrules::{
    AssignEnv, ConvertToPointer, FAIL, HIDDENRET_PTRPARAM, HIDDENRET_SPECIALREG, HIDDENRET_SPECIALREG_VOID, ModelRule,
    NO_ASSIGNMENT, SUCCESS, SizeRestrictedFilter,
};
use crate::op::{OpId, PcodeOp};
use crate::opcodes::OpCode;
use crate::pcodeinject::{CALLFIXUP_TYPE, CALLMECHANISM_TYPE, ELEM_INJECT, ELEM_PCODE};
use crate::pcoderaw::VarnodeData;
use crate::rangemap::{RangeMap, RangeRecord, RangeSubsort};
use crate::space::{SpaceRef, SpaceType, same_space};
use crate::translate::{AddrSpaceManager, JoinRecord, Translate};
use crate::types::{TypeClass, TypeFactory, TypeId, TypeMetatype, metatype2typeclass};
use crate::varmap::AliasChecker;
use crate::varnode::{Varnode, VarnodeId};

pub const ATTRIB_CUSTOM: AttributeId = AttributeId::new("custom", 114);
pub const ATTRIB_DOTDOTDOT: AttributeId = AttributeId::new("dotdotdot", 115);
pub const ATTRIB_EXTENSION: AttributeId = AttributeId::new("extension", 116);
pub const ATTRIB_HASTHIS: AttributeId = AttributeId::new("hasthis", 117);
pub const ATTRIB_INLINE: AttributeId = AttributeId::new("inline", 118);
pub const ATTRIB_KILLEDBYCALL: AttributeId = AttributeId::new("killedbycall", 119);
pub const ATTRIB_MAXSIZE: AttributeId = AttributeId::new("maxsize", 120);
pub const ATTRIB_MINSIZE: AttributeId = AttributeId::new("minsize", 121);
pub const ATTRIB_MODELLOCK: AttributeId = AttributeId::new("modellock", 122);
pub const ATTRIB_NORETURN: AttributeId = AttributeId::new("noreturn", 123);
pub const ATTRIB_POINTERMAX: AttributeId = AttributeId::new("pointermax", 124);
pub const ATTRIB_SEPARATEFLOAT: AttributeId = AttributeId::new("separatefloat", 125);
pub const ATTRIB_STACKSHIFT: AttributeId = AttributeId::new("stackshift", 126);
pub const ATTRIB_STRATEGY: AttributeId = AttributeId::new("strategy", 127);
pub const ATTRIB_THISBEFORERETPOINTER: AttributeId = AttributeId::new("thisbeforeretpointer", 128);
pub const ATTRIB_VOIDLOCK: AttributeId = AttributeId::new("voidlock", 129);
pub const ELEM_GROUP: ElementId = ElementId::new("group", 160);
pub const ELEM_INTERNALLIST: ElementId = ElementId::new("internallist", 161);
pub const ELEM_KILLEDBYCALL: ElementId = ElementId::new("killedbycall", 162);
pub const ELEM_LIKELYTRASH: ElementId = ElementId::new("likelytrash", 163);
pub const ELEM_LOCALRANGE: ElementId = ElementId::new("localrange", 164);
pub const ELEM_MODEL: ElementId = ElementId::new("model", 165);
pub const ELEM_PARAM: ElementId = ElementId::new("param", 166);
pub const ELEM_PARAMRANGE: ElementId = ElementId::new("paramrange", 167);
pub const ELEM_PENTRY: ElementId = ElementId::new("pentry", 168);
pub const ELEM_PROTOTYPE: ElementId = ElementId::new("prototype", 169);
pub const ELEM_RESOLVEPROTOTYPE: ElementId = ElementId::new("resolveprototype", 170);
pub const ELEM_RETPARAM: ElementId = ElementId::new("retparam", 171);
pub const ELEM_RETURNSYM: ElementId = ElementId::new("returnsym", 172);
pub const ELEM_UNAFFECTED: ElementId = ElementId::new("unaffected", 173);
pub const ELEM_INTERNAL_STORAGE: ElementId = ElementId::new("internal_storage", 286);

define_id!(CallSpecId);

define_id!(ModelId);

fn space_eq(first: Option<&SpaceRef>, second: Option<&SpaceRef>) -> bool {
    match (first, second) {
        (None, None) => true,
        (Some(left), Some(right)) => left.get_index() == right.get_index(),
        _ => false,
    }
}

fn types_ref(glb: &Architecture) -> &TypeFactory {
    glb.types.as_deref().expect("architecture has no type factory")
}

fn types_mut(glb: &mut Architecture) -> &mut TypeFactory {
    glb.types.as_deref_mut().expect("architecture has no type factory")
}

fn symtab_ref(glb: &Architecture) -> &Database {
    glb.symboltab.as_deref().expect("architecture has no symbol table")
}

#[derive(Clone, Debug)]
pub struct ParamEntry {
    flags: u32,
    tp: TypeClass,
    group_set: Vec<i32>,
    spaceid: Option<SpaceRef>,
    addressbase: u64,
    size: i32,
    minsize: i32,
    alignment: i32,
    numslots: i32,
    joinrec: Option<Arc<JoinRecord>>,
}

impl ParamEntry {
    pub const FORCE_LEFT_JUSTIFY: u32 = 1;
    pub const REVERSE_STACK: u32 = 2;
    pub const SMALLSIZE_ZEXT: u32 = 4;
    pub const SMALLSIZE_SEXT: u32 = 8;
    pub const SMALLSIZE_INTTYPE: u32 = 0x20;
    pub const SMALLSIZE_FLOATEXT: u32 = 0x40;
    pub const EXTRACHECK_HIGH: u32 = 0x80;
    pub const EXTRACHECK_LOW: u32 = 0x100;
    pub const IS_GROUPED: u32 = 0x200;
    pub const OVERLAPPING: u32 = 0x400;
    pub const FIRST_STORAGE: u32 = 0x800;

    pub const NO_CONTAINMENT: i32 = 0;
    pub const CONTAINS_UNJUSTIFIED: i32 = 1;
    pub const CONTAINS_JUSTIFIED: i32 = 2;
    pub const CONTAINED_BY: i32 = 3;

    pub fn new(grp: i32) -> ParamEntry {
        ParamEntry {
            flags: 0,
            tp: TypeClass::General,
            group_set: vec![grp],
            spaceid: None,
            addressbase: 0,
            size: 0,
            minsize: 0,
            alignment: 0,
            numslots: 0,
            joinrec: None,
        }
    }

    fn space(&self) -> &SpaceRef {
        self.spaceid.as_ref().expect("param entry has no address space")
    }

    pub fn find_entry_by_storage(entry_list: &[Arc<ParamEntry>], vn: &VarnodeData) -> Option<usize> {
        for index in (0..entry_list.len()).rev() {
            let entry = &entry_list[index];
            if same_space(&entry.spaceid, &vn.space) && entry.addressbase == vn.offset && entry.size as u32 == vn.size {
                return Some(index);
            }
        }
        None
    }

    pub fn resolve_first(&mut self, cur_list: &[Arc<ParamEntry>]) {
        match cur_list.last() {
            None => self.flags |= ParamEntry::FIRST_STORAGE,
            Some(previous) => {
                if self.tp != previous.tp {
                    self.flags |= ParamEntry::FIRST_STORAGE;
                }
            }
        }
    }

    pub fn resolve_join(&mut self, cur_list: &[Arc<ParamEntry>]) -> Result<()> {
        self.joinrec = self.space().find_join(self.addressbase)?;
        let Some(joinrec) = self.joinrec.clone() else {
            return Ok(());
        };
        self.group_set.clear();
        for index in 0..joinrec.num_pieces() {
            if let Some(found) = ParamEntry::find_entry_by_storage(cur_list, joinrec.get_piece(index)) {
                let groups = cur_list[found].group_set.clone();
                self.group_set.extend(groups);
                self.flags |= if index == 0 {
                    ParamEntry::EXTRACHECK_LOW
                } else {
                    ParamEntry::EXTRACHECK_HIGH
                };
            }
        }
        if self.group_set.is_empty() {
            return Err(Error::Lowlevel(
                "<pentry> join must overlap at least one previous entry".to_string(),
            ));
        }
        self.group_set.sort();
        self.flags |= ParamEntry::OVERLAPPING;
        Ok(())
    }

    pub fn resolve_overlap(&mut self, cur_list: &[Arc<ParamEntry>]) -> Result<()> {
        if self.joinrec.is_some() {
            return Ok(());
        }
        let mut overlap_set: Vec<i32> = Vec::new();
        let addr = Address::from_parts(self.spaceid.clone(), self.addressbase);
        for entry in cur_list {
            if !entry.intersects(&addr, self.size) {
                continue;
            }
            if self.contains(entry) {
                if entry.is_overlap() {
                    continue;
                }
                overlap_set.extend_from_slice(&entry.group_set);
                let big_endian = self.space().is_big_endian();
                if self.addressbase == entry.addressbase {
                    self.flags |= if big_endian {
                        ParamEntry::EXTRACHECK_LOW
                    } else {
                        ParamEntry::EXTRACHECK_HIGH
                    };
                } else {
                    self.flags |= if big_endian {
                        ParamEntry::EXTRACHECK_HIGH
                    } else {
                        ParamEntry::EXTRACHECK_LOW
                    };
                }
            } else {
                return Err(Error::Lowlevel(
                    "Illegal overlap of <pentry> in compiler spec".to_string(),
                ));
            }
        }
        if overlap_set.is_empty() {
            return Ok(());
        }
        overlap_set.sort();
        self.group_set = overlap_set;
        self.flags |= ParamEntry::OVERLAPPING;
        Ok(())
    }

    pub fn is_left_justified(&self) -> bool {
        ((self.flags & ParamEntry::FORCE_LEFT_JUSTIFY) != 0) || !self.space().is_big_endian()
    }

    pub fn get_group(&self) -> i32 {
        self.group_set[0]
    }

    pub fn get_all_groups(&self) -> &Vec<i32> {
        &self.group_set
    }

    pub fn group_overlap(&self, op2: &ParamEntry) -> bool {
        let mut index_this = 0usize;
        let mut index_other = 0usize;
        let mut val_this = self.group_set[index_this];
        let mut val_other = op2.group_set[index_other];
        while val_this != val_other {
            if val_this < val_other {
                index_this += 1;
                if index_this >= self.group_set.len() {
                    return false;
                }
                val_this = self.group_set[index_this];
            } else {
                index_other += 1;
                if index_other >= op2.group_set.len() {
                    return false;
                }
                val_other = op2.group_set[index_other];
            }
        }
        true
    }

    pub fn get_size(&self) -> i32 {
        self.size
    }

    pub fn get_min_size(&self) -> i32 {
        self.minsize
    }

    pub fn get_align(&self) -> i32 {
        self.alignment
    }

    pub fn get_join_record(&self) -> Option<&Arc<JoinRecord>> {
        self.joinrec.as_ref()
    }

    pub fn get_type(&self) -> TypeClass {
        self.tp
    }

    pub fn is_exclusion(&self) -> bool {
        self.alignment == 0
    }

    pub fn is_reverse_stack(&self) -> bool {
        (self.flags & ParamEntry::REVERSE_STACK) != 0
    }

    pub fn is_grouped(&self) -> bool {
        (self.flags & ParamEntry::IS_GROUPED) != 0
    }

    pub fn is_overlap(&self) -> bool {
        (self.flags & ParamEntry::OVERLAPPING) != 0
    }

    pub fn is_first_in_class(&self) -> bool {
        (self.flags & ParamEntry::FIRST_STORAGE) != 0
    }

    pub fn subsumes_definition(&self, op2: &ParamEntry) -> bool {
        if self.tp != TypeClass::General && op2.tp != self.tp {
            return false;
        }
        if !same_space(&self.spaceid, &op2.spaceid) {
            return false;
        }
        if op2.addressbase < self.addressbase {
            return false;
        }
        let op2_end = op2.addressbase.wrapping_add(op2.size as i64 as u64).wrapping_sub(1);
        let this_end = self.addressbase.wrapping_add(self.size as i64 as u64).wrapping_sub(1);
        if op2_end > this_end {
            return false;
        }
        if self.alignment != op2.alignment {
            return false;
        }
        true
    }

    pub fn contained_by(&self, addr: &Address, sz: i32) -> bool {
        if !space_eq(self.spaceid.as_ref(), addr.get_space()) {
            return false;
        }
        if self.addressbase < addr.get_offset() {
            return false;
        }
        let entryoff = self.addressbase.wrapping_add(self.size as i64 as u64).wrapping_sub(1);
        let rangeoff = addr.get_offset().wrapping_add(sz as i64 as u64).wrapping_sub(1);
        entryoff <= rangeoff
    }

    pub fn intersects(&self, addr: &Address, sz: i32) -> bool {
        if let Some(joinrec) = &self.joinrec {
            let rangeend = addr.get_offset().wrapping_add(sz as i64 as u64).wrapping_sub(1);
            for index in 0..joinrec.num_pieces() {
                let vdata = joinrec.get_piece(index);
                if !space_eq(addr.get_space(), vdata.space.as_ref()) {
                    continue;
                }
                let vdataend = vdata.offset.wrapping_add(vdata.size as u64).wrapping_sub(1);
                if addr.get_offset() < vdata.offset && rangeend < vdataend {
                    continue;
                }
                if addr.get_offset() > vdata.offset && rangeend > vdataend {
                    continue;
                }
                return true;
            }
        }
        if !space_eq(self.spaceid.as_ref(), addr.get_space()) {
            return false;
        }
        let rangeend = addr.get_offset().wrapping_add(sz as i64 as u64).wrapping_sub(1);
        let thisend = self.addressbase.wrapping_add(self.size as i64 as u64).wrapping_sub(1);
        if addr.get_offset() < self.addressbase && rangeend < thisend {
            return false;
        }
        if addr.get_offset() > self.addressbase && rangeend > thisend {
            return false;
        }
        true
    }

    pub fn justified_contain(&self, addr: &Address, sz: i32) -> i32 {
        if let Some(joinrec) = &self.joinrec {
            let mut res = 0;
            for index in (0..joinrec.num_pieces()).rev() {
                let vdata = joinrec.get_piece(index);
                let cur = vdata.get_addr().justified_contain(vdata.size as i32, addr, sz, false);
                if cur < 0 {
                    res += vdata.size as i32;
                } else {
                    return res + cur;
                }
            }
            return -1;
        }
        if self.alignment == 0 {
            let entry = Address::from_parts(self.spaceid.clone(), self.addressbase);
            return entry.justified_contain(self.size, addr, sz, (self.flags & ParamEntry::FORCE_LEFT_JUSTIFY) != 0);
        }
        if !space_eq(self.spaceid.as_ref(), addr.get_space()) {
            return -1;
        }
        let mut startaddr = addr.get_offset();
        if startaddr < self.addressbase {
            return -1;
        }
        let mut endaddr = startaddr.wrapping_add(sz as i64 as u64).wrapping_sub(1);
        if endaddr < startaddr {
            return -1;
        }
        if endaddr > self.addressbase.wrapping_add(self.size as i64 as u64).wrapping_sub(1) {
            return -1;
        }
        startaddr = startaddr.wrapping_sub(self.addressbase);
        endaddr = endaddr.wrapping_sub(self.addressbase);
        let alignment = self.alignment as i64 as u64;
        if !self.is_left_justified() {
            let res = (endaddr.wrapping_add(1) % alignment) as i32;
            if res == 0 {
                return 0;
            }
            return self.alignment - res;
        }
        (startaddr % alignment) as i32
    }

    pub fn get_container(&self, addr: &Address, sz: i32, res: &mut VarnodeData) -> bool {
        let endaddr = addr.add((sz - 1) as i64);
        if let Some(joinrec) = &self.joinrec {
            for index in (0..joinrec.num_pieces()).rev() {
                let vdata = joinrec.get_piece(index);
                if addr.overlap(0, &vdata.get_addr(), vdata.size as i32) >= 0
                    && endaddr.overlap(0, &vdata.get_addr(), vdata.size as i32) >= 0
                {
                    *res = vdata.clone();
                    return true;
                }
            }
            return false;
        }
        let entry = Address::from_parts(self.spaceid.clone(), self.addressbase);
        if addr.overlap(0, &entry, self.size) < 0 {
            return false;
        }
        if endaddr.overlap(0, &entry, self.size) < 0 {
            return false;
        }
        if self.alignment == 0 {
            res.space = self.spaceid.clone();
            res.offset = self.addressbase;
            res.size = self.size as u32;
            return true;
        }
        let alignment = self.alignment as i64 as u64;
        let al = addr.get_offset().wrapping_sub(self.addressbase) % alignment;
        res.space = self.spaceid.clone();
        res.offset = addr.get_offset().wrapping_sub(al);
        res.size = (endaddr.get_offset().wrapping_sub(res.offset) as i32).wrapping_add(1) as u32;
        let al2 = res.size % (self.alignment as u32);
        if al2 != 0 {
            res.size = res.size.wrapping_add((self.alignment as u32).wrapping_sub(al2));
        }
        true
    }

    pub fn contains(&self, op2: &ParamEntry) -> bool {
        if op2.joinrec.is_some() {
            return false;
        }
        let Some(joinrec) = &self.joinrec else {
            let addr = Address::from_parts(self.spaceid.clone(), self.addressbase);
            return op2.contained_by(&addr, self.size);
        };
        for index in 0..joinrec.num_pieces() {
            let vdata = joinrec.get_piece(index);
            let addr = vdata.get_addr();
            if op2.contained_by(&addr, vdata.size as i32) {
                return true;
            }
        }
        false
    }

    pub fn assumed_extension(&self, addr: &Address, sz: i32, res: &mut VarnodeData) -> OpCode {
        if (self.flags & (ParamEntry::SMALLSIZE_ZEXT | ParamEntry::SMALLSIZE_SEXT | ParamEntry::SMALLSIZE_INTTYPE)) == 0
        {
            return OpCode::Copy;
        }
        if self.alignment != 0 {
            if sz >= self.alignment {
                return OpCode::Copy;
            }
        } else if sz >= self.size {
            return OpCode::Copy;
        }
        if self.joinrec.is_some() {
            return OpCode::Copy;
        }
        if self.justified_contain(addr, sz) != 0 {
            return OpCode::Copy;
        }
        if self.alignment == 0 {
            res.space = self.spaceid.clone();
            res.offset = self.addressbase;
            res.size = self.size as u32;
        } else {
            res.space = self.spaceid.clone();
            let align_adjust =
                (addr.get_offset().wrapping_sub(self.addressbase) % (self.alignment as i64 as u64)) as i32;
            res.offset = addr.get_offset().wrapping_sub(align_adjust as i64 as u64);
            res.size = self.alignment as u32;
        }
        if (self.flags & ParamEntry::SMALLSIZE_ZEXT) != 0 {
            return OpCode::IntZext;
        }
        if (self.flags & ParamEntry::SMALLSIZE_INTTYPE) != 0 {
            return OpCode::Piece;
        }
        OpCode::IntSext
    }

    pub fn get_slot(&self, addr: &Address, skip: i32) -> i32 {
        let mut res = self.group_set[0];
        if self.alignment != 0 {
            let diff = addr
                .get_offset()
                .wrapping_add(skip as i64 as u64)
                .wrapping_sub(self.addressbase);
            let baseslot = (diff as i32).wrapping_div(self.alignment);
            if self.is_reverse_stack() {
                res += (self.numslots - 1) - baseslot;
            } else {
                res += baseslot;
            }
        } else if skip != 0 {
            res = *self.group_set.last().expect("param entry has no groups");
        }
        res
    }

    pub fn get_space(&self) -> Option<&SpaceRef> {
        self.spaceid.as_ref()
    }

    pub fn get_base(&self) -> u64 {
        self.addressbase
    }

    pub fn get_addr_by_slot_justified(
        &self,
        slot: &mut i32,
        sz: i32,
        type_align: i32,
        justify_right: bool,
        manager: &AddrSpaceManager,
    ) -> Result<Address> {
        let mut res = Address::invalid();
        let spaceused;
        if sz < self.minsize {
            return Ok(res);
        }
        if self.alignment == 0 {
            if *slot != 0 {
                return Ok(res);
            }
            if sz > self.size {
                return Ok(res);
            }
            res = Address::from_parts(self.spaceid.clone(), self.addressbase);
            spaceused = self.size;
            if (self.flags & ParamEntry::SMALLSIZE_FLOATEXT) != 0 && sz != self.size {
                res = manager.construct_float_extension_address(&res, self.size, sz)?;
                return Ok(res);
            }
        } else {
            if type_align > self.alignment {
                let tmp = (*slot * self.alignment) % type_align;
                if tmp != 0 {
                    *slot += (type_align - tmp) / self.alignment;
                }
            }
            let mut slotsused = sz / self.alignment;
            if (sz % self.alignment) != 0 {
                slotsused += 1;
            }
            if *slot + slotsused > self.numslots {
                return Ok(res);
            }
            spaceused = slotsused * self.alignment;
            let index = if self.is_reverse_stack() {
                self.numslots - *slot - slotsused
            } else {
                *slot
            };
            res = Address::from_parts(
                self.spaceid.clone(),
                self.addressbase
                    .wrapping_add(index.wrapping_mul(self.alignment) as i64 as u64),
            );
            *slot += slotsused;
        }
        if justify_right {
            res = res.add((spaceused - sz) as i64);
        }
        Ok(res)
    }

    pub fn get_addr_by_slot(
        &self,
        slot: &mut i32,
        sz: i32,
        type_align: i32,
        manager: &AddrSpaceManager,
    ) -> Result<Address> {
        let justify_right = !self.is_left_justified();
        self.get_addr_by_slot_justified(slot, sz, type_align, justify_right, manager)
    }

    pub fn decode(
        &mut self,
        decoder: &mut dyn Decoder,
        normalstack: bool,
        grouped: bool,
        cur_list: &[Arc<ParamEntry>],
    ) -> Result<()> {
        self.flags = 0;
        self.tp = TypeClass::General;
        self.size = -1;
        self.minsize = -1;
        self.alignment = 0;
        self.numslots = 1;

        let elem_id = decoder.open_element_expect(ELEM_PENTRY)?;
        loop {
            let attrib_id = decoder.get_next_attribute_id()?;
            if attrib_id == 0 {
                break;
            }
            if attrib_id == ATTRIB_MINSIZE {
                self.minsize = decoder.read_signed_integer()? as i32;
            } else if attrib_id == ATTRIB_SIZE || attrib_id == ATTRIB_ALIGN {
                self.alignment = decoder.read_signed_integer()? as i32;
            } else if attrib_id == ATTRIB_MAXSIZE {
                self.size = decoder.read_signed_integer()? as i32;
            } else if attrib_id == ATTRIB_STORAGE || attrib_id == ATTRIB_METATYPE {
                self.tp = crate::types::string2typeclass(&decoder.read_string()?)?;
            } else if attrib_id == ATTRIB_EXTENSION {
                self.flags &=
                    !(ParamEntry::SMALLSIZE_ZEXT | ParamEntry::SMALLSIZE_SEXT | ParamEntry::SMALLSIZE_INTTYPE);
                let ext = decoder.read_string()?;
                if ext == "sign" {
                    self.flags |= ParamEntry::SMALLSIZE_SEXT;
                } else if ext == "zero" {
                    self.flags |= ParamEntry::SMALLSIZE_ZEXT;
                } else if ext == "inttype" {
                    self.flags |= ParamEntry::SMALLSIZE_INTTYPE;
                } else if ext == "float" {
                    self.flags |= ParamEntry::SMALLSIZE_FLOATEXT;
                } else if ext != "none" {
                    return Err(Error::Lowlevel("Bad extension attribute".to_string()));
                }
            } else {
                return Err(Error::Lowlevel("Unknown <pentry> attribute".to_string()));
            }
        }
        if self.size == -1 || self.minsize == -1 {
            return Err(Error::Lowlevel("ParamEntry not fully specified".to_string()));
        }
        if self.alignment == self.size {
            self.alignment = 0;
        }
        let addr = Address::decode(decoder)?;
        decoder.close_element(elem_id)?;
        self.spaceid = addr.get_space().cloned();
        self.addressbase = addr.get_offset();
        if self.alignment != 0 {
            self.numslots = self.size / self.alignment;
        }
        if self.space().is_reverse_justified() {
            if self.space().is_big_endian() {
                self.flags |= ParamEntry::FORCE_LEFT_JUSTIFY;
            } else {
                return Err(Error::Lowlevel(
                    "No support for right justification in little endian encoding".to_string(),
                ));
            }
        }
        if !normalstack {
            self.flags |= ParamEntry::REVERSE_STACK;
            if self.alignment != 0 && (self.size % self.alignment) != 0 {
                return Err(Error::Lowlevel(
                    "For positive stack growth, <pentry> size must match alignment".to_string(),
                ));
            }
        }
        if grouped {
            self.flags |= ParamEntry::IS_GROUPED;
        }
        self.resolve_first(cur_list);
        self.resolve_join(cur_list)?;
        self.resolve_overlap(cur_list)?;
        Ok(())
    }

    pub fn is_param_check_high(&self) -> bool {
        (self.flags & ParamEntry::EXTRACHECK_HIGH) != 0
    }

    pub fn is_param_check_low(&self) -> bool {
        (self.flags & ParamEntry::EXTRACHECK_LOW) != 0
    }

    pub fn order_within_group(entry1: &ParamEntry, entry2: &ParamEntry) -> Result<()> {
        if entry2.minsize > entry1.size || entry1.minsize > entry2.size {
            return Ok(());
        }
        if entry1.tp != entry2.tp {
            if entry1.tp == TypeClass::General {
                return Err(Error::Lowlevel(
                    "<pentry> tags with a specific type must come before the general type".to_string(),
                ));
            }
            return Ok(());
        }
        Err(Error::Lowlevel(
            "<pentry> tags within a group must be distinguished by size or type".to_string(),
        ))
    }
}

#[derive(Clone, Copy, Debug)]
pub struct InitData {
    position: i32,
    entry: usize,
}

impl InitData {
    pub fn new(pos: i32, entry: usize) -> InitData {
        InitData { position: pos, entry }
    }
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, PartialOrd, Ord)]
pub struct SubsortPosition {
    position: i32,
}

impl SubsortPosition {
    pub fn new(pos: i32) -> SubsortPosition {
        SubsortPosition { position: pos }
    }

    pub fn from_bool(val: bool) -> SubsortPosition {
        SubsortPosition {
            position: if val { 1000000 } else { 0 },
        }
    }
}

#[derive(Clone, Debug)]
pub struct ParamEntryRange {
    first: u64,
    last: u64,
    position: i32,
    entry: usize,
}

impl ParamEntryRange {
    pub fn new(data: &InitData, first: u64, last: u64) -> ParamEntryRange {
        ParamEntryRange {
            first,
            last,
            position: data.position,
            entry: data.entry,
        }
    }

    pub fn get_first(&self) -> u64 {
        self.first
    }

    pub fn get_last(&self) -> u64 {
        self.last
    }

    pub fn get_subsort(&self) -> SubsortPosition {
        SubsortPosition::new(self.position)
    }

    pub fn get_param_entry(&self) -> usize {
        self.entry
    }
}

impl RangeSubsort for SubsortPosition {
    fn from_bool(val: bool) -> SubsortPosition {
        SubsortPosition::from_bool(val)
    }
}

impl RangeRecord for ParamEntryRange {
    type Line = u64;
    type Subsort = SubsortPosition;
    type Init = InitData;

    fn new_record(data: &InitData, first: u64, last: u64) -> ParamEntryRange {
        ParamEntryRange::new(data, first, last)
    }

    fn get_first(&self) -> u64 {
        self.first
    }

    fn get_last(&self) -> u64 {
        self.last
    }

    fn get_subsort(&self) -> SubsortPosition {
        SubsortPosition::new(self.position)
    }
}

pub type ParamEntryResolver = RangeMap<ParamEntryRange>;

#[derive(Clone, Debug)]
pub struct ParamTrial {
    flags: u32,
    addr: Address,
    size: i32,
    slot: i32,
    entry: Option<usize>,
    entry_data: Option<Arc<ParamEntry>>,
    offset: i32,
    fixed_position: i32,
}

impl ParamTrial {
    pub const CHECKED: u32 = 1;
    pub const USED: u32 = 2;
    pub const DEFNOUSE: u32 = 4;
    pub const ACTIVE: u32 = 8;
    pub const UNREF: u32 = 0x10;
    pub const KILLEDBYCALL: u32 = 0x20;
    pub const REM_FORMED: u32 = 0x40;
    pub const INDCREATE_FORMED: u32 = 0x80;
    pub const CONDEXE_EFFECT: u32 = 0x100;
    pub const ANCESTOR_REALISTIC: u32 = 0x200;
    pub const ANCESTOR_SOLID: u32 = 0x400;

    pub fn new(ad: &Address, sz: i32, sl: i32) -> ParamTrial {
        ParamTrial {
            flags: 0,
            addr: ad.clone(),
            size: sz,
            slot: sl,
            entry: None,
            entry_data: None,
            offset: -1,
            fixed_position: -1,
        }
    }

    pub fn new_from(op2: &ParamTrial, sl: i32) -> ParamTrial {
        ParamTrial {
            flags: op2.flags,
            addr: op2.addr.clone(),
            size: op2.size,
            slot: sl,
            entry: None,
            entry_data: None,
            offset: -1,
            fixed_position: -1,
        }
    }

    pub fn get_address(&self) -> &Address {
        &self.addr
    }

    pub fn get_size(&self) -> i32 {
        self.size
    }

    pub fn get_slot(&self) -> i32 {
        self.slot
    }

    pub fn set_slot(&mut self, val: i32) {
        self.slot = val;
    }

    pub fn get_entry(&self) -> Option<usize> {
        self.entry
    }

    pub fn get_entry_data(&self) -> Option<&ParamEntry> {
        self.entry_data.as_deref()
    }

    pub fn get_offset(&self) -> i32 {
        self.offset
    }

    pub fn set_entry(&mut self, ent: Option<(usize, &Arc<ParamEntry>)>, off: i32) {
        match ent {
            Some((index, data)) => {
                self.entry = Some(index);
                self.entry_data = Some(data.clone());
            }
            None => {
                self.entry = None;
                self.entry_data = None;
            }
        }
        self.offset = off;
    }

    pub fn mark_used(&mut self) {
        self.flags |= ParamTrial::USED;
    }

    pub fn mark_active(&mut self) {
        self.flags |= ParamTrial::ACTIVE | ParamTrial::CHECKED;
    }

    pub fn mark_inactive(&mut self) {
        self.flags &= !ParamTrial::ACTIVE;
        self.flags |= ParamTrial::CHECKED;
    }

    pub fn mark_no_use(&mut self) {
        self.flags &= !(ParamTrial::ACTIVE | ParamTrial::USED);
        self.flags |= ParamTrial::CHECKED | ParamTrial::DEFNOUSE;
    }

    pub fn mark_unref(&mut self) {
        self.flags |= ParamTrial::UNREF | ParamTrial::CHECKED;
        self.slot = -1;
    }

    pub fn mark_killed_by_call(&mut self) {
        self.flags |= ParamTrial::KILLEDBYCALL;
    }

    pub fn is_checked(&self) -> bool {
        (self.flags & ParamTrial::CHECKED) != 0
    }

    pub fn is_active(&self) -> bool {
        (self.flags & ParamTrial::ACTIVE) != 0
    }

    pub fn is_definitely_not_used(&self) -> bool {
        (self.flags & ParamTrial::DEFNOUSE) != 0
    }

    pub fn is_used(&self) -> bool {
        (self.flags & ParamTrial::USED) != 0
    }

    pub fn is_unref(&self) -> bool {
        (self.flags & ParamTrial::UNREF) != 0
    }

    pub fn is_killed_by_call(&self) -> bool {
        (self.flags & ParamTrial::KILLEDBYCALL) != 0
    }

    pub fn set_rem_formed(&mut self) {
        self.flags |= ParamTrial::REM_FORMED;
    }

    pub fn is_rem_formed(&self) -> bool {
        (self.flags & ParamTrial::REM_FORMED) != 0
    }

    pub fn set_ind_create_formed(&mut self) {
        self.flags |= ParamTrial::INDCREATE_FORMED;
    }

    pub fn is_ind_create_formed(&self) -> bool {
        (self.flags & ParamTrial::INDCREATE_FORMED) != 0
    }

    pub fn set_cond_exe_effect(&mut self) {
        self.flags |= ParamTrial::CONDEXE_EFFECT;
    }

    pub fn has_cond_exe_effect(&self) -> bool {
        (self.flags & ParamTrial::CONDEXE_EFFECT) != 0
    }

    pub fn set_ancestor_realistic(&mut self) {
        self.flags |= ParamTrial::ANCESTOR_REALISTIC;
    }

    pub fn has_ancestor_realistic(&self) -> bool {
        (self.flags & ParamTrial::ANCESTOR_REALISTIC) != 0
    }

    pub fn set_ancestor_solid(&mut self) {
        self.flags |= ParamTrial::ANCESTOR_SOLID;
    }

    pub fn has_ancestor_solid(&self) -> bool {
        (self.flags & ParamTrial::ANCESTOR_SOLID) != 0
    }

    pub fn slot_group(&self) -> i32 {
        self.entry_data
            .as_ref()
            .expect("trial has no param entry")
            .get_slot(&self.addr, self.size - 1)
    }

    pub fn set_address(&mut self, ad: &Address, sz: i32) {
        self.addr = ad.clone();
        self.size = sz;
    }

    pub fn split_hi(&self, sz: i32) -> ParamTrial {
        let mut res = ParamTrial::new(&self.addr, sz, self.slot);
        res.flags = self.flags;
        res
    }

    pub fn split_lo(&self, sz: i32) -> ParamTrial {
        let newaddr = self.addr.add((self.size - sz) as i64);
        let mut res = ParamTrial::new(&newaddr, sz, self.slot + 1);
        res.flags = self.flags;
        res
    }

    pub fn test_shrink(&self, newaddr: &Address, sz: i32) -> bool {
        let testaddr = if self.addr.is_big_endian() {
            self.addr.add((self.size - sz) as i64)
        } else {
            self.addr.clone()
        };
        if testaddr != *newaddr {
            return false;
        }
        if self.entry.is_some() {
            return false;
        }
        true
    }

    pub fn less_than(&self, other: &ParamTrial) -> bool {
        let (Some(entry_a), Some(data_a)) = (self.entry, self.entry_data.as_ref()) else {
            return false;
        };
        let (Some(entry_b), Some(data_b)) = (other.entry, other.entry_data.as_ref()) else {
            return true;
        };
        let grpa = data_a.get_group();
        let grpb = data_b.get_group();
        if grpa != grpb {
            return grpa < grpb;
        }
        if entry_a != entry_b {
            return entry_a < entry_b;
        }
        if data_a.is_exclusion() {
            return self.offset < other.offset;
        }
        if self.addr != other.addr {
            if data_a.is_reverse_stack() {
                return other.addr < self.addr;
            }
            return self.addr < other.addr;
        }
        self.size < other.size
    }

    pub fn set_fixed_position(&mut self, pos: i32) {
        self.fixed_position = pos;
    }

    pub fn fixed_position_compare(first: &ParamTrial, other: &ParamTrial) -> bool {
        if first.fixed_position == -1 && other.fixed_position == -1 {
            return first.less_than(other);
        }
        if first.fixed_position == -1 {
            return false;
        }
        if other.fixed_position == -1 {
            return true;
        }
        first.fixed_position < other.fixed_position
    }
}

#[derive(Clone, Debug)]
pub struct ParamActive {
    trial: Vec<ParamTrial>,
    slotbase: i32,
    stackplaceholder: i32,
    numpasses: i32,
    maxpass: i32,
    isfullychecked: bool,
    needsfinalcheck: bool,
    recoversubcall: bool,
    join_reverse: bool,
}

impl ParamActive {
    pub fn new(recoversub: bool) -> ParamActive {
        ParamActive {
            trial: Vec::new(),
            slotbase: 1,
            stackplaceholder: -1,
            numpasses: 0,
            maxpass: 0,
            isfullychecked: false,
            needsfinalcheck: false,
            recoversubcall: recoversub,
            join_reverse: false,
        }
    }

    pub fn clear(&mut self) {
        self.trial.clear();
        self.slotbase = 1;
        self.stackplaceholder = -1;
        self.numpasses = 0;
        self.isfullychecked = false;
        self.join_reverse = false;
    }

    pub fn register_trial(&mut self, addr: &Address, sz: i32) {
        self.trial.push(ParamTrial::new(addr, sz, self.slotbase));
        let spacebase = addr
            .get_space()
            .is_some_and(|spc| spc.get_type() == SpaceType::Spacebase);
        if !spacebase {
            self.trial
                .last_mut()
                .expect("trial was just registered")
                .mark_killed_by_call();
        }
        self.slotbase += 1;
    }

    pub fn reregister_trial(&mut self, old_trial: &ParamTrial) {
        self.trial.push(ParamTrial::new_from(old_trial, self.slotbase));
        self.slotbase += 1;
    }

    pub fn get_num_trials(&self) -> i32 {
        self.trial.len() as i32
    }

    pub fn get_trial(&self, index: i32) -> &ParamTrial {
        &self.trial[index as usize]
    }

    pub fn get_trial_mut(&mut self, index: i32) -> &mut ParamTrial {
        &mut self.trial[index as usize]
    }

    pub fn get_trial_for_input_varnode(&self, slot: i32) -> &ParamTrial {
        let adjusted = slot
            - if self.stackplaceholder < 0 || slot < self.stackplaceholder {
                1
            } else {
                2
            };
        &self.trial[adjusted as usize]
    }

    pub fn which_trial(&self, addr: &Address, sz: i32) -> i32 {
        for (index, trial) in self.trial.iter().enumerate() {
            if addr.overlap(0, trial.get_address(), trial.get_size()) >= 0 {
                return index as i32;
            }
            if sz <= 1 {
                return -1;
            }
            let endaddr = addr.add((sz - 1) as i64);
            if endaddr.overlap(0, trial.get_address(), trial.get_size()) >= 0 {
                return index as i32;
            }
        }
        -1
    }

    pub fn needs_final_check(&self) -> bool {
        self.needsfinalcheck
    }

    pub fn mark_needs_final_check(&mut self) {
        self.needsfinalcheck = true;
    }

    pub fn is_join_reverse(&self) -> bool {
        self.join_reverse
    }

    pub fn set_join_reverse(&mut self) {
        self.join_reverse = true;
    }

    pub fn is_recover_subcall(&self) -> bool {
        self.recoversubcall
    }

    pub fn is_fully_checked(&self) -> bool {
        self.isfullychecked
    }

    pub fn mark_fully_checked(&mut self) {
        self.isfullychecked = true;
    }

    pub fn set_placeholder_slot(&mut self) {
        self.stackplaceholder = self.slotbase;
        self.slotbase += 1;
    }

    pub fn free_placeholder_slot(&mut self) {
        for trial in self.trial.iter_mut() {
            if trial.get_slot() > self.stackplaceholder {
                let slot = trial.get_slot();
                trial.set_slot(slot - 1);
            }
        }
        self.stackplaceholder = -2;
        self.slotbase -= 1;
        self.maxpass = 0;
    }

    pub fn get_num_passes(&self) -> i32 {
        self.numpasses
    }

    pub fn get_max_pass(&self) -> i32 {
        self.maxpass
    }

    pub fn set_max_pass(&mut self, val: i32) {
        self.maxpass = val;
    }

    pub fn finish_pass(&mut self) {
        self.numpasses += 1;
    }

    pub fn sort_trials(&mut self) {
        std_sort(&mut self.trial, ParamTrial::less_than);
    }

    pub fn sort_fixed_position(&mut self) {
        std_sort(&mut self.trial, ParamTrial::fixed_position_compare);
    }

    pub fn delete_unused_trials(&mut self) {
        let mut newtrials: Vec<ParamTrial> = Vec::new();
        let mut slot = 1;
        for curtrial in self.trial.iter_mut() {
            if curtrial.is_used() {
                curtrial.set_slot(slot);
                slot += 1;
                newtrials.push(curtrial.clone());
            }
        }
        self.trial = newtrials;
    }

    pub fn split_trial(&mut self, index: i32, sz: i32) -> Result<()> {
        if self.stackplaceholder >= 0 {
            return Err(Error::Lowlevel(
                "Cannot split parameter when the placeholder has not been recovered".to_string(),
            ));
        }
        let index = index as usize;
        let mut newtrials: Vec<ParamTrial> = Vec::new();
        let slot = self.trial[index].get_slot();
        for position in 0..index {
            let mut copy = self.trial[position].clone();
            let oldslot = copy.get_slot();
            if oldslot > slot {
                copy.set_slot(oldslot + 1);
            }
            newtrials.push(copy);
        }
        newtrials.push(self.trial[index].split_hi(sz));
        newtrials.push(self.trial[index].split_lo(self.trial[index].get_size() - sz));
        for position in (index + 1)..self.trial.len() {
            let mut copy = self.trial[position].clone();
            let oldslot = copy.get_slot();
            if oldslot > slot {
                copy.set_slot(oldslot + 1);
            }
            newtrials.push(copy);
        }
        self.slotbase += 1;
        self.trial = newtrials;
        Ok(())
    }

    pub fn join_trial(&mut self, slot: i32, addr: &Address, sz: i32) -> Result<()> {
        if self.stackplaceholder >= 0 {
            return Err(Error::Lowlevel(
                "Cannot join parameters when the placeholder has not been removed".to_string(),
            ));
        }
        let mut newtrials: Vec<ParamTrial> = Vec::new();
        let mut sizecheck = 0;
        for curtrial in &self.trial {
            let curslot = curtrial.get_slot();
            if curslot < slot {
                newtrials.push(curtrial.clone());
            } else if curslot == slot {
                sizecheck += curtrial.get_size();
                let mut joined = ParamTrial::new(addr, sz, slot);
                joined.mark_used();
                joined.mark_active();
                newtrials.push(joined);
            } else if curslot == slot + 1 {
                sizecheck += curtrial.get_size();
            } else {
                let mut copy = curtrial.clone();
                copy.set_slot(curslot - 1);
                newtrials.push(copy);
            }
        }
        if sizecheck != sz {
            return Err(Error::Lowlevel("Size mismatch when joining parameters".to_string()));
        }
        self.slotbase -= 1;
        self.trial = newtrials;
        Ok(())
    }

    pub fn get_num_used(&self) -> i32 {
        let mut count = 0;
        while (count as usize) < self.trial.len() {
            if !self.trial[count as usize].is_used() {
                break;
            }
            count += 1;
        }
        count
    }

    pub fn test_shrink(&self, index: i32, addr: &Address, sz: i32) -> bool {
        self.trial[index as usize].test_shrink(addr, sz)
    }

    pub fn shrink(&mut self, index: i32, addr: &Address, sz: i32) {
        self.trial[index as usize].set_address(addr, sz);
    }
}

pub struct FspecSpace;

impl FspecSpace {
    pub const NAME: &'static str = "fspec";

    pub fn encode_attributes(fc: &FuncCallSpecs, encoder: &mut dyn Encoder) -> Result<()> {
        match fc.get_entry_address().get_space() {
            None => encoder.write_string(ATTRIB_SPACE, "fspec"),
            Some(id) => {
                encoder.write_space(ATTRIB_SPACE, id);
                encoder.write_unsigned_integer(ATTRIB_OFFSET, fc.get_entry_address().get_offset());
            }
        }
        Ok(())
    }

    pub fn encode_attributes_size(fc: &FuncCallSpecs, encoder: &mut dyn Encoder, size: i32) -> Result<()> {
        match fc.get_entry_address().get_space() {
            None => encoder.write_string(ATTRIB_SPACE, "fspec"),
            Some(id) => {
                encoder.write_space(ATTRIB_SPACE, id);
                encoder.write_unsigned_integer(ATTRIB_OFFSET, fc.get_entry_address().get_offset());
                encoder.write_signed_integer(ATTRIB_SIZE, size as i64);
            }
        }
        Ok(())
    }

    pub fn print_raw(fc: &FuncCallSpecs, out: &mut String) {
        if !fc.get_name().is_empty() {
            out.push_str(fc.get_name());
        } else {
            out.push_str("func_");
            fc.get_entry_address().print_raw(out);
        }
    }

    pub fn decode(_decoder: &mut dyn Decoder) -> Result<()> {
        Err(Error::Lowlevel(
            "Should never decode fspec space from stream".to_string(),
        ))
    }
}

#[derive(Clone, Debug, Default)]
pub struct ParameterPieces {
    pub addr: Address,
    pub tp: Option<TypeId>,
    pub flags: u32,
}

impl ParameterPieces {
    pub const ISTHIS: u32 = 1;
    pub const HIDDENRETPARM: u32 = 2;
    pub const INDIRECTSTORAGE: u32 = 4;
    pub const NAMELOCK: u32 = 8;
    pub const TYPELOCK: u32 = 16;
    pub const SIZELOCK: u32 = 32;

    fn get_type(&self) -> TypeId {
        self.tp.expect("parameter pieces have no data-type")
    }

    pub fn swap_markup(&mut self, op: &mut ParameterPieces) {
        std::mem::swap(&mut self.flags, &mut op.flags);
        std::mem::swap(&mut self.tp, &mut op.tp);
    }

    pub fn assign_address_from_pieces(
        &mut self,
        pieces: &mut Vec<VarnodeData>,
        most_to_least: bool,
        manager: &AddrSpaceManager,
        translate: &dyn Translate,
    ) -> Result<()> {
        if !most_to_least && pieces.len() > 1 {
            pieces.reverse();
        }
        JoinRecord::merge_sequence(pieces, translate);
        if pieces.len() == 1 {
            self.addr = pieces[0].get_addr();
            return Ok(());
        }
        let join_record = manager.find_add_join(pieces, 0)?;
        self.addr = join_record.get_unified().get_addr();
        Ok(())
    }
}

#[derive(Clone, Debug, Default)]
pub struct PrototypePieces {
    pub model: Option<ModelId>,
    pub name: String,
    pub outtype: Option<TypeId>,
    pub intypes: Vec<TypeId>,
    pub innames: Vec<String>,
    pub first_var_arg_slot: i32,
}

#[derive(Clone, Debug, Default)]
pub struct EffectRecord {
    range: VarnodeData,
    tp: u32,
}

impl EffectRecord {
    pub const UNAFFECTED: u32 = 1;
    pub const KILLEDBYCALL: u32 = 2;
    pub const RETURN_ADDRESS: u32 = 3;
    pub const UNKNOWN_EFFECT: u32 = 4;

    pub fn new() -> EffectRecord {
        EffectRecord::default()
    }

    pub fn from_address(addr: &Address, size: i32) -> EffectRecord {
        EffectRecord {
            range: VarnodeData {
                space: addr.get_space().cloned(),
                offset: addr.get_offset(),
                size: size as u32,
            },
            tp: EffectRecord::UNKNOWN_EFFECT,
        }
    }

    pub fn from_param_entry(entry: &ParamEntry, tag: u32) -> EffectRecord {
        EffectRecord {
            range: VarnodeData {
                space: entry.get_space().cloned(),
                offset: entry.get_base(),
                size: entry.get_size() as u32,
            },
            tp: tag,
        }
    }

    pub fn from_varnode_data(addr: &VarnodeData, tag: u32) -> EffectRecord {
        EffectRecord {
            range: addr.clone(),
            tp: tag,
        }
    }

    pub fn get_type(&self) -> u32 {
        self.tp
    }

    pub fn get_address(&self) -> Address {
        Address::from_parts(self.range.space.clone(), self.range.offset)
    }

    pub fn get_size(&self) -> i32 {
        self.range.size as i32
    }

    pub fn encode(&self, encoder: &mut dyn Encoder) -> Result<()> {
        let addr = Address::from_parts(self.range.space.clone(), self.range.offset);
        if self.tp == EffectRecord::UNAFFECTED
            || self.tp == EffectRecord::KILLEDBYCALL
            || self.tp == EffectRecord::RETURN_ADDRESS
        {
            addr.encode_size(encoder, self.range.size as i32)
        } else {
            Err(Error::Lowlevel("Bad EffectRecord type".to_string()))
        }
    }

    pub fn decode(&mut self, grouptype: u32, decoder: &mut dyn Decoder) -> Result<()> {
        self.tp = grouptype;
        self.range = VarnodeData::decode(decoder)?;
        Ok(())
    }

    pub fn compare_by_address(op1: &EffectRecord, op2: &EffectRecord) -> bool {
        let space1 = op1.range.space.as_ref().expect("effect record has no space");
        let space2 = op2.range.space.as_ref().expect("effect record has no space");
        if space1.get_index() != space2.get_index() {
            return space1.get_index() < space2.get_index();
        }
        op1.range.offset < op2.range.offset
    }
}

impl PartialEq for EffectRecord {
    fn eq(&self, op2: &EffectRecord) -> bool {
        if self.range != op2.range {
            return false;
        }
        self.tp == op2.tp
    }
}

impl Eq for EffectRecord {}

pub const P_STANDARD: u32 = 0;
pub const P_STANDARD_OUT: u32 = 1;
pub const P_REGISTER: u32 = 2;
pub const P_REGISTER_OUT: u32 = 3;
pub const P_MERGED: u32 = 4;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ParamListKind {
    Standard,
    StandardOut,
    RegisterOut,
    Register,
    Merged,
}

pub struct ParamListStandard {
    kind: ParamListKind,
    numgroup: i32,
    maxdelay: i32,
    thisbeforeret: bool,
    auto_killed_by_call: bool,
    resource_start: Vec<i32>,
    entry: Vec<Arc<ParamEntry>>,
    resolver_map: Vec<Option<Box<ParamEntryResolver>>>,
    model_rules: Vec<ModelRule>,
    spacebase: Option<SpaceRef>,
    use_fillin_fallback: bool,
}

impl ParamListStandard {
    pub fn new(kind: ParamListKind) -> ParamListStandard {
        ParamListStandard {
            kind,
            numgroup: 0,
            maxdelay: 0,
            thisbeforeret: false,
            auto_killed_by_call: false,
            resource_start: Vec::new(),
            entry: Vec::new(),
            resolver_map: Vec::new(),
            model_rules: Vec::new(),
            spacebase: None,
            use_fillin_fallback: false,
        }
    }

    pub fn clone_list(&self) -> Result<Box<ParamListStandard>> {
        let mut res = ParamListStandard {
            kind: self.kind,
            numgroup: self.numgroup,
            maxdelay: self.maxdelay,
            thisbeforeret: self.thisbeforeret,
            auto_killed_by_call: self.auto_killed_by_call,
            resource_start: self.resource_start.clone(),
            entry: self.entry.clone(),
            resolver_map: Vec::new(),
            model_rules: Vec::new(),
            spacebase: self.spacebase.clone(),
            use_fillin_fallback: self.use_fillin_fallback,
        };
        for rule in &self.model_rules {
            res.model_rules.push(ModelRule::new_copy(rule, self)?);
        }
        res.populate_resolver();
        Ok(Box::new(res))
    }

    pub fn get_kind(&self) -> ParamListKind {
        self.kind
    }

    fn resolver(&self, loc: &Address) -> Option<&ParamEntryResolver> {
        let index = loc.get_space()?.get_index();
        if index < 0 || index as usize >= self.resolver_map.len() {
            return None;
        }
        self.resolver_map[index as usize].as_deref()
    }

    fn entry_ref(&self, index: usize) -> (usize, &Arc<ParamEntry>) {
        (index, &self.entry[index])
    }

    pub fn find_entry(&self, loc: &Address, size: i32, just: bool) -> Option<usize> {
        let resolver = self.resolver(loc)?;
        let (mut first, last) = resolver.find(&loc.get_offset());
        while first != last {
            let test_index = resolver.part(first).get_param_entry();
            first += 1;
            let test_entry = &self.entry[test_index];
            if test_entry.get_min_size() > size {
                continue;
            }
            if !just || test_entry.justified_contain(loc, size) == 0 {
                return Some(test_index);
            }
        }
        None
    }

    pub fn select_unreference_entry(&self, grp: i32, pref_type: TypeClass) -> Option<usize> {
        let mut best_score = -1;
        let mut best_entry: Option<usize> = None;
        for (index, cur_entry) in self.entry.iter().enumerate() {
            if cur_entry.get_group() != grp {
                continue;
            }
            let cur_score = if cur_entry.get_type() == pref_type {
                2
            } else if pref_type == TypeClass::General {
                1
            } else {
                0
            };
            if cur_score > best_score {
                best_score = cur_score;
                best_entry = Some(index);
            }
        }
        best_entry
    }

    pub fn build_trial_map(&self, active: &mut ParamActive, manager: &AddrSpaceManager) -> Result<()> {
        let mut hitlist: Vec<Option<usize>> = Vec::new();
        let mut float_count = 0;
        let mut int_count = 0;

        for index in 0..active.get_num_trials() {
            let (addr, size) = {
                let paramtrial = active.get_trial(index);
                (paramtrial.get_address().clone(), paramtrial.get_size())
            };
            let entry_slot = self.find_entry(&addr, size, true);
            let paramtrial = active.get_trial_mut(index);
            match entry_slot {
                None => paramtrial.mark_no_use(),
                Some(slot_index) => {
                    paramtrial.set_entry(Some(self.entry_ref(slot_index)), 0);
                    let slot_entry = &self.entry[slot_index];
                    if paramtrial.is_active() {
                        if slot_entry.get_type() == TypeClass::Float {
                            float_count += 1;
                        } else {
                            int_count += 1;
                        }
                    }
                    let grp = slot_entry.get_group();
                    while hitlist.len() as i32 <= grp {
                        hitlist.push(None);
                    }
                    if hitlist[grp as usize].is_none() {
                        hitlist[grp as usize] = Some(slot_index);
                    }
                }
            }
        }

        for group_index in 0..hitlist.len() {
            match hitlist[group_index] {
                None => {
                    let pref = if float_count > int_count {
                        TypeClass::Float
                    } else {
                        TypeClass::General
                    };
                    let Some(curentry_index) = self.select_unreference_entry(group_index as i32, pref) else {
                        continue;
                    };
                    let curentry = &self.entry[curentry_index];
                    let sz = if curentry.is_exclusion() {
                        curentry.get_size()
                    } else {
                        curentry.get_align()
                    };
                    let mut nextslot = 0;
                    let addr = curentry.get_addr_by_slot(&mut nextslot, sz, 1, manager)?;
                    let trialpos = active.get_num_trials();
                    active.register_trial(&addr, sz);
                    let paramtrial = active.get_trial_mut(trialpos);
                    paramtrial.mark_unref();
                    paramtrial.set_entry(Some(self.entry_ref(curentry_index)), 0);
                }
                Some(curentry_index) => {
                    let curentry = &self.entry[curentry_index];
                    if curentry.is_exclusion() {
                        continue;
                    }
                    let mut slotlist: Vec<i32> = Vec::new();
                    for trial_index in 0..active.get_num_trials() {
                        let paramtrial = active.get_trial(trial_index);
                        if paramtrial.get_entry() != Some(curentry_index) {
                            continue;
                        }
                        let mut slot = curentry.get_slot(paramtrial.get_address(), 0) - curentry.get_group();
                        let mut endslot = curentry.get_slot(paramtrial.get_address(), paramtrial.get_size() - 1)
                            - curentry.get_group();
                        if endslot < slot {
                            std::mem::swap(&mut slot, &mut endslot);
                        }
                        while slotlist.len() as i32 <= endslot {
                            slotlist.push(0);
                        }
                        while slot <= endslot {
                            slotlist[slot as usize] = 1;
                            slot += 1;
                        }
                    }
                    for slot_index in 0..slotlist.len() {
                        if slotlist[slot_index] == 0 {
                            let mut nextslot = slot_index as i32;
                            let addr = curentry.get_addr_by_slot(&mut nextslot, curentry.get_align(), 1, manager)?;
                            let trialpos = active.get_num_trials();
                            active.register_trial(&addr, curentry.get_align());
                            let paramtrial = active.get_trial_mut(trialpos);
                            paramtrial.mark_unref();
                            paramtrial.set_entry(Some(self.entry_ref(curentry_index)), 0);
                        }
                    }
                }
            }
        }
        active.sort_trials();
        Ok(())
    }

    pub fn separate_sections(&self, active: &ParamActive, trial_start: &mut Vec<i32>) -> Result<()> {
        let numtrials = active.get_num_trials();
        let mut current_trial = 0;
        let mut next_group = self.resource_start.get(1).copied().unwrap_or(i32::MAX);
        let mut next_section = 2usize;
        trial_start.push(current_trial);
        while current_trial < numtrials {
            let curtrial = active.get_trial(current_trial);
            if let Some(entry) = curtrial.get_entry_data()
                && entry.get_group() >= next_group
            {
                if next_section > self.resource_start.len() {
                    return Err(Error::Lowlevel("Missing next resource start".to_string()));
                }
                next_group = self.resource_start.get(next_section).copied().unwrap_or(i32::MAX);
                next_section += 1;
                trial_start.push(current_trial);
            }
            current_trial += 1;
        }
        trial_start.push(numtrials);
        Ok(())
    }

    pub fn mark_group_no_use(active: &mut ParamActive, active_trial: i32, trial_start: i32) {
        let num_trials = active.get_num_trials();
        let active_entry = active
            .get_trial(active_trial)
            .entry_data
            .clone()
            .expect("active trial has no param entry");
        for index in trial_start..num_trials {
            if index == active_trial {
                continue;
            }
            let othertrial = active.get_trial_mut(index);
            if othertrial.is_definitely_not_used() {
                continue;
            }
            if !othertrial
                .get_entry_data()
                .expect("trial has no param entry")
                .group_overlap(&active_entry)
            {
                break;
            }
            othertrial.mark_no_use();
        }
    }

    pub fn mark_best_inactive(active: &mut ParamActive, group: i32, group_start: i32, pref_type: TypeClass) {
        let num_trials = active.get_num_trials();
        let mut best_trial = -1;
        let mut best_score = -1;
        for index in group_start..num_trials {
            let trial = active.get_trial(index);
            if trial.is_definitely_not_used() {
                continue;
            }
            let entry = trial.get_entry_data().expect("trial has no param entry");
            let grp = entry.get_group();
            if grp != group {
                break;
            }
            if entry.get_all_groups().len() > 1 {
                continue;
            }
            let mut score = 0;
            if trial.has_ancestor_realistic() {
                score += 5;
                if trial.has_ancestor_solid() {
                    score += 5;
                }
            }
            if entry.get_type() == pref_type {
                score += 1;
            }
            if score > best_score {
                best_score = score;
                best_trial = index;
            }
        }
        if best_trial >= 0 {
            ParamListStandard::mark_group_no_use(active, best_trial, group_start);
        }
    }

    pub fn force_exclusion_group(active: &mut ParamActive) {
        let num_trials = active.get_num_trials();
        let mut cur_group = -1;
        let mut group_start = -1;
        let mut inactive_count = 0;
        for index in 0..num_trials {
            let curtrial = active.get_trial(index);
            if curtrial.is_definitely_not_used()
                || !curtrial
                    .get_entry_data()
                    .expect("trial has no param entry")
                    .is_exclusion()
            {
                continue;
            }
            let grp = curtrial.get_entry_data().expect("trial has no param entry").get_group();
            let is_active = curtrial.is_active();
            if grp != cur_group {
                if inactive_count > 1 {
                    ParamListStandard::mark_best_inactive(active, cur_group, group_start, TypeClass::General);
                }
                cur_group = grp;
                group_start = index;
                inactive_count = 0;
            }
            if is_active {
                ParamListStandard::mark_group_no_use(active, index, group_start);
            } else {
                inactive_count += 1;
            }
        }
        if inactive_count > 1 {
            ParamListStandard::mark_best_inactive(active, cur_group, group_start, TypeClass::General);
        }
    }

    pub fn force_no_use(active: &mut ParamActive, start: i32, stop: i32) {
        let mut seendefnouse = false;
        let mut curgroup = -1;
        let mut alldefnouse = false;
        for index in start..stop {
            let curtrial = active.get_trial_mut(index);
            let Some(entry) = curtrial.get_entry_data() else {
                continue;
            };
            let grp = entry.get_group();
            let exclusion = entry.is_exclusion();
            if grp <= curgroup && exclusion {
                if !curtrial.is_definitely_not_used() {
                    alldefnouse = false;
                }
            } else {
                if alldefnouse {
                    seendefnouse = true;
                }
                alldefnouse = curtrial.is_definitely_not_used();
                curgroup = grp;
            }
            if seendefnouse {
                curtrial.mark_inactive();
            }
        }
    }

    pub fn force_inactive_chain(active: &mut ParamActive, maxchain: i32, start: i32, stop: i32, groupstart: i32) {
        let mut seenchain = false;
        let mut chainlength = 0;
        let mut max = -1;
        let recover_subcall = active.is_recover_subcall();
        for index in start..stop {
            let trial = active.get_trial(index);
            if trial.is_definitely_not_used() {
                continue;
            }
            if !trial.is_active() {
                if trial.is_unref() && recover_subcall {
                    let spacebase = trial
                        .get_address()
                        .get_space()
                        .is_some_and(|spc| spc.get_type() == SpaceType::Spacebase);
                    if spacebase {
                        seenchain = true;
                    }
                }
                if index == start {
                    chainlength += trial.slot_group() - groupstart + 1;
                } else {
                    chainlength += trial.slot_group() - active.get_trial(index - 1).slot_group();
                }
                if chainlength > maxchain {
                    seenchain = true;
                }
            } else {
                chainlength = 0;
                if !seenchain {
                    max = index;
                }
            }
            if seenchain {
                active.get_trial_mut(index).mark_inactive();
            }
        }
        let mut index = start;
        while index <= max {
            let trial = active.get_trial_mut(index);
            index += 1;
            if trial.is_definitely_not_used() {
                continue;
            }
            if !trial.is_active() {
                trial.mark_active();
            }
        }
    }

    pub fn calc_delay(&mut self) {
        self.maxdelay = 0;
        for entry in &self.entry {
            let delay = entry.get_space().expect("param entry has no address space").get_delay();
            if delay > self.maxdelay {
                self.maxdelay = delay;
            }
        }
    }

    pub fn add_resolver_range(&mut self, spc: &SpaceRef, first: u64, last: u64, param_entry: usize, position: i32) {
        let index = spc.get_index() as usize;
        while self.resolver_map.len() <= index {
            self.resolver_map.push(None);
        }
        let resolver = self.resolver_map[index].get_or_insert_with(|| Box::new(ParamEntryResolver::new()));
        let init_data = InitData::new(position, param_entry);
        resolver.insert(&init_data, first, last);
    }

    pub fn populate_resolver(&mut self) {
        let mut position = 0;
        for index in 0..self.entry.len() {
            let param_entry = self.entry[index].clone();
            let spc = param_entry
                .get_space()
                .expect("param entry has no address space")
                .clone();
            if spc.get_type() == SpaceType::Join {
                let join_rec = param_entry
                    .get_join_record()
                    .expect("join param entry has no join record")
                    .clone();
                for piece_index in 0..join_rec.num_pieces() {
                    let v_data = join_rec.get_piece(piece_index);
                    let last = v_data.offset.wrapping_add((v_data.size as u64).wrapping_sub(1));
                    let piece_space = v_data.space.as_ref().expect("join piece has no address space");
                    self.add_resolver_range(piece_space, v_data.offset, last, index, position);
                    position += 1;
                }
            } else {
                let first = param_entry.get_base();
                let last = first.wrapping_add((param_entry.get_size() as i64 - 1) as u64);
                self.add_resolver_range(&spc, first, last, index, position);
                position += 1;
            }
        }
    }

    pub fn parse_pentry(
        &mut self,
        decoder: &mut dyn Decoder,
        effectlist: &mut Vec<EffectRecord>,
        groupid: i32,
        normalstack: bool,
        split_float: bool,
        grouped: bool,
    ) -> Result<()> {
        let mut last_class = TypeClass::Class4;
        if let Some(back) = self.entry.last() {
            last_class = if back.is_grouped() {
                TypeClass::General
            } else {
                back.get_type()
            };
        }
        let mut new_entry = ParamEntry::new(groupid);
        new_entry.decode(decoder, normalstack, grouped, &self.entry)?;
        self.entry.push(Arc::new(new_entry));
        let back = self.entry.last().expect("entry was just added").clone();
        if split_float {
            let current_class = if grouped { TypeClass::General } else { back.get_type() };
            if last_class != current_class {
                if last_class < current_class {
                    return Err(Error::Lowlevel(
                        "parameter list entries must be ordered by storage class".to_string(),
                    ));
                }
                self.resource_start.push(groupid);
            }
        }
        let spc = back.get_space().expect("param entry has no address space").clone();
        if spc.get_type() == SpaceType::Spacebase {
            self.spacebase = Some(spc);
        } else if self.auto_killed_by_call {
            effectlist.push(EffectRecord::from_param_entry(&back, EffectRecord::KILLEDBYCALL));
        }
        let maxgroup = back.get_all_groups().last().expect("param entry has no groups") + 1;
        if maxgroup > self.numgroup {
            self.numgroup = maxgroup;
        }
        Ok(())
    }

    pub fn parse_group(
        &mut self,
        decoder: &mut dyn Decoder,
        effectlist: &mut Vec<EffectRecord>,
        _groupid: i32,
        normalstack: bool,
        split_float: bool,
    ) -> Result<()> {
        let basegroup = self.numgroup;
        let mut previous1: Option<usize> = None;
        let mut previous2: Option<usize> = None;
        let elem_id = decoder.open_element_expect(ELEM_GROUP)?;
        while decoder.peek_element()? != 0 {
            self.parse_pentry(decoder, effectlist, basegroup, normalstack, split_float, true)?;
            let pentry_index = self.entry.len() - 1;
            let pentry = &self.entry[pentry_index];
            if pentry.get_space().expect("param entry has no address space").get_type() == SpaceType::Join {
                return Err(Error::Lowlevel(
                    "<pentry> in the join space not allowed in <group> tag".to_string(),
                ));
            }
            if let Some(first_previous) = previous1 {
                ParamEntry::order_within_group(&self.entry[first_previous], pentry)?;
                if let Some(second_previous) = previous2 {
                    ParamEntry::order_within_group(&self.entry[second_previous], pentry)?;
                }
            }
            previous2 = previous1;
            previous1 = Some(pentry_index);
        }
        decoder.close_element(elem_id)?;
        Ok(())
    }

    pub fn get_entry(&self) -> &[Arc<ParamEntry>] {
        &self.entry
    }

    pub fn is_big_endian(&self) -> bool {
        self.entry[0]
            .get_space()
            .expect("param entry has no address space")
            .is_big_endian()
    }

    pub fn extract_tiles(&self, tiles: &mut Vec<usize>, tp: TypeClass) {
        for (index, cur_entry) in self.entry.iter().enumerate() {
            if !cur_entry.is_exclusion() {
                continue;
            }
            if cur_entry.get_type() != tp || cur_entry.get_all_groups().len() != 1 {
                continue;
            }
            tiles.push(index);
        }
    }

    pub fn get_stack_entry(&self) -> Option<usize> {
        let cur_entry = self.entry.last()?;
        let spacebase = cur_entry
            .get_space()
            .is_some_and(|spc| spc.get_type() == SpaceType::Spacebase);
        if !cur_entry.is_exclusion() && spacebase {
            return Some(self.entry.len() - 1);
        }
        None
    }

    pub fn assign_address_fallback(
        &self,
        resource: TypeClass,
        tp: TypeId,
        match_exact: bool,
        status: &mut [i32],
        param: &mut ParameterPieces,
        types: &TypeFactory,
        manager: &AddrSpaceManager,
    ) -> Result<u32> {
        for cur_entry in &self.entry {
            let grp = cur_entry.get_group();
            if status[grp as usize] < 0 {
                continue;
            }
            if resource != cur_entry.get_type() && (match_exact || cur_entry.get_type() != TypeClass::General) {
                continue;
            }
            let datatype = types.get(tp);
            param.addr = cur_entry.get_addr_by_slot(
                &mut status[grp as usize],
                datatype.get_align_size(),
                datatype.get_alignment(),
                manager,
            )?;
            if param.addr.is_invalid() {
                continue;
            }
            if cur_entry.is_exclusion() {
                for group in cur_entry.get_all_groups() {
                    status[*group as usize] = -1;
                }
            }
            param.tp = Some(tp);
            param.flags = 0;
            return Ok(SUCCESS);
        }
        Ok(FAIL)
    }

    pub fn assign_address(
        &self,
        dt: TypeId,
        proto: &PrototypePieces,
        pos: i32,
        tlst: &mut TypeFactory,
        status: &mut Vec<i32>,
        res: &mut ParameterPieces,
        env: &AssignEnv<'_>,
    ) -> Result<u32> {
        for rule in &self.model_rules {
            let response_code = rule.assign_address(dt, proto, pos, tlst, status, res, self, env)?;
            if response_code != FAIL {
                return Ok(response_code);
            }
        }
        let store = metatype2typeclass(tlst.get(dt).get_metatype());
        self.assign_address_fallback(store, dt, false, status, res, tlst, env.manager)
    }

    pub fn get_type(&self) -> u32 {
        match self.kind {
            ParamListKind::Standard => P_STANDARD,
            ParamListKind::StandardOut => P_STANDARD_OUT,
            ParamListKind::RegisterOut => P_REGISTER_OUT,
            ParamListKind::Register => P_REGISTER,
            ParamListKind::Merged => P_MERGED,
        }
    }

    fn unassigned_error(types: &TypeFactory, tp: TypeId) -> Error {
        Error::ParamUnassigned(format!(
            "Cannot assign parameter address for {}",
            types.get(tp).get_name()
        ))
    }

    fn assign_map_standard(
        &self,
        proto: &PrototypePieces,
        typefactory: &mut TypeFactory,
        res: &mut Vec<ParameterPieces>,
        env: &AssignEnv<'_>,
    ) -> Result<()> {
        let mut status: Vec<i32> = vec![0; self.numgroup.max(0) as usize];
        if res.len() == 2 {
            let back_index = res.len() - 1;
            let dt = res[back_index].get_type();
            if (res[back_index].flags & ParameterPieces::HIDDENRETPARM) != 0 {
                if self.assign_address_fallback(
                    TypeClass::HiddenRet,
                    dt,
                    false,
                    &mut status,
                    &mut res[back_index],
                    typefactory,
                    env.manager,
                )? == FAIL
                {
                    return Err(ParamListStandard::unassigned_error(
                        typefactory,
                        res[back_index].get_type(),
                    ));
                }
            } else if self.assign_address(dt, proto, 0, typefactory, &mut status, &mut res[back_index], env)? == FAIL {
                return Err(ParamListStandard::unassigned_error(
                    typefactory,
                    res[back_index].get_type(),
                ));
            }
            res[back_index].flags |= ParameterPieces::HIDDENRETPARM;
        }
        for (index, dt) in proto.intypes.iter().enumerate() {
            res.push(ParameterPieces::default());
            let back_index = res.len() - 1;
            let response_code = self.assign_address(
                *dt,
                proto,
                index as i32,
                typefactory,
                &mut status,
                &mut res[back_index],
                env,
            )?;
            if response_code == FAIL || response_code == NO_ASSIGNMENT {
                return Err(ParamListStandard::unassigned_error(typefactory, *dt));
            }
        }
        Ok(())
    }

    fn assign_map_register_out(
        &self,
        proto: &PrototypePieces,
        typefactory: &mut TypeFactory,
        res: &mut Vec<ParameterPieces>,
        env: &AssignEnv<'_>,
    ) -> Result<()> {
        let mut status: Vec<i32> = vec![0; self.numgroup.max(0) as usize];
        res.push(ParameterPieces::default());
        let back_index = res.len() - 1;
        let outtype = proto.outtype.expect("prototype pieces have no output data-type");
        if typefactory.get(outtype).get_metatype() != TypeMetatype::Void {
            self.assign_address(outtype, proto, -1, typefactory, &mut status, &mut res[back_index], env)?;
            if res[back_index].addr.is_invalid() {
                return Err(ParamListStandard::unassigned_error(typefactory, outtype));
            }
        } else {
            res[back_index].tp = Some(outtype);
            res[back_index].flags = 0;
        }
        Ok(())
    }

    fn assign_map_standard_out(
        &self,
        proto: &PrototypePieces,
        typefactory: &mut TypeFactory,
        res: &mut Vec<ParameterPieces>,
        env: &AssignEnv<'_>,
    ) -> Result<()> {
        let mut status: Vec<i32> = vec![0; self.numgroup.max(0) as usize];
        res.push(ParameterPieces::default());
        let back_index = res.len() - 1;
        let outtype = proto.outtype.expect("prototype pieces have no output data-type");
        if typefactory.get(outtype).get_metatype() == TypeMetatype::Void {
            res[back_index].tp = Some(outtype);
            res[back_index].flags = 0;
            return Ok(());
        }
        let mut response_code =
            self.assign_address(outtype, proto, -1, typefactory, &mut status, &mut res[back_index], env)?;
        if response_code == FAIL {
            response_code = HIDDENRET_PTRPARAM;
        }
        if response_code == HIDDENRET_PTRPARAM
            || response_code == HIDDENRET_SPECIALREG
            || response_code == HIDDENRET_SPECIALREG_VOID
        {
            let spc = match &self.spacebase {
                Some(spc) => spc.clone(),
                None => env.manager.get_default_data_space().expect("no default data space"),
            };
            let pointersize = spc.get_addr_size() as i32;
            let wordsize = spc.get_word_size();
            let pointertp = typefactory.get_type_pointer(pointersize, outtype, wordsize)?;
            if response_code == HIDDENRET_SPECIALREG_VOID {
                res[back_index].tp = Some(typefactory.get_type_void()?);
            } else {
                res[back_index].tp = Some(pointertp);
                if self.assign_address(
                    pointertp,
                    proto,
                    -1,
                    typefactory,
                    &mut status,
                    &mut res[back_index],
                    env,
                )? == FAIL
                {
                    return Err(Error::ParamUnassigned(
                        "Cannot assign return value as a pointer".to_string(),
                    ));
                }
            }
            res[back_index].flags = ParameterPieces::INDIRECTSTORAGE;

            let is_special = response_code == HIDDENRET_SPECIALREG || response_code == HIDDENRET_SPECIALREG_VOID;
            res.push(ParameterPieces {
                addr: Address::invalid(),
                tp: Some(pointertp),
                flags: if is_special { ParameterPieces::HIDDENRETPARM } else { 0 },
            });
        }
        Ok(())
    }

    pub fn assign_map(
        &self,
        proto: &PrototypePieces,
        typefactory: &mut TypeFactory,
        res: &mut Vec<ParameterPieces>,
        env: &AssignEnv<'_>,
    ) -> Result<()> {
        match self.kind {
            ParamListKind::Standard | ParamListKind::Register => self.assign_map_standard(proto, typefactory, res, env),
            ParamListKind::StandardOut => self.assign_map_standard_out(proto, typefactory, res, env),
            ParamListKind::RegisterOut => self.assign_map_register_out(proto, typefactory, res, env),
            ParamListKind::Merged => Err(Error::Lowlevel(
                "Cannot assign prototype before model has been resolved".to_string(),
            )),
        }
    }

    fn fillin_map_standard(&self, active: &mut ParamActive, manager: &AddrSpaceManager) -> Result<()> {
        if active.get_num_trials() == 0 {
            return Ok(());
        }
        if self.entry.is_empty() {
            return Err(Error::Lowlevel(
                "Cannot derive parameter storage for prototype model without parameter entries".to_string(),
            ));
        }
        self.build_trial_map(active, manager)?;
        ParamListStandard::force_exclusion_group(active);
        let mut trial_start: Vec<i32> = Vec::new();
        self.separate_sections(active, &mut trial_start)?;
        let num_section = trial_start.len() - 1;
        for index in 0..num_section {
            ParamListStandard::force_no_use(active, trial_start[index], trial_start[index + 1]);
        }
        for index in 0..num_section {
            ParamListStandard::force_inactive_chain(
                active,
                2,
                trial_start[index],
                trial_start[index + 1],
                self.resource_start[index],
            );
        }
        for index in 0..active.get_num_trials() {
            let paramtrial = active.get_trial_mut(index);
            if paramtrial.is_active() {
                paramtrial.mark_used();
            }
        }
        Ok(())
    }

    fn fillin_map_register(&self, active: &mut ParamActive) {
        if active.get_num_trials() == 0 {
            return;
        }
        for index in 0..active.get_num_trials() {
            let (addr, size) = {
                let paramtrial = active.get_trial(index);
                (paramtrial.get_address().clone(), paramtrial.get_size())
            };
            let entry_slot = self.find_entry(&addr, size, true);
            let paramtrial = active.get_trial_mut(index);
            match entry_slot {
                None => paramtrial.mark_no_use(),
                Some(slot_index) => {
                    paramtrial.set_entry(Some(self.entry_ref(slot_index)), 0);
                    if paramtrial.is_active() {
                        paramtrial.mark_used();
                    }
                }
            }
        }
        active.sort_trials();
    }

    fn fillin_map_out(&self, active: &mut ParamActive) {
        if active.get_num_trials() == 0 {
            return;
        }
        if self.use_fillin_fallback {
            self.fillin_map_fallback_internal(active, false);
            return;
        }
        for index in 0..active.get_num_trials() {
            let trial = active.get_trial_mut(index);
            trial.set_entry(None, 0);
            if !trial.is_active() {
                continue;
            }
            let addr = trial.get_address().clone();
            let size = trial.get_size();
            let Some(entry_index) = self.find_entry(&addr, size, false) else {
                trial.mark_no_use();
                continue;
            };
            let entry = &self.entry[entry_index];
            let res = entry.justified_contain(&addr, size);
            if (trial.is_rem_formed() || trial.is_ind_create_formed()) && !entry.is_first_in_class() {
                trial.mark_no_use();
                continue;
            }
            trial.set_entry(Some(self.entry_ref(entry_index)), res);
        }
        active.sort_trials();
        for rule in &self.model_rules {
            if rule.fillin_output_map(active, self) {
                for index in 0..active.get_num_trials() {
                    let trial = active.get_trial_mut(index);
                    if trial.is_active() {
                        trial.mark_used();
                    } else {
                        trial.mark_no_use();
                        trial.set_entry(None, 0);
                    }
                }
                return;
            }
        }
        self.fillin_map_fallback_internal(active, true);
    }

    pub fn fillin_map(&self, active: &mut ParamActive, manager: &AddrSpaceManager) -> Result<()> {
        match self.kind {
            ParamListKind::Standard => self.fillin_map_standard(active, manager),
            ParamListKind::StandardOut | ParamListKind::RegisterOut => {
                self.fillin_map_out(active);
                Ok(())
            }
            ParamListKind::Register => {
                self.fillin_map_register(active);
                Ok(())
            }
            ParamListKind::Merged => Err(Error::Lowlevel(
                "Cannot determine prototype before model has been resolved".to_string(),
            )),
        }
    }

    pub fn check_join(&self, hiaddr: &Address, hisize: i32, loaddr: &Address, losize: i32) -> bool {
        let Some(entry_hi) = self.find_entry(hiaddr, hisize, true) else {
            return false;
        };
        let Some(entry_lo) = self.find_entry(loaddr, losize, true) else {
            return false;
        };
        let entry_hi = &self.entry[entry_hi];
        let entry_lo = &self.entry[entry_lo];
        if entry_hi.get_group() == entry_lo.get_group() {
            if entry_hi.is_exclusion() || entry_lo.is_exclusion() {
                return false;
            }
            if !hiaddr.is_contiguous(hisize, loaddr, losize) {
                return false;
            }
            if !hiaddr
                .get_offset()
                .wrapping_sub(entry_hi.get_base())
                .is_multiple_of(entry_hi.get_align() as i64 as u64)
            {
                return false;
            }
            if !loaddr
                .get_offset()
                .wrapping_sub(entry_lo.get_base())
                .is_multiple_of(entry_lo.get_align() as i64 as u64)
            {
                return false;
            }
            return true;
        }
        let sizesum = hisize + losize;
        for entry in &self.entry {
            if entry.get_size() < sizesum {
                continue;
            }
            if entry.justified_contain(loaddr, losize) != 0 {
                continue;
            }
            if entry.justified_contain(hiaddr, hisize) != losize {
                continue;
            }
            return true;
        }
        false
    }

    pub fn check_split(&self, loc: &Address, size: i32, splitpoint: i32) -> bool {
        let loc2 = loc.add(splitpoint as i64);
        let size2 = size - splitpoint;
        if self.find_entry(loc, splitpoint, true).is_none() {
            return false;
        }
        if self.find_entry(&loc2, size2, true).is_none() {
            return false;
        }
        true
    }

    pub fn characterize_as_param(&self, loc: &Address, size: i32) -> i32 {
        let Some(resolver) = self.resolver(loc) else {
            return ParamEntry::NO_CONTAINMENT;
        };
        let (mut first, second) = resolver.find(&loc.get_offset());
        let mut res_contains = false;
        let mut res_contained_by = false;
        while first != second {
            let test_entry = &self.entry[resolver.part(first).get_param_entry()];
            let off = test_entry.justified_contain(loc, size);
            if off == 0 {
                return ParamEntry::CONTAINS_JUSTIFIED;
            } else if off > 0 {
                res_contains = true;
            }
            if test_entry.is_exclusion() && test_entry.contained_by(loc, size) {
                res_contained_by = true;
            }
            first += 1;
        }
        if res_contains {
            return ParamEntry::CONTAINS_UNJUSTIFIED;
        }
        if res_contained_by {
            return ParamEntry::CONTAINED_BY;
        }
        if first != resolver.end() {
            let second = resolver.find_end(&loc.get_offset().wrapping_add((size - 1) as i64 as u64));
            while first != second {
                let test_entry = &self.entry[resolver.part(first).get_param_entry()];
                if test_entry.is_exclusion() && test_entry.contained_by(loc, size) {
                    return ParamEntry::CONTAINED_BY;
                }
                first += 1;
            }
        }
        ParamEntry::NO_CONTAINMENT
    }

    pub fn possible_param(&self, loc: &Address, size: i32) -> bool {
        match self.kind {
            ParamListKind::StandardOut | ParamListKind::RegisterOut => {
                for entry in &self.entry {
                    if entry.justified_contain(loc, size) >= 0 {
                        return true;
                    }
                }
                false
            }
            _ => self.find_entry(loc, size, true).is_some(),
        }
    }

    pub fn possible_param_with_slot(&self, loc: &Address, size: i32, slot: &mut i32, slotsize: &mut i32) -> bool {
        let Some(entry_num) = self.find_entry(loc, size, true) else {
            return false;
        };
        let entry = &self.entry[entry_num];
        *slot = entry.get_slot(loc, 0);
        if entry.is_exclusion() {
            *slotsize = entry.get_all_groups().len() as i32;
        } else {
            *slotsize = ((size - 1) / entry.get_align()) + 1;
        }
        true
    }

    pub fn get_biggest_contained_param(&self, loc: &Address, size: i32, res: &mut VarnodeData) -> bool {
        let Some(resolver) = self.resolver(loc) else {
            return false;
        };
        let end_loc = loc.add((size - 1) as i64);
        if end_loc.get_offset() < loc.get_offset() {
            return false;
        }
        let mut max_entry: Option<&Arc<ParamEntry>> = None;
        let mut iter = resolver.find_begin(&loc.get_offset());
        let enditer = resolver.find_end(&end_loc.get_offset());
        while iter != enditer {
            let test_entry = &self.entry[resolver.part(iter).get_param_entry()];
            iter += 1;
            if test_entry.contained_by(loc, size) {
                match max_entry {
                    None => max_entry = Some(test_entry),
                    Some(current) => {
                        if test_entry.get_size() > current.get_size() {
                            max_entry = Some(test_entry);
                        }
                    }
                }
            }
        }
        if let Some(max_entry) = max_entry {
            if !max_entry.is_exclusion() {
                return false;
            }
            res.space = max_entry.get_space().cloned();
            res.offset = max_entry.get_base();
            res.size = max_entry.get_size() as u32;
            return true;
        }
        false
    }

    pub fn unjustified_container(&self, loc: &Address, size: i32, res: &mut VarnodeData) -> bool {
        for entry in &self.entry {
            if entry.get_min_size() > size {
                continue;
            }
            let just = entry.justified_contain(loc, size);
            if just < 0 {
                continue;
            }
            if just == 0 {
                return false;
            }
            entry.get_container(loc, size, res);
            return true;
        }
        false
    }

    pub fn assumed_extension(&self, addr: &Address, size: i32, res: &mut VarnodeData) -> OpCode {
        for entry in &self.entry {
            if entry.get_min_size() > size {
                continue;
            }
            let ext = entry.assumed_extension(addr, size, res);
            if ext != OpCode::Copy {
                return ext;
            }
        }
        OpCode::Copy
    }

    pub fn get_spacebase(&self) -> Option<&SpaceRef> {
        self.spacebase.as_ref()
    }

    pub fn is_this_before_ret_pointer(&self) -> bool {
        self.thisbeforeret
    }

    pub fn get_range_list(&self, spc: &SpaceRef, res: &mut RangeList) {
        for entry in &self.entry {
            if !space_eq(entry.get_space(), Some(spc)) {
                continue;
            }
            let baseoff = entry.get_base();
            let endoff = baseoff.wrapping_add(entry.get_size() as i64 as u64).wrapping_sub(1);
            res.insert_range(spc, baseoff, endoff);
        }
    }

    pub fn get_max_delay(&self) -> i32 {
        self.maxdelay
    }

    pub fn is_auto_killed_by_call(&self) -> bool {
        self.auto_killed_by_call
    }

    fn decode_standard(
        &mut self,
        decoder: &mut dyn Decoder,
        effectlist: &mut Vec<EffectRecord>,
        normalstack: bool,
    ) -> Result<()> {
        self.numgroup = 0;
        self.spacebase = None;
        let mut pointermax = 0;
        self.thisbeforeret = false;
        self.auto_killed_by_call = false;
        let mut split_float = true;
        let elem_id = decoder.open_element()?;
        loop {
            let attrib_id = decoder.get_next_attribute_id()?;
            if attrib_id == 0 {
                break;
            }
            if attrib_id == ATTRIB_POINTERMAX {
                pointermax = decoder.read_signed_integer()? as i32;
            } else if attrib_id == ATTRIB_THISBEFORERETPOINTER {
                self.thisbeforeret = decoder.read_bool()?;
            } else if attrib_id == ATTRIB_KILLEDBYCALL {
                self.auto_killed_by_call = decoder.read_bool()?;
            } else if attrib_id == ATTRIB_SEPARATEFLOAT {
                split_float = decoder.read_bool()?;
            }
        }
        loop {
            let sub_id = decoder.peek_element()?;
            if sub_id == 0 {
                break;
            }
            if sub_id == ELEM_PENTRY {
                let groupid = self.numgroup;
                self.parse_pentry(decoder, effectlist, groupid, normalstack, split_float, false)?;
            } else if sub_id == ELEM_GROUP {
                let groupid = self.numgroup;
                self.parse_group(decoder, effectlist, groupid, normalstack, split_float)?;
            } else if sub_id == ELEM_RULE {
                break;
            }
        }
        loop {
            let sub_id = decoder.peek_element()?;
            if sub_id == 0 {
                break;
            }
            if sub_id == ELEM_RULE {
                let mut rule = ModelRule::new();
                rule.decode(decoder, self)?;
                self.model_rules.push(rule);
            } else {
                return Err(Error::Lowlevel(
                    "<pentry> and <group> elements must come before any <modelrule>".to_string(),
                ));
            }
        }
        decoder.close_element(elem_id)?;
        self.resource_start.push(self.numgroup);
        self.calc_delay();
        self.populate_resolver();
        if pointermax > 0 {
            let type_filter = SizeRestrictedFilter::new(pointermax + 1, 0);
            let action = ConvertToPointer::new(self);
            let rule = ModelRule::new_from(&type_filter, &action, self)?;
            self.model_rules.push(rule);
        }
        Ok(())
    }

    pub fn decode(
        &mut self,
        decoder: &mut dyn Decoder,
        effectlist: &mut Vec<EffectRecord>,
        normalstack: bool,
    ) -> Result<()> {
        match self.kind {
            ParamListKind::StandardOut | ParamListKind::RegisterOut => {
                self.decode_standard(decoder, effectlist, normalstack)?;
                self.initialize();
                Ok(())
            }
            _ => self.decode_standard(decoder, effectlist, normalstack),
        }
    }

    pub fn initialize(&mut self) {
        self.use_fillin_fallback = true;
        for rule in &self.model_rules {
            if rule.can_affect_fillin_output() {
                self.use_fillin_fallback = false;
                break;
            }
        }
        if self.use_fillin_fallback {
            self.auto_killed_by_call = true;
        }
    }

    fn fillin_map_fallback_internal(&self, active: &mut ParamActive, first_only: bool) {
        let mut bestentry: Option<usize> = None;
        let mut bestcover = 0;
        let mut bestclass = TypeClass::Ptr;

        for (entry_index, curentry) in self.entry.iter().enumerate() {
            if first_only
                && !curentry.is_first_in_class()
                && curentry.is_exclusion()
                && curentry.get_all_groups().len() == 1
            {
                continue;
            }
            let mut putativematch = false;
            for index in 0..active.get_num_trials() {
                let paramtrial = active.get_trial_mut(index);
                if paramtrial.is_active() {
                    let res = curentry.justified_contain(paramtrial.get_address(), paramtrial.get_size());
                    if res >= 0 {
                        paramtrial.set_entry(Some(self.entry_ref(entry_index)), res);
                        putativematch = true;
                    } else {
                        paramtrial.set_entry(None, 0);
                    }
                } else {
                    paramtrial.set_entry(None, 0);
                }
            }
            if !putativematch {
                continue;
            }
            active.sort_trials();
            let mut offmatch = 0;
            let mut matched_count = 0;
            while matched_count < active.get_num_trials() {
                let paramtrial = active.get_trial(matched_count);
                if paramtrial.get_entry().is_none() {
                    matched_count += 1;
                    continue;
                }
                if offmatch != paramtrial.get_offset() {
                    break;
                }
                if ((offmatch == 0) && curentry.is_param_check_low())
                    || ((offmatch != 0) && curentry.is_param_check_high())
                {
                    if paramtrial.is_rem_formed() {
                        break;
                    }
                    if paramtrial.is_ind_create_formed() {
                        break;
                    }
                }
                offmatch += paramtrial.get_size();
                matched_count += 1;
            }
            if offmatch < curentry.get_min_size() {
                matched_count = 0;
            }
            if matched_count == active.get_num_trials() && (curentry.get_type() < bestclass || offmatch > bestcover) {
                bestentry = Some(entry_index);
                bestcover = offmatch;
                bestclass = curentry.get_type();
            }
        }
        match bestentry {
            None => {
                for index in 0..active.get_num_trials() {
                    active.get_trial_mut(index).mark_no_use();
                }
            }
            Some(best_index) => {
                let best = &self.entry[best_index];
                for index in 0..active.get_num_trials() {
                    let paramtrial = active.get_trial_mut(index);
                    if paramtrial.is_active() {
                        let res = best.justified_contain(paramtrial.get_address(), paramtrial.get_size());
                        if res >= 0 {
                            paramtrial.mark_used();
                            paramtrial.set_entry(Some(self.entry_ref(best_index)), res);
                        } else {
                            paramtrial.mark_no_use();
                            paramtrial.set_entry(None, 0);
                        }
                    } else {
                        paramtrial.mark_no_use();
                        paramtrial.set_entry(None, 0);
                    }
                }
                active.sort_trials();
            }
        }
    }

    pub fn fillin_map_fallback(
        &self,
        active: &mut ParamActive,
        first_only: bool,
        _manager: &AddrSpaceManager,
    ) -> Result<()> {
        self.fillin_map_fallback_internal(active, first_only);
        Ok(())
    }

    pub fn fold_in(&mut self, op2: &ParamListStandard) -> Result<()> {
        if self.entry.is_empty() {
            self.spacebase = op2.get_spacebase().cloned();
            self.entry = op2.entry.clone();
            return Ok(());
        }
        if !space_eq(self.spacebase.as_ref(), op2.get_spacebase()) && op2.get_spacebase().is_some() {
            return Err(Error::Lowlevel(
                "Cannot merge prototype models with different stacks".to_string(),
            ));
        }
        for opentry in &op2.entry {
            let mut typeint = 0;
            let mut found: Option<usize> = None;
            for (index, cur) in self.entry.iter().enumerate() {
                if cur.subsumes_definition(opentry) {
                    typeint = 2;
                    found = Some(index);
                    break;
                }
                if opentry.subsumes_definition(cur) {
                    typeint = 1;
                    found = Some(index);
                    break;
                }
            }
            if typeint == 2 {
                let index = found.expect("subsuming entry was found");
                if self.entry[index].get_min_size() != opentry.get_min_size() {
                    typeint = 0;
                }
            } else if typeint == 1 {
                let index = found.expect("subsumed entry was found");
                if self.entry[index].get_min_size() != opentry.get_min_size() {
                    typeint = 0;
                } else {
                    self.entry[index] = opentry.clone();
                }
            }
            if typeint == 0 {
                self.entry.push(opentry.clone());
            }
        }
        Ok(())
    }

    pub fn finalize(&mut self) {
        self.populate_resolver();
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ProtoModelKind {
    Standard,
    Unknown { placeholder_model: ModelId },
    Merged { modellist: Vec<ModelId> },
}

pub struct ProtoModel {
    id: ModelId,
    name: String,
    extrapop: i32,
    input: Option<Box<ParamListStandard>>,
    output: Option<Box<ParamListStandard>>,
    compat_model: Option<ModelId>,
    effectlist: Vec<EffectRecord>,
    likelytrash: Vec<VarnodeData>,
    internalstorage: Vec<VarnodeData>,
    inject_upon_entry: i32,
    inject_upon_return: i32,
    localrange: RangeList,
    paramrange: RangeList,
    stackgrowsnegative: bool,
    has_this: bool,
    is_construct: bool,
    is_printed: bool,
    kind: ProtoModelKind,
}

impl ProtoModel {
    pub const EXTRAPOP_UNKNOWN: i32 = 0x8000;

    pub fn new(id: ModelId, manager: &AddrSpaceManager) -> ProtoModel {
        let mut model = ProtoModel {
            id,
            name: String::new(),
            extrapop: 0,
            input: None,
            output: None,
            compat_model: None,
            effectlist: Vec::new(),
            likelytrash: Vec::new(),
            internalstorage: Vec::new(),
            inject_upon_entry: -1,
            inject_upon_return: -1,
            localrange: RangeList::new(),
            paramrange: RangeList::new(),
            stackgrowsnegative: true,
            has_this: false,
            is_construct: false,
            is_printed: true,
            kind: ProtoModelKind::Standard,
        };
        model.default_local_range(manager);
        model.default_param_range(manager);
        model
    }

    pub fn new_copy(id: ModelId, nm: &str, op2: &ProtoModel) -> Result<ProtoModel> {
        let input = match &op2.input {
            Some(list) => Some(list.clone_list()?),
            None => None,
        };
        let output = match &op2.output {
            Some(list) => Some(list.clone_list()?),
            None => None,
        };
        let mut model = ProtoModel {
            id,
            name: nm.to_string(),
            extrapop: op2.extrapop,
            input,
            output,
            compat_model: Some(op2.id),
            effectlist: op2.effectlist.clone(),
            likelytrash: op2.likelytrash.clone(),
            internalstorage: op2.internalstorage.clone(),
            inject_upon_entry: op2.inject_upon_entry,
            inject_upon_return: op2.inject_upon_return,
            localrange: op2.localrange.clone(),
            paramrange: op2.paramrange.clone(),
            stackgrowsnegative: op2.stackgrowsnegative,
            has_this: op2.has_this,
            is_construct: op2.is_construct,
            is_printed: true,
            kind: ProtoModelKind::Standard,
        };
        if model.name == "__thiscall" {
            model.has_this = true;
        }
        Ok(model)
    }

    pub fn new_unknown(id: ModelId, nm: &str, place_hold: &ProtoModel) -> Result<ProtoModel> {
        let mut model = ProtoModel::new_copy(id, nm, place_hold)?;
        model.kind = ProtoModelKind::Unknown {
            placeholder_model: place_hold.id,
        };
        Ok(model)
    }

    pub fn new_merged(id: ModelId, manager: &AddrSpaceManager) -> ProtoModel {
        let mut model = ProtoModel::new(id, manager);
        model.kind = ProtoModelKind::Merged { modellist: Vec::new() };
        model
    }

    fn input_list(&self) -> &ParamListStandard {
        self.input.as_ref().expect("prototype model has no input list")
    }

    fn output_list(&self) -> &ParamListStandard {
        self.output.as_ref().expect("prototype model has no output list")
    }

    pub fn get_input(&self) -> Option<&ParamListStandard> {
        self.input.as_deref()
    }

    pub fn get_output(&self) -> Option<&ParamListStandard> {
        self.output.as_deref()
    }

    pub fn default_local_range(&mut self, manager: &AddrSpaceManager) {
        let Some(spc) = manager.get_stack_space() else {
            return;
        };
        if self.stackgrowsnegative {
            let last = spc.get_highest();
            let mut size = last >> 1;
            if size > 0x7fffffff {
                size = 0x7fffffff;
            }
            let first = last - size;
            self.localrange.insert_range(&spc, first, last);
        } else {
            let first = 0;
            let mut last = spc.get_highest() >> 1;
            if last > 0x7fffffff {
                last = 0x7fffffff;
            }
            self.localrange.insert_range(&spc, first, last);
        }
    }

    pub fn default_param_range(&mut self, manager: &AddrSpaceManager) {
        let Some(spc) = manager.get_stack_space() else {
            return;
        };
        if self.stackgrowsnegative {
            let first = 0;
            let mut last = spc.get_highest() >> 2;
            if last > 0x7fffffff {
                last = 0x7fffffff;
            }
            self.paramrange.insert_range(&spc, first, last);
        } else {
            let last = spc.get_highest();
            let mut size = last >> 2;
            if size > 0x7fffffff {
                size = 0x7fffffff;
            }
            let first = last - size;
            self.paramrange.insert_range(&spc, first, last);
        }
    }

    pub fn build_param_list(&mut self, strategy: &str) -> Result<()> {
        if strategy.is_empty() || strategy == "standard" {
            self.input = Some(Box::new(ParamListStandard::new(ParamListKind::Standard)));
            self.output = Some(Box::new(ParamListStandard::new(ParamListKind::StandardOut)));
        } else if strategy == "register" {
            self.input = Some(Box::new(ParamListStandard::new(ParamListKind::Register)));
            self.output = Some(Box::new(ParamListStandard::new(ParamListKind::RegisterOut)));
        } else {
            return Err(Error::Lowlevel(format!("Unknown strategy type: {}", strategy)));
        }
        Ok(())
    }

    pub fn get_id(&self) -> ModelId {
        self.id
    }

    pub fn get_kind(&self) -> &ProtoModelKind {
        &self.kind
    }

    pub fn get_name(&self) -> &str {
        &self.name
    }

    pub fn get_alias_parent(&self) -> Option<ModelId> {
        self.compat_model
    }

    pub fn has_effect(&self, addr: &Address, size: i32) -> u32 {
        ProtoModel::lookup_effect(&self.effectlist, addr, size)
    }

    pub fn get_extra_pop(&self) -> i32 {
        self.extrapop
    }

    pub fn set_extra_pop(&mut self, ep: i32) {
        self.extrapop = ep;
    }

    pub fn get_inject_upon_entry(&self) -> i32 {
        self.inject_upon_entry
    }

    pub fn get_inject_upon_return(&self) -> i32 {
        self.inject_upon_return
    }

    pub fn is_compatible(&self, op2: &ProtoModel) -> bool {
        self.id == op2.id || self.compat_model == Some(op2.id) || op2.compat_model == Some(self.id)
    }

    pub fn derive_input_map(&self, active: &mut ParamActive, manager: &AddrSpaceManager) -> Result<()> {
        self.input_list().fillin_map(active, manager)
    }

    pub fn derive_output_map(&self, active: &mut ParamActive, manager: &AddrSpaceManager) -> Result<()> {
        self.output_list().fillin_map(active, manager)
    }

    pub fn assign_parameter_storage(
        &self,
        proto: &PrototypePieces,
        res: &mut Vec<ParameterPieces>,
        ignore_output_error: bool,
        types: &mut TypeFactory,
        env: &AssignEnv<'_>,
    ) -> Result<()> {
        if ignore_output_error {
            match self.output_list().assign_map(proto, types, res, env) {
                Ok(()) => {}
                Err(Error::ParamUnassigned(_)) => {
                    res.clear();
                    res.push(ParameterPieces {
                        addr: Address::invalid(),
                        tp: Some(types.get_type_void()?),
                        flags: 0,
                    });
                }
                Err(err) => return Err(err),
            }
        } else {
            self.output_list().assign_map(proto, types, res, env)?;
        }
        self.input_list().assign_map(proto, types, res, env)?;

        if self.has_this && res.len() > 1 {
            let mut this_index = 1;
            if (res[1].flags & ParameterPieces::HIDDENRETPARM) != 0 && res.len() > 2 {
                if self.input_list().is_this_before_ret_pointer() {
                    let (first, second) = res.split_at_mut(2);
                    first[1].swap_markup(&mut second[0]);
                } else {
                    this_index = 2;
                }
            }
            res[this_index].flags |= ParameterPieces::ISTHIS;
        }
        Ok(())
    }

    pub fn check_input_join(&self, hiaddr: &Address, hisize: i32, loaddr: &Address, losize: i32) -> bool {
        self.input_list().check_join(hiaddr, hisize, loaddr, losize)
    }

    pub fn check_output_join(&self, hiaddr: &Address, hisize: i32, loaddr: &Address, losize: i32) -> bool {
        self.output_list().check_join(hiaddr, hisize, loaddr, losize)
    }

    pub fn check_input_split(&self, loc: &Address, size: i32, splitpoint: i32) -> bool {
        self.input_list().check_split(loc, size, splitpoint)
    }

    pub fn get_local_range(&self) -> &RangeList {
        &self.localrange
    }

    pub fn get_param_range(&self) -> &RangeList {
        &self.paramrange
    }

    pub fn get_effects(&self) -> &[EffectRecord] {
        &self.effectlist
    }

    pub fn get_trash(&self) -> &[VarnodeData] {
        &self.likelytrash
    }

    pub fn get_internal_storage(&self) -> &[VarnodeData] {
        &self.internalstorage
    }

    pub fn characterize_as_input_param(&self, loc: &Address, size: i32) -> i32 {
        self.input_list().characterize_as_param(loc, size)
    }

    pub fn characterize_as_output(&self, loc: &Address, size: i32) -> i32 {
        self.output_list().characterize_as_param(loc, size)
    }

    pub fn possible_input_param(&self, loc: &Address, size: i32) -> bool {
        self.input_list().possible_param(loc, size)
    }

    pub fn possible_output_param(&self, loc: &Address, size: i32) -> bool {
        self.output_list().possible_param(loc, size)
    }

    pub fn possible_input_param_with_slot(&self, loc: &Address, size: i32, slot: &mut i32, slotsize: &mut i32) -> bool {
        self.input_list().possible_param_with_slot(loc, size, slot, slotsize)
    }

    pub fn possible_output_param_with_slot(
        &self,
        loc: &Address,
        size: i32,
        slot: &mut i32,
        slotsize: &mut i32,
    ) -> bool {
        self.output_list().possible_param_with_slot(loc, size, slot, slotsize)
    }

    pub fn unjustified_input_param(&self, loc: &Address, size: i32, res: &mut VarnodeData) -> bool {
        self.input_list().unjustified_container(loc, size, res)
    }

    pub fn assumed_input_extension(&self, addr: &Address, size: i32, res: &mut VarnodeData) -> OpCode {
        self.input_list().assumed_extension(addr, size, res)
    }

    pub fn assumed_output_extension(&self, addr: &Address, size: i32, res: &mut VarnodeData) -> OpCode {
        self.output_list().assumed_extension(addr, size, res)
    }

    pub fn get_biggest_contained_input_param(&self, loc: &Address, size: i32, res: &mut VarnodeData) -> bool {
        self.input_list().get_biggest_contained_param(loc, size, res)
    }

    pub fn get_biggest_contained_output(&self, loc: &Address, size: i32, res: &mut VarnodeData) -> bool {
        self.output_list().get_biggest_contained_param(loc, size, res)
    }

    pub fn get_spacebase(&self) -> Option<&SpaceRef> {
        self.input_list().get_spacebase()
    }

    pub fn is_stack_grows_negative(&self) -> bool {
        self.stackgrowsnegative
    }

    pub fn has_this_pointer(&self) -> bool {
        self.has_this
    }

    pub fn is_constructor(&self) -> bool {
        self.is_construct
    }

    pub fn print_in_decl(&self) -> bool {
        self.is_printed
    }

    pub fn set_print_in_decl(&mut self, val: bool) {
        self.is_printed = val;
    }

    pub fn get_max_input_delay(&self) -> i32 {
        self.input_list().get_max_delay()
    }

    pub fn get_max_output_delay(&self) -> i32 {
        self.output_list().get_max_delay()
    }

    pub fn is_auto_killed_by_call(&self) -> bool {
        self.output_list().is_auto_killed_by_call()
    }

    pub fn is_merged(&self) -> bool {
        matches!(self.kind, ProtoModelKind::Merged { .. })
    }

    pub fn is_unknown(&self) -> bool {
        matches!(self.kind, ProtoModelKind::Unknown { .. })
    }

    fn decode_effect_group(
        list: &mut Vec<EffectRecord>,
        grouptype: u32,
        sub_id: u32,
        decoder: &mut dyn Decoder,
    ) -> Result<()> {
        decoder.open_element()?;
        while decoder.peek_element()? != 0 {
            let mut record = EffectRecord::new();
            record.decode(grouptype, decoder)?;
            list.push(record);
        }
        decoder.close_element(sub_id)?;
        Ok(())
    }

    fn decode_varnode_group(list: &mut Vec<VarnodeData>, sub_id: u32, decoder: &mut dyn Decoder) -> Result<()> {
        decoder.open_element()?;
        while decoder.peek_element()? != 0 {
            list.push(VarnodeData::decode(decoder)?);
        }
        decoder.close_element(sub_id)?;
        Ok(())
    }

    fn decode_standard(&mut self, decoder: &mut dyn Decoder, glb: &mut Architecture) -> Result<()> {
        let mut sawlocalrange = false;
        let mut sawparamrange = false;
        let mut sawretaddr = false;
        self.stackgrowsnegative = true;
        let stackspc = glb.manager.get_stack_space();
        if let Some(spc) = &stackspc {
            self.stackgrowsnegative = spc.stack_grows_negative();
        }
        let mut strategystring = String::new();
        self.localrange.clear();
        self.paramrange.clear();
        self.extrapop = -300;
        self.has_this = false;
        self.is_construct = false;
        self.is_printed = true;
        self.effectlist.clear();
        self.inject_upon_entry = -1;
        self.inject_upon_return = -1;
        self.likelytrash.clear();
        self.internalstorage.clear();
        let elem_id = decoder.open_element_expect(ELEM_PROTOTYPE)?;
        loop {
            let attrib_id = decoder.get_next_attribute_id()?;
            if attrib_id == 0 {
                break;
            }
            if attrib_id == ATTRIB_NAME {
                self.name = decoder.read_string()?;
            } else if attrib_id == ATTRIB_EXTRAPOP {
                self.extrapop =
                    decoder.read_signed_integer_expect_string("unknown", ProtoModel::EXTRAPOP_UNKNOWN as i64)? as i32;
            } else if attrib_id == ATTRIB_STACKSHIFT {
            } else if attrib_id == ATTRIB_STRATEGY {
                strategystring = decoder.read_string()?;
            } else if attrib_id == ATTRIB_HASTHIS {
                self.has_this = decoder.read_bool()?;
            } else if attrib_id == ATTRIB_CONSTRUCTOR {
                self.is_construct = decoder.read_bool()?;
            } else {
                return Err(Error::Lowlevel("Unknown prototype attribute".to_string()));
            }
        }
        if self.name == "__thiscall" {
            self.has_this = true;
        }
        if self.extrapop == -300 {
            return Err(Error::Lowlevel("Missing prototype attributes".to_string()));
        }

        self.build_param_list(&strategystring)?;
        loop {
            let sub_id = decoder.peek_element()?;
            if sub_id == 0 {
                break;
            }
            if sub_id == ELEM_INPUT {
                let input = self.input.as_mut().expect("prototype model has no input list");
                input.decode(decoder, &mut self.effectlist, self.stackgrowsnegative)?;
                if let Some(spc) = &stackspc {
                    input.get_range_list(spc, &mut self.paramrange);
                    if !self.paramrange.empty() {
                        sawparamrange = true;
                    }
                }
            } else if sub_id == ELEM_OUTPUT {
                let output = self.output.as_mut().expect("prototype model has no output list");
                output.decode(decoder, &mut self.effectlist, self.stackgrowsnegative)?;
            } else if sub_id == ELEM_UNAFFECTED {
                ProtoModel::decode_effect_group(&mut self.effectlist, EffectRecord::UNAFFECTED, sub_id, decoder)?;
            } else if sub_id == ELEM_KILLEDBYCALL {
                ProtoModel::decode_effect_group(&mut self.effectlist, EffectRecord::KILLEDBYCALL, sub_id, decoder)?;
            } else if sub_id == ELEM_RETURNADDRESS {
                ProtoModel::decode_effect_group(&mut self.effectlist, EffectRecord::RETURN_ADDRESS, sub_id, decoder)?;
                sawretaddr = true;
            } else if sub_id == ELEM_LOCALRANGE {
                sawlocalrange = true;
                decoder.open_element()?;
                while decoder.peek_element()? != 0 {
                    let range = Range::decode(decoder)?;
                    self.localrange.insert(&range);
                }
                decoder.close_element(sub_id)?;
            } else if sub_id == ELEM_PARAMRANGE {
                sawparamrange = true;
                decoder.open_element()?;
                while decoder.peek_element()? != 0 {
                    let range = Range::decode(decoder)?;
                    self.paramrange.insert(&range);
                }
                decoder.close_element(sub_id)?;
            } else if sub_id == ELEM_LIKELYTRASH {
                ProtoModel::decode_varnode_group(&mut self.likelytrash, sub_id, decoder)?;
            } else if sub_id == ELEM_INTERNAL_STORAGE {
                ProtoModel::decode_varnode_group(&mut self.internalstorage, sub_id, decoder)?;
            } else if sub_id == ELEM_PCODE {
                let mut library = glb
                    .pcodeinjectlib
                    .take()
                    .expect("architecture has no p-code inject library");
                let source = format!("Protomodel : {}", self.name);
                let decoded = library.decode_inject(&source, &self.name, CALLMECHANISM_TYPE, decoder, glb);
                let inject_id = match decoded {
                    Ok(inject_id) => inject_id,
                    Err(err) => {
                        glb.pcodeinjectlib = Some(library);
                        return Err(err);
                    }
                };
                let payload_name = library.get_payload(inject_id).get_name();
                glb.pcodeinjectlib = Some(library);
                if payload_name.contains("uponentry") {
                    self.inject_upon_entry = inject_id;
                } else {
                    self.inject_upon_return = inject_id;
                }
            } else {
                return Err(Error::Lowlevel("Unknown element in prototype".to_string()));
            }
        }
        decoder.close_element(elem_id)?;
        if !sawretaddr && glb.default_return_addr.space.is_some() {
            self.effectlist.push(EffectRecord::from_varnode_data(
                &glb.default_return_addr,
                EffectRecord::RETURN_ADDRESS,
            ));
        }
        std_sort(&mut self.effectlist, EffectRecord::compare_by_address);
        std_sort(&mut self.likelytrash, |first, second| first < second);
        std_sort(&mut self.internalstorage, |first, second| first < second);
        if !sawlocalrange {
            self.default_local_range(&glb.manager);
        }
        if !sawparamrange {
            self.default_param_range(&glb.manager);
        }
        Ok(())
    }

    fn decode_merged(&mut self, decoder: &mut dyn Decoder, glb: &mut Architecture) -> Result<()> {
        let elem_id = decoder.open_element_expect(ELEM_RESOLVEPROTOTYPE)?;
        self.name = decoder.read_string_attr(ATTRIB_NAME)?;
        loop {
            let sub_id = decoder.open_element()?;
            if sub_id != ELEM_MODEL {
                break;
            }
            let model_name = decoder.read_string_attr(ATTRIB_NAME)?;
            let Some(mymodel) = glb.get_model(&model_name) else {
                return Err(Error::Lowlevel(format!("Missing prototype model: {}", model_name)));
            };
            decoder.close_element(sub_id)?;
            self.fold_in(&glb.proto_models[mymodel])?;
            if let ProtoModelKind::Merged { modellist } = &mut self.kind {
                modellist.push(mymodel);
            }
        }
        decoder.close_element(elem_id)?;
        self.input
            .as_mut()
            .expect("merged prototype model has no input list")
            .finalize();
        Ok(())
    }

    pub fn decode(&mut self, decoder: &mut dyn Decoder, glb: &mut Architecture) -> Result<()> {
        match self.kind {
            ProtoModelKind::Merged { .. } => self.decode_merged(decoder, glb),
            _ => self.decode_standard(decoder, glb),
        }
    }

    pub fn lookup_effect(efflist: &[EffectRecord], addr: &Address, size: i32) -> u32 {
        if addr
            .get_space()
            .is_some_and(|spc| spc.get_type() == SpaceType::Internal)
        {
            return EffectRecord::UNAFFECTED;
        }
        let cur = EffectRecord::from_address(addr, size);
        let upper = efflist.partition_point(|elem| !EffectRecord::compare_by_address(&cur, elem));
        if upper == 0 {
            return EffectRecord::UNKNOWN_EFFECT;
        }
        let found = &efflist[upper - 1];
        let hit = found.get_address();
        let sz = found.get_size();
        if sz == 0 && space_eq(hit.get_space(), addr.get_space()) {
            return EffectRecord::UNAFFECTED;
        }
        let where_off = addr.overlap(0, &hit, sz);
        if where_off >= 0 && where_off + size <= sz {
            return found.get_type();
        }
        EffectRecord::UNKNOWN_EFFECT
    }

    pub fn lookup_record(efflist: &[EffectRecord], list_size: i32, addr: &Address, size: i32) -> i32 {
        if list_size == 0 {
            return -1;
        }
        let cur = EffectRecord::from_address(addr, size);
        let sublist = &efflist[..list_size as usize];
        let upper = sublist.partition_point(|elem| !EffectRecord::compare_by_address(&cur, elem));
        if upper == 0 {
            let close_addr = efflist[0].get_address();
            return if close_addr.overlap(0, addr, size) < 0 { -1 } else { -2 };
        }
        let found = &efflist[upper - 1];
        let close_addr = found.get_address();
        let sz = found.get_size();
        if *addr == close_addr && size == sz {
            return (upper - 1) as i32;
        }
        if addr.overlap(0, &close_addr, sz) < 0 { -1 } else { -2 }
    }

    pub fn get_placeholder_model(&self) -> Option<ModelId> {
        match &self.kind {
            ProtoModelKind::Unknown { placeholder_model } => Some(*placeholder_model),
            _ => None,
        }
    }

    fn merged_list(&self) -> &Vec<ModelId> {
        match &self.kind {
            ProtoModelKind::Merged { modellist } => modellist,
            _ => panic!("prototype model is not merged"),
        }
    }

    pub fn intersect_effects(&mut self, efflist: &[EffectRecord]) {
        let mut newlist: Vec<EffectRecord> = Vec::new();
        let mut first_index = 0;
        let mut second_index = 0;
        while first_index < self.effectlist.len() && second_index < efflist.len() {
            let eff1 = &self.effectlist[first_index];
            let eff2 = &efflist[second_index];
            if EffectRecord::compare_by_address(eff1, eff2) {
                first_index += 1;
            } else if EffectRecord::compare_by_address(eff2, eff1) {
                second_index += 1;
            } else {
                if eff1 == eff2 {
                    newlist.push(eff1.clone());
                }
                first_index += 1;
                second_index += 1;
            }
        }
        self.effectlist = newlist;
    }

    pub fn intersect_registers(reg_list1: &mut Vec<VarnodeData>, reg_list2: &[VarnodeData]) {
        let mut newlist: Vec<VarnodeData> = Vec::new();
        let mut first_index = 0;
        let mut second_index = 0;
        while first_index < reg_list1.len() && second_index < reg_list2.len() {
            let trs1 = &reg_list1[first_index];
            let trs2 = &reg_list2[second_index];
            if trs1 < trs2 {
                first_index += 1;
            } else if trs2 < trs1 {
                second_index += 1;
            } else {
                newlist.push(trs1.clone());
                first_index += 1;
                second_index += 1;
            }
        }
        *reg_list1 = newlist;
    }

    pub fn num_models(&self) -> i32 {
        self.merged_list().len() as i32
    }

    pub fn get_model(&self, index: i32) -> ModelId {
        self.merged_list()[index as usize]
    }

    pub fn fold_in(&mut self, model: &ProtoModel) -> Result<()> {
        let input_type = model.input_list().get_type();
        if input_type != P_STANDARD && input_type != P_REGISTER {
            return Err(Error::Lowlevel(
                "Can only resolve between standard prototype models".to_string(),
            ));
        }
        if self.input.is_none() {
            let mut merged = ParamListStandard::new(ParamListKind::Merged);
            let mut output = model.output_list().clone_list()?;
            output.kind = ParamListKind::StandardOut;
            merged.fold_in(model.input_list())?;
            self.input = Some(Box::new(merged));
            self.output = Some(output);
            self.extrapop = model.extrapop;
            self.effectlist = model.effectlist.clone();
            self.inject_upon_entry = model.inject_upon_entry;
            self.inject_upon_return = model.inject_upon_return;
            self.likelytrash = model.likelytrash.clone();
            self.localrange = model.localrange.clone();
            self.paramrange = model.paramrange.clone();
        } else {
            self.input
                .as_mut()
                .expect("merged prototype model has no input list")
                .fold_in(model.input_list())?;
            if self.extrapop != model.extrapop {
                self.extrapop = ProtoModel::EXTRAPOP_UNKNOWN;
            }
            if self.inject_upon_entry != model.inject_upon_entry || self.inject_upon_return != model.inject_upon_return
            {
                return Err(Error::Lowlevel(
                    "Cannot merge prototype models with different inject ids".to_string(),
                ));
            }
            self.intersect_effects(&model.effectlist);
            ProtoModel::intersect_registers(&mut self.likelytrash, &model.likelytrash);
            ProtoModel::intersect_registers(&mut self.internalstorage, &model.internalstorage);
            for range in model.localrange.iter() {
                self.localrange.insert(range);
            }
            for range in model.paramrange.iter() {
                self.paramrange.insert(range);
            }
        }
        Ok(())
    }

    pub fn select_model(
        &self,
        active: &mut ParamActive,
        models: &Arena<ModelId, ProtoModel>,
        _manager: &AddrSpaceManager,
    ) -> Result<ModelId> {
        let mut bestscore = 500;
        let mut bestindex: i32 = -1;
        let modellist = self.merged_list();
        for (index, model) in modellist.iter().enumerate() {
            let numtrials = active.get_num_trials();
            let mut scoremodel = ScoreProtoModel::new(true, *model, numtrials);
            for trial_index in 0..numtrials {
                let trial = active.get_trial(trial_index);
                if trial.is_active() {
                    scoremodel.add_parameter(trial.get_address(), trial.get_size(), models);
                }
            }
            scoremodel.do_score(models);
            let score = scoremodel.get_score();
            if score < bestscore {
                bestscore = score;
                bestindex = index as i32;
                if bestscore == 0 {
                    break;
                }
            }
        }
        if bestindex >= 0 {
            return Ok(modellist[bestindex as usize]);
        }
        Err(Error::Lowlevel("No model matches : missing default".to_string()))
    }
}

#[derive(Clone, Copy, Debug)]
pub struct PEntry {
    pub orig_index: i32,
    pub slot: i32,
    pub size: i32,
}

impl PartialEq for PEntry {
    fn eq(&self, op2: &PEntry) -> bool {
        self.slot == op2.slot
    }
}

impl Eq for PEntry {}

impl PartialOrd for PEntry {
    fn partial_cmp(&self, op2: &PEntry) -> Option<Ordering> {
        Some(self.cmp(op2))
    }
}

impl Ord for PEntry {
    fn cmp(&self, op2: &PEntry) -> Ordering {
        self.slot.cmp(&op2.slot)
    }
}

pub struct ScoreProtoModel {
    isinputscore: bool,
    entry: Vec<PEntry>,
    model: ModelId,
    finalscore: i32,
    mismatch: i32,
}

impl ScoreProtoModel {
    pub fn new(isinput: bool, model: ModelId, numparam: i32) -> ScoreProtoModel {
        ScoreProtoModel {
            isinputscore: isinput,
            entry: Vec::with_capacity(numparam.max(0) as usize),
            model,
            finalscore: -1,
            mismatch: 0,
        }
    }

    pub fn add_parameter(&mut self, addr: &Address, sz: i32, models: &Arena<ModelId, ProtoModel>) {
        let orig = self.entry.len() as i32;
        let mut slot = 0;
        let mut slotsize = 0;
        let model = &models[self.model];
        let isparam = if self.isinputscore {
            model.possible_input_param_with_slot(addr, sz, &mut slot, &mut slotsize)
        } else {
            model.possible_output_param_with_slot(addr, sz, &mut slot, &mut slotsize)
        };
        if isparam {
            self.entry.push(PEntry {
                orig_index: orig,
                slot,
                size: slotsize,
            });
        } else {
            self.mismatch += 1;
        }
    }

    pub fn do_score(&mut self, _models: &Arena<ModelId, ProtoModel>) {
        std_sort(&mut self.entry, |first, second| first.slot < second.slot);

        let mut nextfree = 0;
        let mut basescore = 0;
        let penalty = [16, 10, 7, 5];
        let penaltyfinal = 3;
        let mismatchpenalty = 20;

        for pentry in &self.entry {
            if pentry.slot > nextfree {
                while nextfree < pentry.slot {
                    if nextfree < 4 {
                        basescore += penalty[nextfree as usize];
                    } else {
                        basescore += penaltyfinal;
                    }
                    nextfree += 1;
                }
                nextfree += pentry.size;
            } else if nextfree > pentry.slot {
                basescore += mismatchpenalty;
                if pentry.slot + pentry.size > nextfree {
                    nextfree = pentry.slot + pentry.size;
                }
            } else {
                nextfree = pentry.slot + pentry.size;
            }
        }
        self.finalscore = basescore + mismatchpenalty * self.mismatch;
    }

    pub fn get_score(&self) -> i32 {
        self.finalscore
    }

    pub fn get_num_mismatch(&self) -> i32 {
        self.mismatch
    }
}

#[derive(Clone, Debug)]
pub struct ParameterBasic {
    name: String,
    addr: Address,
    tp: TypeId,
    flags: u32,
}

impl ParameterBasic {
    pub fn new(nm: &str, ad: &Address, tp: TypeId, fl: u32) -> ParameterBasic {
        ParameterBasic {
            name: nm.to_string(),
            addr: ad.clone(),
            tp,
            flags: fl,
        }
    }

    pub fn from_type(tp: TypeId) -> ParameterBasic {
        ParameterBasic {
            name: String::new(),
            addr: Address::default(),
            tp,
            flags: 0,
        }
    }

    pub fn get_name(&self) -> &str {
        &self.name
    }

    pub fn get_type(&self) -> TypeId {
        self.tp
    }

    pub fn get_address(&self) -> Address {
        self.addr.clone()
    }

    pub fn get_size(&self, glb: &Architecture) -> i32 {
        types_ref(glb).get(self.tp).get_size()
    }

    pub fn is_type_locked(&self) -> bool {
        (self.flags & ParameterPieces::TYPELOCK) != 0
    }

    pub fn is_name_locked(&self) -> bool {
        (self.flags & ParameterPieces::NAMELOCK) != 0
    }

    pub fn is_size_type_locked(&self) -> bool {
        (self.flags & ParameterPieces::SIZELOCK) != 0
    }

    pub fn is_this_pointer(&self) -> bool {
        (self.flags & ParameterPieces::ISTHIS) != 0
    }

    pub fn is_indirect_storage(&self) -> bool {
        (self.flags & ParameterPieces::INDIRECTSTORAGE) != 0
    }

    pub fn is_hidden_return(&self) -> bool {
        (self.flags & ParameterPieces::HIDDENRETPARM) != 0
    }

    pub fn is_name_undefined(&self) -> bool {
        self.name.is_empty()
    }

    pub fn set_type_lock(&mut self, val: bool, glb: &Architecture) {
        if val {
            self.flags |= ParameterPieces::TYPELOCK;
            if types_ref(glb).get(self.tp).get_metatype() == TypeMetatype::Unknown {
                self.flags |= ParameterPieces::SIZELOCK;
            }
        } else {
            self.flags &= !(ParameterPieces::TYPELOCK | ParameterPieces::SIZELOCK);
        }
    }

    pub fn set_name_lock(&mut self, val: bool) {
        if val {
            self.flags |= ParameterPieces::NAMELOCK;
        } else {
            self.flags &= !ParameterPieces::NAMELOCK;
        }
    }

    pub fn set_this_pointer(&mut self, val: bool) {
        if val {
            self.flags |= ParameterPieces::ISTHIS;
        } else {
            self.flags &= !ParameterPieces::ISTHIS;
        }
    }

    pub fn override_size_lock_type(&mut self, ct: TypeId, glb: &Architecture) -> Result<()> {
        let types = types_ref(glb);
        if types.get(self.tp).get_size() == types.get(ct).get_size() {
            if !self.is_size_type_locked() {
                return Err(Error::Lowlevel(
                    "Overriding parameter that is not size locked".to_string(),
                ));
            }
            self.tp = ct;
            return Ok(());
        }
        Err(Error::Lowlevel(
            "Overriding parameter with different type size".to_string(),
        ))
    }

    pub fn reset_size_lock_type(&mut self, factory: &mut TypeFactory) -> Result<()> {
        if factory.get(self.tp).get_metatype() == TypeMetatype::Unknown {
            return Ok(());
        }
        let size = factory.get(self.tp).get_size();
        self.tp = factory.get_base(size, TypeMetatype::Unknown)?;
        Ok(())
    }

    pub fn clone_param(&self) -> ParameterBasic {
        ParameterBasic::new(&self.name, &self.addr, self.tp, self.flags)
    }

    pub fn get_symbol(&self) -> Result<SymbolId> {
        Err(Error::Lowlevel("Parameter is not a real symbol".to_string()))
    }
}

#[derive(Clone, Debug, Default)]
pub struct ParameterSymbol {
    sym: Option<SymbolId>,
}

impl ParameterSymbol {
    pub fn new() -> ParameterSymbol {
        ParameterSymbol { sym: None }
    }

    fn symbol_id(&self) -> SymbolId {
        self.sym.expect("parameter has no backing symbol")
    }

    fn symbol<'a>(&self, glb: &'a Architecture) -> &'a Symbol {
        symtab_ref(glb).symbol(self.symbol_id())
    }

    pub fn get_name<'a>(&self, glb: &'a Architecture) -> &'a str {
        self.symbol(glb).get_name()
    }

    pub fn get_type(&self, glb: &Architecture) -> TypeId {
        self.symbol(glb).get_type().expect("parameter symbol has no data-type")
    }

    pub fn get_address(&self, glb: &Architecture) -> Address {
        let db = symtab_ref(glb);
        let entry = db
            .symbol_get_first_whole_map(self.symbol_id())
            .expect("parameter symbol has no storage mapping");
        let entry = db.entry(entry);
        if entry.is_dynamic() {
            return Address::invalid();
        }
        entry.get_addr().clone()
    }

    pub fn get_size(&self, glb: &Architecture) -> i32 {
        let db = symtab_ref(glb);
        let entry = db
            .symbol_get_first_whole_map(self.symbol_id())
            .expect("parameter symbol has no storage mapping");
        db.entry(entry).get_size()
    }

    pub fn is_type_locked(&self, glb: &Architecture) -> bool {
        self.symbol(glb).is_type_locked()
    }

    pub fn is_name_locked(&self, glb: &Architecture) -> bool {
        self.symbol(glb).is_name_locked()
    }

    pub fn is_size_type_locked(&self, glb: &Architecture) -> bool {
        self.symbol(glb).is_size_type_locked()
    }

    pub fn is_this_pointer(&self, glb: &Architecture) -> bool {
        self.symbol(glb).is_this_pointer()
    }

    pub fn is_indirect_storage(&self, glb: &Architecture) -> bool {
        self.symbol(glb).is_indirect_storage()
    }

    pub fn is_hidden_return(&self, glb: &Architecture) -> bool {
        self.symbol(glb).is_hidden_return()
    }

    pub fn is_name_undefined(&self, glb: &Architecture) -> bool {
        self.symbol(glb).is_name_undefined()
    }

    pub fn set_type_lock(&mut self, val: bool, glb: &mut Architecture) {
        let sym = self.symbol_id();
        let (db, types) = split_symtab_types(glb);
        let scope = db.symbol(sym).get_scope();
        let mut attrs = Varnode::TYPELOCK;
        if !db.symbol(sym).is_name_undefined() {
            attrs |= Varnode::NAMELOCK;
        }
        if val {
            db.scope_set_attribute(types, scope, sym, attrs);
        } else {
            db.scope_clear_attribute(types, scope, sym, attrs);
        }
    }

    pub fn set_name_lock(&mut self, val: bool, glb: &mut Architecture) {
        let sym = self.symbol_id();
        let (db, types) = split_symtab_types(glb);
        let scope = db.symbol(sym).get_scope();
        if val {
            db.scope_set_attribute(types, scope, sym, Varnode::NAMELOCK);
        } else {
            db.scope_clear_attribute(types, scope, sym, Varnode::NAMELOCK);
        }
    }

    pub fn set_this_pointer(&mut self, val: bool, glb: &mut Architecture) {
        let sym = self.symbol_id();
        let (db, _types) = split_symtab_types(glb);
        db.scope_set_this_pointer(sym, val);
    }

    pub fn override_size_lock_type(&mut self, ct: TypeId, glb: &mut Architecture) -> Result<()> {
        let sym = self.symbol_id();
        let (db, types) = split_symtab_types(glb);
        let scope = db.symbol(sym).get_scope();
        db.scope_override_size_lock_type(scope, sym, ct, types)
    }

    pub fn reset_size_lock_type(&mut self, glb: &mut Architecture) -> Result<()> {
        let sym = self.symbol_id();
        let scope = symtab_ref(glb).symbol(sym).get_scope();
        Database::scope_reset_size_lock_type(glb, scope, sym)
    }

    pub fn clone_param(&self) -> Result<ParameterSymbol> {
        Err(Error::Lowlevel("Should not be cloning ParameterSymbol".to_string()))
    }

    pub fn get_symbol(&self) -> Result<SymbolId> {
        Ok(self.symbol_id())
    }
}

fn split_symtab_types(glb: &mut Architecture) -> (&mut Database, &TypeFactory) {
    (
        glb.symboltab.as_deref_mut().expect("architecture has no symbol table"),
        glb.types.as_deref().expect("architecture has no type factory"),
    )
}

#[derive(Clone, Debug)]
pub enum ProtoParameter {
    Basic(ParameterBasic),
    Symbol(ParameterSymbol),
}

impl ProtoParameter {
    pub fn get_name<'a>(&'a self, glb: &'a Architecture) -> &'a str {
        match self {
            ProtoParameter::Basic(param) => param.get_name(),
            ProtoParameter::Symbol(param) => param.get_name(glb),
        }
    }

    pub fn get_type(&self, glb: &Architecture) -> TypeId {
        match self {
            ProtoParameter::Basic(param) => param.get_type(),
            ProtoParameter::Symbol(param) => param.get_type(glb),
        }
    }

    pub fn get_address(&self, glb: &Architecture) -> Address {
        match self {
            ProtoParameter::Basic(param) => param.get_address(),
            ProtoParameter::Symbol(param) => param.get_address(glb),
        }
    }

    pub fn get_size(&self, glb: &Architecture) -> i32 {
        match self {
            ProtoParameter::Basic(param) => param.get_size(glb),
            ProtoParameter::Symbol(param) => param.get_size(glb),
        }
    }

    pub fn is_type_locked(&self, glb: &Architecture) -> bool {
        match self {
            ProtoParameter::Basic(param) => param.is_type_locked(),
            ProtoParameter::Symbol(param) => param.is_type_locked(glb),
        }
    }

    pub fn is_name_locked(&self, glb: &Architecture) -> bool {
        match self {
            ProtoParameter::Basic(param) => param.is_name_locked(),
            ProtoParameter::Symbol(param) => param.is_name_locked(glb),
        }
    }

    pub fn is_size_type_locked(&self, glb: &Architecture) -> bool {
        match self {
            ProtoParameter::Basic(param) => param.is_size_type_locked(),
            ProtoParameter::Symbol(param) => param.is_size_type_locked(glb),
        }
    }

    pub fn is_this_pointer(&self, glb: &Architecture) -> bool {
        match self {
            ProtoParameter::Basic(param) => param.is_this_pointer(),
            ProtoParameter::Symbol(param) => param.is_this_pointer(glb),
        }
    }

    pub fn is_indirect_storage(&self, glb: &Architecture) -> bool {
        match self {
            ProtoParameter::Basic(param) => param.is_indirect_storage(),
            ProtoParameter::Symbol(param) => param.is_indirect_storage(glb),
        }
    }

    pub fn is_hidden_return(&self, glb: &Architecture) -> bool {
        match self {
            ProtoParameter::Basic(param) => param.is_hidden_return(),
            ProtoParameter::Symbol(param) => param.is_hidden_return(glb),
        }
    }

    pub fn is_name_undefined(&self, glb: &Architecture) -> bool {
        match self {
            ProtoParameter::Basic(param) => param.is_name_undefined(),
            ProtoParameter::Symbol(param) => param.is_name_undefined(glb),
        }
    }

    pub fn set_type_lock(&mut self, val: bool, glb: &mut Architecture) {
        match self {
            ProtoParameter::Basic(param) => param.set_type_lock(val, glb),
            ProtoParameter::Symbol(param) => param.set_type_lock(val, glb),
        }
    }

    pub fn set_name_lock(&mut self, val: bool, glb: &mut Architecture) {
        match self {
            ProtoParameter::Basic(param) => param.set_name_lock(val),
            ProtoParameter::Symbol(param) => param.set_name_lock(val, glb),
        }
    }

    pub fn set_this_pointer(&mut self, val: bool, glb: &mut Architecture) {
        match self {
            ProtoParameter::Basic(param) => param.set_this_pointer(val),
            ProtoParameter::Symbol(param) => param.set_this_pointer(val, glb),
        }
    }

    pub fn override_size_lock_type(&mut self, ct: TypeId, glb: &mut Architecture) -> Result<()> {
        match self {
            ProtoParameter::Basic(param) => param.override_size_lock_type(ct, glb),
            ProtoParameter::Symbol(param) => param.override_size_lock_type(ct, glb),
        }
    }

    pub fn reset_size_lock_type(&mut self, glb: &mut Architecture) -> Result<()> {
        match self {
            ProtoParameter::Basic(param) => param.reset_size_lock_type(types_mut(glb)),
            ProtoParameter::Symbol(param) => param.reset_size_lock_type(glb),
        }
    }

    pub fn clone_param(&self) -> Result<ProtoParameter> {
        match self {
            ProtoParameter::Basic(param) => Ok(ProtoParameter::Basic(param.clone_param())),
            ProtoParameter::Symbol(param) => Ok(ProtoParameter::Symbol(param.clone_param()?)),
        }
    }

    pub fn get_symbol(&self) -> Result<SymbolId> {
        match self {
            ProtoParameter::Basic(param) => param.get_symbol(),
            ProtoParameter::Symbol(param) => param.get_symbol(),
        }
    }

    pub fn equals(&self, op2: &ProtoParameter, glb: &Architecture) -> bool {
        if self.get_address(glb) != op2.get_address(glb) {
            return false;
        }
        if self.get_type(glb) != op2.get_type(glb) {
            return false;
        }
        true
    }

    pub fn not_equals(&self, op2: &ProtoParameter, glb: &Architecture) -> bool {
        !self.equals(op2, glb)
    }
}

pub struct ProtoStoreSymbol {
    scope: ScopeId,
    restricted_usepoint: Address,
    inparam: Vec<Option<Box<ProtoParameter>>>,
    outparam: Option<Box<ProtoParameter>>,
}

const FUNCTION_PARAMETER: i32 = Symbol::FUNCTION_PARAMETER as i32;

impl ProtoStoreSymbol {
    pub fn new(sc: ScopeId, usepoint: &Address, glb: &mut Architecture) -> Result<ProtoStoreSymbol> {
        let voidtype = types_mut(glb).get_type_void()?;
        Ok(ProtoStoreSymbol {
            scope: sc,
            restricted_usepoint: usepoint.clone(),
            inparam: Vec::new(),
            outparam: Some(Box::new(ProtoParameter::Basic(ParameterBasic::new(
                "",
                &Address::invalid(),
                voidtype,
                0,
            )))),
        })
    }

    pub fn get_symbol_backed(&mut self, index: i32) -> &mut ParameterSymbol {
        let index = index as usize;
        while self.inparam.len() <= index {
            self.inparam.push(None);
        }
        let is_symbol = matches!(self.inparam[index].as_deref(), Some(ProtoParameter::Symbol(_)));
        if !is_symbol {
            self.inparam[index] = Some(Box::new(ProtoParameter::Symbol(ParameterSymbol::new())));
        }
        match self.inparam[index].as_deref_mut() {
            Some(ProtoParameter::Symbol(param)) => param,
            _ => panic!("parameter slot is not symbol backed"),
        }
    }

    fn param_at(&mut self, index: i32) -> &mut ProtoParameter {
        self.inparam[index as usize]
            .as_deref_mut()
            .expect("input parameter slot is empty")
    }

    pub fn set_input(
        &mut self,
        index: i32,
        nm: &str,
        pieces: &ParameterPieces,
        glb: &mut Architecture,
    ) -> Result<&mut ProtoParameter> {
        self.get_symbol_backed(index);
        let scope = self.scope;
        let tp = pieces.get_type();
        let type_size = types_ref(glb).get(tp).get_size();
        let isindirect = (pieces.flags & ParameterPieces::INDIRECTSTORAGE) != 0;
        let ishidden = (pieces.flags & ParameterPieces::HIDDENRETPARM) != 0;
        let istypelock = (pieces.flags & ParameterPieces::TYPELOCK) != 0;
        let isnamelock = (pieces.flags & ParameterPieces::NAMELOCK) != 0;
        let mut sym = symtab_ref(glb).scope_get_category_symbol(scope, FUNCTION_PARAMETER, index);
        self.get_symbol_backed(index).sym = sym;
        if let Some(current) = sym {
            let db = symtab_ref(glb);
            let entry = db.entry(db.symbol_get_first_whole_map(current)?);
            if *entry.get_addr() != pieces.addr || entry.get_size() != type_size {
                split_symtab_types(glb).0.scope_remove_symbol(scope, current);
                sym = None;
                self.get_symbol_backed(index).sym = None;
            }
        }
        let Some(sym) = sym else {
            let mut usepoint = Address::invalid();
            if symtab_ref(glb)
                .scope_discover_scope(scope, &pieces.addr, type_size, &usepoint)
                .is_none()
            {
                usepoint = self.restricted_usepoint.clone();
            }
            let entry = Database::scope_add_symbol_at(glb, scope, nm, Some(tp), &pieces.addr, &usepoint)?;
            let new_sym = symtab_ref(glb).entry(entry).get_symbol();
            self.get_symbol_backed(index).sym = Some(new_sym);
            let (db, types) = split_symtab_types(glb);
            db.scope_set_category(scope, new_sym, FUNCTION_PARAMETER, index);
            if isindirect || ishidden || istypelock || isnamelock {
                let mut mirror = 0;
                if isindirect {
                    mirror |= Varnode::INDIRECTSTORAGE;
                }
                if ishidden {
                    mirror |= Varnode::HIDDENRETPARM;
                }
                if istypelock {
                    mirror |= Varnode::TYPELOCK;
                }
                if isnamelock {
                    mirror |= Varnode::NAMELOCK;
                }
                db.scope_set_attribute(types, scope, new_sym, mirror);
            }
            return Ok(self.param_at(index));
        };
        let (db, types) = split_symtab_types(glb);
        if db.symbol(sym).is_indirect_storage() != isindirect {
            if isindirect {
                db.scope_set_attribute(types, scope, sym, Varnode::INDIRECTSTORAGE);
            } else {
                db.scope_clear_attribute(types, scope, sym, Varnode::INDIRECTSTORAGE);
            }
        }
        if db.symbol(sym).is_hidden_return() != ishidden {
            if ishidden {
                db.scope_set_attribute(types, scope, sym, Varnode::HIDDENRETPARM);
            } else {
                db.scope_clear_attribute(types, scope, sym, Varnode::HIDDENRETPARM);
            }
        }
        if db.symbol(sym).is_type_locked() != istypelock {
            if istypelock {
                db.scope_set_attribute(types, scope, sym, Varnode::TYPELOCK);
            } else {
                db.scope_clear_attribute(types, scope, sym, Varnode::TYPELOCK);
            }
        }
        if db.symbol(sym).is_name_locked() != isnamelock {
            if isnamelock {
                db.scope_set_attribute(types, scope, sym, Varnode::NAMELOCK);
            } else {
                db.scope_clear_attribute(types, scope, sym, Varnode::NAMELOCK);
            }
        }
        if !nm.is_empty() && nm != db.symbol(sym).get_name() {
            db.scope_rename_symbol(scope, sym, nm)?;
        }
        if Some(tp) != db.symbol(sym).get_type() {
            Database::scope_retype_symbol(glb, scope, sym, tp)?;
        }
        Ok(self.param_at(index))
    }

    pub fn clear_input(&mut self, index: i32, glb: &mut Architecture) {
        let scope = self.scope;
        let db = split_symtab_types(glb).0;
        if let Some(sym) = db.scope_get_category_symbol(scope, FUNCTION_PARAMETER, index) {
            db.scope_set_category(scope, sym, Symbol::NO_CATEGORY as i32, 0);
            db.scope_remove_symbol(scope, sym);
        }
        let sz = db.scope_get_category_size(scope, FUNCTION_PARAMETER);
        for position in (index + 1)..sz {
            if let Some(sym) = db.scope_get_category_symbol(scope, FUNCTION_PARAMETER, position) {
                db.scope_set_category(scope, sym, FUNCTION_PARAMETER, position - 1);
            }
        }
    }

    pub fn clear_all_inputs(&mut self, glb: &mut Architecture) {
        split_symtab_types(glb).0.scope_clear_category(self.scope, 0);
    }

    pub fn get_num_inputs(&self, glb: &Architecture) -> i32 {
        symtab_ref(glb).scope_get_category_size(self.scope, FUNCTION_PARAMETER)
    }

    pub fn get_input(&mut self, index: i32, glb: &Architecture) -> Option<&mut ProtoParameter> {
        let sym = symtab_ref(glb).scope_get_category_symbol(self.scope, FUNCTION_PARAMETER, index)?;
        self.get_symbol_backed(index).sym = Some(sym);
        Some(self.param_at(index))
    }

    pub fn set_output(&mut self, piece: &ParameterPieces, _glb: &mut Architecture) -> Result<&mut ProtoParameter> {
        self.outparam = Some(Box::new(ProtoParameter::Basic(ParameterBasic::new(
            "",
            &piece.addr,
            piece.get_type(),
            piece.flags,
        ))));
        Ok(self.outparam.as_deref_mut().expect("output was just set"))
    }

    pub fn clear_output(&mut self, glb: &mut Architecture) -> Result<()> {
        let pieces = ParameterPieces {
            addr: Address::invalid(),
            tp: Some(types_mut(glb).get_type_void()?),
            flags: 0,
        };
        self.set_output(&pieces, glb)?;
        Ok(())
    }

    pub fn get_output(&mut self) -> Option<&mut ProtoParameter> {
        self.outparam.as_deref_mut()
    }

    pub fn get_output_ref(&self) -> Option<&ProtoParameter> {
        self.outparam.as_deref()
    }

    pub fn clone_store(&self) -> Result<ProtoStoreSymbol> {
        let outparam = match &self.outparam {
            Some(param) => Some(Box::new(param.clone_param()?)),
            None => None,
        };
        Ok(ProtoStoreSymbol {
            scope: self.scope,
            restricted_usepoint: self.restricted_usepoint.clone(),
            inparam: Vec::new(),
            outparam,
        })
    }

    pub fn encode(&self, _encoder: &mut dyn Encoder) -> Result<()> {
        Ok(())
    }

    pub fn decode(&mut self, _decoder: &mut dyn Decoder, _model: Option<ModelId>) -> Result<()> {
        Err(Error::Lowlevel(
            "Do not decode symbol-backed prototype through this interface".to_string(),
        ))
    }
}

pub struct ProtoStoreInternal {
    voidtype: TypeId,
    inparam: Vec<Option<Box<ProtoParameter>>>,
    outparam: Option<Box<ProtoParameter>>,
}

impl ProtoStoreInternal {
    pub fn new(vt: TypeId) -> ProtoStoreInternal {
        ProtoStoreInternal {
            voidtype: vt,
            inparam: Vec::new(),
            outparam: Some(Box::new(ProtoParameter::Basic(ParameterBasic::new(
                "",
                &Address::invalid(),
                vt,
                0,
            )))),
        }
    }

    pub fn set_input(&mut self, index: i32, nm: &str, pieces: &ParameterPieces) -> Result<&mut ProtoParameter> {
        let index = index as usize;
        while self.inparam.len() <= index {
            self.inparam.push(None);
        }
        self.inparam[index] = Some(Box::new(ProtoParameter::Basic(ParameterBasic::new(
            nm,
            &pieces.addr,
            pieces.get_type(),
            pieces.flags,
        ))));
        Ok(self.inparam[index].as_deref_mut().expect("input was just set"))
    }

    pub fn clear_input(&mut self, index: i32) {
        let sz = self.inparam.len();
        let index = index as usize;
        if index >= sz {
            return;
        }
        self.inparam[index] = None;
        for position in (index + 1)..sz {
            self.inparam[position - 1] = self.inparam[position].take();
        }
        while let Some(None) = self.inparam.last() {
            self.inparam.pop();
        }
    }

    pub fn clear_all_inputs(&mut self) {
        self.inparam.clear();
    }

    pub fn get_num_inputs(&self) -> i32 {
        self.inparam.len() as i32
    }

    pub fn get_input(&mut self, index: i32) -> Option<&mut ProtoParameter> {
        if index < 0 || index as usize >= self.inparam.len() {
            return None;
        }
        self.inparam[index as usize].as_deref_mut()
    }

    pub fn set_output(&mut self, piece: &ParameterPieces) -> Result<&mut ProtoParameter> {
        self.outparam = Some(Box::new(ProtoParameter::Basic(ParameterBasic::new(
            "",
            &piece.addr,
            piece.get_type(),
            piece.flags,
        ))));
        Ok(self.outparam.as_deref_mut().expect("output was just set"))
    }

    pub fn clear_output(&mut self) {
        self.outparam = Some(Box::new(ProtoParameter::Basic(ParameterBasic::from_type(
            self.voidtype,
        ))));
    }

    pub fn get_output(&mut self) -> Option<&mut ProtoParameter> {
        self.outparam.as_deref_mut()
    }

    pub fn get_output_ref(&self) -> Option<&ProtoParameter> {
        self.outparam.as_deref()
    }

    pub fn clone_store(&self) -> Result<ProtoStoreInternal> {
        let outparam = match &self.outparam {
            Some(param) => Some(Box::new(param.clone_param()?)),
            None => None,
        };
        let mut inparam = Vec::with_capacity(self.inparam.len());
        for param in &self.inparam {
            inparam.push(match param {
                Some(param) => Some(Box::new(param.clone_param()?)),
                None => None,
            });
        }
        Ok(ProtoStoreInternal {
            voidtype: self.voidtype,
            inparam,
            outparam,
        })
    }

    pub fn encode(&self, encoder: &mut dyn Encoder, glb: &Architecture) -> Result<()> {
        let types = types_ref(glb);
        encoder.open_element(ELEM_INTERNALLIST);
        match &self.outparam {
            Some(outparam) => {
                encoder.open_element(ELEM_RETPARAM);
                if outparam.is_type_locked(glb) {
                    encoder.write_bool(ATTRIB_TYPELOCK, true);
                }
                outparam.get_address(glb).encode(encoder)?;
                types.get(outparam.get_type(glb)).encode_ref(encoder, glb)?;
                encoder.close_element(ELEM_RETPARAM);
            }
            None => {
                encoder.open_element(ELEM_RETPARAM);
                encoder.open_element(ELEM_ADDR);
                encoder.close_element(ELEM_ADDR);
                encoder.open_element(ELEM_VOID);
                encoder.close_element(ELEM_VOID);
                encoder.close_element(ELEM_RETPARAM);
            }
        }
        for param in &self.inparam {
            let param = param.as_deref().expect("input parameter slot is empty");
            encoder.open_element(ELEM_PARAM);
            if !param.get_name(glb).is_empty() {
                encoder.write_string(ATTRIB_NAME, param.get_name(glb));
            }
            if param.is_type_locked(glb) {
                encoder.write_bool(ATTRIB_TYPELOCK, true);
            }
            if param.is_name_locked(glb) {
                encoder.write_bool(ATTRIB_NAMELOCK, true);
            }
            if param.is_this_pointer(glb) {
                encoder.write_bool(ATTRIB_THISPTR, true);
            }
            if param.is_indirect_storage(glb) {
                encoder.write_bool(ATTRIB_INDIRECTSTORAGE, true);
            }
            if param.is_hidden_return(glb) {
                encoder.write_bool(ATTRIB_HIDDENRETPARM, true);
            }
            param.get_address(glb).encode(encoder)?;
            types.get(param.get_type(glb)).encode_ref(encoder, glb)?;
            encoder.close_element(ELEM_PARAM);
        }
        encoder.close_element(ELEM_INTERNALLIST);
        Ok(())
    }

    pub fn decode(&mut self, decoder: &mut dyn Decoder, model: Option<ModelId>, glb: &mut Architecture) -> Result<()> {
        let model_id = model.expect("internal prototype store decoded without a model");
        let mut pieces: Vec<ParameterPieces> = Vec::new();
        let mut proto = PrototypePieces {
            model: Some(model_id),
            first_var_arg_slot: -1,
            ..PrototypePieces::default()
        };
        let mut addressesdetermined = true;

        {
            let outparam = self
                .outparam
                .as_deref()
                .expect("internal prototype store has no output parameter");
            let mut flags = 0;
            if outparam.is_type_locked(glb) {
                flags |= ParameterPieces::TYPELOCK;
            }
            if outparam.is_indirect_storage(glb) {
                flags |= ParameterPieces::INDIRECTSTORAGE;
            }
            if outparam.get_address(glb).is_invalid() {
                addressesdetermined = false;
            }
            pieces.push(ParameterPieces {
                addr: Address::invalid(),
                tp: Some(outparam.get_type(glb)),
                flags,
            });
        }

        let elem_id = decoder.open_element_expect(ELEM_INTERNALLIST)?;
        let first_id = decoder.get_next_attribute_id()?;
        if first_id == ATTRIB_FIRST {
            proto.first_var_arg_slot = decoder.read_signed_integer()? as i32;
        }
        loop {
            let sub_id = decoder.open_element()?;
            if sub_id == 0 {
                break;
            }
            let mut name = String::new();
            let mut flags = 0;
            loop {
                let attrib_id = decoder.get_next_attribute_id()?;
                if attrib_id == 0 {
                    break;
                }
                if attrib_id == ATTRIB_NAME {
                    name = decoder.read_string()?;
                } else if attrib_id == ATTRIB_TYPELOCK {
                    if decoder.read_bool()? {
                        flags |= ParameterPieces::TYPELOCK;
                    }
                } else if attrib_id == ATTRIB_NAMELOCK {
                    if decoder.read_bool()? {
                        flags |= ParameterPieces::NAMELOCK;
                    }
                } else if attrib_id == ATTRIB_THISPTR {
                    if decoder.read_bool()? {
                        flags |= ParameterPieces::ISTHIS;
                    }
                } else if attrib_id == ATTRIB_INDIRECTSTORAGE {
                    if decoder.read_bool()? {
                        flags |= ParameterPieces::INDIRECTSTORAGE;
                    }
                } else if attrib_id == ATTRIB_HIDDENRETPARM && decoder.read_bool()? {
                    flags |= ParameterPieces::HIDDENRETPARM;
                }
            }
            if (flags & ParameterPieces::HIDDENRETPARM) == 0 {
                proto.innames.push(name);
            }
            let addr = Address::decode(decoder)?;
            let tp = TypeFactory::decode_type(glb, decoder)?;
            if addr.is_invalid() {
                addressesdetermined = false;
            }
            pieces.push(ParameterPieces {
                addr,
                tp: Some(tp),
                flags,
            });
            decoder.close_element(sub_id)?;
        }
        decoder.close_element(elem_id)?;
        if !addressesdetermined {
            proto.outtype = pieces[0].tp;
            for piece in pieces.iter().skip(1) {
                proto.intypes.push(piece.get_type());
            }
            let mut addr_pieces: Vec<ParameterPieces> = Vec::new();
            assign_storage_glb(model_id, &proto, &mut addr_pieces, true, glb)?;
            std::mem::swap(&mut addr_pieces, &mut pieces);
            let mut slot = 0usize;
            for piece in pieces.iter_mut() {
                if (piece.flags & ParameterPieces::HIDDENRETPARM) != 0 {
                    continue;
                }
                piece.flags = addr_pieces[slot].flags;
                slot += 1;
            }
            if pieces[0].addr.is_invalid() {
                pieces[0].flags &= !ParameterPieces::TYPELOCK;
            }
            let locked = (pieces[0].flags & ParameterPieces::TYPELOCK) != 0;
            let curparam = self.set_output(&pieces[0])?;
            curparam.set_type_lock(locked, glb);
        }
        let mut name_index = 0usize;
        for index in 1..pieces.len() {
            if (pieces[index].flags & ParameterPieces::HIDDENRETPARM) != 0 {
                let locked = (pieces[0].flags & ParameterPieces::TYPELOCK) != 0;
                let curparam = self.set_input((index - 1) as i32, "rethidden", &pieces[index])?;
                curparam.set_type_lock(locked, glb);
                continue;
            }
            let type_locked = (pieces[index].flags & ParameterPieces::TYPELOCK) != 0;
            let name_locked = (pieces[index].flags & ParameterPieces::NAMELOCK) != 0;
            let curparam = self.set_input((index - 1) as i32, &proto.innames[name_index], &pieces[index])?;
            curparam.set_type_lock(type_locked, glb);
            curparam.set_name_lock(name_locked, glb);
            name_index += 1;
        }
        Ok(())
    }
}

pub enum ProtoStore {
    Symbol(ProtoStoreSymbol),
    Internal(ProtoStoreInternal),
}

impl ProtoStore {
    pub fn set_input(
        &mut self,
        index: i32,
        nm: &str,
        pieces: &ParameterPieces,
        glb: &mut Architecture,
    ) -> Result<&mut ProtoParameter> {
        match self {
            ProtoStore::Symbol(store) => store.set_input(index, nm, pieces, glb),
            ProtoStore::Internal(store) => store.set_input(index, nm, pieces),
        }
    }

    pub fn clear_input(&mut self, index: i32, glb: &mut Architecture) {
        match self {
            ProtoStore::Symbol(store) => store.clear_input(index, glb),
            ProtoStore::Internal(store) => store.clear_input(index),
        }
    }

    pub fn clear_all_inputs(&mut self, glb: &mut Architecture) {
        match self {
            ProtoStore::Symbol(store) => store.clear_all_inputs(glb),
            ProtoStore::Internal(store) => store.clear_all_inputs(),
        }
    }

    pub fn get_num_inputs(&self, glb: &Architecture) -> i32 {
        match self {
            ProtoStore::Symbol(store) => store.get_num_inputs(glb),
            ProtoStore::Internal(store) => store.get_num_inputs(),
        }
    }

    pub fn get_input(&mut self, index: i32, glb: &Architecture) -> Option<&mut ProtoParameter> {
        match self {
            ProtoStore::Symbol(store) => store.get_input(index, glb),
            ProtoStore::Internal(store) => store.get_input(index),
        }
    }

    pub fn set_output(&mut self, piece: &ParameterPieces, glb: &mut Architecture) -> Result<&mut ProtoParameter> {
        match self {
            ProtoStore::Symbol(store) => store.set_output(piece, glb),
            ProtoStore::Internal(store) => store.set_output(piece),
        }
    }

    pub fn clear_output(&mut self, glb: &mut Architecture) -> Result<()> {
        match self {
            ProtoStore::Symbol(store) => store.clear_output(glb),
            ProtoStore::Internal(store) => {
                store.clear_output();
                Ok(())
            }
        }
    }

    pub fn get_output(&mut self) -> Option<&mut ProtoParameter> {
        match self {
            ProtoStore::Symbol(store) => store.get_output(),
            ProtoStore::Internal(store) => store.get_output(),
        }
    }

    pub fn get_output_ref(&self) -> Option<&ProtoParameter> {
        match self {
            ProtoStore::Symbol(store) => store.get_output_ref(),
            ProtoStore::Internal(store) => store.get_output_ref(),
        }
    }

    pub fn clone_store(&self) -> Result<ProtoStore> {
        match self {
            ProtoStore::Symbol(store) => Ok(ProtoStore::Symbol(store.clone_store()?)),
            ProtoStore::Internal(store) => Ok(ProtoStore::Internal(store.clone_store()?)),
        }
    }

    pub fn encode(&self, encoder: &mut dyn Encoder, glb: &Architecture) -> Result<()> {
        match self {
            ProtoStore::Symbol(store) => store.encode(encoder),
            ProtoStore::Internal(store) => store.encode(encoder, glb),
        }
    }

    pub fn decode(&mut self, decoder: &mut dyn Decoder, model: Option<ModelId>, glb: &mut Architecture) -> Result<()> {
        match self {
            ProtoStore::Symbol(store) => store.decode(decoder, model),
            ProtoStore::Internal(store) => store.decode(decoder, model, glb),
        }
    }
}

pub fn assign_storage_glb(
    model: ModelId,
    proto: &PrototypePieces,
    res: &mut Vec<ParameterPieces>,
    ignore_output_error: bool,
    glb: &mut Architecture,
) -> Result<()> {
    let types = glb.types.as_deref_mut().expect("architecture has no type factory");
    let translate = glb.translate.as_deref().expect("architecture has no translator");
    let env = AssignEnv {
        manager: &glb.manager,
        translate,
    };
    glb.proto_models[model].assign_parameter_storage(proto, res, ignore_output_error, types, &env)
}

pub struct FuncProto {
    model: Option<ModelId>,
    store: Option<Box<ProtoStore>>,
    extrapop: i32,
    flags: u32,
    effectlist: Vec<EffectRecord>,
    likelytrash: Vec<VarnodeData>,
    injectid: i32,
    return_bytes_consumed: i32,
}

impl Default for FuncProto {
    fn default() -> FuncProto {
        FuncProto::new()
    }
}

impl FuncProto {
    pub const DOTDOTDOT: u32 = 1;
    pub const VOIDINPUTLOCK: u32 = 2;
    pub const MODELLOCK: u32 = 4;
    pub const IS_INLINE: u32 = 8;
    pub const NO_RETURN: u32 = 16;
    pub const PARAMSHIFT_APPLIED: u32 = 32;
    pub const ERROR_INPUTPARAM: u32 = 64;
    pub const ERROR_OUTPUTPARAM: u32 = 128;
    pub const CUSTOM_STORAGE: u32 = 256;
    pub const IS_CONSTRUCTOR: u32 = 0x200;
    pub const IS_DESTRUCTOR: u32 = 0x400;
    pub const HAS_THISPTR: u32 = 0x800;
    pub const IS_OVERRIDE: u32 = 0x1000;
    pub const AUTO_KILLEDBYCALL: u32 = 0x2000;

    pub fn new() -> FuncProto {
        FuncProto {
            model: None,
            store: None,
            extrapop: 0,
            flags: 0,
            effectlist: Vec::new(),
            likelytrash: Vec::new(),
            injectid: -1,
            return_bytes_consumed: 0,
        }
    }

    fn model_ref<'a>(&self, glb: &'a Architecture) -> &'a ProtoModel {
        &glb.proto_models[self.model.expect("prototype has no model")]
    }

    fn store_ref(&self) -> &ProtoStore {
        self.store.as_ref().expect("prototype has no parameter store")
    }

    fn store_mut(&mut self) -> &mut ProtoStore {
        self.store.as_mut().expect("prototype has no parameter store")
    }

    fn set_flag(&mut self, flag: u32, val: bool) {
        self.flags = if val { self.flags | flag } else { self.flags & !flag };
    }

    fn param_at(&mut self, index: i32, glb: &Architecture) -> &mut ProtoParameter {
        self.store_mut().get_input(index, glb).expect("missing input parameter")
    }

    fn output_param(&mut self) -> &mut ProtoParameter {
        self.store_mut()
            .get_output()
            .expect("prototype has no output parameter")
    }

    pub fn update_this_pointer(&mut self, glb: &mut Architecture) -> Result<()> {
        if !self.model_ref(glb).has_this_pointer() {
            return Ok(());
        }
        let num_inputs = self.store_ref().get_num_inputs(glb);
        if num_inputs == 0 {
            return Ok(());
        }
        let mut index = 0;
        if self.param_at(0, glb).is_hidden_return(glb) {
            if num_inputs < 2 {
                return Ok(());
            }
            index = 1;
        }
        self.param_at(index, glb).set_this_pointer(true, glb);
        Ok(())
    }

    pub fn encode_effect(&self, encoder: &mut dyn Encoder, glb: &Architecture) -> Result<()> {
        if self.effectlist.is_empty() {
            return Ok(());
        }
        let mut unaffected_list: Vec<&EffectRecord> = Vec::new();
        let mut killed_by_call_list: Vec<&EffectRecord> = Vec::new();
        let mut ret_addr: Option<&EffectRecord> = None;
        let model = self.model_ref(glb);
        for cur_record in &self.effectlist {
            let tp = model.has_effect(&cur_record.get_address(), cur_record.get_size());
            if tp == cur_record.get_type() {
                continue;
            }
            if cur_record.get_type() == EffectRecord::UNAFFECTED {
                unaffected_list.push(cur_record);
            } else if cur_record.get_type() == EffectRecord::KILLEDBYCALL {
                killed_by_call_list.push(cur_record);
            } else if cur_record.get_type() == EffectRecord::RETURN_ADDRESS {
                ret_addr = Some(cur_record);
            }
        }
        if !unaffected_list.is_empty() {
            encoder.open_element(ELEM_UNAFFECTED);
            for record in &unaffected_list {
                record.encode(encoder)?;
            }
            encoder.close_element(ELEM_UNAFFECTED);
        }
        if !killed_by_call_list.is_empty() {
            encoder.open_element(ELEM_KILLEDBYCALL);
            for record in &killed_by_call_list {
                record.encode(encoder)?;
            }
            encoder.close_element(ELEM_KILLEDBYCALL);
        }
        if let Some(record) = ret_addr {
            encoder.open_element(ELEM_RETURNADDRESS);
            record.encode(encoder)?;
            encoder.close_element(ELEM_RETURNADDRESS);
        }
        Ok(())
    }

    pub fn encode_likely_trash(&self, encoder: &mut dyn Encoder, glb: &Architecture) -> Result<()> {
        if self.likelytrash.is_empty() {
            return Ok(());
        }
        let model_trash = self.model_ref(glb).get_trash();
        encoder.open_element(ELEM_LIKELYTRASH);
        for cur in &self.likelytrash {
            if model_trash.binary_search(cur).is_ok() {
                continue;
            }
            encoder.open_element(ELEM_ADDR);
            cur.space
                .as_ref()
                .expect("likely trash register has no space")
                .encode_attributes_size(encoder, cur.offset, cur.size as i32)?;
            encoder.close_element(ELEM_ADDR);
        }
        encoder.close_element(ELEM_LIKELYTRASH);
        Ok(())
    }

    pub fn decode_effect(&mut self, glb: &Architecture) -> Result<()> {
        if self.effectlist.is_empty() {
            return Ok(());
        }
        let tmp_list = std::mem::take(&mut self.effectlist);
        self.effectlist.extend_from_slice(self.model_ref(glb).get_effects());
        let mut has_new = false;
        let list_size = self.effectlist.len() as i32;
        for cur_record in &tmp_list {
            let off = ProtoModel::lookup_record(
                &self.effectlist,
                list_size,
                &cur_record.get_address(),
                cur_record.get_size(),
            );
            if off == -2 {
                return Err(Error::Lowlevel(
                    "Partial overlap of prototype override with existing effects".to_string(),
                ));
            } else if off >= 0 {
                self.effectlist[off as usize] = cur_record.clone();
            } else {
                self.effectlist.push(cur_record.clone());
                has_new = true;
            }
        }
        if has_new {
            std_sort(&mut self.effectlist, EffectRecord::compare_by_address);
        }
        Ok(())
    }

    pub fn decode_likely_trash(&mut self, glb: &Architecture) {
        if self.likelytrash.is_empty() {
            return;
        }
        let tmp_list = std::mem::take(&mut self.likelytrash);
        let model_trash = self.model_ref(glb).get_trash();
        self.likelytrash.extend_from_slice(model_trash);
        for cur in &tmp_list {
            if model_trash.binary_search(cur).is_err() {
                self.likelytrash.push(cur.clone());
            }
        }
        std_sort(&mut self.likelytrash, |first, second| first < second);
    }

    pub fn param_shift(&mut self, paramshift: i32, glb: &mut Architecture) -> Result<()> {
        let (Some(model), true) = (self.model, self.store.is_some()) else {
            return Err(Error::Lowlevel("Cannot parameter shift without a model".to_string()));
        };
        let mut proto = PrototypePieces {
            model: Some(model),
            first_var_arg_slot: -1,
            ..PrototypePieces::default()
        };
        if self.is_output_locked(glb) {
            proto.outtype = Some(self.get_output_type(glb));
        } else {
            proto.outtype = Some(types_mut(glb).get_type_void()?);
        }
        let extra = types_mut(glb).get_base(4, TypeMetatype::Unknown)?;
        for _ in 0..paramshift {
            proto.innames.push(String::new());
            proto.intypes.push(extra);
        }
        if self.is_input_locked(glb) {
            let num = self.num_params(glb);
            for index in 0..num {
                let param = self.param_at(index, glb);
                let name = param.get_name(glb).to_string();
                let tp = param.get_type(glb);
                proto.innames.push(name);
                proto.intypes.push(tp);
            }
        } else {
            proto.first_var_arg_slot = paramshift;
        }

        let mut pieces: Vec<ParameterPieces> = Vec::new();
        assign_storage_glb(model, &proto, &mut pieces, false, glb)?;

        let voidtype = types_mut(glb).get_type_void()?;
        self.store = Some(Box::new(ProtoStore::Internal(ProtoStoreInternal::new(voidtype))));
        let store = self.store_mut();
        store.set_output(&pieces[0], glb)?;
        let mut name_index = 0usize;
        for index in 1..pieces.len() {
            if (pieces[index].flags & ParameterPieces::HIDDENRETPARM) != 0 {
                store.set_input((index - 1) as i32, "rethidden", &pieces[index], glb)?;
                continue;
            }
            store.set_input(name_index as i32, &proto.innames[name_index], &pieces[index], glb)?;
            name_index += 1;
        }
        self.set_input_lock(true, glb);
        self.set_dotdotdot(proto.first_var_arg_slot >= 0);
        Ok(())
    }

    pub fn is_paramshift_applied(&self) -> bool {
        (self.flags & FuncProto::PARAMSHIFT_APPLIED) != 0
    }

    pub fn set_paramshift_applied(&mut self, val: bool) {
        self.set_flag(FuncProto::PARAMSHIFT_APPLIED, val);
    }

    pub fn get_model(&self) -> Option<ModelId> {
        self.model
    }

    pub fn copy(&mut self, op2: &FuncProto) -> Result<()> {
        self.model = op2.model;
        self.extrapop = op2.extrapop;
        self.flags = op2.flags;
        self.store = match &op2.store {
            Some(store) => Some(Box::new(store.clone_store()?)),
            None => None,
        };
        self.effectlist = op2.effectlist.clone();
        self.likelytrash = op2.likelytrash.clone();
        self.injectid = op2.injectid;
        Ok(())
    }

    pub fn copy_flow_effects(&mut self, op2: &FuncProto) {
        self.flags &= !(FuncProto::IS_INLINE | FuncProto::NO_RETURN);
        self.flags |= op2.flags & (FuncProto::IS_INLINE | FuncProto::NO_RETURN);
        self.injectid = op2.injectid;
    }

    pub fn get_pieces(&mut self, pieces: &mut PrototypePieces, glb: &Architecture) {
        pieces.model = self.model;
        if self.store.is_none() {
            return;
        }
        pieces.outtype = Some(self.output_param().get_type(glb));
        let num = self.store_ref().get_num_inputs(glb);
        for index in 0..num {
            let param = self.param_at(index, glb);
            let tp = param.get_type(glb);
            let name = param.get_name(glb).to_string();
            pieces.intypes.push(tp);
            pieces.innames.push(name);
        }
        pieces.first_var_arg_slot = if self.is_dotdotdot() { num } else { -1 };
    }

    pub fn set_pieces(&mut self, pieces: &PrototypePieces, glb: &mut Architecture) -> Result<()> {
        if pieces.model.is_some() {
            self.set_model(pieces.model, glb);
        }
        self.update_all_types(pieces, glb)?;
        self.set_input_lock(true, glb);
        self.set_output_lock(true, glb);
        self.set_model_lock(true);
        Ok(())
    }

    pub fn set_scope(&mut self, scope: ScopeId, startpoint: &Address, glb: &mut Architecture) -> Result<()> {
        self.store = Some(Box::new(ProtoStore::Symbol(ProtoStoreSymbol::new(
            scope, startpoint, glb,
        )?)));
        if self.model.is_none() {
            let defaultfp = glb.defaultfp;
            self.set_model(defaultfp, glb);
        }
        Ok(())
    }

    pub fn set_internal(&mut self, model: ModelId, vt: TypeId, glb: &Architecture) {
        self.store = Some(Box::new(ProtoStore::Internal(ProtoStoreInternal::new(vt))));
        if self.model.is_none() {
            self.set_model(Some(model), glb);
        }
    }

    pub fn set_model(&mut self, model_2: Option<ModelId>, glb: &Architecture) {
        match model_2 {
            Some(model_id) => {
                let model = &glb.proto_models[model_id];
                let expop = model.get_extra_pop();
                if self.model.is_none() || expop != ProtoModel::EXTRAPOP_UNKNOWN {
                    self.extrapop = expop;
                }
                if model.has_this_pointer() {
                    self.flags |= FuncProto::HAS_THISPTR;
                }
                if model.is_constructor() {
                    self.flags |= FuncProto::IS_CONSTRUCTOR;
                }
                if model.is_auto_killed_by_call() {
                    self.flags |= FuncProto::AUTO_KILLEDBYCALL;
                }
                self.model = Some(model_id);
            }
            None => {
                self.model = None;
                self.extrapop = ProtoModel::EXTRAPOP_UNKNOWN;
            }
        }
    }

    pub fn has_model(&self) -> bool {
        self.model.is_some()
    }

    pub fn has_matching_model(&self, op2: Option<ModelId>) -> bool {
        self.model == op2
    }

    pub fn get_model_name<'a>(&self, glb: &'a Architecture) -> &'a str {
        self.model_ref(glb).get_name()
    }

    pub fn get_model_extra_pop(&self, glb: &Architecture) -> i32 {
        self.model_ref(glb).get_extra_pop()
    }

    pub fn is_model_unknown(&self, glb: &Architecture) -> bool {
        self.model_ref(glb).is_unknown()
    }

    pub fn print_model_in_decl(&self, glb: &Architecture) -> bool {
        self.model_ref(glb).print_in_decl()
    }

    pub fn is_input_locked(&mut self, glb: &Architecture) -> bool {
        if (self.flags & FuncProto::VOIDINPUTLOCK) != 0 {
            return true;
        }
        if self.num_params(glb) == 0 {
            return false;
        }
        self.param_at(0, glb).is_type_locked(glb)
    }

    pub fn is_output_locked(&self, glb: &Architecture) -> bool {
        self.store_ref()
            .get_output_ref()
            .expect("prototype has no output parameter")
            .is_type_locked(glb)
    }

    pub fn is_model_locked(&self) -> bool {
        (self.flags & FuncProto::MODELLOCK) != 0
    }

    pub fn has_custom_storage(&self) -> bool {
        (self.flags & FuncProto::CUSTOM_STORAGE) != 0
    }

    pub fn set_input_lock(&mut self, val: bool, glb: &mut Architecture) {
        if val {
            self.flags |= FuncProto::MODELLOCK;
        }
        let num = self.num_params(glb);
        if num == 0 {
            self.set_flag(FuncProto::VOIDINPUTLOCK, val);
            return;
        }
        for index in 0..num {
            self.param_at(index, glb).set_type_lock(val, glb);
        }
    }

    pub fn set_output_lock(&mut self, val: bool, glb: &mut Architecture) {
        if val {
            self.flags |= FuncProto::MODELLOCK;
        }
        self.output_param().set_type_lock(val, glb);
    }

    pub fn set_model_lock(&mut self, val: bool) {
        self.set_flag(FuncProto::MODELLOCK, val);
    }

    pub fn is_inline(&self) -> bool {
        (self.flags & FuncProto::IS_INLINE) != 0
    }

    pub fn set_inline(&mut self, val: bool) {
        self.set_flag(FuncProto::IS_INLINE, val);
    }

    pub fn get_inject_id(&self) -> i32 {
        self.injectid
    }

    pub fn get_return_bytes_consumed(&self) -> i32 {
        self.return_bytes_consumed
    }

    pub fn set_return_bytes_consumed(&mut self, val: i32) -> bool {
        if val == 0 {
            return false;
        }
        if self.return_bytes_consumed == 0 || val < self.return_bytes_consumed {
            self.return_bytes_consumed = val;
            return true;
        }
        false
    }

    pub fn is_no_return(&self) -> bool {
        (self.flags & FuncProto::NO_RETURN) != 0
    }

    pub fn set_no_return(&mut self, val: bool) {
        self.set_flag(FuncProto::NO_RETURN, val);
    }

    pub fn has_this_pointer(&self) -> bool {
        (self.flags & FuncProto::HAS_THISPTR) != 0
    }

    pub fn is_constructor(&self) -> bool {
        (self.flags & FuncProto::IS_CONSTRUCTOR) != 0
    }

    pub fn set_constructor(&mut self, val: bool) {
        self.set_flag(FuncProto::IS_CONSTRUCTOR, val);
    }

    pub fn is_destructor(&self) -> bool {
        (self.flags & FuncProto::IS_DESTRUCTOR) != 0
    }

    pub fn set_destructor(&mut self, val: bool) {
        self.set_flag(FuncProto::IS_DESTRUCTOR, val);
    }

    pub fn has_input_errors(&self) -> bool {
        (self.flags & FuncProto::ERROR_INPUTPARAM) != 0
    }

    pub fn has_output_errors(&self) -> bool {
        (self.flags & FuncProto::ERROR_OUTPUTPARAM) != 0
    }

    pub fn set_input_errors(&mut self, val: bool) {
        self.set_flag(FuncProto::ERROR_INPUTPARAM, val);
    }

    pub fn set_output_errors(&mut self, val: bool) {
        self.set_flag(FuncProto::ERROR_OUTPUTPARAM, val);
    }

    pub fn get_extra_pop(&self) -> i32 {
        self.extrapop
    }

    pub fn set_extra_pop(&mut self, ep: i32) {
        self.extrapop = ep;
    }

    pub fn get_inject_upon_entry(&self, glb: &Architecture) -> i32 {
        self.model_ref(glb).get_inject_upon_entry()
    }

    pub fn get_inject_upon_return(&self, glb: &Architecture) -> i32 {
        self.model_ref(glb).get_inject_upon_return()
    }

    pub fn resolve_extra_pop(&mut self, glb: &Architecture) {
        if !self.is_input_locked(glb) {
            return;
        }
        let numparams = self.num_params(glb);
        if self.is_dotdotdot() {
            if numparams != 0 {
                self.set_extra_pop(4);
            }
            return;
        }
        let mut expop = 4;
        for index in 0..numparams {
            let param = self.param_at(index, glb);
            let addr = param.get_address(glb);
            if addr.get_space().expect("parameter has no address space").get_type() != SpaceType::Spacebase {
                continue;
            }
            let mut cur = (addr.get_offset() as i32).wrapping_add(param.get_size(glb));
            cur = cur.wrapping_add(3) & 0xffffffc;
            if cur > expop {
                expop = cur;
            }
        }
        self.set_extra_pop(expop);
    }

    pub fn clear_unlocked_input(&mut self, glb: &mut Architecture) {
        if self.is_input_locked(glb) {
            return;
        }
        self.store_mut().clear_all_inputs(glb);
    }

    pub fn clear_unlocked_output(&mut self, glb: &mut Architecture) -> Result<()> {
        let has_model = self.model.is_some();
        let outparam = self.output_param();
        if outparam.is_type_locked(glb) {
            if outparam.is_size_type_locked(glb) && has_model {
                outparam.reset_size_lock_type(glb)?;
            }
        } else {
            self.store_mut().clear_output(glb)?;
        }
        self.return_bytes_consumed = 0;
        Ok(())
    }

    pub fn clear_input(&mut self, glb: &mut Architecture) {
        self.store_mut().clear_all_inputs(glb);
        self.flags &= !FuncProto::VOIDINPUTLOCK;
    }

    pub fn set_inject_id(&mut self, id: i32) {
        if id < 0 {
            self.cancel_inject_id();
        } else {
            self.injectid = id;
            self.flags |= FuncProto::IS_INLINE;
        }
    }

    pub fn cancel_inject_id(&mut self) {
        self.injectid = -1;
        self.flags &= !FuncProto::IS_INLINE;
    }

    pub fn resolve_model(&mut self, active: &mut ParamActive, glb: &Architecture) -> Result<()> {
        let Some(model) = self.model else {
            return Ok(());
        };
        let merged = &glb.proto_models[model];
        if !merged.is_merged() {
            return Ok(());
        }
        let newmodel = merged.select_model(active, &glb.proto_models, &glb.manager)?;
        self.set_model(Some(newmodel), glb);
        Ok(())
    }

    pub fn derive_input_map(&self, active: &mut ParamActive, glb: &Architecture) -> Result<()> {
        self.model_ref(glb).derive_input_map(active, &glb.manager)
    }

    pub fn derive_output_map(&self, active: &mut ParamActive, glb: &Architecture) -> Result<()> {
        self.model_ref(glb).derive_output_map(active, &glb.manager)
    }

    pub fn check_input_join(
        &self,
        hiaddr: &Address,
        hisz: i32,
        loaddr: &Address,
        losz: i32,
        glb: &Architecture,
    ) -> bool {
        self.model_ref(glb).check_input_join(hiaddr, hisz, loaddr, losz)
    }

    pub fn check_input_split(&self, loc: &Address, size: i32, splitpoint: i32, glb: &Architecture) -> bool {
        self.model_ref(glb).check_input_split(loc, size, splitpoint)
    }

    pub fn update_input_types(
        &mut self,
        _data: &mut Funcdata,
        type_list: &[TypeId],
        activeinput: &mut ParamActive,
        glb: &mut Architecture,
    ) -> Result<()> {
        self.store_mut().clear_all_inputs(glb);
        let mut count = 0;
        let numtrials = activeinput.get_num_trials();
        for index in 0..numtrials {
            let trial = activeinput.get_trial(index);
            if trial.is_used() {
                let pieces = ParameterPieces {
                    addr: trial.get_address().clone(),
                    tp: Some(type_list[(trial.get_slot() - 1) as usize]),
                    flags: 0,
                };
                self.store_mut().set_input(count, "", &pieces, glb)?;
                count += 1;
            }
        }
        self.update_this_pointer(glb)
    }

    pub fn update_output_types(
        &mut self,
        triallist: &[VarnodeId],
        data: &mut Funcdata,
        glb: &mut Architecture,
    ) -> Result<()> {
        let (type_locked, size_type_locked) = {
            let outparm = self.output_param();
            (outparm.is_type_locked(glb), outparm.is_size_type_locked(glb))
        };
        if !type_locked {
            if triallist.is_empty() {
                self.store_mut().clear_output(glb)?;
                return Ok(());
            }
        } else if size_type_locked {
            if triallist.is_empty() {
                return Ok(());
            }
            let vn_addr = data.vn(triallist[0]).get_addr().clone();
            let vn_size = data.vn(triallist[0]).get_size();
            let outparm = self.output_param();
            if vn_addr == outparm.get_address(glb) && vn_size == outparm.get_size(glb) {
                let high = data.vn(triallist[0]).get_high()?;
                let tp = data.high_get_type(high, glb);
                self.output_param().override_size_lock_type(tp, glb)?;
            }
            return Ok(());
        } else {
            return Ok(());
        }

        if triallist.is_empty() {
            return Ok(());
        }
        let high = data.vn(triallist[0]).get_high()?;
        let pieces = ParameterPieces {
            addr: data.vn(triallist[0]).get_addr().clone(),
            tp: Some(data.high_get_type(high, glb)),
            flags: 0,
        };
        self.store_mut().set_output(&pieces, glb)?;
        Ok(())
    }

    pub fn update_output_no_types(
        &mut self,
        triallist: &[VarnodeId],
        data: &Funcdata,
        glb: &mut Architecture,
    ) -> Result<()> {
        if self.is_output_locked(glb) {
            return Ok(());
        }
        if triallist.is_empty() {
            self.store_mut().clear_output(glb)?;
            return Ok(());
        }
        let vn = data.vn(triallist[0]);
        let pieces = ParameterPieces {
            tp: Some(types_mut(glb).get_base(vn.get_size(), TypeMetatype::Unknown)?),
            addr: vn.get_addr().clone(),
            flags: 0,
        };
        self.store_mut().set_output(&pieces, glb)?;
        Ok(())
    }

    pub fn update_all_types(&mut self, proto: &PrototypePieces, glb: &mut Architecture) -> Result<()> {
        let model = self.model;
        self.set_model(model, glb);
        self.store_mut().clear_all_inputs(glb);
        self.store_mut().clear_output(glb)?;
        self.flags &= !FuncProto::VOIDINPUTLOCK;
        self.set_dotdotdot(proto.first_var_arg_slot >= 0);

        let mut pieces: Vec<ParameterPieces> = Vec::new();
        let model = self.model.expect("prototype has no model");
        match assign_storage_glb(model, proto, &mut pieces, false, glb) {
            Ok(()) => {
                let store = self.store_mut();
                store.set_output(&pieces[0], glb)?;
                let mut name_index = 0usize;
                for index in 1..pieces.len() {
                    if (pieces[index].flags & ParameterPieces::HIDDENRETPARM) != 0 {
                        store.set_input((index - 1) as i32, "rethidden", &pieces[index], glb)?;
                        continue;
                    }
                    let name = if name_index >= proto.innames.len() {
                        String::new()
                    } else {
                        proto.innames[name_index].clone()
                    };
                    store.set_input((index - 1) as i32, &name, &pieces[index], glb)?;
                    name_index += 1;
                }
            }
            Err(Error::ParamUnassigned(_)) => {
                self.flags |= FuncProto::ERROR_INPUTPARAM;
            }
            Err(err) => return Err(err),
        }
        self.update_this_pointer(glb)
    }

    pub fn get_param(&mut self, index: i32, glb: &Architecture) -> Option<&mut ProtoParameter> {
        self.store_mut().get_input(index, glb)
    }

    pub fn set_param(&mut self, index: i32, name: &str, piece: &ParameterPieces, glb: &mut Architecture) -> Result<()> {
        self.store_mut().set_input(index, name, piece, glb)?;
        Ok(())
    }

    pub fn remove_param(&mut self, index: i32, glb: &mut Architecture) {
        self.store_mut().clear_input(index, glb);
    }

    pub fn num_params(&self, glb: &Architecture) -> i32 {
        self.store_ref().get_num_inputs(glb)
    }

    pub fn get_output(&mut self) -> Option<&mut ProtoParameter> {
        self.store_mut().get_output()
    }

    pub fn get_output_ref(&self) -> Option<&ProtoParameter> {
        self.store_ref().get_output_ref()
    }

    pub fn set_output(&mut self, piece: &ParameterPieces, glb: &mut Architecture) -> Result<()> {
        self.store_mut().set_output(piece, glb)?;
        Ok(())
    }

    pub fn get_output_type(&self, glb: &Architecture) -> TypeId {
        self.store_ref()
            .get_output_ref()
            .expect("prototype has no output parameter")
            .get_type(glb)
    }

    pub fn get_local_range<'a>(&self, glb: &'a Architecture) -> &'a RangeList {
        self.model_ref(glb).get_local_range()
    }

    pub fn get_param_range<'a>(&self, glb: &'a Architecture) -> &'a RangeList {
        self.model_ref(glb).get_param_range()
    }

    pub fn is_stack_grows_negative(&self, glb: &Architecture) -> bool {
        self.model_ref(glb).is_stack_grows_negative()
    }

    pub fn is_dotdotdot(&self) -> bool {
        (self.flags & FuncProto::DOTDOTDOT) != 0
    }

    pub fn set_dotdotdot(&mut self, val: bool) {
        self.set_flag(FuncProto::DOTDOTDOT, val);
    }

    pub fn is_override(&self) -> bool {
        (self.flags & FuncProto::IS_OVERRIDE) != 0
    }

    pub fn set_override(&mut self, val: bool) {
        self.set_flag(FuncProto::IS_OVERRIDE, val);
    }

    pub fn has_effect(&self, addr: &Address, size: i32, glb: &Architecture) -> u32 {
        if self.effectlist.is_empty() {
            return self.model_ref(glb).has_effect(addr, size);
        }
        ProtoModel::lookup_effect(&self.effectlist, addr, size)
    }

    pub fn get_effects<'a>(&'a self, glb: &'a Architecture) -> &'a [EffectRecord] {
        if self.effectlist.is_empty() {
            return self.model_ref(glb).get_effects();
        }
        &self.effectlist
    }

    pub fn get_trash<'a>(&'a self, glb: &'a Architecture) -> &'a [VarnodeData] {
        if self.likelytrash.is_empty() {
            return self.model_ref(glb).get_trash();
        }
        &self.likelytrash
    }

    pub fn get_internal_storage<'a>(&self, glb: &'a Architecture) -> &'a [VarnodeData] {
        self.model_ref(glb).get_internal_storage()
    }

    pub fn characterize_as_input_param(&mut self, addr: &Address, size: i32, glb: &Architecture) -> i32 {
        if !self.is_dotdotdot() {
            if (self.flags & FuncProto::VOIDINPUTLOCK) != 0 {
                return 0;
            }
            let num = self.num_params(glb);
            if num > 0 {
                let mut locktest = false;
                let mut res_contains = false;
                let mut res_contained_by = false;
                for index in 0..num {
                    let param = self.param_at(index, glb);
                    if !param.is_type_locked(glb) {
                        continue;
                    }
                    locktest = true;
                    let iaddr = param.get_address(glb);
                    let param_size = param.get_size(glb);
                    let off = iaddr.justified_contain(param_size, addr, size, false);
                    if off == 0 {
                        return ParamEntry::CONTAINS_JUSTIFIED;
                    } else if off > 0 {
                        res_contains = true;
                    }
                    if iaddr.contained_by(param_size, addr, size) {
                        res_contained_by = true;
                    }
                }
                if locktest {
                    if res_contains {
                        return ParamEntry::CONTAINS_UNJUSTIFIED;
                    }
                    if res_contained_by {
                        return ParamEntry::CONTAINED_BY;
                    }
                    return ParamEntry::NO_CONTAINMENT;
                }
            }
        }
        self.model_ref(glb).characterize_as_input_param(addr, size)
    }

    pub fn characterize_as_output(&mut self, addr: &Address, size: i32, glb: &Architecture) -> i32 {
        if self.is_output_locked(glb) {
            let outparam = self.output_param();
            if types_ref(glb).get(outparam.get_type(glb)).get_metatype() == TypeMetatype::Void {
                return ParamEntry::NO_CONTAINMENT;
            }
            let iaddr = outparam.get_address(glb);
            let out_size = outparam.get_size(glb);
            let off = iaddr.justified_contain(out_size, addr, size, false);
            if off == 0 {
                return ParamEntry::CONTAINS_JUSTIFIED;
            } else if off > 0 {
                return ParamEntry::CONTAINS_UNJUSTIFIED;
            }
            if iaddr.contained_by(out_size, addr, size) {
                return ParamEntry::CONTAINED_BY;
            }
            return ParamEntry::NO_CONTAINMENT;
        }
        self.model_ref(glb).characterize_as_output(addr, size)
    }

    pub fn possible_input_param(&mut self, addr: &Address, size: i32, glb: &Architecture) -> bool {
        if !self.is_dotdotdot() {
            if (self.flags & FuncProto::VOIDINPUTLOCK) != 0 {
                return false;
            }
            let num = self.num_params(glb);
            if num > 0 {
                let mut locktest = false;
                for index in 0..num {
                    let param = self.param_at(index, glb);
                    if !param.is_type_locked(glb) {
                        continue;
                    }
                    locktest = true;
                    let iaddr = param.get_address(glb);
                    if iaddr.justified_contain(param.get_size(glb), addr, size, false) == 0 {
                        return true;
                    }
                }
                if locktest {
                    return false;
                }
            }
        }
        self.model_ref(glb).possible_input_param(addr, size)
    }

    pub fn possible_output_param(&mut self, addr: &Address, size: i32, glb: &Architecture) -> bool {
        if self.is_output_locked(glb) {
            let outparam = self.output_param();
            if types_ref(glb).get(outparam.get_type(glb)).get_metatype() == TypeMetatype::Void {
                return false;
            }
            let iaddr = outparam.get_address(glb);
            return iaddr.justified_contain(outparam.get_size(glb), addr, size, false) == 0;
        }
        self.model_ref(glb).possible_output_param(addr, size)
    }

    pub fn get_max_input_delay(&self, glb: &Architecture) -> i32 {
        self.model_ref(glb).get_max_input_delay()
    }

    pub fn get_max_output_delay(&self, glb: &Architecture) -> i32 {
        self.model_ref(glb).get_max_output_delay()
    }

    pub fn unjustified_input_param(
        &mut self,
        addr: &Address,
        size: i32,
        res: &mut VarnodeData,
        glb: &Architecture,
    ) -> bool {
        if !self.is_dotdotdot() {
            if (self.flags & FuncProto::VOIDINPUTLOCK) != 0 {
                return false;
            }
            let num = self.num_params(glb);
            if num > 0 {
                let mut locktest = false;
                for index in 0..num {
                    let param = self.param_at(index, glb);
                    if !param.is_type_locked(glb) {
                        continue;
                    }
                    locktest = true;
                    let iaddr = param.get_address(glb);
                    let param_size = param.get_size(glb);
                    let just = iaddr.justified_contain(param_size, addr, size, false);
                    if just == 0 {
                        return false;
                    }
                    if just > 0 {
                        res.space = iaddr.get_space().cloned();
                        res.offset = iaddr.get_offset();
                        res.size = param_size as u32;
                        return true;
                    }
                }
                if locktest {
                    return false;
                }
            }
        }
        self.model_ref(glb).unjustified_input_param(addr, size, res)
    }

    pub fn assumed_input_extension(
        &self,
        addr: &Address,
        size: i32,
        res: &mut VarnodeData,
        glb: &Architecture,
    ) -> OpCode {
        self.model_ref(glb).assumed_input_extension(addr, size, res)
    }

    pub fn assumed_output_extension(
        &self,
        addr: &Address,
        size: i32,
        res: &mut VarnodeData,
        glb: &Architecture,
    ) -> OpCode {
        self.model_ref(glb).assumed_output_extension(addr, size, res)
    }

    pub fn get_biggest_contained_input_param(
        &mut self,
        loc: &Address,
        size: i32,
        res: &mut VarnodeData,
        glb: &Architecture,
    ) -> bool {
        if !self.is_dotdotdot() {
            if (self.flags & FuncProto::VOIDINPUTLOCK) != 0 {
                return false;
            }
            let num = self.num_params(glb);
            if num > 0 {
                let mut locktest = false;
                res.size = 0;
                for index in 0..num {
                    let param = self.param_at(index, glb);
                    if !param.is_type_locked(glb) {
                        continue;
                    }
                    locktest = true;
                    let iaddr = param.get_address(glb);
                    let param_size = param.get_size(glb);
                    if iaddr.contained_by(param_size, loc, size) && param_size as u32 > res.size {
                        res.space = iaddr.get_space().cloned();
                        res.offset = iaddr.get_offset();
                        res.size = param_size as u32;
                    }
                }
                if locktest {
                    return res.size == 0;
                }
            }
        }
        self.model_ref(glb).get_biggest_contained_input_param(loc, size, res)
    }

    pub fn get_biggest_contained_output(
        &mut self,
        loc: &Address,
        size: i32,
        res: &mut VarnodeData,
        glb: &Architecture,
    ) -> bool {
        if self.is_output_locked(glb) {
            let outparam = self.output_param();
            if types_ref(glb).get(outparam.get_type(glb)).get_metatype() == TypeMetatype::Void {
                return false;
            }
            let iaddr = outparam.get_address(glb);
            let out_size = outparam.get_size(glb);
            if iaddr.contained_by(out_size, loc, size) {
                res.space = iaddr.get_space().cloned();
                res.offset = iaddr.get_offset();
                res.size = out_size as u32;
                return true;
            }
            return false;
        }
        self.model_ref(glb).get_biggest_contained_output(loc, size, res)
    }

    pub fn get_this_pointer_storage(&mut self, dt: TypeId, glb: &mut Architecture) -> Result<Address> {
        let model = self.model.expect("prototype has no model");
        if !glb.proto_models[model].has_this_pointer() {
            return Ok(Address::invalid());
        }
        let proto = PrototypePieces {
            model: Some(model),
            first_var_arg_slot: -1,
            outtype: Some(self.get_output_type(glb)),
            intypes: vec![dt],
            ..PrototypePieces::default()
        };
        let mut res: Vec<ParameterPieces> = Vec::new();
        assign_storage_glb(model, &proto, &mut res, true, glb)?;
        for piece in res.iter().skip(1) {
            if (piece.flags & ParameterPieces::HIDDENRETPARM) != 0 {
                continue;
            }
            return Ok(piece.addr.clone());
        }
        Ok(Address::invalid())
    }

    pub fn is_compatible(&mut self, op2: &mut FuncProto, glb: &Architecture) -> bool {
        let this_model = self.model_ref(glb);
        let compatible = match op2.model {
            Some(other) => this_model.is_compatible(&glb.proto_models[other]),
            None => this_model.get_alias_parent().is_none(),
        };
        if !compatible {
            return false;
        }
        if op2.is_output_locked(glb) && self.is_output_locked(glb) {
            let out1 = self
                .store_ref()
                .get_output_ref()
                .expect("prototype has no output parameter");
            let out2 = op2
                .store_ref()
                .get_output_ref()
                .expect("prototype has no output parameter");
            if out1.not_equals(out2, glb) {
                return false;
            }
        }
        if self.extrapop != ProtoModel::EXTRAPOP_UNKNOWN && self.extrapop != op2.extrapop {
            return false;
        }
        if self.is_dotdotdot() != op2.is_dotdotdot() {
            if op2.is_dotdotdot() {
                if self.is_input_locked(glb) {
                    return false;
                }
            } else {
                return false;
            }
        }
        if self.injectid != op2.injectid {
            return false;
        }
        if (self.flags & (FuncProto::IS_INLINE | FuncProto::NO_RETURN))
            != (op2.flags & (FuncProto::IS_INLINE | FuncProto::NO_RETURN))
        {
            return false;
        }
        if self.effectlist.len() != op2.effectlist.len() {
            return false;
        }
        for index in 0..self.effectlist.len() {
            if self.effectlist[index] != op2.effectlist[index] {
                return false;
            }
        }
        if self.likelytrash.len() != op2.likelytrash.len() {
            return false;
        }
        for index in 0..self.likelytrash.len() {
            if self.likelytrash[index] != op2.likelytrash[index] {
                return false;
            }
        }
        true
    }

    pub fn get_spacebase<'a>(&self, glb: &'a Architecture) -> Option<&'a SpaceRef> {
        self.model_ref(glb).get_spacebase()
    }

    pub fn print_raw(&mut self, funcname: &str, out: &mut String, glb: &Architecture) {
        match self.model {
            Some(model) => {
                out.push_str(glb.proto_models[model].get_name());
                out.push(' ');
            }
            None => out.push_str("(no model) "),
        }
        let types = types_ref(glb);
        types.get(self.get_output_type(glb)).print_raw(out, types);
        out.push(' ');
        out.push_str(funcname);
        out.push('(');
        let num = self.num_params(glb);
        for index in 0..num {
            if index != 0 {
                out.push(',');
            }
            let tp = self.param_at(index, glb).get_type(glb);
            types.get(tp).print_raw(out, types);
        }
        if self.is_dotdotdot() {
            if num != 0 {
                out.push(',');
            }
            out.push_str("...");
        }
        out.push_str(&format!(") extrapop={}", self.extrapop));
    }

    pub fn get_comparable_flags(&self) -> u32 {
        self.flags
            & (FuncProto::DOTDOTDOT | FuncProto::IS_CONSTRUCTOR | FuncProto::IS_DESTRUCTOR | FuncProto::HAS_THISPTR)
    }

    pub fn is_auto_killed_by_call(&self, glb: &Architecture) -> bool {
        if (self.flags & FuncProto::AUTO_KILLEDBYCALL) != 0 {
            return true;
        }
        self.is_output_locked(glb)
    }

    pub fn encode(&self, encoder: &mut dyn Encoder, glb: &Architecture) -> Result<()> {
        encoder.open_element(ELEM_PROTOTYPE);
        encoder.write_string(ATTRIB_MODEL, self.model_ref(glb).get_name());
        if self.extrapop == ProtoModel::EXTRAPOP_UNKNOWN {
            encoder.write_string(ATTRIB_EXTRAPOP, "unknown");
        } else {
            encoder.write_signed_integer(ATTRIB_EXTRAPOP, self.extrapop as i64);
        }
        if self.is_dotdotdot() {
            encoder.write_bool(ATTRIB_DOTDOTDOT, true);
        }
        if self.is_model_locked() {
            encoder.write_bool(ATTRIB_MODELLOCK, true);
        }
        if (self.flags & FuncProto::VOIDINPUTLOCK) != 0 {
            encoder.write_bool(ATTRIB_VOIDLOCK, true);
        }
        if self.is_inline() {
            encoder.write_bool(ATTRIB_INLINE, true);
        }
        if self.is_no_return() {
            encoder.write_bool(ATTRIB_NORETURN, true);
        }
        if self.has_custom_storage() {
            encoder.write_bool(ATTRIB_CUSTOM, true);
        }
        if self.is_constructor() {
            encoder.write_bool(ATTRIB_CONSTRUCTOR, true);
        }
        if self.is_destructor() {
            encoder.write_bool(ATTRIB_DESTRUCTOR, true);
        }
        let outparam = self
            .store_ref()
            .get_output_ref()
            .expect("prototype has no output parameter");
        encoder.open_element(ELEM_RETURNSYM);
        if outparam.is_type_locked(glb) {
            encoder.write_bool(ATTRIB_TYPELOCK, true);
        }
        outparam.get_address(glb).encode_size(encoder, outparam.get_size(glb))?;
        let types = types_ref(glb);
        types.get(outparam.get_type(glb)).encode_ref(encoder, glb)?;
        encoder.close_element(ELEM_RETURNSYM);
        self.encode_effect(encoder, glb)?;
        self.encode_likely_trash(encoder, glb)?;
        if self.injectid >= 0 {
            encoder.open_element(ELEM_INJECT);
            let name = glb
                .pcodeinjectlib
                .as_deref()
                .expect("architecture has no p-code inject library")
                .get_call_fixup_name(self.injectid);
            encoder.write_string(ATTRIB_CONTENT, &name);
            encoder.close_element(ELEM_INJECT);
        }
        self.store_ref().encode(encoder, glb)?;
        encoder.close_element(ELEM_PROTOTYPE);
        Ok(())
    }

    pub fn decode(&mut self, decoder: &mut dyn Decoder, glb: &mut Architecture) -> Result<()> {
        if self.store.is_none() {
            return Err(Error::Lowlevel(
                "Prototype storage must be set before restoring FuncProto".to_string(),
            ));
        }
        let mut model: Option<ModelId> = None;
        let mut seenextrapop = false;
        let mut readextrapop = 0;
        self.flags = 0;
        self.injectid = -1;
        let elem_id = decoder.open_element_expect(ELEM_PROTOTYPE)?;
        loop {
            let attrib_id = decoder.get_next_attribute_id()?;
            if attrib_id == 0 {
                break;
            }
            if attrib_id == ATTRIB_MODEL {
                let modelname = decoder.read_string()?;
                if modelname.is_empty() || modelname == "default" {
                    model = glb.defaultfp;
                } else {
                    model = glb.get_model(&modelname);
                    if model.is_none() {
                        model = Some(glb.create_unknown_model(&modelname)?);
                    }
                }
            } else if attrib_id == ATTRIB_EXTRAPOP {
                seenextrapop = true;
                readextrapop =
                    decoder.read_signed_integer_expect_string("unknown", ProtoModel::EXTRAPOP_UNKNOWN as i64)? as i32;
            } else if attrib_id == ATTRIB_MODELLOCK {
                if decoder.read_bool()? {
                    self.flags |= FuncProto::MODELLOCK;
                }
            } else if attrib_id == ATTRIB_DOTDOTDOT {
                if decoder.read_bool()? {
                    self.flags |= FuncProto::DOTDOTDOT;
                }
            } else if attrib_id == ATTRIB_VOIDLOCK {
                if decoder.read_bool()? {
                    self.flags |= FuncProto::VOIDINPUTLOCK;
                }
            } else if attrib_id == ATTRIB_INLINE {
                if decoder.read_bool()? {
                    self.flags |= FuncProto::IS_INLINE;
                }
            } else if attrib_id == ATTRIB_NORETURN {
                if decoder.read_bool()? {
                    self.flags |= FuncProto::NO_RETURN;
                }
            } else if attrib_id == ATTRIB_CUSTOM {
                if decoder.read_bool()? {
                    self.flags |= FuncProto::CUSTOM_STORAGE;
                }
            } else if attrib_id == ATTRIB_CONSTRUCTOR {
                if decoder.read_bool()? {
                    self.flags |= FuncProto::IS_CONSTRUCTOR;
                }
            } else if attrib_id == ATTRIB_DESTRUCTOR && decoder.read_bool()? {
                self.flags |= FuncProto::IS_DESTRUCTOR;
            }
        }
        if model.is_some() {
            self.set_model(model, glb);
        }
        if seenextrapop {
            self.extrapop = readextrapop;
        }

        let sub_id = decoder.peek_element()?;
        if sub_id != 0 {
            let mut outpieces = ParameterPieces::default();
            let mut outputlock = false;
            if sub_id == ELEM_RETURNSYM {
                decoder.open_element()?;
                loop {
                    let attrib_id = decoder.get_next_attribute_id()?;
                    if attrib_id == 0 {
                        break;
                    }
                    if attrib_id == ATTRIB_TYPELOCK {
                        outputlock = decoder.read_bool()?;
                    }
                }
                let (addr, _size) = Address::decode_size(decoder)?;
                outpieces.addr = addr;
                outpieces.tp = Some(TypeFactory::decode_type(glb, decoder)?);
                outpieces.flags = 0;
                decoder.close_element(sub_id)?;
            } else if sub_id == ELEM_ADDR {
                let (addr, _size) = Address::decode_size(decoder)?;
                outpieces.addr = addr;
                outpieces.tp = Some(TypeFactory::decode_type(glb, decoder)?);
                outpieces.flags = 0;
            } else {
                return Err(Error::Lowlevel("Missing <returnsym> tag".to_string()));
            }
            self.store_mut().set_output(&outpieces, glb)?;
            self.output_param().set_type_lock(outputlock, glb);
        } else {
            return Err(Error::Lowlevel("Missing <returnsym> tag".to_string()));
        }

        if (self.flags & FuncProto::VOIDINPUTLOCK) != 0 || self.is_output_locked(glb) {
            self.flags |= FuncProto::MODELLOCK;
        }

        loop {
            let sub_id = decoder.peek_element()?;
            if sub_id == 0 {
                break;
            }
            if sub_id == ELEM_UNAFFECTED {
                ProtoModel::decode_effect_group(&mut self.effectlist, EffectRecord::UNAFFECTED, sub_id, decoder)?;
            } else if sub_id == ELEM_KILLEDBYCALL {
                ProtoModel::decode_effect_group(&mut self.effectlist, EffectRecord::KILLEDBYCALL, sub_id, decoder)?;
            } else if sub_id == ELEM_RETURNADDRESS {
                ProtoModel::decode_effect_group(&mut self.effectlist, EffectRecord::RETURN_ADDRESS, sub_id, decoder)?;
            } else if sub_id == ELEM_LIKELYTRASH {
                ProtoModel::decode_varnode_group(&mut self.likelytrash, sub_id, decoder)?;
            } else if sub_id == ELEM_INJECT {
                decoder.open_element()?;
                let inject_string = decoder.read_string_attr(ATTRIB_CONTENT)?;
                self.injectid = glb
                    .pcodeinjectlib
                    .as_deref()
                    .expect("architecture has no p-code inject library")
                    .get_payload_id(CALLFIXUP_TYPE, &inject_string);
                self.flags |= FuncProto::IS_INLINE;
                decoder.close_element(sub_id)?;
            } else if sub_id == ELEM_INTERNALLIST {
                let model = self.model;
                let mut store = self.store.take().expect("prototype has no parameter store");
                let decoded = store.decode(decoder, model, glb);
                self.store = Some(store);
                decoded?;
            }
        }
        decoder.close_element(elem_id)?;
        self.decode_effect(glb)?;
        self.decode_likely_trash(glb);
        if !self.is_model_locked() && self.is_input_locked(glb) {
            self.flags |= FuncProto::MODELLOCK;
        }
        if self.extrapop == ProtoModel::EXTRAPOP_UNKNOWN {
            self.resolve_extra_pop(glb);
        }

        let outparam = self.output_param();
        let is_void = types_ref(glb).get(outparam.get_type(glb)).get_metatype() == TypeMetatype::Void;
        if !is_void && outparam.get_address(glb).is_invalid() {
            return Err(Error::Lowlevel(
                "<returnsym> tag must include a valid storage address".to_string(),
            ));
        }
        self.update_this_pointer(glb)
    }
}

pub struct FuncCallSpecs {
    pub proto: FuncProto,
    op: OpId,
    name: String,
    entryaddress: Address,
    fd: Option<SymbolId>,
    effective_extrapop: i32,
    stackoffset: u64,
    stack_placeholder_slot: i32,
    paramshift: i32,
    match_call_count: i32,
    activeinput: ParamActive,
    activeoutput: ParamActive,
    input_consume: Vec<i32>,
    isinputactive: bool,
    isoutputactive: bool,
    isbadjumptable: bool,
    isstackoutputlock: bool,
}

impl Deref for FuncCallSpecs {
    type Target = FuncProto;

    fn deref(&self) -> &FuncProto {
        &self.proto
    }
}

impl DerefMut for FuncCallSpecs {
    fn deref_mut(&mut self) -> &mut FuncProto {
        &mut self.proto
    }
}

fn copy_trial(data: &Funcdata, fc: CallSpecId, index: i32, output: bool) -> ParamTrial {
    let spec = data.call_spec(fc);
    if output {
        spec.activeoutput.get_trial(index).clone()
    } else {
        spec.activeinput.get_trial(index).clone()
    }
}

impl FuncCallSpecs {
    pub const OFFSET_UNKNOWN: u64 = 0xBADBEEF;

    pub fn new(call_op: OpId, data: &Funcdata) -> FuncCallSpecs {
        let mut entryaddress = Address::invalid();
        let op = data.op(call_op);
        if op.code() == OpCode::Call {
            entryaddress = data.vn(op.get_in(0)).get_addr().clone();
            let is_fspec = entryaddress
                .get_space()
                .is_some_and(|spc| spc.get_type() == SpaceType::Fspec);
            if is_fspec {
                let otherfc = FuncCallSpecs::get_fspec_from_const(&entryaddress);
                entryaddress = data
                    .callspecs
                    .try_get(otherfc)
                    .map(|other| other.entryaddress.clone())
                    .unwrap_or_default();
            }
        }
        FuncCallSpecs {
            proto: FuncProto::new(),
            op: call_op,
            name: String::new(),
            entryaddress,
            fd: None,
            effective_extrapop: ProtoModel::EXTRAPOP_UNKNOWN,
            stackoffset: FuncCallSpecs::OFFSET_UNKNOWN,
            stack_placeholder_slot: -1,
            paramshift: 0,
            match_call_count: 0,
            activeinput: ParamActive::new(true),
            activeoutput: ParamActive::new(true),
            input_consume: Vec::new(),
            isinputactive: false,
            isoutputactive: false,
            isbadjumptable: false,
            isstackoutputlock: false,
        }
    }

    pub fn get_spacebase_relative(data: &Funcdata, fc: CallSpecId) -> Option<VarnodeId> {
        let spec = data.call_spec(fc);
        if spec.stack_placeholder_slot < 0 {
            return None;
        }
        let tmpvn = data.op(spec.op).get_in(spec.stack_placeholder_slot);
        let tmp = data.vn(tmpvn);
        if !tmp.is_spacebase_placeholder() {
            return None;
        }
        if !tmp.is_written() {
            return None;
        }
        let loadop = tmp.get_def()?;
        if data.op(loadop).code() != OpCode::Load {
            return None;
        }
        Some(data.op(loadop).get_in(1))
    }

    pub fn build_param(
        data: &mut Funcdata,
        fc: CallSpecId,
        vn: Option<VarnodeId>,
        param_addr: &Address,
        param_size: i32,
        stackref: Option<VarnodeId>,
        glb: &mut Architecture,
    ) -> Result<VarnodeId> {
        let op = data.call_spec(fc).op;
        let Some(vn) = vn else {
            let spc = param_addr
                .get_space()
                .expect("stack parameter has no address space")
                .clone();
            let off = param_addr.get_offset();
            return data.op_stack_load(&spc, off, param_size as u32, op, stackref, false, glb);
        };
        if data.vn(vn).get_size() == param_size {
            return Ok(vn);
        }
        let op_addr = data.op(op).get_addr().clone();
        let newop = data.new_op(2, &op_addr);
        data.op_set_opcode(newop, OpCode::Subpiece, glb);
        let newout = data.new_unique_out(param_size, newop, glb)?;
        let mut vn = vn;
        let vn_ref = data.vn(vn);
        if vn_ref.is_free() && !vn_ref.is_constant() && !vn_ref.has_no_descend() {
            let size = vn_ref.get_size();
            let addr = vn_ref.get_addr().clone();
            vn = data.new_varnode(size, &addr, None, glb)?;
        }
        data.op_set_input(newop, vn, 0)?;
        let zero = data.new_constant(4, 0, glb);
        data.op_set_input(newop, zero, 1)?;
        data.op_insert_before(newop, op);
        Ok(newout)
    }

    pub fn transfer_locked_input_param(
        data: &mut Funcdata,
        fc: CallSpecId,
        param: &ProtoParameter,
        glb: &Architecture,
    ) -> i32 {
        let startaddr = param.get_address(glb);
        let sz = param.get_size(glb);
        let lastaddr = startaddr.add((sz - 1) as i64);
        let activeinput = &mut data.call_spec_mut(fc).activeinput;
        let numtrials = activeinput.get_num_trials();
        for index in 0..numtrials {
            let curtrial = activeinput.get_trial_mut(index);
            if startaddr < *curtrial.get_address() {
                continue;
            }
            let trialend = curtrial.get_address().add((curtrial.get_size() - 1) as i64);
            if trialend < lastaddr {
                continue;
            }
            if curtrial.is_definitely_not_used() {
                return 0;
            }
            curtrial.mark_used();
            return curtrial.get_slot();
        }
        if startaddr
            .get_space()
            .is_some_and(|spc| spc.get_type() == SpaceType::Spacebase)
        {
            return -1;
        }
        0
    }

    pub fn transfer_locked_output_param(
        data: &mut Funcdata,
        fc: CallSpecId,
        param: &ProtoParameter,
        newoutput: &mut Vec<VarnodeId>,
        glb: &Architecture,
    ) {
        let param_addr = param.get_address(glb);
        let param_size = param.get_size(glb);
        let op = data.call_spec(fc).op;
        let overlaps = |vn: &Varnode| {
            param_addr.justified_contain(param_size, vn.get_addr(), vn.get_size(), false) >= 0
                || vn
                    .get_addr()
                    .justified_contain(vn.get_size(), &param_addr, param_size, false)
                    >= 0
        };
        if let Some(vn) = data.op(op).get_out()
            && overlaps(data.vn(vn))
        {
            newoutput.push(vn);
        }
        let mut indop = data.op_previous_op(op);
        while let Some(current) = indop {
            if data.op(current).code() != OpCode::Indirect {
                break;
            }
            if data.op(current).is_indirect_creation() {
                let vn = data.op(current).get_out().expect("indirect creation has no output");
                if overlaps(data.vn(vn)) {
                    newoutput.push(vn);
                }
            }
            indop = data.op_previous_op(current);
        }
    }

    pub fn transfer_locked_input(
        data: &mut Funcdata,
        fc: CallSpecId,
        newinput: &mut Vec<Option<VarnodeId>>,
        source: &mut FuncProto,
        glb: &mut Architecture,
    ) -> Result<bool> {
        let op = data.call_spec(fc).op;
        newinput.push(Some(data.op(op).get_in(0)));
        let numparams = source.num_params(glb);
        let mut stackref: Option<VarnodeId> = None;
        for index in 0..numparams {
            let param = source.get_param(index, glb).expect("missing input parameter").clone();
            let reuse = FuncCallSpecs::transfer_locked_input_param(data, fc, &param, glb);
            if reuse == 0 {
                return Ok(false);
            }
            if reuse > 0 {
                newinput.push(Some(data.op(op).get_in(reuse)));
            } else {
                if stackref.is_none() {
                    stackref = FuncCallSpecs::get_spacebase_relative(data, fc);
                }
                if stackref.is_none() {
                    return Ok(false);
                }
                newinput.push(None);
            }
        }
        Ok(true)
    }

    pub fn transfer_locked_output(
        data: &mut Funcdata,
        fc: CallSpecId,
        newoutput: &mut Vec<VarnodeId>,
        source: &mut FuncProto,
        glb: &mut Architecture,
    ) -> Result<bool> {
        let param = source.get_output().expect("prototype has no output parameter").clone();
        if types_ref(glb).get(param.get_type(glb)).get_metatype() == TypeMetatype::Void {
            return Ok(true);
        }
        FuncCallSpecs::transfer_locked_output_param(data, fc, &param, newoutput, glb);
        Ok(true)
    }

    pub fn collect_unlocked_trials(data: &Funcdata, fc: CallSpecId, unlocked_trials: &mut Vec<ParamTrial>) {
        let spec = data.call_spec(fc);
        if !spec.is_dotdotdot() {
            return;
        }
        let num_input = data.op(spec.op).num_input();
        for index in 0..spec.activeinput.get_num_trials() {
            let trial = spec.activeinput.get_trial(index);
            if trial.is_used() {
                continue;
            }
            let slot = trial.get_slot();
            if slot < 1 || slot >= num_input {
                continue;
            }
            unlocked_trials.push(trial.clone());
        }
    }

    pub fn commit_new_inputs(
        data: &mut Funcdata,
        fc: CallSpecId,
        newinput: &mut Vec<Option<VarnodeId>>,
        glb: &mut Architecture,
    ) -> Result<()> {
        if !data.call_spec_mut(fc).is_input_locked(glb) {
            return Ok(());
        }
        let op = data.call_spec(fc).op;
        let stackref = FuncCallSpecs::get_spacebase_relative(data, fc);
        let mut placeholder: Option<VarnodeId> = None;
        let mut unlocked_trials: Vec<ParamTrial> = Vec::new();
        FuncCallSpecs::collect_unlocked_trials(data, fc, &mut unlocked_trials);
        let placeholder_slot = data.call_spec(fc).stack_placeholder_slot;
        if placeholder_slot >= 0 {
            placeholder = Some(data.op(op).get_in(placeholder_slot));
        }
        let mut noplacehold = true;

        let num_passes = {
            let spec = data.call_spec_mut(fc);
            spec.stack_placeholder_slot = -1;
            let num_passes = spec.activeinput.get_num_passes();
            spec.activeinput.clear();
            num_passes
        };

        let numparams = data.call_spec(fc).num_params(glb);
        for index in 0..numparams {
            let (param_addr, param_size) = {
                let param = data
                    .call_spec_mut(fc)
                    .get_param(index, glb)
                    .expect("missing input parameter");
                (param.get_address(glb), param.get_size(glb))
            };
            let slot = (1 + index) as usize;
            let vn = FuncCallSpecs::build_param(data, fc, newinput[slot], &param_addr, param_size, stackref, glb)?;
            newinput[slot] = Some(vn);
            let activeinput = &mut data.call_spec_mut(fc).activeinput;
            activeinput.register_trial(&param_addr, param_size);
            activeinput.get_trial_mut(index).mark_active();
            let is_spacebase = param_addr
                .get_space()
                .is_some_and(|spc| spc.get_type() == SpaceType::Spacebase);
            if noplacehold && is_spacebase {
                data.vn_mut(vn).set_spacebase_placeholder();
                noplacehold = false;
                placeholder = None;
            }
        }
        for trial in &unlocked_trials {
            let vn = data.op(op).get_in(trial.get_slot());
            newinput.push(Some(vn));
            data.call_spec_mut(fc).activeinput.reregister_trial(trial);
        }
        if let Some(placeholder) = placeholder {
            newinput.push(Some(placeholder));
            let slot = (newinput.len() - 1) as i32;
            data.call_spec_mut(fc).set_stack_placeholder_slot(slot);
        }
        let inputs: Vec<VarnodeId> = newinput
            .iter()
            .map(|vn| vn.expect("missing new input varnode"))
            .collect();
        data.op_set_all_input(op, &inputs)?;
        let spec = data.call_spec_mut(fc);
        if !spec.is_dotdotdot() {
            spec.clear_active_input();
        } else if num_passes > 0 {
            spec.activeinput.finish_pass();
        }
        Ok(())
    }

    pub fn commit_new_outputs(
        data: &mut Funcdata,
        fc: CallSpecId,
        newoutput: &mut [VarnodeId],
        glb: &mut Architecture,
    ) -> Result<()> {
        if !data.call_spec(fc).is_output_locked(glb) {
            return Ok(());
        }
        let op = data.call_spec(fc).op;
        data.call_spec_mut(fc).activeoutput.clear();

        if !newoutput.is_empty() {
            let (param_addr, param_size, param_type) = {
                let param = data
                    .call_spec_mut(fc)
                    .get_output()
                    .expect("prototype has no output parameter");
                (param.get_address(glb), param.get_size(glb), param.get_type(glb))
            };
            data.call_spec_mut(fc)
                .activeoutput
                .register_trial(&param_addr, param_size);
            let param_meta = types_ref(glb).get(param_type).get_metatype();
            if param_size == 1 && param_meta == TypeMetatype::Bool && data.is_type_recovery_on() {
                data.op_mark_calculated_bool(op);
            }
            let mut exact_match: Option<VarnodeId> = None;
            for vn in newoutput.iter() {
                if data.vn(*vn).get_size() == param_size {
                    exact_match = Some(*vn);
                    break;
                }
            }
            let real_out = match exact_match {
                Some(exact) => {
                    let ind_op = data.vn(exact).get_def();
                    if ind_op != Some(op) {
                        data.op_set_output(op, exact, glb)?;
                        data.op_unlink(ind_op.expect("exact output has no defining op"))?;
                    }
                    exact
                }
                None => {
                    data.op_unset_output(op)?;
                    data.new_varnode_out(param_size, &param_addr, op, glb)?
                }
            };
            let op_addr = data.op(op).get_addr().clone();

            for old_out in newoutput.iter().copied() {
                if Some(old_out) == exact_match {
                    continue;
                }
                let mut ind_op = data.vn(old_out).get_def();
                if ind_op == Some(op) {
                    ind_op = None;
                }
                let old_size = data.vn(old_out).get_size();
                let old_addr = data.vn(old_out).get_addr().clone();
                let real_addr = data.vn(real_out).get_addr().clone();
                let real_size = data.vn(real_out).get_size();
                if old_size < param_size {
                    let ind_op = match ind_op {
                        Some(ind_op) => {
                            data.op_uninsert(ind_op);
                            data.op_set_opcode(ind_op, OpCode::Subpiece, glb);
                            ind_op
                        }
                        None => {
                            let ind_op = data.new_op(2, &op_addr);
                            data.op_set_opcode(ind_op, OpCode::Subpiece, glb);
                            data.op_set_output(ind_op, old_out, glb)?;
                            ind_op
                        }
                    };
                    let overlap = data.vn(old_out).overlap_addr(&real_addr, real_size);
                    data.op_set_input(ind_op, real_out, 0)?;
                    let constant = data.new_constant(4, overlap as i64 as u64, glb);
                    data.op_set_input(ind_op, constant, 1)?;
                    data.op_insert_after(ind_op, op);
                } else if param_size < old_size {
                    let overlap = old_addr.justified_contain(old_size, &param_addr, param_size, false);
                    let mut vardata = VarnodeData::default();
                    let mut opc =
                        data.call_spec(fc)
                            .assumed_output_extension(&param_addr, param_size, &mut vardata, glb);
                    if opc != OpCode::Copy && overlap == 0 {
                        if opc == OpCode::Piece {
                            opc = if param_meta == TypeMetatype::Int {
                                OpCode::IntSext
                            } else {
                                OpCode::IntZext
                            };
                        }
                        match ind_op {
                            Some(ind_op) => {
                                data.op_uninsert(ind_op);
                                data.op_remove_input(ind_op, 1);
                                data.op_set_opcode(ind_op, opc, glb);
                                data.op_set_input(ind_op, real_out, 0)?;
                                data.op_insert_after(ind_op, op);
                            }
                            None => {
                                let extop = data.new_op(1, &op_addr);
                                data.op_set_opcode(extop, opc, glb);
                                data.op_set_output(extop, old_out, glb)?;
                                data.op_set_input(extop, real_out, 0)?;
                                data.op_insert_after(extop, op);
                            }
                        }
                    } else {
                        if let Some(ind_op) = ind_op {
                            data.op_unlink(ind_op)?;
                        }
                        let most_sig_size = old_size - overlap - real_size;
                        let mut last_op = op;
                        if overlap != 0 {
                            let mut lo_addr = old_addr.clone();
                            if lo_addr.is_big_endian() {
                                lo_addr = lo_addr.add((old_size - overlap) as i64);
                            }
                            let new_ind_op = data.new_indirect_creation(op, &lo_addr, overlap, true, glb)?;
                            let concat_op = data.new_op(2, &op_addr);
                            data.op_set_opcode(concat_op, OpCode::Piece, glb);
                            data.op_set_input(concat_op, real_out, 0)?;
                            let ind_out = data.op(new_ind_op).get_out().expect("indirect creation has no output");
                            data.op_set_input(concat_op, ind_out, 1)?;
                            data.op_insert_after(concat_op, op);
                            if most_sig_size != 0 {
                                if lo_addr.is_big_endian() {
                                    data.new_varnode_out(overlap + real_size, &real_addr, concat_op, glb)?;
                                } else {
                                    data.new_varnode_out(overlap + real_size, &lo_addr, concat_op, glb)?;
                                }
                            }
                            last_op = concat_op;
                        }
                        if most_sig_size != 0 {
                            let mut hi_addr = old_addr.clone();
                            if !hi_addr.is_big_endian() {
                                hi_addr = hi_addr.add((real_size + overlap) as i64);
                            }
                            let new_ind_op = data.new_indirect_creation(op, &hi_addr, most_sig_size, true, glb)?;
                            let concat_op = data.new_op(2, &op_addr);
                            data.op_set_opcode(concat_op, OpCode::Piece, glb);
                            let ind_out = data.op(new_ind_op).get_out().expect("indirect creation has no output");
                            data.op_set_input(concat_op, ind_out, 0)?;
                            let last_out = data.op(last_op).get_out().expect("previous op has no output");
                            data.op_set_input(concat_op, last_out, 1)?;
                            data.op_insert_after(concat_op, last_op);
                            last_op = concat_op;
                        }
                        data.op_set_output(last_op, old_out, glb)?;
                    }
                }
            }
        }
        data.call_spec_mut(fc).clear_active_output();
        Ok(())
    }

    pub fn collect_output_trial_varnodes(
        data: &mut Funcdata,
        fc: CallSpecId,
        trialvn: &mut Vec<Option<VarnodeId>>,
    ) -> Result<()> {
        let op = data.call_spec(fc).op;
        if data.op(op).get_out().is_some() {
            return Err(Error::Lowlevel("Output of call was determined prematurely".to_string()));
        }
        while (trialvn.len() as i32) < data.call_spec(fc).activeoutput.get_num_trials() {
            trialvn.push(None);
        }
        let mut indop = data.op_previous_op(op);
        while let Some(current) = indop {
            if data.op(current).code() != OpCode::Indirect {
                break;
            }
            if data.op(current).is_indirect_creation() {
                let vn = data.op(current).get_out().expect("indirect creation has no output");
                let addr = data.vn(vn).get_addr().clone();
                let size = data.vn(vn).get_size();
                let activeoutput = &mut data.call_spec_mut(fc).activeoutput;
                let index = activeoutput.which_trial(&addr, size);
                if index >= 0 {
                    trialvn[index as usize] = Some(vn);
                    activeoutput.get_trial_mut(index).set_address(&addr, size);
                }
            }
            indop = data.op_previous_op(current);
        }
        Ok(())
    }

    pub fn set_stack_placeholder_slot(&mut self, slot: i32) {
        self.stack_placeholder_slot = slot;
        if self.isinputactive {
            self.activeinput.set_placeholder_slot();
        }
    }

    pub fn clear_stack_placeholder_slot(&mut self) {
        self.stack_placeholder_slot = -1;
        if self.isinputactive {
            self.activeinput.free_placeholder_slot();
        }
    }

    pub fn set_address(&mut self, addr: &Address) {
        self.entryaddress = addr.clone();
    }

    pub fn get_op(&self) -> OpId {
        self.op
    }

    pub fn get_funcdata(&self) -> Option<SymbolId> {
        self.fd
    }

    pub fn set_funcdata(&mut self, function_symbol: SymbolId, glb: &mut Architecture) -> Result<()> {
        if self.fd.is_some() {
            return Err(Error::Lowlevel("Setting call spec function multiple times".to_string()));
        }
        self.fd = Some(function_symbol);
        let db = symtab_ref(glb);
        let entry = db.symbol_get_first_whole_map(function_symbol)?;
        self.entryaddress = db.entry(entry).get_addr().clone();
        let display_name = db.symbol(function_symbol).get_display_name();
        if !display_name.is_empty() {
            self.name = display_name.to_string();
        }
        Ok(())
    }

    pub fn clone_spec(&self, newop: OpId, data: &Funcdata) -> Result<FuncCallSpecs> {
        let mut res = FuncCallSpecs::new(newop, data);
        if let Some(fd) = self.fd {
            res.fd = Some(fd);
            res.entryaddress = self.entryaddress.clone();
            res.name = self.name.clone();
        }
        res.effective_extrapop = self.effective_extrapop;
        res.stackoffset = self.stackoffset;
        res.paramshift = self.paramshift;
        res.isbadjumptable = self.isbadjumptable;
        res.proto.copy(&self.proto)?;
        Ok(res)
    }

    pub fn get_name(&self) -> &str {
        &self.name
    }

    pub fn get_entry_address(&self) -> &Address {
        &self.entryaddress
    }

    pub fn set_effective_extra_pop(&mut self, epop: i32) {
        self.effective_extrapop = epop;
    }

    pub fn get_effective_extra_pop(&self) -> i32 {
        self.effective_extrapop
    }

    pub fn get_spacebase_offset(&self) -> u64 {
        self.stackoffset
    }

    pub fn set_paramshift(&mut self, val: i32) {
        self.paramshift = val;
    }

    pub fn get_paramshift(&self) -> i32 {
        self.paramshift
    }

    pub fn get_match_call_count(&self) -> i32 {
        self.match_call_count
    }

    pub fn get_stack_placeholder_slot(&self) -> i32 {
        self.stack_placeholder_slot
    }

    pub fn init_active_input(&mut self, glb: &Architecture) {
        self.isinputactive = true;
        let mut maxdelay = self.proto.get_max_input_delay(glb);
        if maxdelay > 0 {
            maxdelay = 3;
        }
        self.activeinput.set_max_pass(maxdelay);
    }

    pub fn clear_active_input(&mut self) {
        self.isinputactive = false;
    }

    pub fn init_active_output(&mut self) {
        self.isoutputactive = true;
    }

    pub fn clear_active_output(&mut self) {
        self.isoutputactive = false;
    }

    pub fn is_input_active(&self) -> bool {
        self.isinputactive
    }

    pub fn is_output_active(&self) -> bool {
        self.isoutputactive
    }

    pub fn set_bad_jump_table(&mut self, val: bool) {
        self.isbadjumptable = val;
    }

    pub fn is_bad_jump_table(&self) -> bool {
        self.isbadjumptable
    }

    pub fn set_stack_output_lock(&mut self, val: bool) {
        self.isstackoutputlock = val;
    }

    pub fn is_stack_output_lock(&self) -> bool {
        self.isstackoutputlock
    }

    pub fn get_active_input(&mut self) -> &mut ParamActive {
        &mut self.activeinput
    }

    pub fn get_active_output(&mut self) -> &mut ParamActive {
        &mut self.activeoutput
    }

    pub fn check_input_join_varnodes(
        data: &Funcdata,
        fc: CallSpecId,
        slot1: i32,
        ishislot: bool,
        vn1: VarnodeId,
        vn2: VarnodeId,
        glb: &Architecture,
    ) -> bool {
        let spec = data.call_spec(fc);
        if spec.is_input_active() {
            return false;
        }
        if slot1 >= spec.activeinput.get_num_trials() {
            return false;
        }
        let vn1_size = data.vn(vn1).get_size();
        let vn2_size = data.vn(vn2).get_size();
        let (hislot, loslot) = if ishislot {
            let hislot = spec.activeinput.get_trial_for_input_varnode(slot1);
            let loslot = spec.activeinput.get_trial_for_input_varnode(slot1 + 1);
            if hislot.get_size() != vn1_size {
                return false;
            }
            if loslot.get_size() != vn2_size {
                return false;
            }
            (hislot, loslot)
        } else {
            let loslot = spec.activeinput.get_trial_for_input_varnode(slot1);
            let hislot = spec.activeinput.get_trial_for_input_varnode(slot1 + 1);
            if loslot.get_size() != vn1_size {
                return false;
            }
            if hislot.get_size() != vn2_size {
                return false;
            }
            (hislot, loslot)
        };
        spec.proto.check_input_join(
            hislot.get_address(),
            hislot.get_size(),
            loslot.get_address(),
            loslot.get_size(),
            glb,
        )
    }

    pub fn do_input_join(
        data: &mut Funcdata,
        fc: CallSpecId,
        slot1: i32,
        ishislot: bool,
        glb: &mut Architecture,
    ) -> Result<()> {
        if data.call_spec_mut(fc).is_input_locked(glb) {
            return Err(Error::Lowlevel(
                "Trying to join parameters on locked function prototype".to_string(),
            ));
        }
        let spec = data.call_spec_mut(fc);
        let (addr1, size1) = {
            let trial1 = spec.activeinput.get_trial_for_input_varnode(slot1);
            (trial1.get_address().clone(), trial1.get_size())
        };
        let (addr2, size2) = {
            let trial2 = spec.activeinput.get_trial_for_input_varnode(slot1 + 1);
            (trial2.get_address().clone(), trial2.get_size())
        };
        let translate = glb.translate.as_deref().expect("architecture has no translator");
        let joinaddr = if ishislot {
            glb.manager
                .construct_join_address(translate, &addr1, size1, &addr2, size2)?
        } else {
            glb.manager
                .construct_join_address(translate, &addr2, size2, &addr1, size1)?
        };
        spec.activeinput.join_trial(slot1, &joinaddr, size1 + size2)
    }

    pub fn late_restriction(
        data: &mut Funcdata,
        fc: CallSpecId,
        restricted_proto: &mut FuncProto,
        newinput: &mut Vec<Option<VarnodeId>>,
        newoutput: &mut Vec<VarnodeId>,
        glb: &mut Architecture,
    ) -> Result<bool> {
        if !data.call_spec(fc).has_model() {
            data.call_spec_mut(fc).proto.copy(restricted_proto)?;
            return Ok(true);
        }
        if !data.call_spec_mut(fc).proto.is_compatible(restricted_proto, glb) {
            return Ok(false);
        }
        if restricted_proto.is_dotdotdot() && !data.call_spec(fc).isinputactive {
            return Ok(false);
        }
        if restricted_proto.is_input_locked(glb)
            && !FuncCallSpecs::transfer_locked_input(data, fc, newinput, restricted_proto, glb)?
        {
            return Ok(false);
        }
        if restricted_proto.is_output_locked(glb)
            && !FuncCallSpecs::transfer_locked_output(data, fc, newoutput, restricted_proto, glb)?
        {
            return Ok(false);
        }
        data.call_spec_mut(fc).proto.copy(restricted_proto)?;
        Ok(true)
    }

    pub fn deindirect(data: &mut Funcdata, fc: CallSpecId, newfd: SymbolId, glb: &mut Architecture) -> Result<()> {
        let mut newproto = FuncProto::new();
        let (entry, display_name) = if data.function_symbol == Some(newfd) {
            newproto.copy(&data.funcp)?;
            (data.get_address().clone(), data.get_display_name().to_string())
        } else {
            let fd = Database::symbol_get_function(glb, newfd)?
                .ok_or_else(|| Error::Lowlevel("function symbol has no function data".to_string()))?;
            newproto.copy(&fd.funcp)?;
            (fd.get_address().clone(), fd.get_display_name().to_string())
        };
        {
            let spec = data.call_spec_mut(fc);
            spec.entryaddress = entry.clone();
            spec.name = display_name;
            spec.fd = Some(newfd);
        }
        let op = data.call_spec(fc).op;
        let vn = data.new_varnode_call_specs(fc, glb);
        data.op_set_input(op, vn, 0)?;
        data.op_set_opcode(op, OpCode::Call, glb);
        let op_addr = data.op(op).get_addr().clone();
        data.get_override().insert_deindirect(&op_addr, &entry);

        let mut newinput: Vec<Option<VarnodeId>> = Vec::new();
        let mut newoutput: Vec<VarnodeId> = Vec::new();
        if !newproto.is_no_return() && !newproto.is_inline() {
            if data.call_spec(fc).is_override() {
                return Ok(());
            }
            if FuncCallSpecs::late_restriction(data, fc, &mut newproto, &mut newinput, &mut newoutput, glb)? {
                FuncCallSpecs::commit_new_inputs(data, fc, &mut newinput, glb)?;
                FuncCallSpecs::commit_new_outputs(data, fc, &mut newoutput, glb)?;
                return Ok(());
            }
        }
        data.set_restart_pending(true);
        Ok(())
    }

    pub fn force_set(data: &mut Funcdata, fc: CallSpecId, fp: &mut FuncProto, glb: &mut Architecture) -> Result<()> {
        let mut newinput: Vec<Option<VarnodeId>> = Vec::new();
        let mut newoutput: Vec<VarnodeId> = Vec::new();
        let mut newproto = FuncProto::new();
        newproto.copy(fp)?;
        let op = data.call_spec(fc).op;
        let op_addr = data.op(op).get_addr().clone();
        data.get_override().insert_proto_override(&op_addr, Box::new(newproto));
        if FuncCallSpecs::late_restriction(data, fc, fp, &mut newinput, &mut newoutput, glb)? {
            FuncCallSpecs::commit_new_inputs(data, fc, &mut newinput, glb)?;
            FuncCallSpecs::commit_new_outputs(data, fc, &mut newoutput, glb)?;
        } else {
            data.set_restart_pending(true);
        }
        let spec = data.call_spec_mut(fc);
        spec.proto.set_input_lock(true, glb);
        spec.proto.set_input_errors(fp.has_input_errors());
        spec.proto.set_output_errors(fp.has_output_errors());
        Ok(())
    }

    pub fn insert_pcode(data: &mut Funcdata, fc: CallSpecId, glb: &mut Architecture) -> Result<()> {
        let id = data.call_spec(fc).get_inject_upon_return(glb);
        if id < 0 {
            return Ok(());
        }
        let op = data.call_spec(fc).op;
        let callop = data.op(op);
        let addr = callop.get_addr().clone();
        let parent = callop.get_parent().expect("call op has no parent block");
        let next = callop.links[PcodeOp::BASIC_LIST].next;
        data.do_live_inject(id, &addr, parent, next, glb)
    }

    pub fn create_placeholder(
        data: &mut Funcdata,
        fc: CallSpecId,
        spacebase: &SpaceRef,
        glb: &mut Architecture,
    ) -> Result<()> {
        let op = data.call_spec(fc).op;
        let slot = data.op(op).num_input();
        let loadval = data.op_stack_load(spacebase, 0, 1, op, None, false, glb)?;
        data.op_insert_input(op, loadval, slot)?;
        data.call_spec_mut(fc).set_stack_placeholder_slot(slot);
        data.vn_mut(loadval).set_spacebase_placeholder();
        Ok(())
    }

    pub fn resolve_spacebase_relative(
        data: &mut Funcdata,
        fc: CallSpecId,
        phvn: VarnodeId,
        glb: &mut Architecture,
    ) -> Result<()> {
        let defop = data.vn(phvn).get_def().expect("placeholder varnode has no defining op");
        let refvn = data.op(defop).get_in(0);
        let spacebase = data
            .vn(refvn)
            .get_space()
            .expect("placeholder reference has no address space")
            .clone();
        if spacebase.get_type() != SpaceType::Spacebase {
            data.warning_header("This function may have set the stack pointer", glb);
        }
        let refoffset = data.vn(refvn).get_offset();
        data.call_spec_mut(fc).stackoffset = refoffset;

        let op = data.call_spec(fc).op;
        let placeholder_slot = data.call_spec(fc).stack_placeholder_slot;
        if placeholder_slot >= 0 && data.op(op).get_in(placeholder_slot) == phvn {
            return FuncCallSpecs::abort_spacebase_relative(data, fc, glb);
        }

        if data.call_spec_mut(fc).is_input_locked(glb) {
            let slot = data.op(op).get_slot(phvn) - 1;
            if slot >= data.call_spec(fc).num_params(glb) {
                return Err(Error::Lowlevel(
                    "Stack placeholder does not line up with locked parameter".to_string(),
                ));
            }
            let addr = data
                .call_spec_mut(fc)
                .get_param(slot, glb)
                .expect("missing input parameter")
                .get_address(glb);
            if !space_eq(addr.get_space(), Some(&spacebase)) && spacebase.get_type() == SpaceType::Spacebase {
                return Err(Error::Lowlevel(
                    "Stack placeholder does not match locked space".to_string(),
                ));
            }
            let spec = data.call_spec_mut(fc);
            spec.stackoffset = spec.stackoffset.wrapping_sub(addr.get_offset());
            spec.stackoffset = spacebase.wrap_offset(spec.stackoffset);
            return Ok(());
        }
        Err(Error::Lowlevel("Unresolved stack placeholder".to_string()))
    }

    pub fn abort_spacebase_relative(data: &mut Funcdata, fc: CallSpecId, _glb: &mut Architecture) -> Result<()> {
        let placeholder_slot = data.call_spec(fc).stack_placeholder_slot;
        if placeholder_slot >= 0 {
            let op = data.call_spec(fc).op;
            let vn = data.op(op).get_in(placeholder_slot);
            data.op_remove_input(op, placeholder_slot);
            data.call_spec_mut(fc).clear_stack_placeholder_slot();
            let vn_ref = data.vn(vn);
            let is_internal = vn_ref
                .get_space()
                .is_some_and(|spc| spc.get_type() == SpaceType::Internal);
            if vn_ref.has_no_descend() && is_internal && vn_ref.is_written() {
                let def = vn_ref.get_def().expect("written varnode has no defining op");
                data.op_destroy(def)?;
            }
        }
        Ok(())
    }

    pub fn final_input_check(data: &mut Funcdata, fc: CallSpecId) {
        let mut ancestor_real = AncestorRealistic::new();
        let op = data.call_spec(fc).op;
        for index in 0..data.call_spec(fc).activeinput.get_num_trials() {
            let mut trial = copy_trial(data, fc, index, false);
            if !trial.is_active() {
                continue;
            }
            if !trial.has_cond_exe_effect() {
                continue;
            }
            let slot = trial.get_slot();
            if !ancestor_real.execute(data, op, slot, &mut trial, false) {
                trial.mark_no_use();
            }
            *data.call_spec_mut(fc).activeinput.get_trial_mut(index) = trial;
        }
    }

    pub fn check_input_trial_use(
        data: &mut Funcdata,
        fc: CallSpecId,
        aliascheck: &mut AliasChecker,
        glb: &mut Architecture,
    ) -> Result<()> {
        let op = data.call_spec(fc).op;
        if data.op(op).is_dead() {
            return Err(Error::Lowlevel("Function call in dead code".to_string()));
        }

        let maxancestor = glb.trim_recurse_max;
        let mut callee_pop = false;
        let mut expop = 0;
        {
            let spec = data.call_spec(fc);
            if spec.has_model() {
                callee_pop = spec.get_model_extra_pop(glb) == ProtoModel::EXTRAPOP_UNKNOWN;
                if callee_pop {
                    expop = spec.get_extra_pop();
                    if expop == ProtoModel::EXTRAPOP_UNKNOWN || expop <= 4 {
                        callee_pop = false;
                    }
                }
            }
        }

        let mut ancestor_real = AncestorRealistic::new();
        for index in 0..data.call_spec(fc).activeinput.get_num_trials() {
            let mut trial = copy_trial(data, fc, index, false);
            if trial.is_checked() {
                continue;
            }
            let slot = trial.get_slot();
            let vn = data.op(op).get_in(slot);
            let is_spacebase = data
                .vn(vn)
                .get_space()
                .is_some_and(|spc| spc.get_type() == SpaceType::Spacebase);
            let mut needs_final_check = false;
            if is_spacebase {
                let vn_addr = data.vn(vn).get_addr().clone();
                if aliascheck.has_local_alias(data, vn) {
                    trial.mark_no_use();
                } else if !data.funcp.get_local_range(glb).in_range(&vn_addr, 1) {
                    trial.mark_no_use();
                } else if callee_pop {
                    if (trial
                        .get_address()
                        .get_offset()
                        .wrapping_add((trial.get_size() - 1) as i64 as u64) as i32)
                        < expop
                    {
                        trial.mark_active();
                    } else {
                        trial.mark_no_use();
                    }
                } else if ancestor_real.execute(data, op, slot, &mut trial, false) {
                    if data.ancestor_op_use(maxancestor, vn, op, &mut trial, 0, 0) {
                        trial.mark_active();
                    } else {
                        trial.mark_inactive();
                    }
                } else {
                    trial.mark_no_use();
                }
            } else if ancestor_real.execute(data, op, slot, &mut trial, true) {
                if data.ancestor_op_use(maxancestor, vn, op, &mut trial, 0, 0) {
                    trial.mark_active();
                    if trial.has_cond_exe_effect() {
                        needs_final_check = true;
                    }
                } else {
                    trial.mark_inactive();
                }
            } else if data.vn(vn).is_input() {
                trial.mark_inactive();
            } else {
                trial.mark_no_use();
            }
            let defnouse = trial.is_definitely_not_used();
            {
                let activeinput = &mut data.call_spec_mut(fc).activeinput;
                *activeinput.get_trial_mut(index) = trial;
                if needs_final_check {
                    activeinput.mark_needs_final_check();
                }
            }
            if defnouse {
                let size = data.vn(vn).get_size();
                let constant = data.new_constant(size, 0, glb);
                data.op_set_input(op, constant, slot)?;
            }
        }
        Ok(())
    }

    pub fn check_output_trial_use(
        data: &mut Funcdata,
        fc: CallSpecId,
        trialvn: &mut Vec<Option<VarnodeId>>,
        _glb: &mut Architecture,
    ) -> Result<()> {
        FuncCallSpecs::collect_output_trial_varnodes(data, fc, trialvn)?;
        let activeoutput = &mut data.call_spec_mut(fc).activeoutput;
        for (index, vn) in trialvn.iter().enumerate() {
            let curtrial = activeoutput.get_trial_mut(index as i32);
            if curtrial.is_checked() {
                return Err(Error::Lowlevel("Output trial has been checked prematurely".to_string()));
            }
            if vn.is_some() {
                curtrial.mark_active();
            } else {
                curtrial.mark_inactive();
            }
        }
        Ok(())
    }

    pub fn build_input_from_trials(data: &mut Funcdata, fc: CallSpecId, glb: &mut Architecture) -> Result<()> {
        let op = data.call_spec(fc).op;
        let mut newparam: Vec<VarnodeId> = vec![data.op(op).get_in(0)];

        if data.call_spec(fc).is_dotdotdot() && data.call_spec_mut(fc).is_input_locked(glb) {
            data.call_spec_mut(fc).activeinput.sort_fixed_position();
        }

        let stackoffset = data.call_spec(fc).stackoffset;
        let op_addr = data.op(op).get_addr().clone();
        let big_endian = glb
            .translate
            .as_deref()
            .expect("architecture has no translator")
            .is_big_endian();
        for index in 0..data.call_spec(fc).activeinput.get_num_trials() {
            let paramtrial = copy_trial(data, fc, index, false);
            if !paramtrial.is_used() {
                continue;
            }
            let sz = paramtrial.get_size();
            let mut isspacebase = false;
            let addr = paramtrial.get_address();
            let spc = addr.get_space().expect("parameter trial has no address space").clone();
            let mut off = addr.get_offset();
            if spc.get_type() == SpaceType::Spacebase {
                isspacebase = true;
                off = spc.wrap_offset(stackoffset.wrapping_add(off));
            }
            let vn = if paramtrial.is_unref() {
                data.new_varnode(sz, &Address::new(spc.clone(), off), None, glb)?
            } else {
                let mut vn = data.op(op).get_in(paramtrial.get_slot());
                if data.vn(vn).get_size() > sz {
                    let newop = data.new_op(2, &op_addr);
                    let vn_addr = data.vn(vn).get_addr().clone();
                    let vn_size = data.vn(vn).get_size();
                    let outvn = if big_endian {
                        data.new_varnode_out(sz, &vn_addr.add((vn_size - sz) as i64), newop, glb)?
                    } else {
                        data.new_varnode_out(sz, &vn_addr, newop, glb)?
                    };
                    data.op_set_opcode(newop, OpCode::Subpiece, glb);
                    data.op_set_input(newop, vn, 0)?;
                    let zero = data.new_constant(1, 0, glb);
                    data.op_set_input(newop, zero, 1)?;
                    data.op_insert_before(newop, op);
                    vn = outvn;
                }
                vn
            };
            newparam.push(vn);
            if isspacebase {
                let scope = data.get_scope_local().expect("function has no local scope");
                Database::local_mark_not_mapped(glb, data, scope, &spc, off, sz, true);
            }
        }
        data.op_set_all_input(op, &newparam)?;
        data.call_spec_mut(fc).activeinput.delete_unused_trials();
        Ok(())
    }

    pub fn build_output_from_trials(
        data: &mut Funcdata,
        fc: CallSpecId,
        trialvn: &mut [Option<VarnodeId>],
        glb: &mut Architecture,
    ) -> Result<()> {
        let op = data.call_spec(fc).op;
        let mut finalvn: Vec<VarnodeId> = Vec::new();
        {
            let activeoutput = &data.call_spec(fc).activeoutput;
            for index in 0..activeoutput.get_num_trials() {
                let curtrial = activeoutput.get_trial(index);
                if !curtrial.is_used() {
                    break;
                }
                let vn = trialvn[(curtrial.get_slot() - 1) as usize].expect("used output trial has no varnode");
                finalvn.push(vn);
            }
        }
        data.call_spec_mut(fc).activeoutput.delete_unused_trials();
        let num_trials = data.call_spec(fc).activeoutput.get_num_trials();
        if num_trials == 0 {
            return Ok(());
        }

        let mut deletedops: Vec<OpId> = Vec::new();
        if num_trials == 1 {
            let finaloutvn = finalvn[0];
            let indop = data
                .vn(finaloutvn)
                .get_def()
                .expect("output trial varnode has no defining op");
            deletedops.push(indop);
            data.op_set_output(op, finaloutvn, glb)?;
        } else if num_trials == 2 {
            let (hivn, lovn) = if data.call_spec(fc).activeoutput.is_join_reverse() {
                (finalvn[0], finalvn[1])
            } else {
                (finalvn[1], finalvn[0])
            };
            if data.is_double_precis_on() {
                data.vbank.varnodes.get_mut(lovn).set_precis_lo(&mut data.highs);
                data.vbank.varnodes.get_mut(hivn).set_precis_hi(&mut data.highs);
            }
            deletedops.push(data.vn(hivn).get_def().expect("output trial has no defining op"));
            deletedops.push(data.vn(lovn).get_def().expect("output trial has no defining op"));
            match FuncCallSpecs::find_preexisting_whole(data, hivn, lovn) {
                None => {
                    let hi_addr = data.vn(hivn).get_addr().clone();
                    let hi_size = data.vn(hivn).get_size();
                    let lo_addr = data.vn(lovn).get_addr().clone();
                    let lo_size = data.vn(lovn).get_size();
                    let translate = glb.translate.as_deref().expect("architecture has no translator");
                    let joinaddr = glb
                        .manager
                        .construct_join_address(translate, &hi_addr, hi_size, &lo_addr, lo_size)?;
                    let finaloutvn = data.new_varnode(hi_size + lo_size, &joinaddr, None, glb)?;
                    data.op_set_output(op, finaloutvn, glb)?;
                    let op_addr = data.op(op).get_addr().clone();
                    let sublo = data.new_op(2, &op_addr);
                    data.op_set_opcode(sublo, OpCode::Subpiece, glb);
                    data.op_set_input(sublo, finaloutvn, 0)?;
                    let zero = data.new_constant(4, 0, glb);
                    data.op_set_input(sublo, zero, 1)?;
                    data.op_set_output(sublo, lovn, glb)?;
                    data.op_insert_after(sublo, op);
                    let subhi = data.new_op(2, &op_addr);
                    data.op_set_opcode(subhi, OpCode::Subpiece, glb);
                    data.op_set_input(subhi, finaloutvn, 0)?;
                    let lo_constant = data.new_constant(4, lo_size as u64, glb);
                    data.op_set_input(subhi, lo_constant, 1)?;
                    data.op_set_output(subhi, hivn, glb)?;
                    data.op_insert_after(subhi, op);
                }
                Some(finaloutvn) => {
                    deletedops.push(data.vn(finaloutvn).get_def().expect("whole varnode has no defining op"));
                    data.op_set_output(op, finaloutvn, glb)?;
                }
            }
        } else {
            return Ok(());
        }

        for dop in deletedops {
            let in0 = data.op(dop).get_in_option(0);
            let in1 = data.op(dop).get_in_option(1);
            data.op_destroy(dop)?;
            if let Some(in0) = in0 {
                data.delete_varnode(in0)?;
            }
            if let Some(in1) = in1 {
                data.delete_varnode(in1)?;
            }
        }
        Ok(())
    }

    pub fn get_input_bytes_consumed(&self, slot: i32) -> i32 {
        if slot < 0 || slot as usize >= self.input_consume.len() {
            return 0;
        }
        self.input_consume[slot as usize]
    }

    pub fn set_input_bytes_consumed(&mut self, slot: i32, val: i32) -> bool {
        while self.input_consume.len() as i32 <= slot {
            self.input_consume.push(0);
        }
        let old_val = self.input_consume[slot as usize];
        if old_val == 0 || val < old_val {
            self.input_consume[slot as usize] = val;
            return true;
        }
        false
    }

    pub fn paramshift_modify_start(&mut self, glb: &mut Architecture) -> Result<()> {
        if self.paramshift == 0 {
            return Ok(());
        }
        let paramshift = self.paramshift;
        self.proto.param_shift(paramshift, glb)
    }

    pub fn paramshift_modify_stop(data: &mut Funcdata, fc: CallSpecId, glb: &mut Architecture) -> Result<bool> {
        let paramshift = data.call_spec(fc).paramshift;
        if paramshift == 0 {
            return Ok(false);
        }
        if data.call_spec(fc).is_paramshift_applied() {
            return Ok(false);
        }
        data.call_spec_mut(fc).set_paramshift_applied(true);
        let op = data.call_spec(fc).op;
        if data.op(op).num_input() < paramshift + 1 {
            return Err(Error::Lowlevel("Paramshift mechanism is confused".to_string()));
        }
        for _ in 0..paramshift {
            data.op_remove_input(op, 1);
            data.call_spec_mut(fc).remove_param(0, glb);
        }
        Ok(true)
    }

    pub fn has_effect_translate(&self, addr: &Address, size: i32, glb: &Architecture) -> u32 {
        let spc = addr.get_space().expect("address has no space");
        if spc.get_type() != SpaceType::Spacebase {
            return self.proto.has_effect(addr, size, glb);
        }
        if self.stackoffset == FuncCallSpecs::OFFSET_UNKNOWN {
            return EffectRecord::UNKNOWN_EFFECT;
        }
        let newoff = spc.wrap_offset(addr.get_offset().wrapping_sub(self.stackoffset));
        self.proto.has_effect(&Address::new(spc.clone(), newoff), size, glb)
    }

    pub fn find_preexisting_whole(data: &Funcdata, vn1: VarnodeId, vn2: VarnodeId) -> Option<VarnodeId> {
        let op1 = data.vn(vn1).lone_descend()?;
        let op2 = data.vn(vn2).lone_descend()?;
        if op1 != op2 {
            return None;
        }
        if data.op(op1).code() != OpCode::Piece {
            return None;
        }
        data.op(op1).get_out()
    }

    pub fn get_fspec_from_const(addr: &Address) -> CallSpecId {
        CallSpecId(addr.get_offset() as u32)
    }

    pub fn compare_by_entry_address(first: &FuncCallSpecs, second: &FuncCallSpecs) -> bool {
        first.entryaddress < second.entryaddress
    }

    pub fn count_matching_calls(data: &mut Funcdata) {
        let mut copy_list: Vec<CallSpecId> = data.qlst.clone();
        {
            let callspecs = &data.callspecs;
            std_sort(&mut copy_list, |first, second| {
                FuncCallSpecs::compare_by_entry_address(&callspecs[*first], &callspecs[*second])
            });
        }
        let mut index = 0usize;
        while index < copy_list.len() {
            if !data.callspecs[copy_list[index]].entryaddress.is_invalid() {
                break;
            }
            data.callspecs[copy_list[index]].match_call_count = 1;
            index += 1;
        }
        if index == copy_list.len() {
            return;
        }
        let mut last_addr = data.callspecs[copy_list[index]].entryaddress.clone();
        let mut last_change = index;
        index += 1;
        while index < copy_list.len() {
            if data.callspecs[copy_list[index]].entryaddress == last_addr {
                index += 1;
                continue;
            }
            let num = (index - last_change) as i32;
            while last_change < index {
                data.callspecs[copy_list[last_change]].match_call_count = num;
                last_change += 1;
            }
            last_addr = data.callspecs[copy_list[index]].entryaddress.clone();
            index += 1;
        }
        let num = (index - last_change) as i32;
        while last_change < index {
            data.callspecs[copy_list[last_change]].match_call_count = num;
            last_change += 1;
        }
    }
}

impl FuncProto {
    pub fn set_internal_model_option(&mut self, model: Option<ModelId>, vt: TypeId, glb: &Architecture) {
        self.store = Some(Box::new(ProtoStore::Internal(ProtoStoreInternal::new(vt))));
        if self.model.is_none() {
            self.set_model(model, glb);
        }
    }
}

impl FuncCallSpecs {
    pub fn get_active_input_ref(&self) -> &ParamActive {
        &self.activeinput
    }
}
