use std::collections::BTreeMap;
use std::ops::Bound;

use crate::address::ELEM_RANGELIST;
use crate::address::{Address, Range, RangeList, calc_mask, sign_extend_size};
use crate::architecture::Architecture;
use crate::arena::Arena;
use crate::crc32::crc_update;
use crate::define_id;
use crate::error::{Error, Result};
use crate::funcdata::{ELEM_FUNCTION, Funcdata};
use crate::istream::{Basefield, read_u32, read_u64};
use crate::jumptable::ATTRIB_LABEL;
use crate::marshal::{
    ATTRIB_CONTENT, ATTRIB_FORMAT, ATTRIB_HIDDENRETPARM, ATTRIB_ID, ATTRIB_INDEX, ATTRIB_INDIRECTSTORAGE, ATTRIB_NAME,
    ATTRIB_NAMELOCK, ATTRIB_READONLY, ATTRIB_THISPTR, ATTRIB_TYPELOCK, ATTRIB_VAL, AttributeId, Decoder, ELEM_SYMBOL,
    ELEM_VAL, ELEM_VALUE, ElementId, Encoder,
};
use crate::partmap::PartMap;
use crate::pcoderaw::VarnodeData;
use crate::rangemap::{RangeMap, RangeRecord, RangeRecordId, RangeSubsort};
use crate::space::SpaceRef;
use crate::translate::AddrSpaceManager;
use crate::types::{Datatype, TypeFactory, TypeId, TypeMetatype};
use crate::varmap::ScopeLocalData;
use crate::varnode::{ATTRIB_ADDRTIED, Varnode, VarnodeId};

pub const ATTRIB_CAT: AttributeId = AttributeId::new("cat", 61);
pub const ATTRIB_FIELD: AttributeId = AttributeId::new("field", 62);
pub const ATTRIB_MERGE: AttributeId = AttributeId::new("merge", 63);
pub const ATTRIB_SCOPEIDBYNAME: AttributeId = AttributeId::new("scopeidbyname", 64);
pub const ATTRIB_VOLATILE: AttributeId = AttributeId::new("volatile", 65);
pub const ELEM_COLLISION: ElementId = ElementId::new("collision", 67);
pub const ELEM_DB: ElementId = ElementId::new("db", 68);
pub const ELEM_EQUATESYMBOL: ElementId = ElementId::new("equatesymbol", 69);
pub const ELEM_EXTERNREFSYMBOL: ElementId = ElementId::new("externrefsymbol", 70);
pub const ELEM_FACETSYMBOL: ElementId = ElementId::new("facetsymbol", 71);
pub const ELEM_FUNCTIONSHELL: ElementId = ElementId::new("functionshell", 72);
pub const ELEM_HASH: ElementId = ElementId::new("hash", 73);
pub const ELEM_HOLE: ElementId = ElementId::new("hole", 74);
pub const ELEM_LABELSYM: ElementId = ElementId::new("labelsym", 75);
pub const ELEM_MAPSYM: ElementId = ElementId::new("mapsym", 76);
pub const ELEM_PARENT: ElementId = ElementId::new("parent", 77);
pub const ELEM_PROPERTY_CHANGEPOINT: ElementId = ElementId::new("property_changepoint", 78);
pub const ELEM_RANGEEQUALSSYMBOLS: ElementId = ElementId::new("rangeequalssymbols", 79);
pub const ELEM_SCOPE: ElementId = ElementId::new("scope", 80);
pub const ELEM_SYMBOLLIST: ElementId = ElementId::new("symbollist", 81);

define_id!(ScopeId);
define_id!(SymbolId);
define_id!(EntryId);

fn same_space(first: &Address, second: &Address) -> bool {
    match (first.get_space(), second.get_space()) {
        (None, None) => true,
        (Some(left), Some(right)) => left.get_index() == right.get_index(),
        _ => false,
    }
}

fn space_index(addr: &Address) -> Option<usize> {
    addr.get_space().map(|spc| spc.get_index() as usize)
}

fn db_and_types(glb: &mut Architecture) -> (&mut Database, &mut TypeFactory) {
    (
        glb.symboltab.as_deref_mut().expect("architecture has no symbol table"),
        glb.types.as_deref_mut().expect("architecture has no type factory"),
    )
}

fn db_ref(glb: &Architecture) -> &Database {
    glb.symboltab.as_deref().expect("architecture has no symbol table")
}

fn db_mut(glb: &mut Architecture) -> &mut Database {
    glb.symboltab.as_deref_mut().expect("architecture has no symbol table")
}

fn types_ref(glb: &Architecture) -> &TypeFactory {
    glb.types.as_deref().expect("architecture has no type factory")
}

fn capitalize_first(name: &str) -> String {
    let mut res = name.to_string();
    if let Some(first) = res.get_mut(0..1) {
        first.make_ascii_uppercase();
    }
    res
}

#[derive(Copy, Clone, Debug, Default, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct EntrySubsort {
    useindex: i32,
    useoffset: u64,
}

impl EntrySubsort {
    pub fn from_addr(addr: &Address) -> EntrySubsort {
        EntrySubsort {
            useindex: addr.get_space().expect("subsort address has no space").get_index(),
            useoffset: addr.get_offset(),
        }
    }

    pub fn new() -> EntrySubsort {
        EntrySubsort {
            useindex: 0,
            useoffset: 0,
        }
    }
}

impl RangeSubsort for EntrySubsort {
    fn from_bool(val: bool) -> EntrySubsort {
        if val {
            EntrySubsort {
                useindex: 0xffff,
                useoffset: 0,
            }
        } else {
            EntrySubsort {
                useindex: 0,
                useoffset: 0,
            }
        }
    }
}

#[derive(Clone, Copy, Debug)]
pub struct SymbolRangeInit {
    pub entry: EntryId,
    pub subsort: EntrySubsort,
}

#[derive(Clone, Debug)]
pub struct SymbolRange {
    pub first: u64,
    pub last: u64,
    pub entry: EntryId,
    pub subsort: EntrySubsort,
}

impl SymbolRange {
    pub fn new(init: &SymbolRangeInit, first: u64, last: u64) -> SymbolRange {
        SymbolRange {
            first,
            last,
            entry: init.entry,
            subsort: init.subsort,
        }
    }

    pub fn compute_subsort(db: &Database, entry: EntryId) -> Result<EntrySubsort> {
        let record = db.entry(entry);
        let mut res = EntrySubsort::new();
        if (db.symbol(record.symbol).get_flags() & Varnode::ADDRTIED) == 0 {
            let range = record
                .get_use_limit()
                .get_first_range()
                .ok_or_else(|| Error::Lowlevel("Map entry with empty uselimit".to_string()))?;
            res.useindex = range.get_space().get_index();
            res.useoffset = range.get_first();
        }
        Ok(res)
    }
}

impl RangeRecord for SymbolRange {
    type Line = u64;
    type Subsort = EntrySubsort;
    type Init = SymbolRangeInit;

    fn new_record(data: &SymbolRangeInit, first: u64, last: u64) -> SymbolRange {
        SymbolRange::new(data, first, last)
    }

    fn get_first(&self) -> u64 {
        self.first
    }

    fn get_last(&self) -> u64 {
        self.last
    }

    fn get_subsort(&self) -> EntrySubsort {
        self.subsort
    }
}

pub type EntryMap = RangeMap<SymbolRange>;

#[derive(Clone, Debug)]
pub enum SymbolEntryKind {
    Map {
        addr: Address,
        map_iterator: Option<RangeRecordId>,
    },
    Conflict {
        addr: Address,
        map_iterator: Option<RangeRecordId>,
        uniq: u32,
    },
    Dynamic {
        hash: u64,
    },
}

#[derive(Clone, Debug)]
pub struct SymbolEntry {
    pub symbol: SymbolId,
    pub uselimit: RangeList,
    pub extraflags: u32,
    pub offset: i32,
    pub size: i32,
    pub is_piece: bool,
    pub kind: SymbolEntryKind,
}

impl SymbolEntry {
    pub const MAP_ENTRY: u16 = 0;
    pub const CONFLICT_ENTRY: u16 = 1;
    pub const DYNAMIC_ENTRY: u16 = 2;

    pub fn new_base(sym: SymbolId, kind: SymbolEntryKind) -> SymbolEntry {
        SymbolEntry {
            symbol: sym,
            uselimit: RangeList::new(),
            extraflags: 0,
            offset: 0,
            size: -1,
            is_piece: false,
            kind,
        }
    }

    pub fn new_with_use(
        sym: SymbolId,
        exflags: u32,
        sz: i32,
        off: i32,
        uselim: &RangeList,
        kind: SymbolEntryKind,
    ) -> SymbolEntry {
        SymbolEntry {
            symbol: sym,
            uselimit: uselim.clone(),
            extraflags: exflags,
            offset: off,
            size: sz,
            is_piece: false,
            kind,
        }
    }

    pub fn new_map(sym: SymbolId, exflags: u32, ad: &Address, sz: i32, off: i32, uselim: &RangeList) -> SymbolEntry {
        SymbolEntry::new_with_use(
            sym,
            exflags,
            sz,
            off,
            uselim,
            SymbolEntryKind::Map {
                addr: ad.clone(),
                map_iterator: None,
            },
        )
    }

    pub fn new_map_empty(sym: SymbolId) -> SymbolEntry {
        SymbolEntry::new_base(
            sym,
            SymbolEntryKind::Map {
                addr: Address::invalid(),
                map_iterator: None,
            },
        )
    }

    pub fn new_conflict(sym: SymbolId, data: &Funcdata, vn: VarnodeId) -> SymbolEntry {
        let varnode = data.vn(vn);
        let def = varnode.get_def().expect("conflict varnode has no defining op");
        let seq_num = data.op(def).get_seq_num();
        let mut entry = SymbolEntry::new_base(
            sym,
            SymbolEntryKind::Conflict {
                addr: varnode.get_addr().clone(),
                map_iterator: None,
                uniq: seq_num.get_time(),
            },
        );
        entry.size = varnode.get_size();
        let seq_addr = seq_num.get_addr();
        entry.uselimit.insert_range(
            seq_addr.get_space().expect("conflict op address has no space"),
            seq_addr.get_offset(),
            seq_addr.get_offset(),
        );
        entry
    }

    pub fn new_dynamic(sym: SymbolId, exfl: u32, hash: u64, off: i32, sz: i32, rnglist: &RangeList) -> SymbolEntry {
        SymbolEntry::new_with_use(sym, exfl, sz, off, rnglist, SymbolEntryKind::Dynamic { hash })
    }

    pub fn new_dynamic_empty(sym: SymbolId) -> SymbolEntry {
        SymbolEntry::new_base(sym, SymbolEntryKind::Dynamic { hash: 0 })
    }

    pub fn get_entry_type(&self) -> u16 {
        match self.kind {
            SymbolEntryKind::Map { .. } => SymbolEntry::MAP_ENTRY,
            SymbolEntryKind::Conflict { .. } => SymbolEntry::CONFLICT_ENTRY,
            SymbolEntryKind::Dynamic { .. } => SymbolEntry::DYNAMIC_ENTRY,
        }
    }

    pub fn is_piece(&self) -> bool {
        self.is_piece
    }

    pub fn is_dynamic(&self) -> bool {
        self.get_entry_type() == SymbolEntry::DYNAMIC_ENTRY
    }

    pub fn is_conflict(&self) -> bool {
        self.get_entry_type() == SymbolEntry::CONFLICT_ENTRY
    }

    pub fn get_offset(&self) -> i32 {
        self.offset
    }

    pub fn get_symbol(&self) -> SymbolId {
        self.symbol
    }

    pub fn get_size(&self) -> i32 {
        self.size
    }

    pub fn in_use(&self, db: &Database, usepoint: &Address) -> bool {
        if (db.symbol(self.symbol).get_flags() & Varnode::ADDRTIED) != 0 {
            return true;
        }
        if usepoint.is_invalid() {
            return false;
        }
        self.uselimit.in_range(usepoint, 1)
    }

    pub fn get_use_limit(&self) -> &RangeList {
        &self.uselimit
    }

    pub fn get_first_use_address(&self) -> Address {
        match self.uselimit.get_first_range() {
            Some(rng) => rng.get_first_addr(),
            None => Address::invalid(),
        }
    }

    pub fn set_use_limit(&mut self, uselim: &RangeList) {
        self.uselimit = uselim.clone();
    }

    pub fn get_addr(&self) -> &Address {
        match &self.kind {
            SymbolEntryKind::Map { addr, .. } | SymbolEntryKind::Conflict { addr, .. } => addr,
            SymbolEntryKind::Dynamic { .. } => panic!("dynamic symbol entry has no storage address"),
        }
    }

    fn set_addr(&mut self, newaddr: Address) {
        match &mut self.kind {
            SymbolEntryKind::Map { addr, .. } | SymbolEntryKind::Conflict { addr, .. } => *addr = newaddr,
            SymbolEntryKind::Dynamic { .. } => panic!("dynamic symbol entry has no storage address"),
        }
    }

    pub fn get_first(&self) -> u64 {
        self.get_addr().get_offset()
    }

    pub fn get_last(&self) -> u64 {
        self.get_addr()
            .get_offset()
            .wrapping_add(self.size as u64)
            .wrapping_sub(1)
    }

    pub fn get_map_iterator(&self) -> Option<RangeRecordId> {
        match &self.kind {
            SymbolEntryKind::Map { map_iterator, .. } | SymbolEntryKind::Conflict { map_iterator, .. } => *map_iterator,
            SymbolEntryKind::Dynamic { .. } => panic!("dynamic symbol entry has no map iterator"),
        }
    }

    fn set_map_iterator(&mut self, iter: Option<RangeRecordId>) {
        match &mut self.kind {
            SymbolEntryKind::Map { map_iterator, .. } | SymbolEntryKind::Conflict { map_iterator, .. } => {
                *map_iterator = iter
            }
            SymbolEntryKind::Dynamic { .. } => panic!("dynamic symbol entry has no map iterator"),
        }
    }

    pub fn get_unique(&self) -> u32 {
        match &self.kind {
            SymbolEntryKind::Conflict { uniq, .. } => *uniq,
            _ => panic!("symbol entry is not a conflict entry"),
        }
    }

    pub fn get_hash(&self) -> u64 {
        match &self.kind {
            SymbolEntryKind::Dynamic { hash } => *hash,
            _ => panic!("symbol entry is not a dynamic entry"),
        }
    }

    pub fn encode(&self, encoder: &mut dyn Encoder) -> Result<()> {
        if self.is_piece() {
            return Ok(());
        }
        match &self.kind {
            SymbolEntryKind::Map { addr, .. } => {
                addr.encode(encoder)?;
            }
            SymbolEntryKind::Conflict { .. } => {
                encoder.open_element(ELEM_HASH);
                encoder.write_unsigned_integer(ATTRIB_VAL, 0);
                encoder.close_element(ELEM_HASH);
            }
            SymbolEntryKind::Dynamic { hash } => {
                encoder.open_element(ELEM_HASH);
                encoder.write_unsigned_integer(ATTRIB_VAL, *hash);
                encoder.close_element(ELEM_HASH);
            }
        }
        self.uselimit.encode(encoder);
        Ok(())
    }

    pub fn decode(&mut self, decoder: &mut dyn Decoder) -> Result<()> {
        match &mut self.kind {
            SymbolEntryKind::Map { addr, .. } => {
                *addr = Address::decode(decoder)?;
                if addr.is_invalid() {
                    return Err(Error::Lowlevel("Invalid address decoding MapEntry".to_string()));
                }
            }
            SymbolEntryKind::Conflict { .. } => {
                return Err(Error::Lowlevel("Cannot decode MapEntryConflict".to_string()));
            }
            SymbolEntryKind::Dynamic { hash } => {
                let elem_id = decoder.open_element_expect(ELEM_HASH)?;
                *hash = decoder.read_unsigned_integer_attr(ATTRIB_VAL)?;
                decoder.close_element(elem_id)?;
            }
        }
        self.uselimit.decode(decoder)
    }
}

pub const SYMBOL_ID_BASE: u64 = 0x4000000000000000;

pub enum SymbolKind {
    Base,
    Function {
        fd: Option<Box<Funcdata>>,
        consume_size: i32,
    },
    Equate {
        value: u64,
    },
    UnionFacet {
        field_num: i32,
        addr_based: bool,
    },
    Label,
    ExternRef {
        refaddr: Address,
    },
}

pub struct Symbol {
    pub scope: ScopeId,
    pub name: String,
    pub display_name: String,
    pub tp: Option<TypeId>,
    pub name_dedup: u32,
    pub flags: u32,
    pub dispflags: u32,
    pub category: i16,
    pub catindex: u16,
    pub symbol_id: u64,
    pub mapentry: Vec<EntryId>,
    pub depth_scope: Option<ScopeId>,
    pub depth_resolution: i32,
    pub whole_count: u32,
    pub function_checked_out: bool,
    pub kind: SymbolKind,
}

impl Symbol {
    pub const FORCE_HEX: u32 = 1;
    pub const FORCE_DEC: u32 = 2;
    pub const FORCE_OCT: u32 = 3;
    pub const FORCE_BIN: u32 = 4;
    pub const FORCE_CHAR: u32 = 5;
    pub const SIZE_TYPELOCK: u32 = 8;
    pub const ISOLATE: u32 = 16;
    pub const MERGE_PROBLEMS: u32 = 32;
    pub const IS_THIS_PTR: u32 = 64;

    pub const NO_CATEGORY: i16 = -1;
    pub const FUNCTION_PARAMETER: i16 = 0;
    pub const EQUATE: i16 = 1;
    pub const UNION_FACET: i16 = 2;
    pub const FAKE_INPUT: i16 = 3;

    pub const ID_BASE: u64 = SYMBOL_ID_BASE;

    pub fn new(sc: ScopeId, nm: &str, ct: Option<TypeId>) -> Symbol {
        Symbol {
            scope: sc,
            name: nm.to_string(),
            display_name: nm.to_string(),
            tp: ct,
            name_dedup: 0,
            flags: 0,
            dispflags: 0,
            category: Symbol::NO_CATEGORY,
            catindex: 0,
            symbol_id: 0,
            mapentry: Vec::new(),
            depth_scope: None,
            depth_resolution: 0,
            whole_count: 0,
            function_checked_out: false,
            kind: SymbolKind::Base,
        }
    }

    pub fn new_empty(sc: ScopeId) -> Symbol {
        Symbol::new(sc, "", None)
    }

    pub fn new_function(types: &mut TypeFactory, sc: ScopeId, nm: &str, size: i32) -> Result<Symbol> {
        let mut sym = Symbol::new_function_empty(types, sc, size)?;
        sym.name = nm.to_string();
        sym.display_name = nm.to_string();
        Ok(sym)
    }

    pub fn new_function_empty(types: &mut TypeFactory, sc: ScopeId, size: i32) -> Result<Symbol> {
        let mut sym = Symbol::new_empty(sc);
        sym.kind = SymbolKind::Function {
            fd: None,
            consume_size: size,
        };
        sym.build_function_type(types)?;
        Ok(sym)
    }

    pub fn new_equate(types: &mut TypeFactory, sc: ScopeId, nm: &str, format: u32, val: u64) -> Result<Symbol> {
        let mut sym = Symbol::new(sc, nm, None);
        sym.kind = SymbolKind::Equate { value: val };
        sym.category = Symbol::EQUATE;
        sym.tp = Some(types.get_base(1, TypeMetatype::Unknown)?);
        sym.dispflags |= format;
        Ok(sym)
    }

    pub fn new_equate_empty(sc: ScopeId) -> Symbol {
        let mut sym = Symbol::new_empty(sc);
        sym.kind = SymbolKind::Equate { value: 0 };
        sym.category = Symbol::EQUATE;
        sym
    }

    pub fn new_union_facet(
        _types: &mut TypeFactory,
        sc: ScopeId,
        nm: &str,
        union_dt: TypeId,
        fld_num: i32,
        is_addr: bool,
    ) -> Symbol {
        let mut sym = Symbol::new(sc, nm, Some(union_dt));
        sym.kind = SymbolKind::UnionFacet {
            field_num: fld_num,
            addr_based: is_addr,
        };
        sym.category = Symbol::UNION_FACET;
        sym
    }

    pub fn new_union_facet_empty(sc: ScopeId) -> Symbol {
        let mut sym = Symbol::new_empty(sc);
        sym.kind = SymbolKind::UnionFacet {
            field_num: -1,
            addr_based: false,
        };
        sym.category = Symbol::UNION_FACET;
        sym
    }

    pub fn new_label(types: &mut TypeFactory, sc: ScopeId, nm: &str) -> Result<Symbol> {
        let mut sym = Symbol::new_label_empty(types, sc)?;
        sym.name = nm.to_string();
        sym.display_name = nm.to_string();
        Ok(sym)
    }

    pub fn new_label_empty(types: &mut TypeFactory, sc: ScopeId) -> Result<Symbol> {
        let mut sym = Symbol::new_empty(sc);
        sym.kind = SymbolKind::Label;
        sym.build_label_type(types)?;
        Ok(sym)
    }

    pub fn new_extern_ref(types: &mut TypeFactory, sc: ScopeId, reference: &Address, nm: &str) -> Result<Symbol> {
        let mut sym = Symbol::new(sc, nm, None);
        sym.kind = SymbolKind::ExternRef {
            refaddr: reference.clone(),
        };
        sym.build_extern_ref_name_type(types)?;
        Ok(sym)
    }

    pub fn new_extern_ref_empty(sc: ScopeId) -> Symbol {
        let mut sym = Symbol::new_empty(sc);
        sym.kind = SymbolKind::ExternRef {
            refaddr: Address::invalid(),
        };
        sym
    }

    pub fn set_display_format(&mut self, val: u32) {
        self.dispflags &= 0xfffffff8;
        self.dispflags |= val;
    }

    pub fn check_size_type_lock(&mut self, types: &TypeFactory) {
        self.dispflags &= !Symbol::SIZE_TYPELOCK;
        if self.is_type_locked()
            && let Some(tp) = self.tp
            && types.get(tp).get_metatype() == TypeMetatype::Unknown
        {
            self.dispflags |= Symbol::SIZE_TYPELOCK;
        }
    }

    pub fn set_this_pointer(&mut self, val: bool) {
        if val {
            self.dispflags |= Symbol::IS_THIS_PTR;
        } else {
            self.dispflags &= !Symbol::IS_THIS_PTR;
        }
    }

    pub fn get_name(&self) -> &str {
        &self.name
    }

    pub fn get_display_name(&self) -> &str {
        &self.display_name
    }

    pub fn get_type(&self) -> Option<TypeId> {
        self.tp
    }

    fn type_id(&self) -> TypeId {
        self.tp.expect("symbol has no data-type")
    }

    pub fn get_id(&self) -> u64 {
        self.symbol_id
    }

    pub fn get_flags(&self) -> u32 {
        self.flags
    }

    pub fn get_display_format(&self) -> u32 {
        self.dispflags & 7
    }

    pub fn get_category(&self) -> i16 {
        self.category
    }

    pub fn get_category_index(&self) -> u16 {
        self.catindex
    }

    pub fn is_type_locked(&self) -> bool {
        (self.flags & Varnode::TYPELOCK) != 0
    }

    pub fn is_name_locked(&self) -> bool {
        (self.flags & Varnode::NAMELOCK) != 0
    }

    pub fn is_size_type_locked(&self) -> bool {
        (self.dispflags & Symbol::SIZE_TYPELOCK) != 0
    }

    pub fn is_volatile(&self) -> bool {
        (self.flags & Varnode::VOLATIL) != 0
    }

    pub fn is_this_pointer(&self) -> bool {
        (self.dispflags & Symbol::IS_THIS_PTR) != 0
    }

    pub fn is_indirect_storage(&self) -> bool {
        (self.flags & Varnode::INDIRECTSTORAGE) != 0
    }

    pub fn is_hidden_return(&self) -> bool {
        (self.flags & Varnode::HIDDENRETPARM) != 0
    }

    pub fn is_name_undefined(&self) -> bool {
        self.name.len() == 15 && self.name.as_bytes().starts_with(b"$$undef")
    }

    pub fn is_multi_entry(&self) -> bool {
        self.whole_count > 1
    }

    pub fn has_merge_problems(&self) -> bool {
        (self.dispflags & Symbol::MERGE_PROBLEMS) != 0
    }

    pub fn set_merge_problems(&mut self) {
        self.dispflags |= Symbol::MERGE_PROBLEMS;
    }

    pub fn is_isolated(&self) -> bool {
        (self.dispflags & Symbol::ISOLATE) != 0
    }

    pub fn set_isolated(&mut self, val: bool, types: &TypeFactory) {
        if val {
            self.dispflags |= Symbol::ISOLATE;
            self.flags |= Varnode::TYPELOCK;
            self.check_size_type_lock(types);
        } else {
            self.dispflags &= !Symbol::ISOLATE;
        }
    }

    pub fn is_function(&self) -> bool {
        matches!(self.kind, SymbolKind::Function { .. })
    }

    pub fn get_scope(&self) -> ScopeId {
        self.scope
    }

    pub fn num_entries(&self) -> i32 {
        self.mapentry.len() as i32
    }

    pub fn get_map_entry_index(&self, index: i32) -> EntryId {
        self.mapentry[index as usize]
    }

    pub fn get_map_entry_position(&self, entry: EntryId, db: &Database, types: &TypeFactory) -> i32 {
        let mut pos = 0;
        for &tmp in self.mapentry.iter() {
            if tmp == entry {
                return pos;
            }
            if db.entry(entry).get_size() == types.get(self.type_id()).get_size() {
                pos += 1;
            }
        }
        -1
    }

    pub fn encode_header(&self, encoder: &mut dyn Encoder) -> Result<()> {
        encoder.write_string(ATTRIB_NAME, &self.name);
        encoder.write_unsigned_integer(ATTRIB_ID, self.get_id());
        if (self.flags & Varnode::NAMELOCK) != 0 {
            encoder.write_bool(ATTRIB_NAMELOCK, true);
        }
        if (self.flags & Varnode::TYPELOCK) != 0 {
            encoder.write_bool(ATTRIB_TYPELOCK, true);
        }
        if (self.flags & Varnode::READONLY) != 0 {
            encoder.write_bool(ATTRIB_READONLY, true);
        }
        if (self.flags & Varnode::VOLATIL) != 0 {
            encoder.write_bool(ATTRIB_VOLATILE, true);
        }
        if (self.flags & Varnode::INDIRECTSTORAGE) != 0 {
            encoder.write_bool(ATTRIB_INDIRECTSTORAGE, true);
        }
        if (self.flags & Varnode::HIDDENRETPARM) != 0 {
            encoder.write_bool(ATTRIB_HIDDENRETPARM, true);
        }
        if (self.dispflags & Symbol::ISOLATE) != 0 {
            encoder.write_bool(ATTRIB_MERGE, false);
        }
        if (self.dispflags & Symbol::IS_THIS_PTR) != 0 {
            encoder.write_bool(ATTRIB_THISPTR, true);
        }
        let format = self.get_display_format();
        if format != 0 {
            encoder.write_string(ATTRIB_FORMAT, &Datatype::decode_integer_format(format)?);
        }
        encoder.write_signed_integer(ATTRIB_CAT, self.category as i64);
        if self.category >= 0 {
            encoder.write_unsigned_integer(ATTRIB_INDEX, self.catindex as u64);
        }
        Ok(())
    }

    pub fn decode_header(&mut self, decoder: &mut dyn Decoder) -> Result<()> {
        self.name.clear();
        self.display_name.clear();
        self.category = Symbol::NO_CATEGORY;
        self.symbol_id = 0;
        loop {
            let attrib_id = decoder.get_next_attribute_id()?;
            if attrib_id == 0 {
                break;
            }
            if attrib_id == ATTRIB_CAT {
                self.category = decoder.read_signed_integer()? as i16;
            } else if attrib_id == ATTRIB_FORMAT {
                self.dispflags |= Datatype::encode_integer_format(&decoder.read_string()?)?;
            } else if attrib_id == ATTRIB_HIDDENRETPARM {
                if decoder.read_bool()? {
                    self.flags |= Varnode::HIDDENRETPARM;
                }
            } else if attrib_id == ATTRIB_ID {
                self.symbol_id = decoder.read_unsigned_integer()?;
                if (self.symbol_id >> 56) == (Symbol::ID_BASE >> 56) {
                    self.symbol_id = 0;
                }
            } else if attrib_id == ATTRIB_INDIRECTSTORAGE {
                if decoder.read_bool()? {
                    self.flags |= Varnode::INDIRECTSTORAGE;
                }
            } else if attrib_id == ATTRIB_MERGE {
                if !decoder.read_bool()? {
                    self.dispflags |= Symbol::ISOLATE;
                    self.flags |= Varnode::TYPELOCK;
                }
            } else if attrib_id == ATTRIB_NAME {
                self.name = decoder.read_string()?;
            } else if attrib_id == ATTRIB_NAMELOCK {
                if decoder.read_bool()? {
                    self.flags |= Varnode::NAMELOCK;
                }
            } else if attrib_id == ATTRIB_READONLY {
                if decoder.read_bool()? {
                    self.flags |= Varnode::READONLY;
                }
            } else if attrib_id == ATTRIB_TYPELOCK {
                if decoder.read_bool()? {
                    self.flags |= Varnode::TYPELOCK;
                }
            } else if attrib_id == ATTRIB_THISPTR {
                if decoder.read_bool()? {
                    self.dispflags |= Symbol::IS_THIS_PTR;
                }
            } else if attrib_id == ATTRIB_VOLATILE {
                if decoder.read_bool()? {
                    self.flags |= Varnode::VOLATIL;
                }
            } else if attrib_id == ATTRIB_LABEL {
                self.display_name = decoder.read_string()?;
            }
        }
        if self.category == Symbol::FUNCTION_PARAMETER {
            self.catindex = decoder.read_unsigned_integer_attr(ATTRIB_INDEX)? as u16;
        } else {
            self.catindex = 0;
        }
        if self.display_name.is_empty() {
            self.display_name = self.name.clone();
        }
        Ok(())
    }

    pub fn get_bytes_consumed(&self, types: &TypeFactory) -> i32 {
        match &self.kind {
            SymbolKind::Function { consume_size, .. } => *consume_size,
            _ => types.get(self.type_id()).get_size(),
        }
    }

    pub fn get_value(&self) -> u64 {
        match &self.kind {
            SymbolKind::Equate { value } => *value,
            _ => panic!("symbol is not an equate"),
        }
    }

    pub fn is_value_close(&self, op2_value: u64, size: i32) -> bool {
        let value = self.get_value();
        if value == op2_value {
            return true;
        }
        let mask = calc_mask(size);
        let mask_value = value & mask;
        if mask_value != value && value != sign_extend_size(mask_value, size, 8) {
            return false;
        }
        if mask_value == (op2_value & mask) {
            return true;
        }
        if mask_value == (!op2_value & mask) {
            return true;
        }
        if mask_value == (op2_value.wrapping_neg() & mask) {
            return true;
        }
        if mask_value == (op2_value.wrapping_add(1) & mask) {
            return true;
        }
        if mask_value == (op2_value.wrapping_sub(1) & mask) {
            return true;
        }
        false
    }

    pub fn get_field_number(&self) -> i32 {
        match &self.kind {
            SymbolKind::UnionFacet { field_num, .. } => *field_num,
            _ => panic!("symbol is not a union facet"),
        }
    }

    pub fn is_addr_based(&self) -> bool {
        match &self.kind {
            SymbolKind::UnionFacet { addr_based, .. } => *addr_based,
            _ => panic!("symbol is not a union facet"),
        }
    }

    pub fn get_ref_addr(&self) -> &Address {
        match &self.kind {
            SymbolKind::ExternRef { refaddr } => refaddr,
            _ => panic!("symbol is not an external reference"),
        }
    }

    pub fn build_function_type(&mut self, types: &mut TypeFactory) -> Result<()> {
        self.tp = Some(types.get_type_code()?);
        self.flags |= Varnode::NAMELOCK | Varnode::TYPELOCK;
        Ok(())
    }

    pub fn build_label_type(&mut self, types: &mut TypeFactory) -> Result<()> {
        self.tp = Some(types.get_base(1, TypeMetatype::Unknown)?);
        Ok(())
    }

    pub fn build_extern_ref_name_type(&mut self, types: &mut TypeFactory) -> Result<()> {
        let refaddr = self.get_ref_addr().clone();
        let code = types.get_type_code()?;
        let word_size = refaddr.get_space().map(|spc| spc.get_word_size()).unwrap_or(1);
        self.tp = Some(types.get_type_pointer(refaddr.get_addr_size(), code, word_size)?);
        if self.name.is_empty() {
            let mut text = String::new();
            text.push(refaddr.get_shortcut());
            refaddr.print_raw(&mut text);
            text.push_str("_exref");
            self.name = text;
        }
        if self.display_name.is_empty() {
            self.display_name = self.name.clone();
        }
        self.flags |= Varnode::EXTERNREF | Varnode::TYPELOCK;
        Ok(())
    }
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct SymbolNameKey {
    pub name: String,
    pub name_dedup: u32,
}

impl SymbolNameKey {
    pub fn of(sym: &Symbol) -> SymbolNameKey {
        SymbolNameKey {
            name: sym.name.clone(),
            name_dedup: sym.name_dedup,
        }
    }

    fn probe(nm: &str, dedup: u32) -> SymbolNameKey {
        SymbolNameKey {
            name: nm.to_string(),
            name_dedup: dedup,
        }
    }
}

pub type SymbolNameTree = BTreeMap<SymbolNameKey, SymbolId>;

fn name_lower_bound(tree: &SymbolNameTree, key: &SymbolNameKey) -> Option<SymbolNameKey> {
    tree.range((Bound::Included(key), Bound::Unbounded))
        .next()
        .map(|(found, _)| found.clone())
}

fn name_upper_bound(tree: &SymbolNameTree, key: &SymbolNameKey) -> Option<SymbolNameKey> {
    tree.range((Bound::Excluded(key), Bound::Unbounded))
        .next()
        .map(|(found, _)| found.clone())
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct MapIterator {
    pub curmap: usize,
    pub curiter: Option<RangeRecordId>,
}

impl MapIterator {
    pub fn new(curmap: usize, curiter: Option<RangeRecordId>) -> MapIterator {
        MapIterator { curmap, curiter }
    }

    pub fn get(&self, scope: &Scope) -> EntryId {
        let map = scope.maptable[self.curmap]
            .as_ref()
            .expect("map iterator points to an empty map slot");
        map.record(self.curiter.expect("map iterator is at the end of a map"))
            .entry
    }

    fn skip_empty(&mut self, scope: &Scope) {
        let len = scope.maptable.len();
        while self.curmap != len && self.curiter.is_none() {
            loop {
                self.curmap += 1;
                if self.curmap == len || scope.maptable[self.curmap].is_some() {
                    break;
                }
            }
            if self.curmap != len {
                self.curiter = scope.maptable[self.curmap]
                    .as_ref()
                    .expect("map slot checked above")
                    .list_front();
            }
        }
    }

    pub fn advance(&mut self, scope: &Scope) {
        let map = scope.maptable[self.curmap]
            .as_ref()
            .expect("map iterator points to an empty map slot");
        self.curiter = map.list_next(self.curiter.expect("map iterator is at the end of a map"));
        self.skip_empty(scope);
    }

    pub fn equals(&self, op2: &MapIterator, scope: &Scope) -> bool {
        if self.curmap != op2.curmap {
            return false;
        }
        if self.curmap == scope.maptable.len() {
            return true;
        }
        self.curiter == op2.curiter
    }
}

pub type ScopeMap = BTreeMap<u64, ScopeId>;

pub enum ScopeKind {
    Internal,
    Local(Box<ScopeLocalData>),
}

pub struct Scope {
    pub rangetree: RangeList,
    pub parent: Option<ScopeId>,
    pub owner: Option<ScopeId>,
    pub children: ScopeMap,
    pub name: String,
    pub display_name: String,
    pub fd: Option<Address>,
    pub unique_id: u64,
    pub debugon: bool,
    pub nametree: SymbolNameTree,
    pub maptable: Vec<Option<Box<EntryMap>>>,
    pub category: Vec<Vec<Option<SymbolId>>>,
    pub dynamicentry: Vec<EntryId>,
    pub multi_entry_set: SymbolNameTree,
    pub next_unique_id: u64,
    pub kind: ScopeKind,
}

impl Scope {
    pub fn new_base(id: u64, nm: &str, own: Option<ScopeId>) -> Scope {
        Scope {
            rangetree: RangeList::new(),
            parent: None,
            owner: own,
            children: BTreeMap::new(),
            name: nm.to_string(),
            display_name: nm.to_string(),
            fd: None,
            unique_id: id,
            debugon: false,
            nametree: BTreeMap::new(),
            maptable: Vec::new(),
            category: Vec::new(),
            dynamicentry: Vec::new(),
            multi_entry_set: BTreeMap::new(),
            next_unique_id: 0,
            kind: ScopeKind::Internal,
        }
    }

    pub fn new_internal(id: u64, nm: &str, num_spaces: i32) -> Scope {
        Scope::new_internal_owned(id, nm, num_spaces, None)
    }

    pub fn new_internal_owned(id: u64, nm: &str, num_spaces: i32, own: Option<ScopeId>) -> Scope {
        let mut scope = Scope::new_base(id, nm, own);
        scope.next_unique_id = 0;
        scope.maptable.resize_with(num_spaces.max(0) as usize, || None);
        scope
    }

    pub fn hash_scope_name(base_id: u64, nm: &str) -> u64 {
        let mut reg1 = (base_id >> 32) as u32;
        let mut reg2 = base_id as u32;
        reg1 = crc_update(reg1, 0xa9);
        reg2 = crc_update(reg2, reg1);
        for &byte in nm.as_bytes() {
            let val = byte as i8 as i32 as u32;
            reg1 = crc_update(reg1, val);
            reg2 = crc_update(reg2, reg1);
        }
        ((reg1 as u64) << 32) | (reg2 as u64)
    }

    pub fn get_range_tree(&self) -> &RangeList {
        &self.rangetree
    }

    pub fn set_display_name(&mut self, nm: &str) {
        self.display_name = nm.to_string();
    }

    pub fn turn_on_debug(&mut self) {
        self.debugon = true;
    }

    pub fn turn_off_debug(&mut self) {
        self.debugon = false;
    }

    pub fn restrict_scope(&mut self, address: Address) {
        self.fd = Some(address);
    }

    pub fn add_range(&mut self, spc: &SpaceRef, first: u64, last: u64) {
        self.rangetree.insert_range(spc, first, last);
    }

    pub fn remove_range(&mut self, spc: &SpaceRef, first: u64, last: u64) {
        self.rangetree.remove_range(spc, first, last);
    }

    pub fn in_scope(&self, addr: &Address, size: i32, _usepoint: &Address) -> bool {
        self.rangetree.in_range(addr, size as u64)
    }

    pub fn get_name(&self) -> &str {
        &self.name
    }

    pub fn get_display_name(&self) -> &str {
        &self.display_name
    }

    pub fn get_id(&self) -> u64 {
        self.unique_id
    }

    pub fn is_global(&self) -> bool {
        self.fd.is_none()
    }

    pub fn get_function(&self) -> Option<&Address> {
        self.fd.as_ref()
    }

    pub fn get_parent(&self) -> Option<ScopeId> {
        self.parent
    }

    pub fn children(&self) -> &ScopeMap {
        &self.children
    }

    pub fn print_bounds(&self, out: &mut String) {
        self.rangetree.print_bounds(out);
    }

    pub fn begin_multi_entry(&self) -> impl Iterator<Item = SymbolId> + '_ {
        self.multi_entry_set.values().copied()
    }

    pub fn is_local(&self) -> bool {
        matches!(self.kind, ScopeKind::Local(_))
    }

    pub fn local_data(&self) -> &ScopeLocalData {
        match &self.kind {
            ScopeKind::Local(data) => data,
            ScopeKind::Internal => panic!("scope is not a local scope"),
        }
    }

    pub fn local_data_mut(&mut self) -> &mut ScopeLocalData {
        match &mut self.kind {
            ScopeKind::Local(data) => data,
            ScopeKind::Internal => panic!("scope is not a local scope"),
        }
    }

    fn entry_map(&self, addr: &Address) -> Option<&EntryMap> {
        let index = space_index(addr)?;
        self.maptable.get(index).and_then(|slot| slot.as_deref())
    }
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, PartialOrd, Ord)]
pub struct NullSubsort;

impl RangeSubsort for NullSubsort {
    fn from_bool(_val: bool) -> NullSubsort {
        NullSubsort
    }
}

#[derive(Clone, Debug)]
pub struct ScopeMapper {
    pub scope: ScopeId,
    pub first: Address,
    pub last: Address,
}

impl ScopeMapper {
    pub fn new(data: &ScopeId, first: &Address, last: &Address) -> ScopeMapper {
        ScopeMapper {
            scope: *data,
            first: first.clone(),
            last: last.clone(),
        }
    }

    pub fn get_scope(&self) -> ScopeId {
        self.scope
    }
}

impl RangeRecord for ScopeMapper {
    type Line = Address;
    type Subsort = NullSubsort;
    type Init = ScopeId;

    fn new_record(data: &ScopeId, first: Address, last: Address) -> ScopeMapper {
        ScopeMapper::new(data, &first, &last)
    }

    fn get_first(&self) -> Address {
        self.first.clone()
    }

    fn get_last(&self) -> Address {
        self.last.clone()
    }

    fn get_subsort(&self) -> NullSubsort {
        NullSubsort
    }
}

pub type ScopeResolve = RangeMap<ScopeMapper>;

pub struct Database {
    pub scopes: Arena<ScopeId, Scope>,
    pub symbols: Arena<SymbolId, Symbol>,
    pub entries: Arena<EntryId, SymbolEntry>,
    pub globalscope: Option<ScopeId>,
    pub resolvemap: ScopeResolve,
    pub idmap: ScopeMap,
    pub flagbase: PartMap<Address, u32>,
    pub id_by_name_hash: bool,
}

impl Database {
    pub fn new(id_by_name: bool) -> Database {
        Database {
            scopes: Arena::new(),
            symbols: Arena::new(),
            entries: Arena::new(),
            globalscope: None,
            resolvemap: RangeMap::new(),
            idmap: BTreeMap::new(),
            flagbase: PartMap::new(),
            id_by_name_hash: id_by_name,
        }
    }

    pub fn scope(&self, id: ScopeId) -> &Scope {
        self.scopes.get(id)
    }

    pub fn scope_mut(&mut self, id: ScopeId) -> &mut Scope {
        self.scopes.get_mut(id)
    }

    pub fn symbol(&self, id: SymbolId) -> &Symbol {
        self.symbols.get(id)
    }

    pub fn symbol_mut(&mut self, id: SymbolId) -> &mut Symbol {
        self.symbols.get_mut(id)
    }

    pub fn entry(&self, id: EntryId) -> &SymbolEntry {
        self.entries.get(id)
    }

    pub fn entry_mut(&mut self, id: EntryId) -> &mut SymbolEntry {
        self.entries.get_mut(id)
    }

    fn scope_owner(&self, scope: ScopeId) -> ScopeId {
        self.scope(scope).owner.unwrap_or(scope)
    }

    fn symbol_type_size(&self, sym: SymbolId, types: &TypeFactory) -> i32 {
        types.get(self.symbol(sym).type_id()).get_size()
    }

    pub fn entry_get_all_flags(&self, entry: EntryId) -> u32 {
        let record = self.entry(entry);
        record.extraflags | self.symbol(record.symbol).get_flags()
    }

    pub fn entry_is_addr_tied(&self, entry: EntryId) -> bool {
        (self.symbol(self.entry(entry).symbol).get_flags() & Varnode::ADDRTIED) != 0
    }

    pub fn entry_in_use(&self, entry: EntryId, usepoint: &Address) -> bool {
        self.entry(entry).in_use(self, usepoint)
    }

    pub fn entry_update_type(
        glb: &mut Architecture,
        entry: EntryId,
        data: &mut Funcdata,
        vn: VarnodeId,
    ) -> Result<bool> {
        let sym = db_ref(glb).entry(entry).symbol;
        if (db_ref(glb).symbol(sym).get_flags() & Varnode::TYPELOCK) != 0 {
            let addr = data.vn(vn).get_addr().clone();
            let size = data.vn(vn).get_size();
            if let Some(dt) = Database::entry_get_sized_type(glb, entry, &addr, size)? {
                return Ok(data.vn_update_type_locked(vn, dt, true, true, glb));
            }
        }
        Ok(false)
    }

    pub fn entry_get_sized_type(
        glb: &mut Architecture,
        entry: EntryId,
        addr: &Address,
        sz: i32,
    ) -> Result<Option<TypeId>> {
        let (db, types) = db_and_types(glb);
        let record = db.entry(entry);
        let cur = db.symbol(record.symbol).type_id();
        let off = match &record.kind {
            SymbolEntryKind::Dynamic { .. } => record.offset,
            SymbolEntryKind::Map { addr: entryaddr, .. } | SymbolEntryKind::Conflict { addr: entryaddr, .. } => {
                (addr.get_offset().wrapping_sub(entryaddr.get_offset()) as i32).wrapping_add(record.offset)
            }
        };
        types.get_exact_piece(cur, off, sz)
    }

    pub fn entry_print_entry(&self, entry: EntryId, out: &mut String, types: &TypeFactory) {
        let record = self.entry(entry);
        let sym = self.symbol(record.symbol);
        let tp = types.get(sym.type_id());
        match &record.kind {
            SymbolEntryKind::Map { addr, .. } | SymbolEntryKind::Conflict { addr, .. } => {
                out.push_str(sym.get_name());
                out.push_str(" : ");
                out.push(addr.get_shortcut());
                addr.print_raw(out);
                out.push_str(&format!(":{}", tp.get_size() as u32));
                out.push(' ');
                tp.print_raw(out, types);
                out.push_str(" : ");
                record.uselimit.print_bounds(out);
                if record.is_conflict() {
                    out.push_str(" (conflicts)");
                }
            }
            SymbolEntryKind::Dynamic { .. } => {
                out.push_str(sym.get_name());
                out.push_str(" : <dynamic>:");
                out.push_str(&format!("{}", tp.get_size() as u32));
                out.push(' ');
                tp.print_raw(out, types);
                out.push_str(" : ");
                record.uselimit.print_bounds(out);
            }
        }
    }

    pub fn symbol_get_first_whole_map(&self, sym: SymbolId) -> Result<EntryId> {
        let symbol = self.symbol(sym);
        symbol
            .mapentry
            .first()
            .copied()
            .ok_or_else(|| Error::Lowlevel(format!("No mapping for symbol: {}", symbol.name)))
    }

    pub fn symbol_get_map_entry(&self, sym: SymbolId, addr: &Address) -> Result<Option<EntryId>> {
        for &entry in self.symbol(sym).mapentry.iter() {
            let record = self.entry(entry);
            if record.is_dynamic() {
                continue;
            }
            let entryaddr = record.get_addr();
            if !same_space(addr, entryaddr) {
                continue;
            }
            if addr.get_offset() < entryaddr.get_offset() {
                continue;
            }
            let diff = addr.get_offset().wrapping_sub(entryaddr.get_offset()) as i32;
            if diff >= record.get_size() {
                continue;
            }
            return Ok(Some(entry));
        }
        Ok(None)
    }

    pub fn symbol_get_resolution_depth(&mut self, sym: SymbolId, use_scope: Option<ScopeId>) -> i32 {
        let scope = self.symbol(sym).scope;
        if Some(scope) == use_scope {
            return 0;
        }
        let Some(use_scope) = use_scope else {
            let mut point = Some(scope);
            let mut count = 0;
            while let Some(current) = point {
                count += 1;
                point = self.scope(current).get_parent();
            }
            return count - 1;
        };
        if self.symbol(sym).depth_scope == Some(use_scope) {
            return self.symbol(sym).depth_resolution;
        }
        let distinguish_scope = self.scope_find_distinguishing_scope(scope, use_scope);
        let mut depth_resolution = 0;
        let distinguish_name: String;
        let terminating_scope: Option<ScopeId>;
        match distinguish_scope {
            None => {
                distinguish_name = self.symbol(sym).name.clone();
                terminating_scope = Some(scope);
            }
            Some(distinguish) => {
                distinguish_name = self.scope(distinguish).name.clone();
                let mut current_scope = Some(scope);
                while current_scope != Some(distinguish) {
                    depth_resolution += 1;
                    current_scope = current_scope.and_then(|current| self.scope(current).get_parent());
                }
                depth_resolution += 1;
                terminating_scope = self.scope(distinguish).get_parent();
            }
        }
        if self.scope_is_name_used(use_scope, &distinguish_name, terminating_scope) {
            depth_resolution += 1;
        }
        let symbol = self.symbol_mut(sym);
        symbol.depth_scope = Some(use_scope);
        symbol.depth_resolution = depth_resolution;
        depth_resolution
    }

    pub fn symbol_encode_body(glb: &Architecture, sym: SymbolId, encoder: &mut dyn Encoder) -> Result<()> {
        let types = types_ref(glb);
        let tp = db_ref(glb).symbol(sym).type_id();
        types.get(tp).encode_ref(encoder, glb)
    }

    pub fn symbol_decode_body(glb: &mut Architecture, sym: SymbolId, decoder: &mut dyn Decoder) -> Result<()> {
        let tp = TypeFactory::decode_type(glb, decoder)?;
        let (db, types) = db_and_types(glb);
        let symbol = db.symbol_mut(sym);
        symbol.tp = Some(tp);
        symbol.check_size_type_lock(types);
        Ok(())
    }

    pub fn symbol_encode(glb: &Architecture, sym: SymbolId, encoder: &mut dyn Encoder) -> Result<()> {
        let symbol = db_ref(glb).symbol(sym);
        match &symbol.kind {
            SymbolKind::Base => {
                encoder.open_element(ELEM_SYMBOL);
                symbol.encode_header(encoder)?;
                Database::symbol_encode_body(glb, sym, encoder)?;
                encoder.close_element(ELEM_SYMBOL);
            }
            SymbolKind::Function { fd, .. } => match fd {
                Some(fd) => fd.encode_no_tree(encoder, symbol.symbol_id, true, glb)?,
                None => {
                    encoder.open_element(ELEM_FUNCTIONSHELL);
                    encoder.write_string(ATTRIB_NAME, &symbol.name);
                    if symbol.symbol_id != 0 {
                        encoder.write_unsigned_integer(ATTRIB_ID, symbol.symbol_id);
                    }
                    encoder.close_element(ELEM_FUNCTIONSHELL);
                }
            },
            SymbolKind::Equate { value } => {
                encoder.open_element(ELEM_EQUATESYMBOL);
                symbol.encode_header(encoder)?;
                encoder.open_element(ELEM_VALUE);
                encoder.write_unsigned_integer(ATTRIB_CONTENT, *value);
                encoder.close_element(ELEM_VALUE);
                encoder.close_element(ELEM_EQUATESYMBOL);
            }
            SymbolKind::UnionFacet { field_num, .. } => {
                encoder.open_element(ELEM_FACETSYMBOL);
                symbol.encode_header(encoder)?;
                encoder.write_signed_integer(ATTRIB_FIELD, *field_num as i64);
                encoder.write_bool(ATTRIB_ADDRTIED, true);
                Database::symbol_encode_body(glb, sym, encoder)?;
                encoder.close_element(ELEM_FACETSYMBOL);
            }
            SymbolKind::Label => {
                encoder.open_element(ELEM_LABELSYM);
                symbol.encode_header(encoder)?;
                encoder.close_element(ELEM_LABELSYM);
            }
            SymbolKind::ExternRef { refaddr } => {
                encoder.open_element(ELEM_EXTERNREFSYMBOL);
                encoder.write_string(ATTRIB_NAME, &symbol.name);
                refaddr.encode(encoder)?;
                encoder.close_element(ELEM_EXTERNREFSYMBOL);
            }
        }
        Ok(())
    }

    fn symbol_decode_header(glb: &mut Architecture, sym: SymbolId, decoder: &mut dyn Decoder) -> Result<()> {
        db_mut(glb).symbol_mut(sym).decode_header(decoder)
    }

    pub fn symbol_decode(glb: &mut Architecture, sym: SymbolId, decoder: &mut dyn Decoder) -> Result<()> {
        enum Flavor {
            Base,
            Function,
            Equate,
            UnionFacet,
            Label,
            ExternRef,
        }
        let flavor = match &db_ref(glb).symbol(sym).kind {
            SymbolKind::Base => Flavor::Base,
            SymbolKind::Function { .. } => Flavor::Function,
            SymbolKind::Equate { .. } => Flavor::Equate,
            SymbolKind::UnionFacet { .. } => Flavor::UnionFacet,
            SymbolKind::Label => Flavor::Label,
            SymbolKind::ExternRef { .. } => Flavor::ExternRef,
        };
        match flavor {
            Flavor::Base => {
                let elem_id = decoder.open_element_expect(ELEM_SYMBOL)?;
                Database::symbol_decode_header(glb, sym, decoder)?;
                Database::symbol_decode_body(glb, sym, decoder)?;
                decoder.close_element(elem_id)
            }
            Flavor::Function => Database::function_symbol_decode(glb, sym, decoder),
            Flavor::Equate => {
                let elem_id = decoder.open_element_expect(ELEM_EQUATESYMBOL)?;
                Database::symbol_decode_header(glb, sym, decoder)?;
                let sub_id = decoder.open_element_expect(ELEM_VALUE)?;
                let val = decoder.read_unsigned_integer_attr(ATTRIB_CONTENT)?;
                decoder.close_element(sub_id)?;
                let (db, types) = db_and_types(glb);
                let tp = types.get_base(1, TypeMetatype::Unknown)?;
                let symbol = db.symbol_mut(sym);
                symbol.kind = SymbolKind::Equate { value: val };
                symbol.tp = Some(tp);
                decoder.close_element(elem_id)
            }
            Flavor::UnionFacet => {
                let elem_id = decoder.open_element_expect(ELEM_FACETSYMBOL)?;
                Database::symbol_decode_header(glb, sym, decoder)?;
                let field_num = decoder.read_signed_integer_attr(ATTRIB_FIELD)? as i32;
                let addr_based = decoder.read_bool_attr(ATTRIB_ADDRTIED)?;
                db_mut(glb).symbol_mut(sym).kind = SymbolKind::UnionFacet { field_num, addr_based };
                Database::symbol_decode_body(glb, sym, decoder)?;
                decoder.close_element(elem_id)?;
                let types = types_ref(glb);
                let mut test_type = db_ref(glb).symbol(sym).type_id();
                if types.get(test_type).get_metatype() == TypeMetatype::Ptr {
                    test_type = types.get(test_type).get_ptr_to();
                }
                if types.get(test_type).get_metatype() != TypeMetatype::Union {
                    return Err(Error::Lowlevel(
                        "<unionfacetsymbol> does not have a union type".to_string(),
                    ));
                }
                if field_num < -1 || field_num >= types.get(test_type).num_depend(types) {
                    return Err(Error::Lowlevel(
                        "<unionfacetsymbol> field attribute is out of bounds".to_string(),
                    ));
                }
                Ok(())
            }
            Flavor::Label => {
                let elem_id = decoder.open_element_expect(ELEM_LABELSYM)?;
                Database::symbol_decode_header(glb, sym, decoder)?;
                decoder.close_element(elem_id)
            }
            Flavor::ExternRef => {
                let elem_id = decoder.open_element_expect(ELEM_EXTERNREFSYMBOL)?;
                let mut name = String::new();
                let mut display_name = String::new();
                loop {
                    let attrib_id = decoder.get_next_attribute_id()?;
                    if attrib_id == 0 {
                        break;
                    }
                    if attrib_id == ATTRIB_NAME {
                        name = decoder.read_string()?;
                    } else if attrib_id == ATTRIB_LABEL {
                        display_name = decoder.read_string()?;
                    }
                }
                let refaddr = Address::decode(decoder)?;
                decoder.close_element(elem_id)?;
                let (db, types) = db_and_types(glb);
                let symbol = db.symbol_mut(sym);
                symbol.name = name;
                symbol.display_name = display_name;
                symbol.kind = SymbolKind::ExternRef { refaddr };
                symbol.build_extern_ref_name_type(types)
            }
        }
    }

    fn function_symbol_decode(glb: &mut Architecture, sym: SymbolId, decoder: &mut dyn Decoder) -> Result<()> {
        let elem_id = decoder.peek_element()?;
        if elem_id == ELEM_FUNCTION {
            let scope = db_ref(glb).symbol(sym).scope;
            let mut fd = Box::new(Funcdata::new(
                "",
                "",
                Some(scope),
                &Address::invalid(),
                Some(sym),
                0,
                glb,
            )?);
            let symbol_id = match fd.decode(decoder, glb) {
                Ok(id) => id,
                Err(err) => {
                    let failure = if err.is_recov() {
                        Error::DuplicateFunction {
                            address: fd.get_address().to_string(),
                            function_name: fd.get_name().to_string(),
                        }
                    } else {
                        err
                    };
                    if let Some(local) = fd.get_scope_local() {
                        let db = db_mut(glb);
                        if db.scopes.contains(local) {
                            let _ = db.delete_scope(local);
                        }
                    }
                    return Err(failure);
                }
            };
            let symbol = db_mut(glb).symbol_mut(sym);
            symbol.symbol_id = symbol_id;
            symbol.name = fd.get_name().to_string();
            symbol.display_name = fd.get_display_name().to_string();
            if let SymbolKind::Function { fd: slot, consume_size } = &mut symbol.kind {
                if *consume_size < fd.get_size() && fd.get_size() > 1 && fd.get_size() <= 8 {
                    *consume_size = fd.get_size();
                }
                *slot = Some(fd);
            }
            Ok(())
        } else {
            decoder.open_element()?;
            let symbol = db_mut(glb).symbol_mut(sym);
            symbol.symbol_id = 0;
            loop {
                let attrib_id = decoder.get_next_attribute_id()?;
                if attrib_id == 0 {
                    break;
                }
                if attrib_id == ATTRIB_NAME {
                    symbol.name = decoder.read_string()?;
                } else if attrib_id == ATTRIB_ID {
                    symbol.symbol_id = decoder.read_unsigned_integer()?;
                } else if attrib_id == ATTRIB_LABEL {
                    symbol.display_name = decoder.read_string()?;
                }
            }
            decoder.close_element(elem_id)
        }
    }

    pub fn symbol_get_function(glb: &mut Architecture, sym: SymbolId) -> Result<Option<&mut Funcdata>> {
        let (needs_creation, name, display_name, scope) = {
            let symbol = db_ref(glb).symbol(sym);
            match &symbol.kind {
                SymbolKind::Function { fd, .. } => (
                    fd.is_none() && !symbol.function_checked_out,
                    symbol.name.clone(),
                    symbol.display_name.clone(),
                    symbol.scope,
                ),
                _ => return Ok(None),
            }
        };
        if needs_creation {
            let db = db_ref(glb);
            let entry = db.symbol_get_first_whole_map(sym)?;
            let addr = db.entry(entry).get_addr().clone();
            let fd = Box::new(Funcdata::new(
                &name,
                &display_name,
                Some(scope),
                &addr,
                Some(sym),
                0,
                glb,
            )?);
            if let SymbolKind::Function { fd: slot, .. } = &mut db_mut(glb).symbol_mut(sym).kind {
                *slot = Some(fd);
            }
        }
        match &mut db_mut(glb).symbol_mut(sym).kind {
            SymbolKind::Function { fd, .. } => Ok(fd.as_deref_mut()),
            _ => Ok(None),
        }
    }

    pub fn symbol_take_function(&mut self, sym: SymbolId) -> Option<Box<Funcdata>> {
        let symbol = self.symbol_mut(sym);
        let taken = match &mut symbol.kind {
            SymbolKind::Function { fd, .. } => fd.take(),
            _ => None,
        };
        if taken.is_some() {
            symbol.function_checked_out = true;
        }
        taken
    }

    pub fn symbol_restore_function(&mut self, sym: SymbolId, function: Box<Funcdata>) {
        let symbol = self.symbol_mut(sym);
        if let SymbolKind::Function { fd, .. } = &mut symbol.kind {
            *fd = Some(function);
        }
        symbol.function_checked_out = false;
    }

    pub fn scope_attach_scope(&mut self, scope: ScopeId, child: ScopeId) -> Result<()> {
        let unique_id = self.scope(child).unique_id;
        self.scope_mut(child).parent = Some(scope);
        self.scope_mut(scope).children.insert(unique_id, child);
        Ok(())
    }

    pub fn scope_detach_scope(&mut self, scope: ScopeId, child_key: u64) {
        if let Some(child) = self.scope_mut(scope).children.remove(&child_key) {
            self.destroy_scope_tree(child);
        }
    }

    fn destroy_symbol(&mut self, sym: SymbolId) {
        let symbol = self.symbols.remove(sym);
        for entry in symbol.mapentry.iter() {
            if self.entries.contains(*entry) {
                self.entries.remove(*entry);
            }
        }
        if let SymbolKind::Function { fd: Some(fd), .. } = symbol.kind
            && let Some(local) = fd.get_scope_local()
            && self.scopes.contains(local)
        {
            let _ = self.delete_scope(local);
        }
    }

    fn destroy_scope_tree(&mut self, scope: ScopeId) {
        let symbols: Vec<SymbolId> = self.scope(scope).nametree.values().copied().collect();
        for sym in symbols {
            self.destroy_symbol(sym);
        }
        let children: Vec<ScopeId> = self.scope(scope).children.values().copied().collect();
        for child in children {
            self.destroy_scope_tree(child);
        }
        self.scopes.remove(scope);
    }

    fn scope_chain(&self, start: Option<ScopeId>, stop: Option<ScopeId>) -> impl Iterator<Item = ScopeId> + '_ {
        std::iter::successors(start, move |scope| self.scope(*scope).get_parent())
            .take_while(move |scope| Some(*scope) != stop)
    }

    pub fn scope_stack_addr(
        &self,
        scope1: ScopeId,
        scope2: Option<ScopeId>,
        addr: &Address,
        usepoint: &Address,
        addrmatch: &mut Option<EntryId>,
    ) -> Option<ScopeId> {
        if addr.is_constant() {
            return None;
        }
        for scope in self.scope_chain(Some(scope1), scope2) {
            if let Some(entry) = self.scope_find_addr(scope, addr, usepoint) {
                *addrmatch = Some(entry);
                return Some(scope);
            }
            if self.scope(scope).in_scope(addr, 1, usepoint) {
                return Some(scope);
            }
        }
        None
    }

    pub fn scope_stack_container(
        &self,
        scope1: ScopeId,
        scope2: Option<ScopeId>,
        addr: &Address,
        size: i32,
        usepoint: &Address,
        addrmatch: &mut Option<EntryId>,
    ) -> Option<ScopeId> {
        if addr.is_constant() {
            return None;
        }
        for scope in self.scope_chain(Some(scope1), scope2) {
            if let Some(entry) = self.scope_find_container(scope, addr, size, usepoint) {
                *addrmatch = Some(entry);
                return Some(scope);
            }
            if self.scope(scope).in_scope(addr, size, usepoint) {
                return Some(scope);
            }
        }
        None
    }

    pub fn scope_stack_closest_fit(
        &self,
        scope1: ScopeId,
        scope2: Option<ScopeId>,
        addr: &Address,
        size: i32,
        usepoint: &Address,
        addrmatch: &mut Option<EntryId>,
    ) -> Option<ScopeId> {
        if addr.is_constant() {
            return None;
        }
        for scope in self.scope_chain(Some(scope1), scope2) {
            if let Some(entry) = self.scope_find_closest_fit(scope, addr, size, usepoint) {
                *addrmatch = Some(entry);
                return Some(scope);
            }
            if self.scope(scope).in_scope(addr, size, usepoint) {
                return Some(scope);
            }
        }
        None
    }

    pub fn scope_stack_function(
        &self,
        scope1: ScopeId,
        scope2: Option<ScopeId>,
        addr: &Address,
        addrmatch: &mut Option<SymbolId>,
    ) -> Option<ScopeId> {
        if addr.is_constant() {
            return None;
        }
        for scope in self.scope_chain(Some(scope1), scope2) {
            if let Some(sym) = self.scope_find_function(scope, addr) {
                *addrmatch = Some(sym);
                return Some(scope);
            }
            if self.scope(scope).in_scope(addr, 1, &Address::invalid()) {
                return Some(scope);
            }
        }
        None
    }

    pub fn scope_stack_external_ref(
        &self,
        scope1: ScopeId,
        scope2: Option<ScopeId>,
        addr: &Address,
        addrmatch: &mut Option<SymbolId>,
    ) -> Option<ScopeId> {
        if addr.is_constant() {
            return None;
        }
        for scope in self.scope_chain(Some(scope1), scope2) {
            if let Some(sym) = self.scope_find_external_ref(scope, addr) {
                *addrmatch = Some(sym);
                return Some(scope);
            }
        }
        None
    }

    pub fn scope_stack_code_label(
        &self,
        scope1: ScopeId,
        scope2: Option<ScopeId>,
        addr: &Address,
        addrmatch: &mut Option<SymbolId>,
    ) -> Option<ScopeId> {
        if addr.is_constant() {
            return None;
        }
        for scope in self.scope_chain(Some(scope1), scope2) {
            if let Some(sym) = self.scope_find_code_label(scope, addr) {
                *addrmatch = Some(sym);
                return Some(scope);
            }
            if self.scope(scope).in_scope(addr, 1, &Address::invalid()) {
                return Some(scope);
            }
        }
        None
    }

    pub fn scope_build_sub_scope(&mut self, _scope: ScopeId, id: u64, nm: &str, num_spaces: i32) -> ScopeId {
        self.scopes.alloc(Scope::new_internal(id, nm, num_spaces))
    }

    pub fn scope_add_symbol_internal(&mut self, scope: ScopeId, sym: SymbolId, types: &TypeFactory) -> Result<()> {
        if self.symbol(sym).symbol_id == 0 {
            let unique_id = self.scope(scope).unique_id;
            let next = self.scope(scope).next_unique_id;
            self.symbol_mut(sym).symbol_id = Symbol::ID_BASE
                .wrapping_add((unique_id & 0xffff) << 40)
                .wrapping_add(next);
            self.scope_mut(scope).next_unique_id = next.wrapping_add(1);
        }
        let res = self.scope_add_symbol_internal_body(scope, sym, types);
        if let Err(err) = res {
            if err.is_lowlevel() {
                self.destroy_symbol(sym);
            }
            return Err(err);
        }
        Ok(())
    }

    fn scope_add_symbol_internal_body(&mut self, scope: ScopeId, sym: SymbolId, types: &TypeFactory) -> Result<()> {
        if self.symbol(sym).name.is_empty() {
            let name = self.scope_build_undefined_name(scope)?;
            let symbol = self.symbol_mut(sym);
            symbol.name = name.clone();
            symbol.display_name = name;
        }
        let Some(tp) = self.symbol(sym).tp else {
            return Err(Error::Lowlevel(format!(
                "{} symbol created with no type",
                self.symbol(sym).name
            )));
        };
        if types.get(tp).get_size() < 1 {
            return Err(Error::Lowlevel(format!(
                "{} symbol created with zero size type",
                self.symbol(sym).name
            )));
        }
        self.scope_insert_name_tree(scope, sym)?;
        let category = self.symbol(sym).category;
        if category >= 0 {
            let cat = category as usize;
            let catlist = &mut self.scopes.get_mut(scope).category;
            while catlist.len() <= cat {
                catlist.push(Vec::new());
            }
            let list = &mut catlist[cat];
            let symbol = self.symbols.get_mut(sym);
            if category > 0 {
                symbol.catindex = list.len() as u16;
            }
            while list.len() <= symbol.catindex as usize {
                list.push(None);
            }
            list[symbol.catindex as usize] = Some(sym);
        }
        Ok(())
    }

    fn note_whole_entry(&mut self, scope: ScopeId, sym: SymbolId, entry_size: i32, types: &TypeFactory) {
        if entry_size == self.symbol_type_size(sym, types) {
            let symbol = self.symbols.get_mut(sym);
            symbol.whole_count += 1;
            if symbol.whole_count == 2 {
                let key = SymbolNameKey::of(symbol);
                self.scopes.get_mut(scope).multi_entry_set.entry(key).or_insert(sym);
            }
        }
    }

    pub fn scope_add_map_internal(
        &mut self,
        scope: ScopeId,
        sym: SymbolId,
        entry: EntryId,
        types: &TypeFactory,
    ) -> Result<()> {
        self.symbol_mut(sym).mapentry.push(entry);
        let entryaddr = self.entry(entry).get_addr().clone();
        let entry_size = self.entry(entry).size;
        let index = space_index(&entryaddr).expect("symbol entry address has no space");
        {
            let maptable = &mut self.scope_mut(scope).maptable;
            if maptable.len() <= index {
                maptable.resize_with(index + 1, || None);
            }
            if maptable[index].is_none() {
                maptable[index] = Some(Box::new(EntryMap::new()));
            }
        }
        let lastaddress = entryaddr.add((entry_size as i64).wrapping_sub(1));
        if lastaddress.get_offset() < entryaddr.get_offset() {
            return Err(Error::Lowlevel(format!(
                "Symbol {} extends beyond the end of the address space",
                self.symbol(sym).name
            )));
        }
        let subsort = SymbolRange::compute_subsort(self, entry)?;
        let init = SymbolRangeInit { entry, subsort };
        let record = self.scopes.get_mut(scope).maptable[index]
            .as_mut()
            .expect("entry map created above")
            .insert(&init, entryaddr.get_offset(), lastaddress.get_offset());
        self.entry_mut(entry).set_map_iterator(Some(record));
        self.note_whole_entry(scope, sym, entry_size, types);
        Ok(())
    }

    pub fn scope_add_dynamic_map_internal(
        &mut self,
        scope: ScopeId,
        sym: SymbolId,
        entry: EntryId,
        types: &TypeFactory,
    ) {
        self.symbol_mut(sym).mapentry.push(entry);
        self.scope_mut(scope).dynamicentry.push(entry);
        let entry_size = self.entry(entry).size;
        self.note_whole_entry(scope, sym, entry_size, types);
    }

    pub fn scope_add_map(glb: &mut Architecture, scope: ScopeId, entry: SymbolEntry) -> Result<EntryId> {
        let mut entry = entry;
        let sym = entry.symbol;
        let (db, types) = db_and_types(glb);
        if db.scope(scope).is_global() {
            db.symbol_mut(sym).flags |= Varnode::PERSIST;
        }
        let glb_scope = db.globalscope.expect("database has no global scope");
        let entryaddr = entry.get_addr().clone();
        if db.scope(glb_scope).in_scope(&entryaddr, 1, &Address::invalid()) {
            db.symbol_mut(sym).flags |= Varnode::PERSIST;
            entry.uselimit.clear();
        }
        entry.extraflags = Varnode::MAPPED;
        entry.offset = 0;
        entry.size = db.symbol(sym).get_bytes_consumed(types);
        if entry.uselimit.empty() {
            let property = db.get_property(&entryaddr);
            let symbol = db.symbol_mut(sym);
            symbol.flags |= Varnode::ADDRTIED;
            symbol.flags |= property;
        }
        let uselimit = entry.uselimit.clone();
        let entry_id = db.entries.alloc(entry);
        db.scope_add_map_internal(scope, sym, entry_id, types)?;
        if entryaddr.is_join() {
            let rec = glb.manager.find_join(entryaddr.get_offset())?;
            let (db, types) = db_and_types(glb);
            let num = rec.num_pieces();
            let mut off: u64 = 0;
            let bigendian = entryaddr.is_big_endian();
            let primitive_whole = types.get(db.symbol(sym).type_id()).is_primitive_whole(types);
            for position in 0..num {
                let piece_index = if bigendian { position } else { num - 1 - position };
                let vdat: &VarnodeData = rec.get_piece(piece_index);
                let mut exfl = 0;
                if primitive_whole {
                    if piece_index == 0 {
                        exfl = Varnode::PRECISHI;
                    } else if piece_index == num - 1 {
                        exfl = Varnode::PRECISLO;
                    } else {
                        exfl = Varnode::PRECISLO | Varnode::PRECISHI;
                    }
                }
                let mut piece =
                    SymbolEntry::new_map(sym, exfl, &vdat.get_addr(), vdat.size as i32, off as i32, &uselimit);
                piece.is_piece = true;
                let piece_id = db.entries.alloc(piece);
                db.scope_add_map_internal(scope, sym, piece_id, types)?;
                off = off.wrapping_add(vdat.size as u64);
            }
        }
        Ok(entry_id)
    }

    pub fn scope_add_dynamic(&mut self, scope: ScopeId, entry: SymbolEntry, types: &TypeFactory) -> Result<EntryId> {
        let mut entry = entry;
        let sym = entry.symbol;
        if self.scope(scope).is_global() {
            self.symbol_mut(sym).flags |= Varnode::PERSIST;
        }
        entry.size = self.symbol(sym).get_bytes_consumed(types);
        entry.extraflags = Varnode::MAPPED;
        entry.offset = 0;
        let entry_id = self.entries.alloc(entry);
        self.scope_add_dynamic_map_internal(scope, sym, entry_id, types);
        Ok(entry_id)
    }

    pub fn scope_set_symbol_id(&mut self, sym: SymbolId, id: u64) {
        self.symbol_mut(sym).symbol_id = id;
    }

    pub fn scope_begin(&self, scope: ScopeId) -> MapIterator {
        let current = self.scope(scope);
        let len = current.maptable.len();
        let mut iter = 0;
        while iter != len && current.maptable[iter].is_none() {
            iter += 1;
        }
        let mut res = MapIterator::new(iter, None);
        if iter != len {
            res.curiter = current.maptable[iter]
                .as_ref()
                .expect("map slot checked above")
                .list_front();
            if res.curiter.is_none() {
                res.skip_empty(current);
            }
        }
        res
    }

    pub fn scope_end(&self, scope: ScopeId) -> MapIterator {
        MapIterator::new(self.scope(scope).maptable.len(), None)
    }

    pub fn scope_dynamic_entries(&self, scope: ScopeId) -> &[EntryId] {
        &self.scope(scope).dynamicentry
    }

    fn name_first(&self, scope: ScopeId) -> Option<SymbolNameKey> {
        self.scope(scope).nametree.keys().next().cloned()
    }

    fn name_next(&self, scope: ScopeId, key: &SymbolNameKey) -> Option<SymbolNameKey> {
        name_upper_bound(&self.scope(scope).nametree, key)
    }

    fn name_symbol(&self, scope: ScopeId, key: &SymbolNameKey) -> SymbolId {
        self.scope(scope).nametree[key]
    }

    pub fn scope_clear(&mut self, scope: ScopeId) {
        let mut iter = self.name_first(scope);
        while let Some(key) = iter {
            let sym = self.name_symbol(scope, &key);
            iter = self.name_next(scope, &key);
            self.scope_remove_symbol(scope, sym);
        }
        self.scope_mut(scope).next_unique_id = 0;
    }

    pub fn scope_category_sanity(&mut self, scope: ScopeId) {
        let num_categories = self.scope(scope).category.len();
        for cat in 0..num_categories {
            let list = self.scope(scope).category[cat].clone();
            if list.is_empty() {
                continue;
            }
            if list.iter().any(|slot| slot.is_none()) {
                for sym in list.into_iter().flatten() {
                    self.scope_set_category(scope, sym, Symbol::NO_CATEGORY as i32, 0);
                }
            }
        }
    }

    pub fn scope_clear_category(&mut self, scope: ScopeId, cat: i32) {
        if cat >= 0 {
            let cat = cat as usize;
            if cat >= self.scope(scope).category.len() {
                return;
            }
            let size = self.scope(scope).category[cat].len();
            for index in 0..size {
                let slot = self.scope(scope).category[cat].get(index).copied().flatten();
                if let Some(sym) = slot {
                    self.scope_remove_symbol(scope, sym);
                }
            }
        } else {
            let mut iter = self.name_first(scope);
            while let Some(key) = iter {
                let sym = self.name_symbol(scope, &key);
                iter = self.name_next(scope, &key);
                if self.symbol(sym).get_category() >= 0 {
                    continue;
                }
                self.scope_remove_symbol(scope, sym);
            }
        }
    }

    pub fn scope_clear_unlocked(&mut self, scope: ScopeId, types: &mut TypeFactory) -> Result<()> {
        let mut iter = self.name_first(scope);
        while let Some(key) = iter {
            let sym = self.name_symbol(scope, &key);
            iter = self.name_next(scope, &key);
            if self.symbol(sym).is_type_locked() {
                if !self.symbol(sym).is_name_locked() && !self.symbol(sym).is_name_undefined() {
                    let newname = self.scope_build_undefined_name(scope)?;
                    self.scope_rename_symbol(scope, sym, &newname)?;
                }
                self.scope_clear_attribute(types, scope, sym, Varnode::NOLOCALALIAS);
                if self.symbol(sym).is_size_type_locked() {
                    self.reset_size_lock_type_internal(sym, types)?;
                }
            } else if self.symbol(sym).get_category() == Symbol::EQUATE {
                continue;
            } else {
                self.scope_remove_symbol(scope, sym);
            }
        }
        Ok(())
    }

    pub fn scope_clear_unlocked_category(&mut self, scope: ScopeId, cat: i32, types: &mut TypeFactory) -> Result<()> {
        if cat >= 0 {
            let cat = cat as usize;
            if cat >= self.scope(scope).category.len() {
                return Ok(());
            }
            let size = self.scope(scope).category[cat].len();
            for index in 0..size {
                let slot = self.scope(scope).category[cat].get(index).copied().flatten();
                let Some(sym) = slot else {
                    continue;
                };
                if self.symbol(sym).is_type_locked() {
                    if !self.symbol(sym).is_name_locked() && !self.symbol(sym).is_name_undefined() {
                        let newname = self.scope_build_undefined_name(scope)?;
                        self.scope_rename_symbol(scope, sym, &newname)?;
                    }
                    if self.symbol(sym).is_size_type_locked() {
                        self.reset_size_lock_type_internal(sym, types)?;
                    }
                } else {
                    self.scope_remove_symbol(scope, sym);
                }
            }
        } else {
            let mut iter = self.name_first(scope);
            while let Some(key) = iter {
                let sym = self.name_symbol(scope, &key);
                iter = self.name_next(scope, &key);
                if self.symbol(sym).get_category() >= 0 {
                    continue;
                }
                if self.symbol(sym).is_type_locked() {
                    if !self.symbol(sym).is_name_locked() && !self.symbol(sym).is_name_undefined() {
                        let newname = self.scope_build_undefined_name(scope)?;
                        self.scope_rename_symbol(scope, sym, &newname)?;
                    }
                } else {
                    self.scope_remove_symbol(scope, sym);
                }
            }
        }
        Ok(())
    }

    pub fn scope_adjust_caches(&mut self, scope: ScopeId, num_spaces: i32) {
        self.scope_mut(scope)
            .maptable
            .resize_with(num_spaces.max(0) as usize, || None);
    }

    pub fn scope_remove_symbol_mappings(&mut self, scope: ScopeId, symbol: SymbolId) {
        if self.symbol(symbol).whole_count > 1 {
            let key = SymbolNameKey::of(self.symbol(symbol));
            self.scope_mut(scope).multi_entry_set.remove(&key);
        }
        let entries = std::mem::take(&mut self.symbol_mut(symbol).mapentry);
        for entry in entries {
            if !self.entries.contains(entry) {
                continue;
            }
            let record = self.entries.remove(entry);
            if record.is_dynamic() {
                let dynamic = &mut self.scope_mut(scope).dynamicentry;
                if let Some(pos) = dynamic.iter().position(|&id| id == entry) {
                    dynamic.remove(pos);
                }
            } else if let Some(iter) = record.get_map_iterator()
                && let Some(index) = space_index(record.get_addr())
                && let Some(Some(rangemap)) = self.scope_mut(scope).maptable.get_mut(index)
            {
                rangemap.erase(iter);
            }
        }
        self.symbol_mut(symbol).whole_count = 0;
    }

    pub fn scope_remove_symbol(&mut self, scope: ScopeId, symbol: SymbolId) {
        let category = self.symbol(symbol).category;
        if category >= 0 {
            let catindex = self.symbol(symbol).catindex as usize;
            if let Some(list) = self.scope_mut(scope).category.get_mut(category as usize) {
                if catindex < list.len() {
                    list[catindex] = None;
                }
                while matches!(list.last(), Some(None)) {
                    list.pop();
                }
            }
        }
        self.scope_remove_symbol_mappings(scope, symbol);
        let key = SymbolNameKey::of(self.symbol(symbol));
        if self.scope(scope).nametree.get(&key) == Some(&symbol) {
            self.scope_mut(scope).nametree.remove(&key);
        }
        self.destroy_symbol(symbol);
    }

    pub fn scope_rename_symbol(&mut self, scope: ScopeId, sym: SymbolId, newname: &str) -> Result<()> {
        let key = SymbolNameKey::of(self.symbol(sym));
        self.scope_mut(scope).nametree.remove(&key);
        let multi = self.symbol(sym).whole_count > 1;
        if multi {
            self.scope_mut(scope).multi_entry_set.remove(&key);
        }
        let symbol = self.symbol_mut(sym);
        symbol.name = newname.to_string();
        symbol.display_name = newname.to_string();
        self.scope_insert_name_tree(scope, sym)?;
        if multi {
            let key = SymbolNameKey::of(self.symbol(sym));
            self.scope_mut(scope).multi_entry_set.entry(key).or_insert(sym);
        }
        Ok(())
    }

    pub fn scope_retype_symbol(glb: &mut Architecture, scope: ScopeId, sym: SymbolId, ct: TypeId) -> Result<()> {
        let (db, types) = db_and_types(glb);
        let mut ct = ct;
        if types.get(ct).has_stripped()
            && let Some(stripped) = types.get(ct).get_stripped()
        {
            ct = stripped;
        }
        let oldsize = db.symbol_type_size(sym, types);
        if oldsize == types.get(ct).get_size() || db.symbol(sym).mapentry.is_empty() {
            let symbol = db.symbol_mut(sym);
            symbol.tp = Some(ct);
            symbol.check_size_type_lock(types);
            return Ok(());
        }
        if db.symbol(sym).mapentry.len() == 1 {
            let entry = *db.symbol(sym).mapentry.last().expect("mapentry has one element");
            if !db.entry(entry).is_dynamic() && db.entry_is_addr_tied(entry) {
                let addr = db.entry(entry).get_addr().clone();
                let iter = db.entry(entry).get_map_iterator();
                if let (Some(index), Some(iter)) = (space_index(&addr), iter)
                    && let Some(Some(rangemap)) = db.scope_mut(scope).maptable.get_mut(index)
                {
                    rangemap.erase(iter);
                }
                db.symbol_mut(sym).mapentry.pop();
                db.entries.remove(entry);
                let symbol = db.symbol_mut(sym);
                symbol.whole_count = 0;
                symbol.tp = Some(ct);
                symbol.check_size_type_lock(types);
                Database::scope_add_map_point(glb, scope, sym, &addr, &Address::invalid())?;
                return Ok(());
            }
        }
        Err(Error::Recov(format!(
            "Unable to retype symbol: {}",
            db.symbol(sym).name
        )))
    }

    const ATTRIBUTE_MASK: u32 = Varnode::TYPELOCK
        | Varnode::NAMELOCK
        | Varnode::READONLY
        | Varnode::INCIDENTAL_COPY
        | Varnode::NOLOCALALIAS
        | Varnode::VOLATIL
        | Varnode::INDIRECTSTORAGE
        | Varnode::HIDDENRETPARM;

    pub fn scope_set_attribute(&mut self, types: &TypeFactory, _scope: ScopeId, sym: SymbolId, attr: u32) {
        let attr = attr & Database::ATTRIBUTE_MASK;
        let symbol = self.symbol_mut(sym);
        symbol.flags |= attr;
        symbol.check_size_type_lock(types);
    }

    pub fn scope_clear_attribute(&mut self, types: &TypeFactory, _scope: ScopeId, sym: SymbolId, attr: u32) {
        let attr = attr & Database::ATTRIBUTE_MASK;
        let symbol = self.symbol_mut(sym);
        symbol.flags &= !attr;
        symbol.check_size_type_lock(types);
    }

    pub fn scope_set_display_format(&mut self, _scope: ScopeId, sym: SymbolId, attr: u32) {
        self.symbol_mut(sym).set_display_format(attr);
    }

    fn usepoint_range(rangemap: &EntryMap, addr: &Address, usepoint: &Address) -> (usize, usize) {
        let upper = if usepoint.is_invalid() {
            EntrySubsort::from_bool(true)
        } else {
            EntrySubsort::from_addr(usepoint)
        };
        rangemap.find_subsort(&addr.get_offset(), &EntrySubsort::from_bool(false), &upper)
    }

    pub fn scope_find_addr(&self, scope: ScopeId, addr: &Address, usepoint: &Address) -> Option<EntryId> {
        let rangemap = self.scope(scope).entry_map(addr)?;
        let (first, mut second) = Database::usepoint_range(rangemap, addr, usepoint);
        while first != second {
            second -= 1;
            let entry = rangemap.part(second).entry;
            if self.entry(entry).get_addr().get_offset() == addr.get_offset() && self.entry_in_use(entry, usepoint) {
                return Some(entry);
            }
        }
        None
    }

    pub fn scope_find_container(
        &self,
        scope: ScopeId,
        addr: &Address,
        size: i32,
        usepoint: &Address,
    ) -> Option<EntryId> {
        let mut bestentry = None;
        let rangemap = self.scope(scope).entry_map(addr)?;
        let (first, mut second) = Database::usepoint_range(rangemap, addr, usepoint);
        let mut oldsize = -1;
        let end = addr.get_offset().wrapping_add(size as u64).wrapping_sub(1);
        while first != second {
            second -= 1;
            let entry = rangemap.part(second).entry;
            let record = self.entry(entry);
            if record.get_last() >= end
                && (record.get_size() < oldsize || oldsize == -1)
                && self.entry_in_use(entry, usepoint)
            {
                bestentry = Some(entry);
                if record.get_size() == size {
                    break;
                }
                oldsize = record.get_size();
            }
        }
        bestentry
    }

    pub fn scope_find_closest_fit(
        &self,
        scope: ScopeId,
        addr: &Address,
        size: i32,
        usepoint: &Address,
    ) -> Option<EntryId> {
        let mut bestentry = None;
        let rangemap = self.scope(scope).entry_map(addr)?;
        let (first, mut second) = Database::usepoint_range(rangemap, addr, usepoint);
        let mut olddiff = -10000;
        while first != second {
            second -= 1;
            let entry = rangemap.part(second).entry;
            let record = self.entry(entry);
            if record.get_last() >= addr.get_offset() {
                let newdiff = record.get_size() - size;
                if ((olddiff < 0 && newdiff > olddiff) || (olddiff >= 0 && newdiff >= 0 && newdiff < olddiff))
                    && self.entry_in_use(entry, usepoint)
                {
                    bestentry = Some(entry);
                    if newdiff == 0 {
                        break;
                    }
                    olddiff = newdiff;
                }
            }
        }
        bestentry
    }

    pub fn scope_find_function(&self, scope: ScopeId, addr: &Address) -> Option<SymbolId> {
        let rangemap = self.scope(scope).entry_map(addr)?;
        let (mut first, second) = rangemap.find(&addr.get_offset());
        while first != second {
            let entry = rangemap.part(first).entry;
            let record = self.entry(entry);
            if record.get_addr().get_offset() == addr.get_offset() && self.symbol(record.symbol).is_function() {
                return Some(record.symbol);
            }
            first += 1;
        }
        None
    }

    pub fn scope_find_external_ref(&self, scope: ScopeId, addr: &Address) -> Option<SymbolId> {
        let rangemap = self.scope(scope).entry_map(addr)?;
        let (mut first, second) = rangemap.find(&addr.get_offset());
        while first != second {
            let entry = rangemap.part(first).entry;
            let record = self.entry(entry);
            if record.get_addr().get_offset() == addr.get_offset() {
                return match self.symbol(record.symbol).kind {
                    SymbolKind::ExternRef { .. } => Some(record.symbol),
                    _ => None,
                };
            }
            first += 1;
        }
        None
    }

    pub fn scope_find_code_label(&self, scope: ScopeId, addr: &Address) -> Option<SymbolId> {
        let rangemap = self.scope(scope).entry_map(addr)?;
        let (first, mut second) = rangemap.find_subsort(
            &addr.get_offset(),
            &EntrySubsort::from_bool(false),
            &EntrySubsort::from_addr(addr),
        );
        while first != second {
            second -= 1;
            let entry = rangemap.part(second).entry;
            let record = self.entry(entry);
            if record.get_addr().get_offset() == addr.get_offset() && self.entry_in_use(entry, addr) {
                return match self.symbol(record.symbol).kind {
                    SymbolKind::Label => Some(record.symbol),
                    _ => None,
                };
            }
        }
        None
    }

    pub fn scope_find_overlap(&self, scope: ScopeId, addr: &Address, size: i32) -> Option<EntryId> {
        let rangemap = self.scope(scope).entry_map(addr)?;
        let last = addr.get_offset().wrapping_add(size as u64).wrapping_sub(1);
        let iter = rangemap.find_overlap(&addr.get_offset(), &last);
        if iter != rangemap.end() {
            return Some(rangemap.part(iter).entry);
        }
        None
    }

    pub fn scope_find_symbol_before(&self, scope: ScopeId, addr: &Address, usepoint: &Address) -> Option<EntryId> {
        let rangemap = self.scope(scope).entry_map(addr)?;
        let mut iter = rangemap.find_last_before(&addr.get_offset());
        if iter != rangemap.end() {
            loop {
                let entry = rangemap.part(iter).entry;
                if self.entry_in_use(entry, usepoint) {
                    return Some(entry);
                }
                if iter == rangemap.begin() {
                    break;
                }
                iter -= 1;
            }
        }
        None
    }

    pub fn scope_find_symbol_after(&self, scope: ScopeId, addr: &Address, usepoint: &Address) -> Option<EntryId> {
        let rangemap = self.scope(scope).entry_map(addr)?;
        let mut iter = rangemap.find_first_after(&addr.get_offset());
        while iter != rangemap.end() {
            let entry = rangemap.part(iter).entry;
            if self.entry_in_use(entry, usepoint) {
                return Some(entry);
            }
            iter += 1;
        }
        None
    }

    pub fn scope_find_by_name(&self, scope: ScopeId, nm: &str, res: &mut Vec<SymbolId>) {
        let Some(first) = self.scope_find_first_by_name(scope, nm) else {
            return;
        };
        for (key, sym) in self
            .scope(scope)
            .nametree
            .range((Bound::Included(first), Bound::Unbounded))
        {
            if key.name != nm {
                break;
            }
            res.push(*sym);
        }
    }

    pub fn scope_is_name_used(&self, scope: ScopeId, nm: &str, op2: Option<ScopeId>) -> bool {
        if let Some(key) = name_lower_bound(&self.scope(scope).nametree, &SymbolNameKey::probe(nm, 0))
            && key.name == nm
        {
            return true;
        }
        let Some(par) = self.scope(scope).get_parent() else {
            return false;
        };
        if Some(par) == op2 {
            return false;
        }
        if self.scope(par).get_parent().is_none() {
            return false;
        }
        self.scope_is_name_used(par, nm, op2)
    }

    pub fn scope_resolve_external_ref_function(&self, scope: ScopeId, sym: SymbolId) -> Option<SymbolId> {
        let refaddr = self.symbol(sym).get_ref_addr().clone();
        self.scope_query_function(scope, &refaddr)
    }

    #[allow(clippy::too_many_arguments)]
    pub fn scope_build_variable_name(
        glb: &Architecture,
        data: Option<&Funcdata>,
        scope: ScopeId,
        addr: &Address,
        pc: &Address,
        ct: Option<TypeId>,
        index: &mut i32,
        flags: u32,
    ) -> Result<String> {
        if db_ref(glb).scope(scope).is_local() {
            return Database::local_build_variable_name(glb, data, scope, addr, pc, ct, index, flags);
        }
        Database::scope_build_variable_name_internal(glb, scope, addr, ct, index, flags)
    }

    fn register_name(glb: &Architecture, addr: &Address, sz: i32) -> String {
        let (Some(trans), Some(spc)) = (glb.translate.as_deref(), addr.get_space()) else {
            return String::new();
        };
        trans.get_register_name(spc, addr.get_offset(), sz)
    }

    fn capitalized_space_address(glb: &Architecture, out: &mut String, addr: &Address, ct: Option<TypeId>) {
        let types = types_ref(glb);
        if let Some(ct) = ct {
            types.get(ct).print_name_base(out, types);
        }
        let spc = addr.get_space().expect("variable address has no space");
        out.push_str(&capitalize_first(spc.get_name()));
        let width = 2 * addr.get_addr_size() as usize;
        let value = crate::space::AddrSpace::byte_to_address(addr.get_offset(), spc.get_word_size());
        out.push_str(&format!("{:0width$x}", value, width = width));
    }

    pub(crate) fn scope_build_variable_name_internal(
        glb: &Architecture,
        scope: ScopeId,
        addr: &Address,
        ct: Option<TypeId>,
        index: &mut i32,
        flags: u32,
    ) -> Result<String> {
        let db = db_ref(glb);
        let types = types_ref(glb);
        let mut text = String::new();
        let sz = match ct {
            None => 1,
            Some(ct) => types.get(ct).get_size(),
        };
        if (flags & Varnode::UNAFFECTED) != 0 {
            if (flags & Varnode::RETURN_ADDRESS) != 0 {
                text.push_str("unaff_retaddr");
            } else {
                let unaffname = Database::register_name(glb, addr, sz);
                if unaffname.is_empty() {
                    text.push_str(&format!("unaff_{:08x}", addr.get_offset()));
                } else {
                    text.push_str("unaff_");
                    text.push_str(&unaffname);
                }
            }
        } else if (flags & Varnode::PERSIST) != 0 {
            let spacename = Database::register_name(glb, addr, sz);
            if !spacename.is_empty() {
                text.push_str(&spacename);
            } else {
                Database::capitalized_space_address(glb, &mut text, addr, ct);
            }
        } else if (flags & Varnode::INPUT) != 0 && *index < 0 {
            let regname = Database::register_name(glb, addr, sz);
            if regname.is_empty() {
                let spc = addr.get_space().expect("variable address has no space");
                text.push_str(&format!("in_{}_{:08x}", spc.get_name(), addr.get_offset()));
            } else {
                text.push_str("in_");
                text.push_str(&regname);
            }
        } else if (flags & Varnode::INPUT) != 0 {
            text.push_str(&format!("param_{}", *index));
        } else if (flags & Varnode::ADDRTIED) != 0 {
            Database::capitalized_space_address(glb, &mut text, addr, ct);
        } else if (flags & Varnode::INDIRECT_CREATION) != 0 {
            text.push_str("extraout_");
            let regname = Database::register_name(glb, addr, sz);
            if !regname.is_empty() {
                text.push_str(&regname);
            } else {
                text.push_str("var");
            }
        } else {
            if let Some(ct) = ct {
                types.get(ct).print_name_base(&mut text, types);
            }
            text.push_str(&format!("Var{}", *index));
            *index = index.wrapping_add(1);
            if db.scope_find_first_by_name(scope, &text).is_some() {
                for _ in 0..10 {
                    let mut s2 = String::new();
                    if let Some(ct) = ct {
                        types.get(ct).print_name_base(&mut s2, types);
                    }
                    s2.push_str(&format!("Var{}", *index));
                    *index = index.wrapping_add(1);
                    if db.scope_find_first_by_name(scope, &s2).is_none() {
                        return Ok(s2);
                    }
                }
            }
        }
        db.scope_make_name_unique(scope, &text)
    }

    pub fn scope_build_undefined_name(&self, scope: ScopeId) -> Result<String> {
        let tree = &self.scope(scope).nametree;
        let testsym = SymbolNameKey::probe("$$undefz", 0);
        let previous = tree
            .range((Bound::Unbounded, Bound::Excluded(&testsym)))
            .next_back()
            .map(|(key, _)| key);
        let candidate = match previous {
            Some(key) => Some(key),
            None => tree
                .range((Bound::Included(&testsym), Bound::Unbounded))
                .next()
                .map(|(key, _)| key),
        };
        if let Some(key) = candidate {
            let symname = &key.name;
            if symname.len() == 15 && symname.as_bytes().starts_with(b"$$undef") {
                let digits = String::from_utf8_lossy(&symname.as_bytes()[7..15]).into_owned();
                let uniq = read_u32(&digits, Basefield::Hex, u32::MAX);
                if uniq == u32::MAX {
                    return Err(Error::Lowlevel("Error creating undefined name".to_string()));
                }
                return Ok(format!("$$undef{:08x}", uniq.wrapping_add(1)));
            }
        }
        Ok("$$undef00000000".to_string())
    }

    pub fn scope_make_name_unique(&self, scope: ScopeId, nm: &str) -> Result<String> {
        let tree = &self.scope(scope).nametree;
        let Some(iter) = self.scope_find_first_by_name(scope, nm) else {
            return Ok(nm.to_string());
        };
        let boundsym = SymbolNameKey::probe(&format!("{}_x99999", nm), 0xffffffff);
        let mut uniqid: u32 = 0xffffffff;
        let nm_bytes = nm.as_bytes();
        for (key, _) in tree.range((Bound::Unbounded, Bound::Excluded(&boundsym))).rev() {
            uniqid = 0xffffffff;
            if *key == iter {
                break;
            }
            let bname = key.name.as_bytes();
            let mut is_xform = false;
            let mut dig_count = 0;
            if bname.len() >= nm_bytes.len() + 3 && bname[nm_bytes.len()] == b'_' {
                let mut pos = nm_bytes.len() + 1;
                if bname[pos] == b'x' {
                    pos += 1;
                    is_xform = true;
                }
                uniqid = 0;
                while pos < bname.len() {
                    let dig = bname[pos];
                    if !dig.is_ascii_digit() {
                        uniqid = 0xffffffff;
                        break;
                    }
                    uniqid = uniqid.wrapping_mul(10);
                    uniqid = uniqid.wrapping_add((dig - b'0') as u32);
                    dig_count += 1;
                    pos += 1;
                }
            }
            if (is_xform && dig_count != 5) || (!is_xform && dig_count != 2) {
                uniqid = 0xffffffff;
            }
            if uniqid != 0xffffffff {
                break;
            }
        }
        let res_string = if uniqid == 0xffffffff {
            format!("{}_00", nm)
        } else {
            let uniqid = uniqid.wrapping_add(1);
            if uniqid < 100 {
                format!("{}_{:02}", nm, uniqid)
            } else {
                format!("{}_x{:05}", nm, uniqid)
            }
        };
        if self.scope_find_first_by_name(scope, &res_string).is_some() {
            return Err(Error::Lowlevel(format!("Unable to uniquify name: {}", res_string)));
        }
        Ok(res_string)
    }

    pub fn scope_encode(glb: &Architecture, scope: ScopeId, encoder: &mut dyn Encoder) -> Result<()> {
        if db_ref(glb).scope(scope).is_local() {
            return Database::local_encode(glb, scope, encoder);
        }
        Database::scope_encode_internal(glb, scope, encoder)
    }

    pub(crate) fn scope_encode_internal(glb: &Architecture, scope: ScopeId, encoder: &mut dyn Encoder) -> Result<()> {
        let db = db_ref(glb);
        let current = db.scope(scope);
        encoder.open_element(ELEM_SCOPE);
        encoder.write_string(ATTRIB_NAME, &current.name);
        encoder.write_unsigned_integer(ATTRIB_ID, current.unique_id);
        if let Some(parent) = current.get_parent() {
            encoder.open_element(ELEM_PARENT);
            encoder.write_unsigned_integer(ATTRIB_ID, db.scope(parent).get_id());
            encoder.close_element(ELEM_PARENT);
        }
        current.get_range_tree().encode(encoder);
        if !current.nametree.is_empty() {
            encoder.open_element(ELEM_SYMBOLLIST);
            for &sym in current.nametree.values() {
                let symbol = db.symbol(sym);
                if symbol.get_category() == Symbol::UNION_FACET {
                    continue;
                }
                encoder.open_element(ELEM_MAPSYM);
                Database::symbol_encode(glb, sym, encoder)?;
                for &entry in symbol.mapentry.iter() {
                    db.entry(entry).encode(encoder)?;
                }
                encoder.close_element(ELEM_MAPSYM);
            }
            encoder.close_element(ELEM_SYMBOLLIST);
        }
        encoder.close_element(ELEM_SCOPE);
        Ok(())
    }

    pub fn scope_decode(glb: &mut Architecture, scope: ScopeId, decoder: &mut dyn Decoder) -> Result<()> {
        if db_ref(glb).scope(scope).is_local() {
            return Database::local_decode(glb, scope, decoder);
        }
        Database::scope_decode_internal(glb, scope, decoder)
    }

    pub(crate) fn scope_decode_internal(
        glb: &mut Architecture,
        scope: ScopeId,
        decoder: &mut dyn Decoder,
    ) -> Result<()> {
        let mut rangeequalssymbols = false;
        let mut sub_id = decoder.peek_element()?;
        if sub_id == ELEM_PARENT {
            decoder.skip_element()?;
            sub_id = decoder.peek_element()?;
        }
        if sub_id == ELEM_RANGELIST {
            let mut newrangetree = RangeList::new();
            newrangetree.decode(decoder)?;
            db_mut(glb).set_range(scope, &newrangetree);
        } else if sub_id == ELEM_RANGEEQUALSSYMBOLS {
            decoder.open_element()?;
            decoder.close_element(sub_id)?;
            rangeequalssymbols = true;
        }
        let sub_id = decoder.open_element_expect(ELEM_SYMBOLLIST)?;
        if sub_id != 0 {
            loop {
                let sym_id = decoder.peek_element()?;
                if sym_id == 0 {
                    break;
                }
                if sym_id == ELEM_MAPSYM {
                    let Some(sym) = Database::scope_add_map_sym(glb, scope, decoder)? else {
                        continue;
                    };
                    if rangeequalssymbols {
                        let db = db_ref(glb);
                        let entry = db.symbol_get_first_whole_map(sym)?;
                        if !db.entry(entry).is_dynamic() {
                            let record = db.entry(entry);
                            let spc = record
                                .get_addr()
                                .get_space()
                                .expect("entry address has no space")
                                .clone();
                            let (first, last) = (record.get_first(), record.get_last());
                            db_mut(glb).add_range(scope, &spc, first, last);
                        }
                    }
                    let props = db_ref(glb).symbol(sym).get_flags() & (Varnode::READONLY | Varnode::VOLATIL);
                    if props != 0 {
                        let db = db_ref(glb);
                        let entry = db.symbol_get_first_whole_map(sym)?;
                        if !db.entry(entry).is_dynamic() {
                            let record = db.entry(entry);
                            let spc = record
                                .get_addr()
                                .get_space()
                                .expect("entry address has no space")
                                .clone();
                            let rng = Range::new(spc, record.get_first(), record.get_last());
                            let Architecture { symboltab, manager, .. } = glb;
                            symboltab
                                .as_deref_mut()
                                .expect("architecture has no symbol table")
                                .set_property_range(props, &rng, manager);
                        }
                    }
                } else if sym_id == ELEM_HOLE {
                    Database::scope_decode_hole(glb, scope, decoder)?;
                } else if sym_id == ELEM_COLLISION {
                    Database::scope_decode_collision(glb, scope, decoder)?;
                } else {
                    return Err(Error::Lowlevel("Unknown symbollist tag".to_string()));
                }
            }
            decoder.close_element(sub_id)?;
        }
        db_mut(glb).scope_category_sanity(scope);
        Ok(())
    }

    pub fn scope_decode_wrapping_attributes(
        glb: &mut Architecture,
        scope: ScopeId,
        decoder: &mut dyn Decoder,
    ) -> Result<()> {
        if db_ref(glb).scope(scope).is_local() {
            return Database::local_decode_wrapping_attributes(glb, scope, decoder);
        }
        Ok(())
    }

    pub fn scope_decode_hole(glb: &mut Architecture, _scope: ScopeId, decoder: &mut dyn Decoder) -> Result<()> {
        let elem_id = decoder.open_element_expect(ELEM_HOLE)?;
        let mut flags = 0;
        let range = Range::decode_from_attributes(decoder)?;
        decoder.rewind_attributes();
        loop {
            let attrib_id = decoder.get_next_attribute_id()?;
            if attrib_id == 0 {
                break;
            }
            if attrib_id == ATTRIB_READONLY && decoder.read_bool()? {
                flags |= Varnode::READONLY;
            } else if attrib_id == ATTRIB_VOLATILE && decoder.read_bool()? {
                flags |= Varnode::VOLATIL;
            }
        }
        if flags != 0 {
            let Architecture { symboltab, manager, .. } = glb;
            symboltab
                .as_deref_mut()
                .expect("architecture has no symbol table")
                .set_property_range(flags, &range, manager);
        }
        decoder.close_element(elem_id)
    }

    pub fn scope_decode_collision(glb: &mut Architecture, scope: ScopeId, decoder: &mut dyn Decoder) -> Result<()> {
        let elem_id = decoder.open_element_expect(ELEM_COLLISION)?;
        let nm = decoder.read_string_attr(ATTRIB_NAME)?;
        decoder.close_element(elem_id)?;
        if db_ref(glb).scope_find_first_by_name(scope, &nm).is_none() {
            let (db, types) = db_and_types(glb);
            let ct = types.get_base(1, TypeMetatype::Int)?;
            db.scope_add_symbol(scope, &nm, Some(ct), types)?;
        }
        Ok(())
    }

    pub fn scope_insert_name_tree(&mut self, scope: ScopeId, sym: SymbolId) -> Result<()> {
        self.symbol_mut(sym).name_dedup = 0;
        let key = SymbolNameKey::of(self.symbol(sym));
        if !self.scope(scope).nametree.contains_key(&key) {
            self.scope_mut(scope).nametree.insert(key, sym);
            return Ok(());
        }
        let probe = SymbolNameKey::probe(&self.symbol(sym).name, 0xffffffff);
        let last_dedup = self
            .scope(scope)
            .nametree
            .range((Bound::Unbounded, Bound::Included(&probe)))
            .next_back()
            .map(|(key, _)| key.name_dedup)
            .expect("name exists in the tree");
        self.symbol_mut(sym).name_dedup = last_dedup.wrapping_add(1);
        let key = SymbolNameKey::of(self.symbol(sym));
        if self.scope(scope).nametree.contains_key(&key) {
            return Err(Error::Lowlevel(format!(
                "Could  not deduplicate symbol: {}",
                self.symbol(sym).name
            )));
        }
        self.scope_mut(scope).nametree.insert(key, sym);
        Ok(())
    }

    pub fn scope_find_first_by_name(&self, scope: ScopeId, nm: &str) -> Option<SymbolNameKey> {
        let key = name_lower_bound(&self.scope(scope).nametree, &SymbolNameKey::probe(nm, 0))?;
        if key.name != nm {
            return None;
        }
        Some(key)
    }

    pub fn scope_print_entries(&self, scope: ScopeId, out: &mut String, types: &TypeFactory) {
        let current = self.scope(scope);
        out.push_str(&format!("Scope {}\n", current.name));
        for rangemap in current.maptable.iter().flatten() {
            for (_, record) in rangemap.list_iter() {
                self.entry_print_entry(record.entry, out, types);
            }
        }
    }

    pub fn scope_get_category_size(&self, scope: ScopeId, cat: i32) -> i32 {
        let category = &self.scope(scope).category;
        if cat < 0 || cat as usize >= category.len() {
            return 0;
        }
        category[cat as usize].len() as i32
    }

    pub fn scope_get_category_symbol(&self, scope: ScopeId, cat: i32, ind: i32) -> Option<SymbolId> {
        let category = &self.scope(scope).category;
        if cat < 0 || cat as usize >= category.len() {
            return None;
        }
        let list = &category[cat as usize];
        if ind < 0 || ind as usize >= list.len() {
            return None;
        }
        list[ind as usize]
    }

    pub fn scope_set_category(&mut self, scope: ScopeId, sym: SymbolId, cat: i32, ind: i32) {
        let oldcat = self.symbol(sym).category;
        if oldcat >= 0 {
            let catindex = self.symbol(sym).catindex as usize;
            if let Some(list) = self.scopes.get_mut(scope).category.get_mut(oldcat as usize) {
                if catindex < list.len() {
                    list[catindex] = None;
                }
                while matches!(list.last(), Some(None)) {
                    list.pop();
                }
            }
        }
        {
            let symbol = self.symbol_mut(sym);
            symbol.category = cat as i16;
            symbol.catindex = ind as u16;
        }
        if cat < 0 {
            return;
        }
        let catlist = &mut self.scopes.get_mut(scope).category;
        while catlist.len() <= cat as usize {
            catlist.push(Vec::new());
        }
        let list = &mut catlist[cat as usize];
        let symbol = self.symbols.get_mut(sym);
        if cat > 0 {
            symbol.catindex = list.len() as u16;
        }
        while list.len() <= symbol.catindex as usize {
            list.push(None);
        }
        list[symbol.catindex as usize] = Some(sym);
    }

    pub fn scope_assign_default_names(
        glb: &mut Architecture,
        data: Option<&mut Funcdata>,
        scope: ScopeId,
        base: &mut i32,
    ) -> Result<()> {
        let mut data = data;
        let testsym = SymbolNameKey::probe("$$undef", 0);
        let mut iter = name_upper_bound(&db_ref(glb).scope(scope).nametree, &testsym);
        while let Some(key) = iter {
            let db = db_ref(glb);
            let sym = db.name_symbol(scope, &key);
            if !db.symbol(sym).is_name_undefined() {
                break;
            }
            iter = db.name_next(scope, &key);
            let nm = Database::scope_build_default_name(glb, data.as_deref_mut(), scope, sym, base, None)?;
            db_mut(glb).scope_rename_symbol(scope, sym, &nm)?;
        }
        Ok(())
    }

    pub fn scope_add_symbol_at(
        glb: &mut Architecture,
        scope: ScopeId,
        nm: &str,
        ct: Option<TypeId>,
        addr: &Address,
        usepoint: &Address,
    ) -> Result<EntryId> {
        let (db, types) = db_and_types(glb);
        let mut ct = ct;
        if let Some(tp) = ct
            && types.get(tp).has_stripped()
        {
            ct = types.get(tp).get_stripped().or(ct);
        }
        let owner = db.scope_owner(scope);
        let sym = db.symbols.alloc(Symbol::new(owner, nm, ct));
        db.scope_add_symbol_internal(scope, sym, types)?;
        Database::scope_add_map_point(glb, scope, sym, addr, usepoint)
    }

    pub fn scope_query_by_name(&self, scope: ScopeId, nm: &str, res: &mut Vec<SymbolId>) {
        self.scope_find_by_name(scope, nm, res);
        if !res.is_empty() {
            return;
        }
        if let Some(parent) = self.scope(scope).get_parent() {
            self.scope_query_by_name(parent, nm, res);
        }
    }

    pub fn scope_query_function_by_name(&self, scope: ScopeId, nm: &str) -> Option<SymbolId> {
        let mut sym_list = Vec::new();
        self.scope_query_by_name(scope, nm, &mut sym_list);
        sym_list.into_iter().find(|&sym| self.symbol(sym).is_function())
    }

    pub fn scope_query_by_addr(&self, scope: ScopeId, addr: &Address, usepoint: &Address) -> Option<EntryId> {
        let mut res = None;
        let basescope = self.map_scope(scope, addr, usepoint);
        self.scope_stack_addr(basescope, None, addr, usepoint, &mut res);
        res
    }

    pub fn scope_query_container(
        &self,
        scope: ScopeId,
        addr: &Address,
        size: i32,
        usepoint: &Address,
    ) -> Option<EntryId> {
        let mut res = None;
        let basescope = self.map_scope(scope, addr, usepoint);
        self.scope_stack_container(basescope, None, addr, size, usepoint, &mut res);
        res
    }

    pub fn scope_query_properties(
        &self,
        scope: ScopeId,
        addr: &Address,
        size: i32,
        usepoint: &Address,
        flags: &mut u32,
    ) -> Option<EntryId> {
        let mut res = None;
        let basescope = self.map_scope(scope, addr, usepoint);
        let finalscope = self.scope_stack_container(basescope, None, addr, size, usepoint, &mut res);
        if let Some(entry) = res {
            *flags = self.entry_get_all_flags(entry);
        } else if let Some(finalscope) = finalscope {
            *flags = Varnode::MAPPED | Varnode::ADDRTIED;
            if self.scope(finalscope).is_global() {
                *flags |= Varnode::PERSIST;
            }
            *flags |= self.get_property(addr);
        } else {
            *flags = self.get_property(addr);
        }
        res
    }

    pub fn scope_query_function(&self, scope: ScopeId, addr: &Address) -> Option<SymbolId> {
        let mut res = None;
        let basescope = self.map_scope(scope, addr, &Address::invalid());
        self.scope_stack_function(basescope, None, addr, &mut res);
        res
    }

    pub fn scope_query_external_ref_function(&self, scope: ScopeId, addr: &Address) -> Option<SymbolId> {
        let mut sym = None;
        let basescope = self.map_scope(scope, addr, &Address::invalid());
        let foundscope = self.scope_stack_external_ref(basescope, None, addr, &mut sym);
        match (sym, foundscope) {
            (Some(sym), Some(foundscope)) => self.scope_resolve_external_ref_function(foundscope, sym),
            _ => None,
        }
    }

    pub fn scope_query_code_label(&self, scope: ScopeId, addr: &Address) -> Option<SymbolId> {
        let mut res = None;
        let basescope = self.map_scope(scope, addr, &Address::invalid());
        self.scope_stack_code_label(basescope, None, addr, &mut res);
        res
    }

    pub fn scope_resolve_scope(&self, scope: ScopeId, nm: &str, strategy: bool) -> Option<ScopeId> {
        let current = self.scope(scope);
        if strategy {
            let key = Scope::hash_scope_name(current.unique_id, nm);
            let child = *current.children.get(&key)?;
            if self.scope(child).name == nm {
                return Some(child);
            }
        } else if nm.as_bytes().first().is_some_and(|first| first.is_ascii_digit()) {
            let key = read_u64(nm, Basefield::Auto, 0);
            return current.children.get(&key).copied();
        } else {
            for &child in current.children.values() {
                if self.scope(child).name == nm {
                    return Some(child);
                }
            }
        }
        None
    }

    pub fn scope_discover_scope(&self, scope: ScopeId, addr: &Address, sz: i32, usepoint: &Address) -> Option<ScopeId> {
        if addr.is_constant() {
            return None;
        }
        let mut basescope = Some(self.map_scope(scope, addr, usepoint));
        while let Some(current) = basescope {
            if self.scope(current).in_scope(addr, sz, usepoint) {
                return Some(current);
            }
            basescope = self.scope(current).get_parent();
        }
        None
    }

    pub fn scope_encode_recursive(
        glb: &Architecture,
        scope: ScopeId,
        encoder: &mut dyn Encoder,
        only_global: bool,
    ) -> Result<()> {
        let db = db_ref(glb);
        if only_global && !db.scope(scope).is_global() {
            return Ok(());
        }
        Database::scope_encode(glb, scope, encoder)?;
        let children: Vec<ScopeId> = db.scope(scope).children.values().copied().collect();
        for child in children {
            Database::scope_encode_recursive(glb, child, encoder, only_global)?;
        }
        Ok(())
    }

    pub fn scope_override_size_lock_type(
        &mut self,
        _scope: ScopeId,
        sym: SymbolId,
        ct: TypeId,
        types: &TypeFactory,
    ) -> Result<()> {
        if self.symbol_type_size(sym, types) == types.get(ct).get_size() {
            if !self.symbol(sym).is_size_type_locked() {
                return Err(Error::Lowlevel("Overriding symbol that is not size locked".to_string()));
            }
            self.symbol_mut(sym).tp = Some(ct);
            return Ok(());
        }
        Err(Error::Lowlevel(
            "Overriding symbol with different type size".to_string(),
        ))
    }

    fn reset_size_lock_type_internal(&mut self, sym: SymbolId, types: &mut TypeFactory) -> Result<()> {
        let tp = self.symbol(sym).type_id();
        if types.get(tp).get_metatype() == TypeMetatype::Unknown {
            return Ok(());
        }
        let size = types.get(tp).get_size();
        let newtype = types.get_base(size, TypeMetatype::Unknown)?;
        self.symbol_mut(sym).tp = Some(newtype);
        Ok(())
    }

    pub fn scope_reset_size_lock_type(glb: &mut Architecture, _scope: ScopeId, sym: SymbolId) -> Result<()> {
        let (db, types) = db_and_types(glb);
        db.reset_size_lock_type_internal(sym, types)
    }

    pub fn scope_set_this_pointer(&mut self, sym: SymbolId, val: bool) {
        self.symbol_mut(sym).set_this_pointer(val);
    }

    pub fn scope_is_sub_scope(&self, scope: ScopeId, scp: ScopeId) -> bool {
        let mut tmp = Some(scope);
        while let Some(current) = tmp {
            if current == scp {
                return true;
            }
            tmp = self.scope(current).parent;
        }
        false
    }

    pub fn scope_get_full_name(&self, scope: ScopeId, delim: &str) -> String {
        let current = self.scope(scope);
        let Some(mut parent) = current.parent else {
            return String::new();
        };
        let mut fname = current.name.clone();
        while let Some(grandparent) = self.scope(parent).parent {
            fname = format!("{}{}{}", self.scope(parent).name, delim, fname);
            parent = grandparent;
        }
        fname
    }

    pub fn scope_get_scope_path(&self, scope: ScopeId, vec: &mut Vec<ScopeId>) {
        let mut path = Vec::new();
        let mut cur = Some(scope);
        while let Some(current) = cur {
            path.push(current);
            cur = self.scope(current).parent;
        }
        path.reverse();
        *vec = path;
    }

    pub fn scope_find_distinguishing_scope(&self, scope: ScopeId, op2: ScopeId) -> Option<ScopeId> {
        if scope == op2 {
            return None;
        }
        let parent = self.scope(scope).parent;
        let op2_parent = self.scope(op2).parent;
        if parent == Some(op2) {
            return Some(scope);
        }
        if op2_parent == Some(scope) {
            return None;
        }
        if parent == op2_parent {
            return Some(scope);
        }
        let mut this_path = Vec::new();
        let mut op2_path = Vec::new();
        self.scope_get_scope_path(scope, &mut this_path);
        self.scope_get_scope_path(op2, &mut op2_path);
        let min = this_path.len().min(op2_path.len());
        for index in 0..min {
            if this_path[index] != op2_path[index] {
                return Some(this_path[index]);
            }
        }
        if min < this_path.len() {
            return Some(this_path[min]);
        }
        if min < op2_path.len() {
            return None;
        }
        Some(scope)
    }

    pub fn scope_add_symbol(
        &mut self,
        scope: ScopeId,
        nm: &str,
        ct: Option<TypeId>,
        types: &TypeFactory,
    ) -> Result<SymbolId> {
        let owner = self.scope_owner(scope);
        let sym = self.symbols.alloc(Symbol::new(owner, nm, ct));
        self.scope_add_symbol_internal(scope, sym, types)?;
        Ok(sym)
    }

    pub fn scope_add_map_point(
        glb: &mut Architecture,
        scope: ScopeId,
        sym: SymbolId,
        addr: &Address,
        usepoint: &Address,
    ) -> Result<EntryId> {
        let mut entry = SymbolEntry::new_map_empty(sym);
        entry.set_addr(addr.clone());
        if !usepoint.is_invalid() {
            let spc = usepoint.get_space().expect("valid usepoint has a space");
            entry
                .uselimit
                .insert_range(spc, usepoint.get_offset(), usepoint.get_offset());
        }
        Database::scope_add_map(glb, scope, entry)
    }

    pub fn scope_add_map_sym(
        glb: &mut Architecture,
        scope: ScopeId,
        decoder: &mut dyn Decoder,
    ) -> Result<Option<SymbolId>> {
        let elem_id = decoder.open_element_expect(ELEM_MAPSYM)?;
        let sub_id = decoder.peek_element()?;
        let min_size = glb.min_funcsymbol_size;
        let (db, types) = db_and_types(glb);
        let owner = db.scope_owner(scope);
        let symbol = if sub_id == ELEM_SYMBOL {
            Symbol::new_empty(owner)
        } else if sub_id == ELEM_EQUATESYMBOL {
            Symbol::new_equate_empty(owner)
        } else if sub_id == ELEM_FUNCTION || sub_id == ELEM_FUNCTIONSHELL {
            Symbol::new_function_empty(types, owner, min_size)?
        } else if sub_id == ELEM_LABELSYM {
            Symbol::new_label_empty(types, owner)?
        } else if sub_id == ELEM_EXTERNREFSYMBOL {
            Symbol::new_extern_ref_empty(owner)
        } else if sub_id == ELEM_FACETSYMBOL {
            Symbol::new_union_facet_empty(owner)
        } else {
            return Err(Error::Lowlevel("Unknown symbol type".to_string()));
        };
        let sym = db.symbols.alloc(symbol);
        if let Err(err) = Database::symbol_decode(glb, sym, decoder) {
            db_mut(glb).destroy_symbol(sym);
            return Err(err);
        }
        {
            let (db, types) = db_and_types(glb);
            db.scope_add_symbol_internal(scope, sym, types)?;
        }
        let mapping = Database::decode_symbol_mappings(glb, scope, sym, decoder);
        let mut res = Some(sym);
        if mapping.is_err() {
            let name = db_ref(glb).symbol(sym).name.clone();
            glb.print_warning(&format!("Throwing out symbol with invalid mapping: {}", name));
            db_mut(glb).scope_remove_symbol(scope, sym);
            res = None;
        }
        decoder.close_element(elem_id)?;
        Ok(res)
    }

    fn decode_symbol_mappings(
        glb: &mut Architecture,
        scope: ScopeId,
        sym: SymbolId,
        decoder: &mut dyn Decoder,
    ) -> Result<()> {
        loop {
            let entry_id = decoder.peek_element()?;
            if entry_id == 0 {
                break;
            }
            if entry_id == ELEM_HASH {
                let mut entry = SymbolEntry::new_dynamic_empty(sym);
                entry.decode(decoder)?;
                let (db, types) = db_and_types(glb);
                db.scope_add_dynamic(scope, entry, types)?;
            } else {
                let mut entry = SymbolEntry::new_map_empty(sym);
                entry.decode(decoder)?;
                Database::scope_add_map(glb, scope, entry)?;
            }
        }
        Ok(())
    }

    pub fn scope_add_function(glb: &mut Architecture, scope: ScopeId, addr: &Address, nm: &str) -> Result<SymbolId> {
        let overlap = db_ref(glb).scope_query_container(scope, addr, 1, &Address::invalid());
        if let Some(overlap) = overlap {
            let db = db_ref(glb);
            let errmsg = format!(
                "Function {} overlaps object: {}",
                nm,
                db.symbol(db.entry(overlap).symbol).get_name()
            );
            glb.print_warning(&errmsg);
        }
        let min_size = glb.min_funcsymbol_size;
        let (db, types) = db_and_types(glb);
        let owner = db.scope_owner(scope);
        let sym = db.symbols.alloc(Symbol::new_function(types, owner, nm, min_size)?);
        db.scope_add_symbol_internal(scope, sym, types)?;
        Database::scope_add_map_point(glb, scope, sym, addr, &Address::invalid())?;
        Ok(sym)
    }

    pub fn scope_add_external_ref(
        glb: &mut Architecture,
        scope: ScopeId,
        addr: &Address,
        refaddr: &Address,
        nm: &str,
    ) -> Result<SymbolId> {
        let (db, types) = db_and_types(glb);
        let owner = db.scope_owner(scope);
        let sym = db.symbols.alloc(Symbol::new_extern_ref(types, owner, refaddr, nm)?);
        db.scope_add_symbol_internal(scope, sym, types)?;
        let ret = Database::scope_add_map_point(glb, scope, sym, addr, &Address::invalid())?;
        let db = db_mut(glb);
        let retsym = db.entry(ret).symbol;
        db.symbol_mut(retsym).flags &= !Varnode::READONLY;
        Ok(sym)
    }

    pub fn scope_add_code_label(glb: &mut Architecture, scope: ScopeId, addr: &Address, nm: &str) -> Result<SymbolId> {
        let overlap = db_ref(glb).scope_query_container(scope, addr, 1, addr);
        if let Some(overlap) = overlap {
            let db = db_ref(glb);
            let oversym = db.symbol(db.entry(overlap).symbol);
            if !oversym.is_function() {
                let errmsg = format!("Codelabel {} overlaps object: {}", nm, oversym.get_name());
                glb.print_warning(&errmsg);
            }
        }
        let (db, types) = db_and_types(glb);
        let owner = db.scope_owner(scope);
        let sym = db.symbols.alloc(Symbol::new_label(types, owner, nm)?);
        db.scope_add_symbol_internal(scope, sym, types)?;
        Database::scope_add_map_point(glb, scope, sym, addr, &Address::invalid())?;
        Ok(sym)
    }

    fn single_point_range(addr: &Address) -> RangeList {
        let mut rnglist = RangeList::new();
        if !addr.is_invalid() {
            let spc = addr.get_space().expect("valid address has a space");
            rnglist.insert_range(spc, addr.get_offset(), addr.get_offset());
        }
        rnglist
    }

    pub fn scope_add_dynamic_symbol(
        &mut self,
        scope: ScopeId,
        nm: &str,
        ct: Option<TypeId>,
        caddr: &Address,
        hash: u64,
        types: &TypeFactory,
    ) -> Result<SymbolId> {
        let owner = self.scope_owner(scope);
        let sym = self.symbols.alloc(Symbol::new(owner, nm, ct));
        self.scope_add_symbol_internal(scope, sym, types)?;
        let rnglist = Database::single_point_range(caddr);
        let size = types.get(ct.expect("dynamic symbol has a data-type")).get_size();
        let entry = self
            .entries
            .alloc(SymbolEntry::new_dynamic(sym, Varnode::MAPPED, hash, 0, size, &rnglist));
        self.scope_add_dynamic_map_internal(scope, sym, entry, types);
        Ok(sym)
    }

    #[allow(clippy::too_many_arguments)]
    pub fn scope_add_equate_symbol(
        glb: &mut Architecture,
        scope: ScopeId,
        nm: &str,
        format: u32,
        value: u64,
        addr: &Address,
        hash: u64,
    ) -> Result<SymbolId> {
        let (db, types) = db_and_types(glb);
        let owner = db.scope_owner(scope);
        let sym = db.symbols.alloc(Symbol::new_equate(types, owner, nm, format, value)?);
        db.scope_add_symbol_internal(scope, sym, types)?;
        let rnglist = Database::single_point_range(addr);
        let entry = db
            .entries
            .alloc(SymbolEntry::new_dynamic(sym, Varnode::MAPPED, hash, 0, 1, &rnglist));
        db.scope_add_dynamic_map_internal(scope, sym, entry, types);
        Ok(sym)
    }

    #[allow(clippy::too_many_arguments)]
    pub fn scope_add_union_facet_symbol(
        glb: &mut Architecture,
        scope: ScopeId,
        nm: &str,
        dt: TypeId,
        field_num: i32,
        addr: &Address,
        hash: u64,
    ) -> Result<SymbolId> {
        let (db, types) = db_and_types(glb);
        let owner = db.scope_owner(scope);
        let sym = db
            .symbols
            .alloc(Symbol::new_union_facet(types, owner, nm, dt, field_num, false));
        db.scope_add_symbol_internal(scope, sym, types)?;
        let rnglist = Database::single_point_range(addr);
        let entry = db
            .entries
            .alloc(SymbolEntry::new_dynamic(sym, Varnode::MAPPED, hash, 0, 1, &rnglist));
        db.scope_add_dynamic_map_internal(scope, sym, entry, types);
        Ok(sym)
    }

    pub fn scope_add_symbol_with_conflict(
        glb: &mut Architecture,
        data: &mut Funcdata,
        scope: ScopeId,
        nm: &str,
        ct: Option<TypeId>,
        vn: VarnodeId,
    ) -> Result<EntryId> {
        if !data.vn(vn).is_written() {
            return Err(Error::Lowlevel(
                "Conflict symbol created on illegal Varnode".to_string(),
            ));
        }
        let (db, types) = db_and_types(glb);
        let mut ct = ct;
        if let Some(tp) = ct
            && types.get(tp).has_stripped()
        {
            ct = types.get(tp).get_stripped().or(ct);
        }
        let owner = db.scope_owner(scope);
        let sym = db.symbols.alloc(Symbol::new(owner, nm, ct));
        db.scope_add_symbol_internal(scope, sym, types)?;
        let entry = SymbolEntry::new_conflict(sym, data, vn);
        Database::scope_add_map(glb, scope, entry)
    }

    pub fn scope_build_default_name(
        glb: &Architecture,
        data: Option<&mut Funcdata>,
        scope: ScopeId,
        sym: SymbolId,
        base: &mut i32,
        vn: Option<VarnodeId>,
    ) -> Result<String> {
        let db = db_ref(glb);
        let symbol = db.symbol(sym);
        let sym_type = symbol.get_type();
        if let Some(vn) = vn {
            let data = data.expect("varnode naming requires its function");
            if !data.vn(vn).is_constant() {
                let mut usepoint = Address::invalid();
                if !data.vn(vn).is_addr_tied() && db.scope(scope).fd.is_some() {
                    usepoint = data.vn_get_use_point(vn);
                }
                let high = data.vn(vn).get_high()?;
                let vn_addr = data.vn(vn).get_addr().clone();
                let vn_flags = data.vn(vn).get_flags();
                if symbol.get_category() == Symbol::FUNCTION_PARAMETER || data.high_is_input(high) {
                    let mut index = -1;
                    if symbol.get_category() == Symbol::FUNCTION_PARAMETER {
                        index = symbol.get_category_index() as i32 + 1;
                    }
                    return Database::scope_build_variable_name(
                        glb,
                        Some(data),
                        scope,
                        &vn_addr,
                        &usepoint,
                        sym_type,
                        &mut index,
                        vn_flags | Varnode::INPUT,
                    );
                }
                return Database::scope_build_variable_name(
                    glb,
                    Some(data),
                    scope,
                    &vn_addr,
                    &usepoint,
                    sym_type,
                    base,
                    vn_flags,
                );
            }
            return Database::scope_build_default_name_entries(glb, Some(data), scope, sym, base);
        }
        Database::scope_build_default_name_entries(glb, data.map(|fd| &*fd), scope, sym, base)
    }

    fn scope_build_default_name_entries(
        glb: &Architecture,
        data: Option<&Funcdata>,
        scope: ScopeId,
        sym: SymbolId,
        base: &mut i32,
    ) -> Result<String> {
        let db = db_ref(glb);
        let symbol = db.symbol(sym);
        let sym_type = symbol.get_type();
        if symbol.num_entries() != 0 {
            let entry = db.entry(symbol.get_map_entry_index(0));
            let addr = if !entry.is_dynamic() {
                entry.get_addr().clone()
            } else {
                Address::invalid()
            };
            let usepoint = entry.get_first_use_address();
            let mut flags = if usepoint.is_invalid() { Varnode::ADDRTIED } else { 0 };
            if symbol.get_category() == Symbol::FUNCTION_PARAMETER {
                flags |= Varnode::INPUT;
                let mut index = symbol.get_category_index() as i32 + 1;
                return Database::scope_build_variable_name(
                    glb, data, scope, &addr, &usepoint, sym_type, &mut index, flags,
                );
            }
            return Database::scope_build_variable_name(glb, data, scope, &addr, &usepoint, sym_type, base, flags);
        }
        Database::scope_build_variable_name(
            glb,
            data,
            scope,
            &Address::invalid(),
            &Address::invalid(),
            sym_type,
            base,
            0,
        )
    }

    pub fn scope_is_read_only(&self, scope: ScopeId, addr: &Address, size: i32, usepoint: &Address) -> bool {
        let mut flags = 0;
        self.scope_query_properties(scope, addr, size, usepoint, &mut flags);
        (flags & Varnode::READONLY) != 0
    }

    pub fn clear_resolve(&mut self, scope: ScopeId) {
        if Some(scope) == self.globalscope {
            return;
        }
        if self.scope(scope).fd.is_some() {
            return;
        }
        let ranges: Vec<Range> = self.scope(scope).rangetree.iter().cloned().collect();
        for rng in ranges {
            let (mut first, second) = self.resolvemap.find(&rng.get_first_addr());
            while first != second {
                if self.resolvemap.part(first).scope == scope {
                    self.resolvemap.erase_part(first);
                    break;
                }
                first += 1;
            }
        }
    }

    pub fn clear_references(&mut self, scope: ScopeId) {
        let children: Vec<ScopeId> = self.scope(scope).children.values().copied().collect();
        for child in children {
            self.clear_references(child);
        }
        let unique_id = self.scope(scope).unique_id;
        self.idmap.remove(&unique_id);
        self.clear_resolve(scope);
    }

    pub fn fill_resolve(&mut self, scope: ScopeId) {
        if Some(scope) == self.globalscope {
            return;
        }
        if self.scope(scope).fd.is_some() {
            return;
        }
        let ranges: Vec<Range> = self.scope(scope).rangetree.iter().cloned().collect();
        for rng in ranges {
            self.resolvemap
                .insert(&scope, rng.get_first_addr(), rng.get_last_addr());
        }
    }

    pub fn parse_parent_tag(&mut self, decoder: &mut dyn Decoder) -> Result<ScopeId> {
        let elem_id = decoder.open_element_expect(ELEM_PARENT)?;
        let id = decoder.read_unsigned_integer_attr(ATTRIB_ID)?;
        let res = self
            .resolve_scope(id)
            .ok_or_else(|| Error::Lowlevel("Could not find scope matching id".to_string()))?;
        decoder.close_element(elem_id)?;
        Ok(res)
    }

    pub fn adjust_caches(&mut self, num_spaces: i32) {
        let scopes: Vec<ScopeId> = self.idmap.values().copied().collect();
        for scope in scopes {
            self.scope_adjust_caches(scope, num_spaces);
        }
    }

    pub fn attach_scope(&mut self, newscope: ScopeId, parent: Option<ScopeId>) -> Result<()> {
        let res = self.attach_scope_checked(newscope, parent);
        if res.is_err() {
            self.destroy_scope_tree(newscope);
        }
        res
    }

    fn attach_scope_checked(&mut self, newscope: ScopeId, parent: Option<ScopeId>) -> Result<()> {
        let Some(parent) = parent else {
            if self.globalscope.is_some() {
                return Err(Error::Lowlevel("Multiple global scopes".to_string()));
            }
            if !self.scope(newscope).name.is_empty() {
                return Err(Error::Lowlevel("Global scope does not have empty name".to_string()));
            }
            self.globalscope = Some(newscope);
            let unique_id = self.scope(newscope).unique_id;
            self.idmap.insert(unique_id, newscope);
            return Ok(());
        };
        if self.scope(newscope).name.is_empty() {
            return Err(Error::Lowlevel("Non-global scope has empty name".to_string()));
        }
        let unique_id = self.scope(newscope).unique_id;
        if self.idmap.contains_key(&unique_id) {
            return Err(Error::Recov(format!(
                "Duplicate scope id: {}",
                self.scope_get_full_name(newscope, "")
            )));
        }
        self.idmap.insert(unique_id, newscope);
        self.scope_attach_scope(parent, newscope)
    }

    pub fn delete_scope(&mut self, scope: ScopeId) -> Result<()> {
        self.clear_references(scope);
        if self.globalscope == Some(scope) {
            self.globalscope = None;
            self.destroy_scope_tree(scope);
            return Ok(());
        }
        let unique_id = self.scope(scope).unique_id;
        let parent = self.scope(scope).parent;
        let found = parent.is_some_and(|parent| self.scope(parent).children.contains_key(&unique_id));
        match parent {
            Some(parent) if found => {
                self.scope_detach_scope(parent, unique_id);
                Ok(())
            }
            _ => Err(Error::Lowlevel(format!(
                "Could not remove parent reference to: {}",
                self.scope(scope).name
            ))),
        }
    }

    pub fn delete_sub_scopes(&mut self, scope: ScopeId) -> Result<()> {
        let children: Vec<(u64, ScopeId)> = self
            .scope(scope)
            .children
            .iter()
            .map(|(key, child)| (*key, *child))
            .collect();
        for (key, child) in children {
            self.clear_references(child);
            self.scope_detach_scope(scope, key);
        }
        Ok(())
    }

    pub fn clear_unlocked(&mut self, scope: ScopeId, types: &mut TypeFactory) -> Result<()> {
        let children: Vec<ScopeId> = self.scope(scope).children.values().copied().collect();
        for child in children {
            self.clear_unlocked(child, types)?;
        }
        self.scope_clear_unlocked(scope, types)
    }

    pub fn set_range(&mut self, scope: ScopeId, rlist: &RangeList) {
        self.clear_resolve(scope);
        self.scope_mut(scope).rangetree = rlist.clone();
        self.fill_resolve(scope);
    }

    pub fn add_range(&mut self, scope: ScopeId, spc: &SpaceRef, first: u64, last: u64) {
        self.clear_resolve(scope);
        self.scope_mut(scope).add_range(spc, first, last);
        self.fill_resolve(scope);
    }

    pub fn remove_range(&mut self, scope: ScopeId, spc: &SpaceRef, first: u64, last: u64) {
        self.clear_resolve(scope);
        self.scope_mut(scope).remove_range(spc, first, last);
        self.fill_resolve(scope);
    }

    pub fn get_global_scope(&self) -> Option<ScopeId> {
        self.globalscope
    }

    pub fn resolve_scope(&self, id: u64) -> Option<ScopeId> {
        self.idmap.get(&id).copied()
    }

    fn find_from(text: &str, pattern: &str, start: usize) -> Option<usize> {
        text.get(start..)
            .and_then(|rest| rest.find(pattern))
            .map(|pos| pos + start)
    }

    pub fn resolve_scope_from_symbol_name(
        &self,
        fullname: &str,
        delim: &str,
        basename: &mut String,
        start: Option<ScopeId>,
    ) -> Option<ScopeId> {
        let mut start = start.or(self.globalscope);
        let mut mark = 0;
        let templateopen = fullname.find('<');
        loop {
            let Some(endmark) = Database::find_from(fullname, delim, mark) else {
                break;
            };
            if templateopen.is_some_and(|open| endmark > open) {
                break;
            }
            if endmark == 0 {
                start = self.globalscope;
            } else {
                let scopename = &fullname[mark..endmark];
                start = self.scope_resolve_scope(start?, scopename, self.id_by_name_hash);
                start?;
            }
            mark = endmark + delim.len();
        }
        *basename = fullname[mark..].to_string();
        start
    }

    pub fn find_create_scope(
        &mut self,
        id: u64,
        nm: &str,
        parent: Option<ScopeId>,
        num_spaces: i32,
    ) -> Result<ScopeId> {
        if let Some(res) = self.resolve_scope(id) {
            return Ok(res);
        }
        let global = self.globalscope.expect("database has no global scope");
        let res = self.scope_build_sub_scope(global, id, nm, num_spaces);
        self.attach_scope(res, parent)?;
        Ok(res)
    }

    pub fn find_create_scope_from_symbol_name(
        &mut self,
        fullname: &str,
        delim: &str,
        basename: &mut String,
        start: Option<ScopeId>,
        num_spaces: i32,
    ) -> Result<ScopeId> {
        let mut start = start.or(self.globalscope).expect("database has no global scope");
        let mut mark = 0;
        let templateopen = fullname.find('<');
        loop {
            let Some(endmark) = Database::find_from(fullname, delim, mark) else {
                break;
            };
            if templateopen.is_some_and(|open| endmark > open) {
                break;
            }
            if !self.id_by_name_hash {
                return Err(Error::Lowlevel("Scope name hashes not allowed".to_string()));
            }
            let scopename = &fullname[mark..endmark];
            let name_id = Scope::hash_scope_name(self.scope(start).unique_id, scopename);
            start = self.find_create_scope(name_id, scopename, Some(start), num_spaces)?;
            mark = endmark + delim.len();
        }
        *basename = fullname[mark..].to_string();
        Ok(start)
    }

    pub fn map_scope(&self, qpoint: ScopeId, addr: &Address, _usepoint: &Address) -> ScopeId {
        if self.resolvemap.empty() {
            return qpoint;
        }
        let (first, second) = self.resolvemap.find(addr);
        if first != second {
            return self.resolvemap.part(first).get_scope();
        }
        qpoint
    }

    pub fn get_property(&self, addr: &Address) -> u32 {
        *self.flagbase.get_value(addr)
    }

    fn property_keys(&mut self, range: &Range, manager: &AddrSpaceManager) -> Vec<Address> {
        let addr1 = range.get_first_addr();
        let addr2 = range.get_last_addr_open(manager);
        self.flagbase.split(&addr1);
        if !addr2.is_invalid() {
            self.flagbase.split(&addr2);
        }
        self.flagbase
            .keys_from(&addr1)
            .into_iter()
            .take_while(|key| addr2.is_invalid() || *key != addr2)
            .collect()
    }

    pub fn set_property_range(&mut self, flags: u32, range: &Range, manager: &AddrSpaceManager) {
        for key in self.property_keys(range, manager) {
            if let Some(val) = self.flagbase.get_mut(&key) {
                *val |= flags;
            }
        }
    }

    pub fn clear_property_range(&mut self, flags: u32, range: &Range, manager: &AddrSpaceManager) {
        let flags = !flags;
        for key in self.property_keys(range, manager) {
            if let Some(val) = self.flagbase.get_mut(&key) {
                *val &= flags;
            }
        }
    }

    pub fn set_properties(&mut self, newflags: &PartMap<Address, u32>) {
        self.flagbase = newflags.clone();
    }

    pub fn get_properties(&self) -> &PartMap<Address, u32> {
        &self.flagbase
    }

    pub fn encode(glb: &Architecture, encoder: &mut dyn Encoder) -> Result<()> {
        let db = db_ref(glb);
        encoder.open_element(ELEM_DB);
        if db.id_by_name_hash {
            encoder.write_bool(ATTRIB_SCOPEIDBYNAME, true);
        }
        for (addr, val) in db.flagbase.iter() {
            encoder.open_element(ELEM_PROPERTY_CHANGEPOINT);
            addr.get_space()
                .ok_or_else(|| Error::Lowlevel("property change point has no space".to_string()))?
                .encode_attributes(encoder, addr.get_offset())?;
            encoder.write_unsigned_integer(ATTRIB_VAL, *val as u64);
            encoder.close_element(ELEM_PROPERTY_CHANGEPOINT);
        }
        if let Some(global) = db.globalscope {
            Database::scope_encode_recursive(glb, global, encoder, true)?;
        }
        encoder.close_element(ELEM_DB);
        Ok(())
    }

    pub fn decode(glb: &mut Architecture, decoder: &mut dyn Decoder) -> Result<()> {
        let elem_id = decoder.open_element_expect(ELEM_DB)?;
        db_mut(glb).id_by_name_hash = false;
        loop {
            let attrib_id = decoder.get_next_attribute_id()?;
            if attrib_id == 0 {
                break;
            }
            if attrib_id == ATTRIB_SCOPEIDBYNAME {
                let val = decoder.read_bool()?;
                db_mut(glb).id_by_name_hash = val;
            }
        }
        loop {
            let sub_id = decoder.peek_element()?;
            if sub_id != ELEM_PROPERTY_CHANGEPOINT {
                break;
            }
            decoder.open_element()?;
            let val = decoder.read_unsigned_integer_attr(ATTRIB_VAL)? as u32;
            let vdata = VarnodeData::decode_from_attributes(decoder)?;
            let addr = vdata.get_addr();
            decoder.close_element(sub_id)?;
            *db_mut(glb).flagbase.split(&addr) = val;
        }
        loop {
            let sub_id = decoder.open_element()?;
            if sub_id != ELEM_SCOPE {
                break;
            }
            let mut name = String::new();
            let mut display_name = String::new();
            let mut id: u64 = 0;
            loop {
                let attrib_id = decoder.get_next_attribute_id()?;
                if attrib_id == 0 {
                    break;
                }
                if attrib_id == ATTRIB_NAME {
                    name = decoder.read_string()?;
                } else if attrib_id == ATTRIB_ID {
                    id = decoder.read_unsigned_integer()?;
                } else if attrib_id == ATTRIB_LABEL {
                    display_name = decoder.read_string()?;
                }
            }
            let mut parent_scope = None;
            let parent_id = decoder.peek_element()?;
            if parent_id == ELEM_PARENT {
                parent_scope = Some(db_mut(glb).parse_parent_tag(decoder)?);
            }
            let num_spaces = glb.manager.num_spaces();
            let new_scope = db_mut(glb).find_create_scope(id, &name, parent_scope, num_spaces)?;
            if !display_name.is_empty() {
                db_mut(glb).scope_mut(new_scope).set_display_name(&display_name);
            }
            Database::scope_decode(glb, new_scope, decoder)?;
            decoder.close_element(sub_id)?;
        }
        decoder.close_element(elem_id)
    }

    pub fn decode_scope(glb: &mut Architecture, decoder: &mut dyn Decoder, new_scope: ScopeId) -> Result<()> {
        let elem_id = decoder.open_element()?;
        if elem_id == ELEM_SCOPE {
            let parent_scope = match db_mut(glb).parse_parent_tag(decoder) {
                Ok(parent) => parent,
                Err(err) => {
                    db_mut(glb).destroy_scope_tree(new_scope);
                    return Err(err);
                }
            };
            db_mut(glb).attach_scope(new_scope, Some(parent_scope))?;
            Database::scope_decode(glb, new_scope, decoder)?;
        } else {
            let prefix = Database::scope_decode_wrapping_attributes(glb, new_scope, decoder)
                .and_then(|_| decoder.open_element_expect(ELEM_SCOPE))
                .and_then(|sub_id| db_mut(glb).parse_parent_tag(decoder).map(|parent| (sub_id, parent)));
            let (sub_id, parent_scope) = match prefix {
                Ok(found) => found,
                Err(err) => {
                    db_mut(glb).destroy_scope_tree(new_scope);
                    return Err(err);
                }
            };
            db_mut(glb).attach_scope(new_scope, Some(parent_scope))?;
            Database::scope_decode(glb, new_scope, decoder)?;
            decoder.close_element(sub_id)?;
        }
        decoder.close_element(elem_id)
    }

    pub fn decode_scope_path(glb: &mut Architecture, decoder: &mut dyn Decoder) -> Result<ScopeId> {
        let mut curscope = db_ref(glb).get_global_scope().expect("database has no global scope");
        let elem_id = decoder.open_element_expect(ELEM_PARENT)?;
        let sub_id = decoder.open_element()?;
        decoder.close_element_skipping(sub_id)?;
        loop {
            let sub_id = decoder.open_element()?;
            if sub_id != ELEM_VAL {
                break;
            }
            let mut display_name = String::new();
            let mut scope_id: u64 = 0;
            loop {
                let attrib_id = decoder.get_next_attribute_id()?;
                if attrib_id == 0 {
                    break;
                }
                if attrib_id == ATTRIB_ID {
                    scope_id = decoder.read_unsigned_integer()?;
                } else if attrib_id == ATTRIB_LABEL {
                    display_name = decoder.read_string()?;
                }
            }
            let name = decoder.read_string_attr(ATTRIB_CONTENT)?;
            if scope_id == 0 {
                return Err(Error::Decoder("Missing name and id in scope".to_string()));
            }
            let num_spaces = glb.manager.num_spaces();
            curscope = db_mut(glb).find_create_scope(scope_id, &name, Some(curscope), num_spaces)?;
            if !display_name.is_empty() {
                db_mut(glb).scope_mut(curscope).set_display_name(&display_name);
            }
            decoder.close_element(sub_id)?;
        }
        decoder.close_element(elem_id)?;
        Ok(curscope)
    }
}
