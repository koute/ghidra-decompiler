use std::collections::BTreeMap;
use std::fmt::Write;

use crate::address::ELEM_ADDR;
use crate::architecture::Architecture;
use crate::arena::Arena;
use crate::cover::{Cover, PcodeOpSet};
use crate::database::{Database, EntryId, Symbol, SymbolId};
use crate::define_id;
use crate::error::{Error, Result};
use crate::funcdata::Funcdata;
use crate::marshal::{ATTRIB_OFFSET, ATTRIB_REF, ATTRIB_TYPELOCK, AttributeId, ElementId, Encoder};
use crate::op::OpId;
use crate::opcodes::OpCode;
use crate::space::SpaceType;
use crate::types::{TypeFactory, TypeId, TypeMetatype};
use crate::varnode::{Varnode, VarnodeId};

pub const ATTRIB_CLASS: AttributeId = AttributeId::new("class", 66);
pub const ATTRIB_REPREF: AttributeId = AttributeId::new("repref", 67);
pub const ATTRIB_SYMREF: AttributeId = AttributeId::new("symref", 68);
pub const ELEM_HIGH: ElementId = ElementId::new("high", 82);

define_id!(HighId);

define_id!(GroupId);

fn type_factory(glb: &Architecture) -> &TypeFactory {
    glb.types.as_deref().expect("architecture has no type factory")
}

fn symbol_table(glb: &Architecture) -> &Database {
    glb.symboltab.as_deref().expect("architecture has no symbol table")
}

#[derive(Clone, Debug, Default)]
pub struct VariableGroup {
    pub(crate) piece_set: BTreeMap<(i32, i32), HighId>,
    pub(crate) size: i32,
    pub(crate) symbol_offset: i32,
}

impl VariableGroup {
    pub fn new() -> VariableGroup {
        VariableGroup {
            piece_set: BTreeMap::new(),
            size: 0,
            symbol_offset: 0,
        }
    }

    pub fn empty(&self) -> bool {
        self.piece_set.is_empty()
    }

    pub fn add_piece(
        groups: &mut Arena<GroupId, VariableGroup>,
        highs: &mut Arena<HighId, HighVariable>,
        group: GroupId,
        piece_high: HighId,
    ) -> Result<()> {
        let piece = highs
            .get_mut(piece_high)
            .piece
            .as_mut()
            .expect("high variable has no piece");
        piece.group = group;
        let key = (piece.group_offset, piece.size);
        let piece_max = piece.group_offset + piece.size;
        let group_data = groups.get_mut(group);
        if group_data.piece_set.contains_key(&key) {
            return Err(Error::Lowlevel("Duplicate VariablePiece".to_string()));
        }
        group_data.piece_set.insert(key, piece_high);
        if piece_max > group_data.size {
            group_data.size = piece_max;
        }
        Ok(())
    }

    pub fn adjust_offsets(
        groups: &mut Arena<GroupId, VariableGroup>,
        highs: &mut Arena<HighId, HighVariable>,
        group: GroupId,
        amt: i32,
    ) {
        let group_data = groups.get_mut(group);
        let old_set = std::mem::take(&mut group_data.piece_set);
        for ((offset, size), piece_high) in old_set {
            if let Some(piece) = highs.get_mut(piece_high).piece.as_mut() {
                piece.group_offset += amt;
            }
            group_data.piece_set.insert((offset + amt, size), piece_high);
        }
        group_data.size += amt;
    }

    pub fn remove_piece(&mut self, piece: &VariablePiece) {
        self.piece_set.remove(&(piece.group_offset, piece.size));
    }

    pub fn get_size(&self) -> i32 {
        self.size
    }

    pub fn set_symbol_offset(&mut self, val: i32) {
        self.symbol_offset = val;
    }

    pub fn get_symbol_offset(&self) -> i32 {
        self.symbol_offset
    }

    pub fn combine_groups(data: &mut Funcdata, group: GroupId, op2: GroupId) -> Result<()> {
        let pieces: Vec<HighId> = data.groups.get(op2).piece_set.values().copied().collect();
        for piece_high in pieces {
            VariablePiece::transfer_group(data, piece_high, group)?;
        }
        Ok(())
    }
}

pub struct VariablePiece {
    pub(crate) group: GroupId,
    pub(crate) high: HighId,
    pub(crate) group_offset: i32,
    pub(crate) size: i32,
    pub(crate) intersection: Vec<HighId>,
    pub(crate) cover: Cover,
}

impl VariablePiece {
    pub fn create(data: &mut Funcdata, high: HighId, offset: i32, grp: Option<HighId>) -> Result<()> {
        let first = data.high(high).get_instance(0);
        let size = data.vn(first).get_size();
        let group = match grp {
            Some(grp_high) => data
                .high(grp_high)
                .piece
                .as_ref()
                .expect("group high variable has no piece")
                .get_group(),
            None => data.groups.alloc(VariableGroup::new()),
        };
        data.high_mut(high).piece = Some(VariablePiece {
            group,
            high,
            group_offset: offset,
            size,
            intersection: Vec::new(),
            cover: Cover::new(),
        });
        VariableGroup::add_piece(&mut data.groups, &mut data.highs, group, high)
    }

    pub fn destroy(data: &mut Funcdata, high: HighId) {
        if let Some(piece) = data.high_mut(high).piece.take() {
            VariablePiece::release(data, piece);
        }
    }

    fn release(data: &mut Funcdata, piece: VariablePiece) {
        let group = piece.group;
        data.groups.get_mut(group).remove_piece(&piece);
        if data.groups.get(group).empty() {
            data.groups.remove(group);
        } else {
            VariablePiece::mark_group_intersection_dirty(&mut data.highs, &data.groups, group);
        }
    }

    pub fn get_high(&self) -> HighId {
        self.high
    }

    pub fn get_group(&self) -> GroupId {
        self.group
    }

    pub fn get_offset(&self) -> i32 {
        self.group_offset
    }

    pub fn get_size(&self) -> i32 {
        self.size
    }

    pub fn get_cover(&self) -> &Cover {
        &self.cover
    }

    pub fn num_intersection(&self) -> i32 {
        self.intersection.len() as i32
    }

    pub fn get_intersection(&self, index: i32) -> HighId {
        self.intersection[index as usize]
    }

    fn mark_group_intersection_dirty(
        highs: &mut Arena<HighId, HighVariable>,
        groups: &Arena<GroupId, VariableGroup>,
        group: GroupId,
    ) {
        for piece_high in groups.get(group).piece_set.values() {
            if let Some(high) = highs.try_get_mut(*piece_high) {
                high.highflags |= HighVariable::INTERSECTDIRTY | HighVariable::EXTENDCOVERDIRTY;
            }
        }
    }

    pub fn mark_intersection_dirty(
        highs: &mut Arena<HighId, HighVariable>,
        groups: &Arena<GroupId, VariableGroup>,
        high: HighId,
    ) {
        let group = highs
            .get(high)
            .piece
            .as_ref()
            .expect("high variable has no piece")
            .group;
        VariablePiece::mark_group_intersection_dirty(highs, groups, group);
    }

    pub fn mark_extend_cover_dirty(highs: &mut Arena<HighId, HighVariable>, high: HighId) {
        if (highs.get(high).highflags & HighVariable::INTERSECTDIRTY) != 0 {
            return;
        }
        let intersection = highs
            .get(high)
            .piece
            .as_ref()
            .expect("high variable has no piece")
            .intersection
            .clone();
        for other in intersection {
            if let Some(other_high) = highs.try_get_mut(other) {
                other_high.highflags |= HighVariable::EXTENDCOVERDIRTY;
            }
        }
        highs.get_mut(high).highflags |= HighVariable::EXTENDCOVERDIRTY;
    }

    pub fn update_intersections(data: &mut Funcdata, high: HighId) {
        if (data.high(high).highflags & HighVariable::INTERSECTDIRTY) == 0 {
            return;
        }
        let piece = data.high(high).piece.as_ref().expect("high variable has no piece");
        let group_offset = piece.group_offset;
        let end_offset = group_offset + piece.size;
        let mut intersection = Vec::new();
        for other_high in data.groups.get(piece.group).piece_set.values() {
            if *other_high == high {
                continue;
            }
            let other = data
                .high(*other_high)
                .piece
                .as_ref()
                .expect("group member has no piece");
            if end_offset <= other.group_offset {
                continue;
            }
            let other_end_offset = other.group_offset + other.size;
            if group_offset >= other_end_offset {
                continue;
            }
            intersection.push(*other_high);
        }
        let high_data = data.high_mut(high);
        high_data
            .piece
            .as_mut()
            .expect("high variable has no piece")
            .intersection = intersection;
        high_data.highflags &= !HighVariable::INTERSECTDIRTY;
    }

    pub fn update_cover(data: &mut Funcdata, high: HighId) {
        if (data.high(high).highflags & (HighVariable::COVERDIRTY | HighVariable::EXTENDCOVERDIRTY)) == 0 {
            return;
        }
        data.high_update_internal_cover(high);
        let mut cover = data.high(high).internal_cover.clone();
        let intersection = data
            .high(high)
            .piece
            .as_ref()
            .expect("high variable has no piece")
            .intersection
            .clone();
        for other in intersection {
            data.high_update_internal_cover(other);
            cover.merge(&data.high(other).internal_cover, data);
        }
        let high_data = data.high_mut(high);
        high_data.piece.as_mut().expect("high variable has no piece").cover = cover;
        high_data.highflags &= !HighVariable::EXTENDCOVERDIRTY;
    }

    pub fn transfer_group(data: &mut Funcdata, high: HighId, new_group: GroupId) -> Result<()> {
        let (group, key) = {
            let piece = data.high(high).piece.as_ref().expect("high variable has no piece");
            (piece.group, (piece.group_offset, piece.size))
        };
        data.groups.get_mut(group).piece_set.remove(&key);
        if data.groups.get(group).empty() {
            data.groups.remove(group);
        }
        VariableGroup::add_piece(&mut data.groups, &mut data.highs, new_group, high)
    }

    pub fn set_high(&mut self, new_high: HighId) {
        self.high = new_high;
    }

    pub fn merge_groups(data: &mut Funcdata, high: HighId, op2: HighId, merge_pairs: &mut Vec<HighId>) -> Result<()> {
        let (this_group, this_offset) = {
            let piece = data.high(high).piece.as_ref().expect("high variable has no piece");
            (piece.group, piece.group_offset)
        };
        let (op2_group, op2_offset) = {
            let piece = data.high(op2).piece.as_ref().expect("high variable has no piece");
            (piece.group, piece.group_offset)
        };
        let diff = this_offset - op2_offset;
        if diff > 0 {
            VariableGroup::adjust_offsets(&mut data.groups, &mut data.highs, op2_group, diff);
        } else if diff < 0 {
            VariableGroup::adjust_offsets(&mut data.groups, &mut data.highs, this_group, -diff);
        }
        let op2_pieces: Vec<((i32, i32), HighId)> = data
            .groups
            .get(op2_group)
            .piece_set
            .iter()
            .map(|(key, value)| (*key, *value))
            .collect();
        for (key, piece_high) in op2_pieces {
            let matched = data.groups.get(this_group).piece_set.get(&key).copied();
            match matched {
                Some(match_high) => {
                    merge_pairs.push(match_high);
                    merge_pairs.push(piece_high);
                    let piece = data
                        .high_mut(piece_high)
                        .piece
                        .take()
                        .expect("group member has no piece");
                    VariablePiece::release(data, piece);
                }
                None => VariablePiece::transfer_group(data, piece_high, this_group)?,
            }
        }
        Ok(())
    }
}

pub struct HighVariable {
    pub(crate) inst: Vec<VarnodeId>,
    pub(crate) num_merge_classes: i32,
    pub(crate) highflags: u32,
    pub(crate) flags: u32,
    pub(crate) tp: Option<TypeId>,
    pub(crate) name_representative: Option<VarnodeId>,
    pub(crate) internal_cover: Cover,
    pub(crate) piece: Option<VariablePiece>,
    pub(crate) symbol: Option<SymbolId>,
    pub(crate) symboloffset: i32,
}

impl HighVariable {
    pub const FLAGSDIRTY: u32 = 1;
    pub const NAMEREPDIRTY: u32 = 2;
    pub const TYPEDIRTY: u32 = 4;
    pub const COVERDIRTY: u32 = 8;
    pub const SYMBOLDIRTY: u32 = 0x10;
    pub const COPY_IN1: u32 = 0x20;
    pub const COPY_IN2: u32 = 0x40;
    pub const TYPE_FINALIZED: u32 = 0x80;
    pub const UNMERGED: u32 = 0x100;
    pub const INTERSECTDIRTY: u32 = 0x200;
    pub const EXTENDCOVERDIRTY: u32 = 0x400;

    pub fn instance_index(&self, vn: VarnodeId) -> i32 {
        for (index, instance) in self.inst.iter().enumerate() {
            if *instance == vn {
                return index as i32;
            }
        }
        -1
    }

    pub fn set_copy_in1(&mut self) {
        self.highflags |= HighVariable::COPY_IN1;
    }

    pub fn set_copy_in2(&mut self) {
        self.highflags |= HighVariable::COPY_IN2;
    }

    pub fn clear_copy_ins(&mut self) {
        self.highflags &= !(HighVariable::COPY_IN1 | HighVariable::COPY_IN2);
    }

    pub fn has_copy_in1(&self) -> bool {
        (self.highflags & HighVariable::COPY_IN1) != 0
    }

    pub fn has_copy_in2(&self) -> bool {
        (self.highflags & HighVariable::COPY_IN2) != 0
    }

    pub fn set_symbol_reference(&mut self, sym: SymbolId, off: i32) {
        self.symbol = Some(sym);
        self.symboloffset = off;
        self.highflags &= !HighVariable::SYMBOLDIRTY;
    }

    pub fn flags_dirty(&mut self) {
        self.highflags |= HighVariable::FLAGSDIRTY | HighVariable::NAMEREPDIRTY;
    }

    pub fn cover_dirty(highs: &mut Arena<HighId, HighVariable>, high: HighId) {
        highs.get_mut(high).highflags |= HighVariable::COVERDIRTY;
        if highs.get(high).piece.is_some() {
            VariablePiece::mark_extend_cover_dirty(highs, high);
        }
    }

    pub fn type_dirty(&mut self) {
        self.highflags |= HighVariable::TYPEDIRTY;
    }

    pub fn symbol_dirty(&mut self) {
        self.highflags |= HighVariable::SYMBOLDIRTY;
    }

    pub fn set_unmerged(&mut self) {
        self.highflags |= HighVariable::UNMERGED;
    }

    pub fn is_cover_dirty(&self) -> bool {
        (self.highflags & (HighVariable::COVERDIRTY | HighVariable::EXTENDCOVERDIRTY)) != 0
    }

    pub fn get_cover(&self) -> &Cover {
        match &self.piece {
            None => &self.internal_cover,
            Some(piece) => piece.get_cover(),
        }
    }

    pub fn get_symbol_offset(&self) -> i32 {
        self.symboloffset
    }

    pub fn num_instances(&self) -> i32 {
        self.inst.len() as i32
    }

    pub fn get_instance(&self, index: i32) -> VarnodeId {
        self.inst[index as usize]
    }

    pub fn print_cover(&self, out: &mut String, data: &Funcdata) {
        if (self.highflags & HighVariable::COVERDIRTY) == 0 {
            self.internal_cover.print(out, data);
        } else {
            out.push_str("Cover dirty");
        }
    }

    pub fn get_num_merge_classes(&self) -> i32 {
        self.num_merge_classes
    }

    pub fn set_mark(&mut self) {
        self.flags |= Varnode::MARK;
    }

    pub fn clear_mark(&mut self) {
        self.flags &= !Varnode::MARK;
    }

    pub fn is_mark(&self) -> bool {
        (self.flags & Varnode::MARK) != 0
    }

    pub fn is_unmerged(&self) -> bool {
        (self.highflags & HighVariable::UNMERGED) != 0
    }

    pub fn is_same_group(&self, op2: &HighVariable) -> bool {
        match (&self.piece, &op2.piece) {
            (Some(piece), Some(other)) => piece.get_group() == other.get_group(),
            _ => false,
        }
    }

    pub fn is_unattached(&self) -> bool {
        self.inst.is_empty()
    }

    pub fn compare_just_loc(first: &Varnode, second: &Varnode) -> bool {
        first.get_addr() < second.get_addr()
    }
}

impl Funcdata {
    fn high_lower_bound(&self, high: HighId, vn: VarnodeId) -> usize {
        let target = self.vn(vn);
        self.high(high)
            .inst
            .partition_point(|instance| HighVariable::compare_just_loc(self.vn(*instance), target))
    }

    pub fn high_create(&mut self, vn: VarnodeId, glb: &Architecture) -> Result<HighId> {
        let high = self.high_create_unmapped(vn);
        if self.vn(vn).get_symbol_entry().is_some() {
            self.high_set_symbol(high, vn, glb)?;
        }
        Ok(high)
    }

    pub(crate) fn high_create_unmapped(&mut self, vn: VarnodeId) -> HighId {
        let high = self.highs.alloc(HighVariable {
            inst: vec![vn],
            num_merge_classes: 1,
            highflags: HighVariable::FLAGSDIRTY
                | HighVariable::NAMEREPDIRTY
                | HighVariable::TYPEDIRTY
                | HighVariable::COVERDIRTY,
            flags: 0,
            tp: None,
            name_representative: None,
            internal_cover: Cover::new(),
            piece: None,
            symbol: None,
            symboloffset: -1,
        });
        self.vn_mut(vn).set_high(Some(high), 0);
        high
    }

    pub fn high_destroy(&mut self, high: HighId) {
        if self.high(high).piece.is_some() {
            VariablePiece::destroy(self, high);
        }
        self.highs.remove(high);
    }

    pub fn high_update_flags(&mut self, high: HighId) {
        if (self.high(high).highflags & HighVariable::FLAGSDIRTY) == 0 {
            return;
        }
        let mut fl = 0;
        for instance in self.high(high).inst.iter() {
            fl |= self.vn(*instance).get_flags();
        }
        let high_data = self.high_mut(high);
        high_data.flags &= Varnode::MARK | Varnode::TYPELOCK;
        high_data.flags |= fl & !(Varnode::MARK | Varnode::DIRECTWRITE | Varnode::TYPELOCK);
        high_data.highflags &= !HighVariable::FLAGSDIRTY;
    }

    pub fn high_update_internal_cover(&mut self, high: HighId) {
        if (self.high(high).highflags & HighVariable::COVERDIRTY) == 0 {
            return;
        }
        let mut cover = std::mem::take(&mut self.high_mut(high).internal_cover);
        cover.clear();
        let inst = self.high(high).inst.clone();
        if self.vn(inst[0]).has_cover() {
            for instance in inst {
                self.vn_update_cover(instance);
                let vn_cover = self.vn(instance).get_cover_raw().expect("varnode has no cover");
                cover.merge(vn_cover, self);
            }
        }
        let high_data = self.high_mut(high);
        high_data.internal_cover = cover;
        high_data.highflags &= !HighVariable::COVERDIRTY;
    }

    pub fn high_update_cover(&mut self, high: HighId) {
        if self.high(high).piece.is_none() {
            self.high_update_internal_cover(high);
        } else {
            VariablePiece::update_intersections(self, high);
            VariablePiece::update_cover(self, high);
        }
    }

    pub fn high_update_type(&mut self, high: HighId, glb: &Architecture) {
        if (self.high(high).highflags & HighVariable::TYPEDIRTY) == 0 {
            return;
        }
        self.high_mut(high).highflags &= !HighVariable::TYPEDIRTY;
        if (self.high(high).highflags & HighVariable::TYPE_FINALIZED) != 0 {
            return;
        }
        let vn = self.high_get_type_representative(high, glb);
        self.high_mut(high).tp = Some(self.vn(vn).get_type());
        self.high_strip_type(high, glb);
        let type_lock = self.vn(vn).is_type_lock();
        let high_data = self.high_mut(high);
        high_data.flags &= !Varnode::TYPELOCK;
        if type_lock {
            high_data.flags |= Varnode::TYPELOCK;
        }
    }

    pub fn high_update_symbol(&mut self, high: HighId, glb: &Architecture) {
        if (self.high(high).highflags & HighVariable::SYMBOLDIRTY) == 0 {
            return;
        }
        let high_data = self.high_mut(high);
        high_data.highflags &= !HighVariable::SYMBOLDIRTY;
        high_data.symbol = None;
        let inst = self.high(high).inst.clone();
        for vn in inst {
            if self.vn(vn).get_symbol_entry().is_some() {
                self.high_set_symbol(high, vn, glb)
                    .expect("symbol assignment failed on a clean high variable");
                return;
            }
        }
    }

    pub fn high_remove(&mut self, high: HighId, vn: VarnodeId) {
        let start = self.high_lower_bound(high, vn);
        let has_entry = self.vn(vn).get_symbol_entry().is_some();
        let position = self.high(high).inst[start..]
            .iter()
            .position(|instance| *instance == vn);
        let Some(position) = position else {
            return;
        };
        let high_data = self.high_mut(high);
        high_data.inst.remove(start + position);
        high_data.highflags |=
            HighVariable::FLAGSDIRTY | HighVariable::NAMEREPDIRTY | HighVariable::COVERDIRTY | HighVariable::TYPEDIRTY;
        if has_entry {
            high_data.highflags |= HighVariable::SYMBOLDIRTY;
        }
        if high_data.piece.is_some() {
            VariablePiece::mark_extend_cover_dirty(&mut self.highs, high);
        }
    }

    pub fn high_insert(&mut self, high: HighId, newvn: VarnodeId, merge_group: i16) {
        let position = self.high_lower_bound(high, newvn);
        self.high_mut(high).inst.insert(position, newvn);
        self.vn_mut(newvn).set_high(Some(high), merge_group);
    }

    pub fn high_merge_internal(&mut self, high: HighId, tv2: HighId, isspeculative: bool) -> Result<()> {
        self.high_mut(high).highflags |=
            HighVariable::FLAGSDIRTY | HighVariable::NAMEREPDIRTY | HighVariable::TYPEDIRTY;
        let (tv2_symbol, tv2_flags, tv2_offset, tv2_classes) = {
            let other = self.high(tv2);
            (
                other.symbol,
                other.highflags,
                other.symboloffset,
                other.num_merge_classes,
            )
        };
        if tv2_symbol.is_some() && (tv2_flags & HighVariable::SYMBOLDIRTY) == 0 {
            let high_data = self.high_mut(high);
            high_data.symbol = tv2_symbol;
            high_data.symboloffset = tv2_offset;
            high_data.highflags &= !HighVariable::SYMBOLDIRTY;
        }
        let tv2_inst = self.high(tv2).inst.clone();
        if isspeculative {
            let classes = self.high(high).num_merge_classes;
            for vn in tv2_inst.iter() {
                let group = self.vn(*vn).get_merge_group() + classes as i16;
                self.vn_mut(*vn).set_high(Some(high), group);
            }
            self.high_mut(high).num_merge_classes += tv2_classes;
        } else {
            if self.high(high).num_merge_classes != 1 || tv2_classes != 1 {
                return Err(Error::Lowlevel(
                    "Making a non-speculative merge after speculative merges have occurred".to_string(),
                ));
            }
            for vn in tv2_inst.iter() {
                let group = self.vn(*vn).get_merge_group();
                self.vn_mut(*vn).set_high(Some(high), group);
            }
        }
        let instcopy = std::mem::take(&mut self.high_mut(high).inst);
        let mut merged = Vec::with_capacity(instcopy.len() + tv2_inst.len());
        let mut first_index = 0;
        let mut second_index = 0;
        while first_index < instcopy.len() && second_index < tv2_inst.len() {
            if HighVariable::compare_just_loc(self.vn(tv2_inst[second_index]), self.vn(instcopy[first_index])) {
                merged.push(tv2_inst[second_index]);
                second_index += 1;
            } else {
                merged.push(instcopy[first_index]);
                first_index += 1;
            }
        }
        merged.extend_from_slice(&instcopy[first_index..]);
        merged.extend_from_slice(&tv2_inst[second_index..]);
        self.high_mut(high).inst = merged;
        self.high_mut(tv2).inst.clear();
        if (self.high(high).highflags & HighVariable::COVERDIRTY) == 0
            && (self.high(tv2).highflags & HighVariable::COVERDIRTY) == 0
        {
            let mut cover = std::mem::take(&mut self.high_mut(high).internal_cover);
            cover.merge(&self.high(tv2).internal_cover, self);
            self.high_mut(high).internal_cover = cover;
        } else {
            self.high_mut(high).highflags |= HighVariable::COVERDIRTY;
        }
        self.high_destroy(tv2);
        Ok(())
    }

    pub fn high_merge(
        &mut self,
        high: HighId,
        tv2: HighId,
        test_cache: Option<&mut HighIntersectTest>,
        isspeculative: bool,
    ) -> Result<()> {
        if tv2 == high {
            return Ok(());
        }
        let mut test_cache = test_cache;
        if let Some(cache) = test_cache.as_mut() {
            cache.move_intersect_tests(self, high, tv2);
        }
        let this_has_piece = self.high(high).piece.is_some();
        let tv2_has_piece = self.high(tv2).piece.is_some();
        if !this_has_piece && !tv2_has_piece {
            return self.high_merge_internal(high, tv2, isspeculative);
        }
        if !tv2_has_piece {
            VariablePiece::mark_extend_cover_dirty(&mut self.highs, high);
            return self.high_merge_internal(high, tv2, isspeculative);
        }
        if !this_has_piece {
            self.high_transfer_piece(high, tv2);
            VariablePiece::mark_extend_cover_dirty(&mut self.highs, high);
            return self.high_merge_internal(high, tv2, isspeculative);
        }
        if isspeculative {
            return Err(Error::Lowlevel(
                "Trying speculatively merge variables in separate groups".to_string(),
            ));
        }
        let mut merge_pairs = Vec::new();
        VariablePiece::merge_groups(self, high, tv2, &mut merge_pairs)?;
        for pair in merge_pairs.chunks(2) {
            let high1 = pair[0];
            let high2 = pair[1];
            if let Some(cache) = test_cache.as_mut() {
                cache.move_intersect_tests(self, high1, high2);
            }
            self.high_merge_internal(high1, high2, isspeculative)?;
        }
        VariablePiece::mark_intersection_dirty(&mut self.highs, &self.groups, high);
        Ok(())
    }

    pub fn high_set_symbol(&mut self, high: HighId, vn: VarnodeId, glb: &Architecture) -> Result<()> {
        let symtab = symbol_table(glb);
        let types = type_factory(glb);
        let entry_id = self.vn(vn).get_symbol_entry().expect("varnode has no symbol entry");
        let entry = symtab.entry(entry_id);
        let entry_symbol = entry.get_symbol();
        let high_data = self.high(high);
        if let Some(current) = high_data.symbol
            && current != entry_symbol
            && (high_data.highflags & HighVariable::SYMBOLDIRTY) == 0
        {
            return Err(Error::Lowlevel(format!(
                "Symbols \"{}\" and \"{}\" assigned to the same variable",
                symtab.symbol(current).get_name(),
                symtab.symbol(entry_symbol).get_name()
            )));
        }
        let sym = symtab.symbol(entry_symbol);
        let varnode = self.vn(vn);
        let symboloffset = if varnode.is_proto_partial() && high_data.piece.is_some() {
            let piece = high_data.piece.as_ref().expect("high variable has no piece");
            piece.get_offset() + self.groups.get(piece.get_group()).get_symbol_offset()
        } else if entry.is_dynamic() {
            -1
        } else if sym.get_category() == Symbol::EQUATE {
            -1
        } else {
            let sym_size = types.get(sym.get_type().expect("symbol has no data-type")).get_size();
            if sym_size == varnode.get_size() && entry.get_addr() == varnode.get_addr() && !entry.is_piece() {
                -1
            } else {
                varnode.get_addr().overlap_join(0, entry.get_addr(), sym_size)? + entry.get_offset()
            }
        };
        let partial_union = high_data
            .tp
            .map(|tp| types.get(tp).get_metatype() == TypeMetatype::PartialUnion)
            .unwrap_or(false);
        let high_data = self.high_mut(high);
        high_data.symbol = Some(entry_symbol);
        high_data.symboloffset = symboloffset;
        if partial_union {
            high_data.highflags |= HighVariable::TYPEDIRTY;
        }
        high_data.highflags &= !HighVariable::SYMBOLDIRTY;
        Ok(())
    }

    pub fn high_transfer_piece(&mut self, high: HighId, tv2: HighId) {
        let mut piece = self.high_mut(tv2).piece.take().expect("high variable has no piece");
        piece.set_high(high);
        let group = piece.group;
        let key = (piece.group_offset, piece.size);
        self.high_mut(high).piece = Some(piece);
        let moved_flags = self.high(tv2).highflags & (HighVariable::INTERSECTDIRTY | HighVariable::EXTENDCOVERDIRTY);
        self.high_mut(high).highflags |= moved_flags;
        self.high_mut(tv2).highflags &= !(HighVariable::INTERSECTDIRTY | HighVariable::EXTENDCOVERDIRTY);
        self.groups.get_mut(group).piece_set.insert(key, high);
        let members: Vec<HighId> = self.groups.get(group).piece_set.values().copied().collect();
        for member in members {
            if let Some(member_piece) = self.high_mut(member).piece.as_mut() {
                for other in member_piece.intersection.iter_mut() {
                    if *other == tv2 {
                        *other = high;
                    }
                }
            }
        }
    }

    pub fn high_strip_type(&mut self, high: HighId, glb: &Architecture) {
        let types = type_factory(glb);
        let symtab = symbol_table(glb);
        let high_data = self.high(high);
        let tp = high_data.tp.expect("high variable has no data-type");
        let datatype = types.get(tp);
        if !datatype.has_stripped() {
            return;
        }
        let meta = datatype.get_metatype();
        if meta == TypeMetatype::PartialUnion || meta == TypeMetatype::PartialStruct {
            if let Some(sym) = high_data.symbol
                && high_data.symboloffset != -1
            {
                let sym_type = symtab.symbol(sym).get_type().expect("symbol has no data-type");
                let submeta = types.get(sym_type).get_metatype();
                if submeta == TypeMetatype::Struct || submeta == TypeMetatype::Union || submeta == TypeMetatype::Array {
                    return;
                }
            }
        } else if datatype.is_enum_type() && high_data.inst.len() == 1 && self.vn(high_data.inst[0]).is_constant() {
            return;
        }
        let stripped = datatype.get_stripped().expect("data-type has no stripped form");
        self.high_mut(high).tp = Some(stripped);
    }

    pub fn high_get_type(&mut self, high: HighId, glb: &Architecture) -> TypeId {
        self.high_update_type(high, glb);
        self.high(high).tp.expect("HighVariable has no data-type")
    }

    pub fn high_get_symbol(&mut self, high: HighId, glb: &Architecture) -> Option<SymbolId> {
        self.high_update_symbol(high, glb);
        self.high(high).symbol
    }

    pub fn high_get_symbol_entry(&self, high: HighId, glb: &Architecture) -> Option<EntryId> {
        let symtab = symbol_table(glb);
        let high_data = self.high(high);
        for instance in high_data.inst.iter() {
            if let Some(entry) = self.vn(*instance).get_symbol_entry()
                && Some(symtab.entry(entry).get_symbol()) == high_data.symbol
            {
                return Some(entry);
            }
        }
        None
    }

    pub fn high_finalize_datatype(&mut self, high: HighId, glb: &mut Architecture) -> Result<()> {
        let Some(sym) = self.high(high).symbol else {
            return Ok(());
        };
        let cur = symbol_table(glb)
            .symbol(sym)
            .get_type()
            .expect("symbol has no data-type");
        let off = self.high(high).symboloffset.max(0);
        let size = self.vn(self.high(high).inst[0]).get_size();
        let types = glb.types.as_deref_mut().expect("architecture has no type factory");
        let Some(tp) = types.get_exact_piece(cur, off, size)? else {
            return Ok(());
        };
        if types.get(tp).get_metatype() == TypeMetatype::Unknown {
            return Ok(());
        }
        self.high_mut(high).tp = Some(tp);
        self.high_strip_type(high, glb);
        self.high_mut(high).highflags |= HighVariable::TYPE_FINALIZED;
        Ok(())
    }

    pub fn high_group_with(&mut self, high: HighId, off: i32, hi2: HighId) -> Result<()> {
        let this_has_piece = self.high(high).piece.is_some();
        let hi2_has_piece = self.high(hi2).piece.is_some();
        if !this_has_piece && !hi2_has_piece {
            VariablePiece::create(self, hi2, 0, None)?;
            VariablePiece::create(self, high, off, Some(hi2))?;
            VariablePiece::mark_intersection_dirty(&mut self.highs, &self.groups, hi2);
            return Ok(());
        }
        if !this_has_piece {
            if (self.high(hi2).highflags & HighVariable::INTERSECTDIRTY) == 0 {
                VariablePiece::mark_intersection_dirty(&mut self.highs, &self.groups, hi2);
            }
            self.high_mut(high).highflags |= HighVariable::INTERSECTDIRTY | HighVariable::EXTENDCOVERDIRTY;
            let off = off
                + self
                    .high(hi2)
                    .piece
                    .as_ref()
                    .expect("high variable has no piece")
                    .get_offset();
            VariablePiece::create(self, high, off, Some(hi2))?;
        } else if !hi2_has_piece {
            let piece_offset = self
                .high(high)
                .piece
                .as_ref()
                .expect("high variable has no piece")
                .get_offset();
            let mut hi2_off = piece_offset - off;
            if hi2_off < 0 {
                let group = self
                    .high(high)
                    .piece
                    .as_ref()
                    .expect("high variable has no piece")
                    .get_group();
                VariableGroup::adjust_offsets(&mut self.groups, &mut self.highs, group, -hi2_off);
                hi2_off = 0;
            }
            if (self.high(high).highflags & HighVariable::INTERSECTDIRTY) == 0 {
                VariablePiece::mark_intersection_dirty(&mut self.highs, &self.groups, high);
            }
            self.high_mut(hi2).highflags |= HighVariable::INTERSECTDIRTY | HighVariable::EXTENDCOVERDIRTY;
            VariablePiece::create(self, hi2, hi2_off, Some(high))?;
        } else {
            let hi2_piece_offset = self
                .high(hi2)
                .piece
                .as_ref()
                .expect("high variable has no piece")
                .get_offset();
            let (this_offset, this_group) = {
                let piece = self.high(high).piece.as_ref().expect("high variable has no piece");
                (piece.get_offset(), piece.get_group())
            };
            let off_diff = hi2_piece_offset + off - this_offset;
            if off_diff != 0 {
                VariableGroup::adjust_offsets(&mut self.groups, &mut self.highs, this_group, off_diff);
            }
            let hi2_group = self
                .high(hi2)
                .piece
                .as_ref()
                .expect("high variable has no piece")
                .get_group();
            VariableGroup::combine_groups(self, hi2_group, this_group)?;
            VariablePiece::mark_intersection_dirty(&mut self.highs, &self.groups, hi2);
        }
        Ok(())
    }

    pub fn high_establish_group_symbol_offset(&mut self, high: HighId, _glb: &Architecture) -> Result<()> {
        let (group, piece_offset) = {
            let piece = self.high(high).piece.as_ref().expect("high variable has no piece");
            (piece.get_group(), piece.get_offset())
        };
        let mut off = self.high(high).symboloffset;
        if off < 0 {
            off = 0;
        }
        off -= piece_offset;
        if off < 0 {
            return Err(Error::Lowlevel(
                "Symbol offset is incompatible with VariableGroup".to_string(),
            ));
        }
        self.groups.get_mut(group).set_symbol_offset(off);
        Ok(())
    }

    pub fn high_print_info(&mut self, high: HighId, out: &mut String, glb: &Architecture) {
        self.high_update_type(high, glb);
        let symtab = symbol_table(glb);
        let types = type_factory(glb);
        let high_data = self.high(high);
        match high_data.symbol {
            None => out.push_str("Variable: UNNAMED\n"),
            Some(sym) => {
                out.push_str("Variable: ");
                out.push_str(symtab.symbol(sym).get_name());
                if high_data.symboloffset != -1 {
                    out.push_str("(partial)");
                }
                out.push('\n');
            }
        }
        out.push_str("Type: ");
        types
            .get(high_data.tp.expect("high variable has no data-type"))
            .print_raw(out, types);
        out.push_str("\n\n");
        for vn in high_data.inst.iter() {
            let _ = write!(out, "{}: ", self.vn(*vn).get_merge_group());
            self.vn_print_info(*vn, out, glb);
        }
    }

    pub fn high_has_name(&mut self, high: HighId) -> Result<bool> {
        let mut indirectonly = true;
        let inst_count = self.high(high).inst.len();
        for index in 0..inst_count {
            let vn = self.vn(self.high(high).inst[index]);
            if !vn.has_cover() {
                if inst_count > 1 {
                    return Err(Error::Lowlevel("Non-coverable varnode has been merged".to_string()));
                }
                return Ok(false);
            }
            if vn.is_implied() {
                if inst_count > 1 {
                    return Err(Error::Lowlevel("Implied varnode has been merged".to_string()));
                }
                return Ok(false);
            }
            if !vn.is_indirect_only() {
                indirectonly = false;
            }
        }
        if self.high_is_unaffected(high) {
            if !self.high_is_input(high) {
                return Ok(false);
            }
            if indirectonly {
                return Ok(false);
            }
            let vn = self.vn(self.high_get_input_varnode(high)?);
            if !vn.is_illegal_input() && vn.is_spacebase() {
                return Ok(false);
            }
        }
        Ok(true)
    }

    pub fn high_get_tied_varnode(&self, high: HighId) -> Result<VarnodeId> {
        for instance in self.high(high).inst.iter() {
            if self.vn(*instance).is_addr_tied() {
                return Ok(*instance);
            }
        }
        Err(Error::Lowlevel("Could not find address-tied varnode".to_string()))
    }

    pub fn high_get_input_varnode(&self, high: HighId) -> Result<VarnodeId> {
        for instance in self.high(high).inst.iter() {
            if self.vn(*instance).is_input() {
                return Ok(*instance);
            }
        }
        Err(Error::Lowlevel("Could not find input varnode".to_string()))
    }

    pub fn high_get_type_representative(&self, high: HighId, glb: &Architecture) -> VarnodeId {
        let types = type_factory(glb);
        let inst = &self.high(high).inst;
        let mut rep = inst[0];
        for vn in inst[1..].iter() {
            let varnode = self.vn(*vn);
            let rep_node = self.vn(rep);
            if rep_node.is_type_lock() != varnode.is_type_lock() {
                if varnode.is_type_lock() {
                    rep = *vn;
                }
            } else if 0 > types
                .get(varnode.get_type())
                .type_order_formal(types.get(rep_node.get_type()), types)
            {
                rep = *vn;
            }
        }
        rep
    }

    pub fn high_get_name_representative(&mut self, high: HighId) -> VarnodeId {
        if (self.high(high).highflags & HighVariable::NAMEREPDIRTY) == 0 {
            return self
                .high(high)
                .name_representative
                .expect("high variable has no name representative");
        }
        self.high_mut(high).highflags &= !HighVariable::NAMEREPDIRTY;
        let inst = self.high(high).inst.clone();
        let mut rep = inst[0];
        for vn in inst[1..].iter() {
            if self.high_compare_name(rep, *vn) {
                rep = *vn;
            }
        }
        self.high_mut(high).name_representative = Some(rep);
        rep
    }

    pub fn high_is_mapped(&mut self, high: HighId) -> bool {
        self.high_update_flags(high);
        (self.high(high).flags & Varnode::MAPPED) != 0
    }

    pub fn high_is_persist(&mut self, high: HighId) -> bool {
        self.high_update_flags(high);
        (self.high(high).flags & Varnode::PERSIST) != 0
    }

    pub fn high_is_addr_tied(&mut self, high: HighId) -> bool {
        self.high_update_flags(high);
        (self.high(high).flags & Varnode::ADDRTIED) != 0
    }

    pub fn high_is_input(&mut self, high: HighId) -> bool {
        self.high_update_flags(high);
        (self.high(high).flags & Varnode::INPUT) != 0
    }

    pub fn high_is_implied(&mut self, high: HighId) -> bool {
        self.high_update_flags(high);
        (self.high(high).flags & Varnode::IMPLIED) != 0
    }

    pub fn high_is_spacebase(&mut self, high: HighId) -> bool {
        self.high_update_flags(high);
        (self.high(high).flags & Varnode::SPACEBASE) != 0
    }

    pub fn high_is_constant(&mut self, high: HighId) -> bool {
        self.high_update_flags(high);
        (self.high(high).flags & Varnode::CONSTANT) != 0
    }

    pub fn high_is_unaffected(&mut self, high: HighId) -> bool {
        self.high_update_flags(high);
        (self.high(high).flags & Varnode::UNAFFECTED) != 0
    }

    pub fn high_is_extra_out(&mut self, high: HighId) -> bool {
        self.high_update_flags(high);
        (self.high(high).flags & (Varnode::INDIRECT_CREATION | Varnode::ADDRTIED)) == Varnode::INDIRECT_CREATION
    }

    pub fn high_is_proto_partial(&mut self, high: HighId) -> bool {
        self.high_update_flags(high);
        (self.high(high).flags & Varnode::PROTO_PARTIAL) != 0
    }

    pub fn high_has_cover(&mut self, high: HighId) -> bool {
        self.high_update_flags(high);
        (self.high(high).flags & (Varnode::CONSTANT | Varnode::ANNOTATION | Varnode::INSERT)) == Varnode::INSERT
    }

    pub fn high_is_type_lock(&mut self, high: HighId, glb: &Architecture) -> bool {
        self.high_update_type(high, glb);
        (self.high(high).flags & Varnode::TYPELOCK) != 0
    }

    pub fn high_is_name_lock(&mut self, high: HighId) -> bool {
        self.high_update_flags(high);
        (self.high(high).flags & Varnode::NAMELOCK) != 0
    }

    pub fn high_encode(&mut self, high: HighId, encoder: &mut dyn Encoder, glb: &Architecture) -> Result<()> {
        let vn = self.high_get_name_representative(high);
        encoder.open_element(ELEM_HIGH);
        encoder.write_unsigned_integer(ATTRIB_REPREF, self.vn(vn).get_create_index() as u64);
        let symbol = self.high(high).symbol;
        if self.high_is_spacebase(high) || self.high_is_implied(high) {
            encoder.write_string(ATTRIB_CLASS, "other");
        } else if self.high_is_persist(high) && self.high_is_addr_tied(high) {
            encoder.write_string(ATTRIB_CLASS, "global");
        } else if self.high_is_constant(high) {
            encoder.write_string(ATTRIB_CLASS, "constant");
        } else if !self.high_is_persist(high) && symbol.is_some() {
            let symtab = symbol_table(glb);
            let sym = symtab.symbol(symbol.expect("symbol checked above"));
            if sym.get_category() == Symbol::FUNCTION_PARAMETER {
                encoder.write_string(ATTRIB_CLASS, "param");
            } else if symtab.scope(sym.get_scope()).is_global() {
                encoder.write_string(ATTRIB_CLASS, "global");
            } else {
                encoder.write_string(ATTRIB_CLASS, "local");
            }
        } else {
            encoder.write_string(ATTRIB_CLASS, "other");
        }
        if self.high_is_type_lock(high, glb) {
            encoder.write_bool(ATTRIB_TYPELOCK, true);
        }
        if let Some(sym) = symbol {
            encoder.write_unsigned_integer(ATTRIB_SYMREF, symbol_table(glb).symbol(sym).get_id());
            if self.high(high).symboloffset >= 0 {
                encoder.write_signed_integer(ATTRIB_OFFSET, self.high(high).symboloffset as i64);
            }
        }
        let tp = self.high_get_type(high, glb);
        let types = type_factory(glb);
        types.get(tp).encode_ref(encoder, glb)?;
        for instance in self.high(high).inst.iter() {
            encoder.open_element(ELEM_ADDR);
            encoder.write_unsigned_integer(ATTRIB_REF, self.vn(*instance).get_create_index() as u64);
            encoder.close_element(ELEM_ADDR);
        }
        encoder.close_element(ELEM_HIGH);
        Ok(())
    }

    pub fn high_verify_cover(&mut self, high: HighId) -> Result<()> {
        let mut accum_cover = Cover::new();
        let inst = self.high(high).inst.clone();
        for index in 0..inst.len() {
            let vn = inst[index];
            self.vn_update_cover(vn);
            let vn_cover = self.vn(vn).get_cover_raw().expect("varnode has no cover");
            if accum_cover.intersect(vn_cover, self) == 2 {
                for other_vn in inst[..index].iter() {
                    self.vn_update_cover(*other_vn);
                    let other_cover = self.vn(*other_vn).get_cover_raw().expect("varnode has no cover");
                    let vn_cover = self.vn(vn).get_cover_raw().expect("varnode has no cover");
                    if other_cover.intersect(vn_cover, self) == 2 && !self.vn_copy_shadow(*other_vn, vn) {
                        return Err(Error::Lowlevel("HighVariable has internal intersection".to_string()));
                    }
                }
            }
            let vn_cover = self.vn(vn).get_cover_raw().expect("varnode has no cover");
            accum_cover.merge(vn_cover, self);
        }
        Ok(())
    }

    pub fn high_compare_name(&mut self, vn1: VarnodeId, vn2: VarnodeId) -> bool {
        let first = self.vn(vn1);
        let second = self.vn(vn2);
        if first.is_name_lock() {
            return false;
        }
        if second.is_name_lock() {
            return true;
        }
        if first.is_unaffected() != second.is_unaffected() {
            return second.is_unaffected();
        }
        if first.is_persist() != second.is_persist() {
            return second.is_persist();
        }
        if first.is_input() != second.is_input() {
            return second.is_input();
        }
        if first.is_addr_tied() != second.is_addr_tied() {
            return second.is_addr_tied();
        }
        if first.is_proto_partial() != second.is_proto_partial() {
            return second.is_proto_partial();
        }
        let first_internal = first.get_space().map(|spc| spc.get_type()) == Some(SpaceType::Internal);
        let second_internal = second.get_space().map(|spc| spc.get_type()) == Some(SpaceType::Internal);
        if !first_internal && second_internal {
            return false;
        }
        if first_internal && !second_internal {
            return true;
        }
        if first.is_written() != second.is_written() {
            return second.is_written();
        }
        if !first.is_written() {
            return false;
        }
        let first_time = self.op(first.get_def().expect("written varnode has no def")).get_time();
        let second_time = self
            .op(second.get_def().expect("written varnode has no def"))
            .get_time();
        if first_time != second_time {
            return second_time < first_time;
        }
        false
    }

    pub fn high_mark_expression(&mut self, vn: VarnodeId, high_list: &mut Vec<HighId>) -> i32 {
        let high = self
            .vn(vn)
            .get_high_option()
            .expect("Requesting non-existent high-level");
        self.high_mut(high).set_mark();
        high_list.push(high);
        let mut ret_val = 0;
        if !self.vn(vn).is_written() {
            return ret_val;
        }
        let mut path: Vec<(OpId, i32)> = Vec::new();
        let op = self.vn(vn).get_def().expect("written varnode has no def");
        if self.op(op).is_call() {
            ret_val |= 1;
        }
        if self.op(op).code() == OpCode::Load {
            ret_val |= 2;
        }
        path.push((op, 0));
        while let Some(node) = path.last_mut() {
            let (node_op, node_slot) = *node;
            if self.op(node_op).num_input() <= node_slot {
                path.pop();
                continue;
            }
            let cur_vn = self.op(node_op).get_in(node_slot);
            node.1 += 1;
            let cur = self.vn(cur_vn);
            if cur.is_annotation() {
                continue;
            }
            if cur.is_explicit() {
                let high = cur.get_high_option().expect("Requesting non-existent high-level");
                if self.high(high).is_mark() {
                    continue;
                }
                self.high_mut(high).set_mark();
                high_list.push(high);
                continue;
            }
            if !cur.is_written() {
                continue;
            }
            let op = cur.get_def().expect("written varnode has no def");
            if self.op(op).is_call() {
                ret_val |= 1;
            }
            if self.op(op).code() == OpCode::Load {
                ret_val |= 2;
            }
            path.push((op, 0));
        }
        ret_val
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct HighEdge {
    pub(crate) first: HighId,
    pub(crate) second: HighId,
}

impl HighEdge {
    pub fn new(first: HighId, second: HighId) -> HighEdge {
        HighEdge { first, second }
    }
}

#[derive(Clone, Debug, Default)]
pub struct HighIntersectTest {
    pub(crate) highedgemap: BTreeMap<HighEdge, bool>,
}

fn varnode_cover(data: &mut Funcdata, vn: VarnodeId) -> Cover {
    data.vn_update_cover(vn);
    data.vn(vn).get_cover_raw().expect("varnode has no cover").clone()
}

impl HighIntersectTest {
    pub fn new() -> HighIntersectTest {
        HighIntersectTest {
            highedgemap: BTreeMap::new(),
        }
    }

    fn edges_from(&self, high: HighId) -> Vec<(HighEdge, bool)> {
        self.highedgemap
            .range(HighEdge::new(high, HighId(0))..HighEdge::new(high, HighId(u32::MAX)))
            .map(|(edge, res)| (*edge, *res))
            .collect()
    }

    pub fn gather_block_varnodes(
        data: &mut Funcdata,
        first: HighId,
        blk: i32,
        cover: &Cover,
        res: &mut Vec<VarnodeId>,
    ) {
        for index in 0..data.high(first).num_instances() {
            let vn = data.high(first).get_instance(index);
            let vn_cover = varnode_cover(data, vn);
            if 1 < vn_cover.intersect_by_block(blk, cover, data) {
                res.push(vn);
            }
        }
    }

    pub fn test_block_intersection(
        data: &mut Funcdata,
        first: HighId,
        blk: i32,
        cover: &Cover,
        rel_off: i32,
        blist: &[VarnodeId],
    ) -> bool {
        for index in 0..data.high(first).num_instances() {
            let vn = data.high(first).get_instance(index);
            let vn_cover = varnode_cover(data, vn);
            if 2 > vn_cover.intersect_by_block(blk, cover, data) {
                continue;
            }
            for vn2 in blist.iter() {
                let vn2_cover = varnode_cover(data, *vn2);
                if 1 < vn2_cover.intersect_by_block(blk, &vn_cover, data) {
                    if data.vn(vn).get_size() == data.vn(*vn2).get_size() {
                        if !data.vn_copy_shadow(vn, *vn2) {
                            return true;
                        }
                    } else if !data.vn_partial_copy_shadow(vn, *vn2, rel_off) {
                        return true;
                    }
                }
            }
        }
        false
    }

    pub fn block_intersection(&mut self, data: &mut Funcdata, first: HighId, second: HighId, blk: i32) -> bool {
        let mut blist = Vec::new();
        let a_cover = data.high(first).get_cover().clone();
        let b_cover = data.high(second).get_cover().clone();
        HighIntersectTest::gather_block_varnodes(data, second, blk, &a_cover, &mut blist);
        if HighIntersectTest::test_block_intersection(data, first, blk, &b_cover, 0, &blist) {
            return true;
        }
        let a_pieces: Option<(i32, Vec<HighId>)> = data
            .high(first)
            .piece
            .as_ref()
            .map(|piece| (piece.get_offset(), piece.intersection.clone()));
        if let Some((base_off, intersection)) = a_pieces.as_ref() {
            for inter_high in intersection.iter() {
                let inter_offset = data
                    .high(*inter_high)
                    .piece
                    .as_ref()
                    .expect("intersection has no piece")
                    .get_offset();
                let off = inter_offset - base_off;
                if HighIntersectTest::test_block_intersection(data, *inter_high, blk, &b_cover, off, &blist) {
                    return true;
                }
            }
        }
        let b_pieces: Option<(i32, Vec<HighId>)> = data
            .high(second)
            .piece
            .as_ref()
            .map(|piece| (piece.get_offset(), piece.intersection.clone()));
        if let Some((b_base_off, b_intersection)) = b_pieces {
            for b_high in b_intersection {
                blist.clear();
                let (b_piece_offset, b_piece_size) = {
                    let piece = data.high(b_high).piece.as_ref().expect("intersection has no piece");
                    (piece.get_offset(), piece.get_size())
                };
                let b_off = b_piece_offset - b_base_off;
                HighIntersectTest::gather_block_varnodes(data, b_high, blk, &a_cover, &mut blist);
                if HighIntersectTest::test_block_intersection(data, first, blk, &b_cover, -b_off, &blist) {
                    return true;
                }
                if let Some((base_off, intersection)) = a_pieces.as_ref() {
                    for inter_high in intersection.iter() {
                        let (inter_offset, inter_size) = {
                            let piece = data
                                .high(*inter_high)
                                .piece
                                .as_ref()
                                .expect("intersection has no piece");
                            (piece.get_offset(), piece.get_size())
                        };
                        let off = (inter_offset - base_off) - b_off;
                        if off > 0 && off >= b_piece_size {
                            continue;
                        }
                        if off < 0 && -off >= inter_size {
                            continue;
                        }
                        if HighIntersectTest::test_block_intersection(data, *inter_high, blk, &b_cover, off, &blist) {
                            return true;
                        }
                    }
                }
            }
        }
        false
    }

    pub fn purge_high(&mut self, high: HighId) {
        let edges = self.edges_from(high);
        for (edge, _) in edges.iter() {
            self.highedgemap.remove(&HighEdge::new(edge.second, edge.first));
        }
        for (edge, _) in edges.iter() {
            self.highedgemap.remove(edge);
        }
    }

    pub fn test_untied_call_intersection(
        &mut self,
        data: &mut Funcdata,
        affecting_ops: &mut dyn PcodeOpSet,
        tied: HighId,
        untied: HighId,
    ) -> Result<bool> {
        if data.high_is_persist(tied) {
            return Ok(false);
        }
        let vn = data.high_get_tied_varnode(tied)?;
        if data.vn(vn).has_no_local_alias() {
            return Ok(false);
        }
        if !affecting_ops.is_populated() {
            affecting_ops.populate(data);
        }
        Ok(data.high(untied).get_cover().intersect_op_set(affecting_ops, vn, data))
    }

    pub fn move_intersect_tests(&mut self, data: &mut Funcdata, high1: HighId, high2: HighId) {
        let mut yesinter = Vec::new();
        let mut nointer = Vec::new();
        let edges = self.edges_from(high2);
        for (edge, res) in edges.iter() {
            let other = edge.second;
            if other == high1 {
                continue;
            }
            if *res {
                yesinter.push(other);
            } else {
                nointer.push(other);
                data.high_mut(other).set_mark();
            }
        }
        for (edge, _) in edges.iter() {
            self.highedgemap.remove(&HighEdge::new(edge.second, edge.first));
        }
        for (edge, _) in edges.iter() {
            self.highedgemap.remove(edge);
        }
        let high1_edges = self.edges_from(high1);
        for (edge, res) in high1_edges {
            if !res && !data.high(edge.second).is_mark() {
                self.highedgemap.remove(&HighEdge::new(edge.second, edge.first));
                self.highedgemap.remove(&edge);
            }
        }
        for other in nointer.iter() {
            data.high_mut(*other).clear_mark();
        }
        for other in yesinter {
            self.highedgemap.insert(HighEdge::new(high1, other), true);
            self.highedgemap.insert(HighEdge::new(other, high1), true);
        }
    }

    pub fn update_high(&mut self, data: &mut Funcdata, first: HighId) -> bool {
        if !data.high(first).is_cover_dirty() {
            return true;
        }
        data.high_update_cover(first);
        self.purge_high(first);
        false
    }

    pub fn intersection(
        &mut self,
        data: &mut Funcdata,
        affecting_ops: &mut dyn PcodeOpSet,
        first: HighId,
        second: HighId,
    ) -> Result<bool> {
        if first == second {
            return Ok(false);
        }
        let ares = self.update_high(data, first);
        let bres = self.update_high(data, second);
        if ares
            && bres
            && let Some(res) = self.highedgemap.get(&HighEdge::new(first, second))
        {
            return Ok(*res);
        }
        let mut res = false;
        let mut blockisect = Vec::new();
        data.high(first)
            .get_cover()
            .intersect_list(&mut blockisect, data.high(second).get_cover(), 2, data);
        for blk in blockisect {
            if self.block_intersection(data, first, second, blk) {
                res = true;
                break;
            }
        }
        if !res {
            let a_tied = data.high_is_addr_tied(first);
            let b_tied = data.high_is_addr_tied(second);
            if a_tied != b_tied {
                res = if a_tied {
                    self.test_untied_call_intersection(data, affecting_ops, first, second)?
                } else {
                    self.test_untied_call_intersection(data, affecting_ops, second, first)?
                };
            }
        }
        self.highedgemap.insert(HighEdge::new(first, second), res);
        self.highedgemap.insert(HighEdge::new(second, first), res);
        Ok(res)
    }

    pub fn clear(&mut self) {
        self.highedgemap.clear();
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn piece_high(highs: &mut Arena<HighId, HighVariable>, group: GroupId, offset: i32, size: i32) -> HighId {
        highs.alloc_with(|id| HighVariable {
            inst: Vec::new(),
            num_merge_classes: 1,
            highflags: 0,
            flags: 0,
            tp: None,
            name_representative: None,
            internal_cover: Cover::new(),
            piece: Some(VariablePiece {
                group,
                high: id,
                group_offset: offset,
                size,
                intersection: Vec::new(),
                cover: Cover::new(),
            }),
            symbol: None,
            symboloffset: -1,
        })
    }

    #[test]
    fn group_pieces_and_offsets() {
        let mut groups: Arena<GroupId, VariableGroup> = Arena::new();
        let mut highs: Arena<HighId, HighVariable> = Arena::new();
        let group = groups.alloc(VariableGroup::new());
        let low = piece_high(&mut highs, group, 0, 4);
        let high = piece_high(&mut highs, group, 4, 4);
        let duplicate = piece_high(&mut highs, group, 4, 4);
        VariableGroup::add_piece(&mut groups, &mut highs, group, low).expect("add failed");
        VariableGroup::add_piece(&mut groups, &mut highs, group, high).expect("add failed");
        assert!(VariableGroup::add_piece(&mut groups, &mut highs, group, duplicate).is_err());
        assert_eq!(groups[group].get_size(), 8);
        VariableGroup::adjust_offsets(&mut groups, &mut highs, group, 2);
        assert_eq!(groups[group].get_size(), 10);
        let keys: Vec<(i32, i32)> = groups[group].piece_set.keys().copied().collect();
        assert_eq!(keys, vec![(2, 4), (6, 4)]);
        assert_eq!(highs[high].piece.as_ref().map(|piece| piece.get_offset()), Some(6));
        VariablePiece::mark_intersection_dirty(&mut highs, &groups, low);
        assert_ne!(highs[high].highflags & HighVariable::INTERSECTDIRTY, 0);
        VariablePiece::mark_extend_cover_dirty(&mut highs, low);
        assert_eq!(
            highs[low].highflags & HighVariable::EXTENDCOVERDIRTY,
            HighVariable::EXTENDCOVERDIRTY
        );
    }

    #[test]
    fn purge_removes_both_directions() {
        let mut test = HighIntersectTest::new();
        let (first, second, third) = (HighId(1), HighId(2), HighId(3));
        test.highedgemap.insert(HighEdge::new(first, second), true);
        test.highedgemap.insert(HighEdge::new(second, first), true);
        test.highedgemap.insert(HighEdge::new(second, third), false);
        test.highedgemap.insert(HighEdge::new(third, second), false);
        test.purge_high(first);
        assert_eq!(test.highedgemap.len(), 2);
        test.purge_high(third);
        assert!(test.highedgemap.is_empty());
    }
}
