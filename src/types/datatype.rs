use std::collections::BTreeMap;
use std::fmt::Write as _;

use super::{
    ATTRIB_ALIGNMENT, ATTRIB_ARRAYSIZE, ATTRIB_CHAR, ATTRIB_CORE, ATTRIB_INCOMPLETE, ATTRIB_OPAQUESTRING, ATTRIB_UTF,
    ATTRIB_VARLENGTH, BASE2SUB, CodeSignature, Datatype, ELEM_DEF, ELEM_TYPE, ELEM_TYPEREF, EnumRepresentation,
    Nearest, SubMetatype, TypeFactory, TypeId, TypeKind, TypeMetatype, metatype2string, string2metatype, types_of,
    types_of_mut,
};
use crate::address::{Address, calc_mask, coveringmask, sign_extend};
use crate::architecture::Architecture;
use crate::database::ScopeId;
use crate::error::{Error, Result};
use crate::fspec::{FuncProto, PrototypePieces};
use crate::jumptable::ATTRIB_LABEL;
use crate::marshal::{
    ATTRIB_CONTENT, ATTRIB_FORMAT, ATTRIB_ID, ATTRIB_METATYPE, ATTRIB_NAME, ATTRIB_OFFSET, ATTRIB_SIZE, ATTRIB_SPACE,
    ATTRIB_VALUE, ATTRIB_WORDSIZE, Decoder, ELEM_OFF, ELEM_VAL, ELEM_VOID, Encoder,
};
use crate::space::AddrSpace;

fn order_code<T: PartialOrd>(first: T, second: T) -> i32 {
    if first < second { -1 } else { 1 }
}

fn space_order_index(space: &Option<crate::space::SpaceRef>) -> i64 {
    match space {
        Some(spc) => spc.get_index() as i64,
        None => -1,
    }
}

impl Datatype {
    pub fn print_raw(&self, out: &mut String, types: &TypeFactory) {
        match &self.kind {
            TypeKind::Pointer(data) => {
                types
                    .get(data.ptrto.expect("pointer without target"))
                    .print_raw(out, types);
                out.push_str(" *");
                if let Some(spc) = &data.spaceid {
                    let _ = write!(out, "({})", spc.get_name());
                }
            }
            TypeKind::PointerRel(data) => {
                types
                    .get(data.pointer.ptrto.expect("pointer without target"))
                    .print_raw(out, types);
                out.push_str(" *+");
                let _ = write!(out, "{}", data.offset);
                out.push('[');
                types
                    .get(data.parent.expect("relative pointer without parent"))
                    .print_raw(out, types);
                out.push(']');
            }
            TypeKind::Array(data) => {
                types
                    .get(data.arrayof.expect("array without element type"))
                    .print_raw(out, types);
                let _ = write!(out, " [{}]", data.arraysize);
            }
            TypeKind::PartialEnum(data) => {
                types.get(data.parent).print_raw(out, types);
                let _ = write!(out, "[off={},sz={}]", data.offset, self.size);
            }
            TypeKind::PartialStruct(data) => {
                types.get(data.container).print_raw(out, types);
                let _ = write!(out, "[off={},sz={}]", data.offset, self.size);
            }
            TypeKind::PartialUnion(data) => {
                types.get(data.container).print_raw(out, types);
                let _ = write!(out, "[off={},sz={}]", data.offset, self.size);
            }
            TypeKind::Code(_) => {
                if !self.name.is_empty() {
                    out.push_str(&self.name);
                } else {
                    out.push_str("funcptr");
                }
                out.push_str("()");
            }
            _ => {
                if !self.name.is_empty() {
                    out.push_str(&self.name);
                } else {
                    let _ = write!(out, "unkbyte{}", self.size);
                }
            }
        }
    }

    pub fn get_sub_type(&self, off: i64, newoff: &mut i64, glb: &Architecture) -> Option<TypeId> {
        self.sub_type(off, newoff, types_of(glb), Some(glb))
    }

    pub fn get_sub_type_local(&self, off: i64, newoff: &mut i64, types: &TypeFactory) -> Option<TypeId> {
        self.sub_type(off, newoff, types, None)
    }

    pub(crate) fn sub_type(
        &self,
        off: i64,
        newoff: &mut i64,
        types: &TypeFactory,
        glb: Option<&Architecture>,
    ) -> Option<TypeId> {
        match &self.kind {
            TypeKind::Pointer(_) | TypeKind::PointerRel(_) => {
                let data = self.pointer_data();
                if let Some(truncate) = data.truncate {
                    let trunc_size = types.get(truncate).get_size() as i64;
                    let min = if (self.flags & Datatype::TRUNCATE_BIGENDIAN) != 0 {
                        self.size as i64 - trunc_size
                    } else {
                        0
                    };
                    if off >= min && off < min + trunc_size {
                        *newoff = off - min;
                        return Some(truncate);
                    }
                }
                *newoff = off;
                None
            }
            TypeKind::Array(data) => {
                if off >= self.size as i64 {
                    *newoff = off;
                    return None;
                }
                let arrayof = data.arrayof.expect("array without element type");
                *newoff = off % types.get(arrayof).get_align_size() as i64;
                Some(arrayof)
            }
            TypeKind::Struct(data) => {
                let index = self.get_field_iter(off as i32, types);
                if index < 0 {
                    *newoff = off;
                    return None;
                }
                let curfield = &data.field[index as usize];
                *newoff = off - curfield.offset as i64;
                Some(curfield.tp)
            }
            TypeKind::PartialStruct(data) => {
                let size_left = self.size as i64 - off;
                let mut cur_off = off + data.offset as i64;
                let mut ct = Some(data.container);
                loop {
                    let current = ct.expect("partial structure container");
                    ct = types.get(current).sub_type(cur_off, newoff, types, glb);
                    match ct {
                        None => break,
                        Some(next) => {
                            cur_off = *newoff;
                            if types.get(next).get_size() as i64 - cur_off <= size_left {
                                break;
                            }
                        }
                    }
                }
                ct
            }
            TypeKind::Code(data) => {
                if !data.factory {
                    return None;
                }
                *newoff = 0;
                types.find_base_existing(1, TypeMetatype::Code)
            }
            TypeKind::Spacebase(_) => {
                let glb = glb.expect("spacebase data-type requires the architecture");
                self.spacebase_sub_type(off, newoff, glb)
            }
            _ => {
                *newoff = off;
                None
            }
        }
    }

    fn spacebase_resolve(&self, off: i64, glb: &Architecture) -> (ScopeId, Address) {
        let scope = self
            .get_map(glb)
            .expect("Trying to get scope from unattached Typespacebase");
        let spaceid = match &self.kind {
            TypeKind::Spacebase(data) => data.spaceid.clone().expect("spacebase without address space"),
            _ => panic!("data-type is not a spacebase"),
        };
        let addr_off = AddrSpace::byte_to_address(off as u64, spaceid.get_word_size());
        let null_point = Address::default();
        let mut full_encoding = 0u64;
        let addr = glb
            .manager
            .resolve_constant(&spaceid, addr_off, -1, &null_point, &mut full_encoding);
        (scope, addr)
    }

    fn spacebase_sub_type(&self, off: i64, newoff: &mut i64, glb: &Architecture) -> Option<TypeId> {
        let (scope, addr) = self.spacebase_resolve(off, glb);
        let null_point = Address::default();
        let db = glb.symboltab.as_deref().expect("symbol table is not initialized");
        let smallest = db.scope_query_container(scope, &addr, 1, &null_point);
        match smallest {
            None => {
                if !db.scope(scope).in_scope(&addr, 1, &null_point) {
                    return None;
                }
                *newoff = 0;
                types_of(glb).find_base_existing(1, TypeMetatype::Unknown)
            }
            Some(entry_id) => {
                let entry = db.entry(entry_id);
                *newoff = (addr.get_offset().wrapping_sub(entry.get_addr().get_offset()) as i64)
                    .wrapping_add(entry.get_offset() as i64);
                db.symbol(entry.get_symbol()).get_type()
            }
        }
    }

    pub fn nearest_arrayed_component_forward(&self, off: i64, res: &mut Nearest, glb: &Architecture) -> bool {
        self.nearest_forward(off, res, types_of(glb), Some(glb))
    }

    pub fn nearest_arrayed_component_backward(&self, off: i64, res: &mut Nearest, glb: &Architecture) -> bool {
        self.nearest_backward(off, res, types_of(glb), Some(glb))
    }

    pub(crate) fn nearest_forward(
        &self,
        off: i64,
        res: &mut Nearest,
        types: &TypeFactory,
        glb: Option<&Architecture>,
    ) -> bool {
        match &self.kind {
            TypeKind::Array(data) => {
                if off > 0 {
                    return false;
                }
                res.offset = off;
                res.el_size = types
                    .get(data.arrayof.expect("array without element type"))
                    .get_align_size();
                res.distance = -off;
                true
            }
            TypeKind::Struct(data) => {
                let mut index = self.get_lower_bound_field(off as i32);
                let mut remain: i64;
                if index < 0 {
                    index += 1;
                    remain = 0;
                } else {
                    remain = off - data.field[index as usize].offset as i64;
                }
                while (index as usize) < data.field.len() {
                    let subfield = &data.field[index as usize];
                    let diff = subfield.offset as i64 - off;
                    let subtype = types.get(subfield.tp);
                    if subtype.nearest_forward(remain, res, types, glb) {
                        res.distance += diff + remain;
                        res.offset = -diff;
                        return true;
                    }
                    index += 1;
                    remain = 0;
                }
                false
            }
            TypeKind::Union(data) => {
                for field in data.field.iter() {
                    if types.get(field.tp).nearest_forward(off, res, types, glb) {
                        return true;
                    }
                }
                false
            }
            TypeKind::Spacebase(_) => {
                let glb = glb.expect("spacebase data-type requires the architecture");
                self.spacebase_nearest_forward(off, res, glb)
            }
            _ => false,
        }
    }

    pub(crate) fn nearest_backward(
        &self,
        off: i64,
        res: &mut Nearest,
        types: &TypeFactory,
        glb: Option<&Architecture>,
    ) -> bool {
        match &self.kind {
            TypeKind::Array(data) => {
                if off < 0 {
                    return false;
                }
                res.offset = off;
                res.el_size = types
                    .get(data.arrayof.expect("array without element type"))
                    .get_align_size();
                if off < self.size as i64 {
                    res.distance = 0;
                } else {
                    res.distance = off - self.size as i64;
                }
                true
            }
            TypeKind::Struct(data) => {
                let first_index = self.get_lower_bound_field(off as i32);
                let mut index = first_index;
                while index >= 0 {
                    let subfield = &data.field[index as usize];
                    let diff = off - subfield.offset as i64;
                    let subtype = types.get(subfield.tp);
                    let remain = if index == first_index {
                        diff
                    } else {
                        subtype.get_size() as i64
                    };
                    if subtype.nearest_backward(remain, res, types, glb) {
                        res.distance += diff - remain;
                        res.offset = diff;
                        return true;
                    }
                    index -= 1;
                }
                false
            }
            TypeKind::Union(data) => {
                for field in data.field.iter() {
                    if types.get(field.tp).nearest_backward(off, res, types, glb) {
                        return true;
                    }
                }
                false
            }
            TypeKind::Spacebase(_) => {
                let glb = glb.expect("spacebase data-type requires the architecture");
                self.spacebase_nearest_backward(off, res, glb)
            }
            _ => false,
        }
    }

    fn spacebase_nearest_forward(&self, off: i64, res: &mut Nearest, glb: &Architecture) -> bool {
        let (scope, addr) = self.spacebase_resolve(off, glb);
        let null_point = Address::default();
        let db = glb.symboltab.as_deref().expect("symbol table is not initialized");
        let types = types_of(glb);
        let smallest = db.scope_query_container(scope, &addr, 1, &null_point);
        if let Some(entry_id) = smallest {
            let entry = db.entry(entry_id);
            if entry.get_offset() == 0 {
                let symbol_type = db
                    .symbol(entry.get_symbol())
                    .get_type()
                    .expect("symbol without data-type");
                let struct_off = addr.get_offset().wrapping_sub(entry.get_addr().get_offset()) as i64;
                if types
                    .get(symbol_type)
                    .nearest_forward(struct_off, res, types, Some(glb))
                {
                    res.offset = struct_off;
                    return true;
                }
            }
        }
        let mut next_addr = addr.clone();
        loop {
            let Some(entry_id) = db.scope_find_symbol_after(scope, &next_addr, &null_point) else {
                return false;
            };
            let entry = db.entry(entry_id);
            if entry.get_offset() != 0 {
                return false;
            }
            next_addr = entry.get_addr().clone();
            let symbol_type = db
                .symbol(entry.get_symbol())
                .get_type()
                .expect("symbol without data-type");
            let struct_off = addr.get_offset().wrapping_sub(next_addr.get_offset()) as i64;
            let symbol_dt = types.get(symbol_type);
            if symbol_dt.nearest_forward(0, res, types, Some(glb)) {
                res.distance = res.distance.wrapping_sub(struct_off);
                res.offset = struct_off;
                if res.distance > Datatype::MAX_ARRAY_SLACK_FORWARD as i64 {
                    return false;
                }
                if res.distance <= symbol_dt.get_size() as i64 || symbol_dt.get_metatype() == TypeMetatype::Array {
                    return true;
                }
            }
            if next_addr.get_offset().wrapping_sub(addr.get_offset()) >= Datatype::MAX_ARRAY_SLACK_FORWARD as u64 {
                break;
            }
        }
        false
    }

    fn spacebase_nearest_backward(&self, off: i64, res: &mut Nearest, glb: &Architecture) -> bool {
        let (scope, addr) = self.spacebase_resolve(off, glb);
        let null_point = Address::default();
        let db = glb.symboltab.as_deref().expect("symbol table is not initialized");
        let types = types_of(glb);
        let mut max = Datatype::MAX_ARRAY_SLACK_BACKWARD;
        let smallest = db.scope_query_container(scope, &addr, 1, &null_point);
        let mut found_at_start = false;
        if let Some(entry_id) = smallest {
            let entry = db.entry(entry_id);
            if entry.get_offset() == 0 {
                found_at_start = true;
                let symbol_type = db
                    .symbol(entry.get_symbol())
                    .get_type()
                    .expect("symbol without data-type");
                let struct_off = addr.get_offset().wrapping_sub(entry.get_addr().get_offset()) as i64;
                if types
                    .get(symbol_type)
                    .nearest_backward(struct_off, res, types, Some(glb))
                {
                    res.offset = struct_off;
                    return true;
                }
            }
        }
        if !found_at_start {
            max = Datatype::MAX_ARRAY_SLACK_FORWARD;
        }
        let mut next_addr = addr.clone();
        loop {
            let Some(entry_id) = db.scope_find_symbol_before(scope, &next_addr, &null_point) else {
                return false;
            };
            let entry = db.entry(entry_id);
            if entry.get_offset() != 0 {
                return false;
            }
            let symbol_type = db
                .symbol(entry.get_symbol())
                .get_type()
                .expect("symbol without data-type");
            next_addr = entry.get_addr().clone();
            let struct_off = addr.get_offset().wrapping_sub(next_addr.get_offset()) as i64;
            let symbol_dt = types.get(symbol_type);
            if symbol_dt.nearest_backward(symbol_dt.get_size() as i64, res, types, Some(glb)) {
                res.distance = res
                    .distance
                    .wrapping_add(struct_off)
                    .wrapping_sub(symbol_dt.get_size() as i64);
                res.offset = struct_off;
                if res.distance > max as i64 {
                    return false;
                }
                if res.distance <= symbol_dt.get_size() as i64 || symbol_dt.get_metatype() == TypeMetatype::Array {
                    return true;
                }
            }
            if addr.get_offset().wrapping_sub(next_addr.get_offset()) >= max as i64 as u64 {
                break;
            }
        }
        false
    }

    pub fn get_hole_size(&self, off: i32, types: &TypeFactory) -> i32 {
        match &self.kind {
            TypeKind::Array(data) => {
                let arrayof = types.get(data.arrayof.expect("array without element type"));
                let new_off = off % arrayof.get_align_size();
                arrayof.get_hole_size(new_off, types)
            }
            TypeKind::Struct(data) => {
                let mut index = self.get_lower_bound_field(off);
                if index >= 0 {
                    let curfield = &data.field[index as usize];
                    let new_off = off - curfield.offset;
                    let field_type = types.get(curfield.tp);
                    if new_off < field_type.get_size() {
                        return field_type.get_hole_size(new_off, types);
                    }
                }
                index += 1;
                if (index as usize) < data.field.len() {
                    return data.field[index as usize].offset - off;
                }
                self.get_size() - off
            }
            TypeKind::PartialStruct(data) => {
                let size_left = self.size - off;
                let res = types.get(data.container).get_hole_size(off + data.offset, types);
                if res > size_left { size_left } else { res }
            }
            _ => 0,
        }
    }

    pub fn num_depend(&self, types: &TypeFactory) -> i32 {
        match &self.kind {
            TypeKind::Pointer(_) | TypeKind::PointerRel(_) => 1,
            TypeKind::Array(_) => 1,
            TypeKind::Struct(data) => data.field.len() as i32,
            TypeKind::Union(data) => data.field.len() as i32,
            TypeKind::PartialUnion(data) => types.get(data.container).num_depend(types),
            _ => 0,
        }
    }

    pub fn get_depend(&self, index: i32, types: &TypeFactory) -> Option<TypeId> {
        match &self.kind {
            TypeKind::Pointer(data) => data.ptrto,
            TypeKind::PointerRel(data) => data.pointer.ptrto,
            TypeKind::Array(data) => data.arrayof,
            TypeKind::Struct(data) => Some(data.field[index as usize].tp),
            TypeKind::Union(data) => Some(data.field[index as usize].tp),
            TypeKind::PartialUnion(data) => {
                let res = types.get(data.container).get_depend(index, types)?;
                if types.get(res).get_size() != self.size {
                    return Some(data.stripped);
                }
                Some(res)
            }
            _ => None,
        }
    }

    pub fn get_ptr_into(&self, off: &mut i32, types: &TypeFactory) -> Option<TypeId> {
        match &self.kind {
            TypeKind::Pointer(data) => {
                *off = 0;
                data.ptrto
            }
            TypeKind::PointerRel(data) => {
                let ptrto = data.pointer.ptrto.expect("pointer without target");
                let meta = types.get(ptrto).get_metatype();
                if meta == TypeMetatype::Struct || meta == TypeMetatype::Union {
                    *off = 0;
                    return Some(ptrto);
                }
                *off = data.offset;
                data.parent
            }
            _ => None,
        }
    }

    pub fn print_name_base(&self, out: &mut String, types: &TypeFactory) {
        match &self.kind {
            TypeKind::Pointer(data) => {
                out.push('p');
                types
                    .get(data.ptrto.expect("pointer without target"))
                    .print_name_base(out, types);
            }
            TypeKind::PointerRel(data) => {
                out.push('p');
                types
                    .get(data.pointer.ptrto.expect("pointer without target"))
                    .print_name_base(out, types);
            }
            TypeKind::Array(data) => {
                out.push('a');
                types
                    .get(data.arrayof.expect("array without element type"))
                    .print_name_base(out, types);
            }
            _ => {
                if let Some(first) = self.name.chars().next() {
                    out.push(first);
                }
            }
        }
    }

    fn compare_base(&self, op: &Datatype) -> i32 {
        if self.submeta != op.submeta {
            return order_code(self.submeta, op.submeta);
        }
        if self.size != op.size {
            return op.size.wrapping_sub(self.size);
        }
        0
    }

    fn compare_ids(&self, op: &Datatype) -> i32 {
        if self.id == op.get_id() {
            return 0;
        }
        order_code(self.id, op.get_id())
    }

    fn compare_pointer(&self, op: &Datatype, mut level: i32, types: &TypeFactory) -> i32 {
        let res = self.compare_base(op);
        if res != 0 {
            return res;
        }
        let data = self.pointer_data();
        let Some(other) = op.pointer_data_option() else {
            return 0;
        };
        if data.wordsize != other.wordsize {
            return order_code(data.wordsize, other.wordsize);
        }
        let space1 = space_order_index(&data.spaceid);
        let space2 = space_order_index(&other.spaceid);
        if space1 != space2 {
            if data.spaceid.is_none() {
                return 1;
            }
            if other.spaceid.is_none() {
                return -1;
            }
            return order_code(space1, space2);
        }
        level -= 1;
        if level < 0 {
            return self.compare_ids(op);
        }
        let ptrto = types.get(data.ptrto.expect("pointer without target"));
        let other_ptrto = types.get(other.ptrto.expect("pointer without target"));
        ptrto.compare(other_ptrto, level, types)
    }

    pub fn compare(&self, op: &Datatype, level: i32, types: &TypeFactory) -> i32 {
        match &self.kind {
            TypeKind::Pointer(_) => self.compare_pointer(op, level, types),
            TypeKind::PointerRel(data) => {
                let res = self.compare_pointer(op, level, types);
                if res != 0 {
                    return res;
                }
                let other_stripped = match &op.kind {
                    TypeKind::PointerRel(other) => other.stripped,
                    _ => None,
                };
                if data.stripped.is_none() {
                    if other_stripped.is_some() {
                        return -1;
                    }
                } else if other_stripped.is_none() {
                    return 1;
                }
                0
            }
            TypeKind::Array(data) => {
                let res = self.compare_base(op);
                if res != 0 {
                    return res;
                }
                let level = level - 1;
                if level < 0 {
                    return self.compare_ids(op);
                }
                let TypeKind::Array(other) = &op.kind else {
                    return 0;
                };
                let arrayof = types.get(data.arrayof.expect("array without element type"));
                let other_arrayof = types.get(other.arrayof.expect("array without element type"));
                arrayof.compare(other_arrayof, level, types)
            }
            TypeKind::Enum(_) => self.compare_dependency(op, types),
            TypeKind::Struct(data) => {
                let res = self.compare_base(op);
                if res != 0 {
                    return res;
                }
                let TypeKind::Struct(other) = &op.kind else {
                    return 0;
                };
                if data.field.len() != other.field.len() {
                    return (other.field.len() as i32).wrapping_sub(data.field.len() as i32);
                }
                for (field1, field2) in data.field.iter().zip(other.field.iter()) {
                    let cmp = field1.compare(field2, types);
                    if cmp != 0 {
                        return cmp;
                    }
                }
                if data.bitfield.len() != other.bitfield.len() {
                    return (other.bitfield.len() as i32).wrapping_sub(data.bitfield.len() as i32);
                }
                for (bit1, bit2) in data.bitfield.iter().zip(other.bitfield.iter()) {
                    let cmp = bit1.compare(bit2, types);
                    if cmp != 0 {
                        return cmp;
                    }
                }
                let level = level - 1;
                if level < 0 {
                    return self.compare_ids(op);
                }
                for (field1, field2) in data.field.iter().zip(other.field.iter()) {
                    if field1.tp != field2.tp {
                        let cmp = types.get(field1.tp).compare(types.get(field2.tp), level, types);
                        if cmp != 0 {
                            return cmp;
                        }
                    }
                }
                for (bit1, bit2) in data.bitfield.iter().zip(other.bitfield.iter()) {
                    if bit1.tp != bit2.tp {
                        let cmp = types.get(bit1.tp).compare(types.get(bit2.tp), level, types);
                        if cmp != 0 {
                            return cmp;
                        }
                    }
                }
                0
            }
            TypeKind::Union(data) => {
                let res = self.compare_base(op);
                if res != 0 {
                    return res;
                }
                let TypeKind::Union(other) = &op.kind else {
                    return 0;
                };
                if data.field.len() != other.field.len() {
                    return (other.field.len() as i32).wrapping_sub(data.field.len() as i32);
                }
                for (field1, field2) in data.field.iter().zip(other.field.iter()) {
                    if field1.name != field2.name {
                        return order_code(&field1.name, &field2.name);
                    }
                    let meta1 = types.get(field1.tp).get_metatype();
                    let meta2 = types.get(field2.tp).get_metatype();
                    if meta1 != meta2 {
                        return order_code(meta1, meta2);
                    }
                }
                let level = level - 1;
                if level < 0 {
                    return self.compare_ids(op);
                }
                for (field1, field2) in data.field.iter().zip(other.field.iter()) {
                    if field1.tp != field2.tp {
                        let cmp = types.get(field1.tp).compare(types.get(field2.tp), level, types);
                        if cmp != 0 {
                            return cmp;
                        }
                    }
                }
                0
            }
            TypeKind::PartialEnum(_) | TypeKind::PartialStruct(_) | TypeKind::PartialUnion(_) => {
                let res = self.compare_base(op);
                if res != 0 {
                    return res;
                }
                let (offset, parent) = self.partial_parts().expect("partial data-type");
                let Some((other_offset, other_parent)) = op.partial_parts() else {
                    return 0;
                };
                if offset != other_offset {
                    return order_code(offset, other_offset);
                }
                let level = level - 1;
                if level < 0 {
                    return self.compare_ids(op);
                }
                types.get(parent).compare(types.get(other_parent), level, types)
            }
            TypeKind::Code(_) => {
                let res = self.compare_base(op);
                if res != 0 {
                    return res;
                }
                let res = self.compare_basic(op);
                if res != 2 {
                    return res;
                }
                let level = level - 1;
                if level < 0 {
                    return self.compare_ids(op);
                }
                let sig1 = self.code_signature().expect("code data-type without prototype");
                let sig2 = op.code_signature().expect("code data-type without prototype");
                for (param1, param2) in sig1.params.iter().zip(sig2.params.iter()) {
                    let cmp = types.get(*param1).compare(types.get(*param2), level, types);
                    if cmp != 0 {
                        return cmp;
                    }
                }
                match (sig1.output, sig2.output) {
                    (None, None) => 0,
                    (None, Some(_)) => 1,
                    (Some(_), None) => -1,
                    (Some(otype), Some(opotype)) => types.get(otype).compare(types.get(opotype), level, types),
                }
            }
            TypeKind::Spacebase(_) => self.compare_dependency(op, types),
            _ => self.compare_base(op),
        }
    }

    fn partial_parts(&self) -> Option<(i32, TypeId)> {
        match &self.kind {
            TypeKind::PartialEnum(data) => Some((data.offset, data.parent)),
            TypeKind::PartialStruct(data) => Some((data.offset, data.container)),
            TypeKind::PartialUnion(data) => Some((data.offset, data.container)),
            _ => None,
        }
    }

    pub fn compare_dependency(&self, op: &Datatype, _types: &TypeFactory) -> i32 {
        match &self.kind {
            TypeKind::Pointer(data) => {
                if self.submeta != op.get_sub_meta() {
                    return order_code(self.submeta, op.get_sub_meta());
                }
                let Some(other) = op.pointer_data_option() else {
                    return op.get_size().wrapping_sub(self.size);
                };
                if data.ptrto != other.ptrto {
                    return order_code(data.ptrto, other.ptrto);
                }
                if data.wordsize != other.wordsize {
                    return order_code(data.wordsize, other.wordsize);
                }
                let space1 = space_order_index(&data.spaceid);
                let space2 = space_order_index(&other.spaceid);
                if space1 != space2 {
                    if data.spaceid.is_none() {
                        return 1;
                    }
                    if other.spaceid.is_none() {
                        return -1;
                    }
                    return order_code(space1, space2);
                }
                op.get_size().wrapping_sub(self.size)
            }
            TypeKind::PointerRel(data) => {
                if self.submeta != op.get_sub_meta() {
                    return order_code(self.submeta, op.get_sub_meta());
                }
                let TypeKind::PointerRel(other) = &op.kind else {
                    return op.get_size().wrapping_sub(self.size);
                };
                if data.pointer.ptrto != other.pointer.ptrto {
                    return order_code(data.pointer.ptrto, other.pointer.ptrto);
                }
                if data.offset != other.offset {
                    return order_code(data.offset, other.offset);
                }
                if data.parent != other.parent {
                    return order_code(data.parent, other.parent);
                }
                if data.pointer.wordsize != other.pointer.wordsize {
                    return order_code(data.pointer.wordsize, other.pointer.wordsize);
                }
                op.get_size().wrapping_sub(self.size)
            }
            TypeKind::Array(data) => {
                if self.submeta != op.get_sub_meta() {
                    return order_code(self.submeta, op.get_sub_meta());
                }
                if let TypeKind::Array(other) = &op.kind
                    && data.arrayof != other.arrayof
                {
                    return order_code(data.arrayof, other.arrayof);
                }
                op.get_size().wrapping_sub(self.size)
            }
            TypeKind::Enum(data) => {
                let res = self.compare_base(op);
                if res != 0 {
                    return res;
                }
                let other_map = match &op.kind {
                    TypeKind::Enum(other) => &other.namemap,
                    TypeKind::PartialEnum(other) => &other.enum_data.namemap,
                    _ => return 0,
                };
                if data.namemap.len() != other_map.len() {
                    return order_code(data.namemap.len(), other_map.len());
                }
                for ((key1, name1), (key2, name2)) in data.namemap.iter().zip(other_map.iter()) {
                    if key1 != key2 {
                        return order_code(key1, key2);
                    }
                    if name1 != name2 {
                        return order_code(name1, name2);
                    }
                }
                0
            }
            TypeKind::Struct(data) => {
                let res = self.compare_base(op);
                if res != 0 {
                    return res;
                }
                let TypeKind::Struct(other) = &op.kind else {
                    return 0;
                };
                if data.field.len() != other.field.len() {
                    return (other.field.len() as i32).wrapping_sub(data.field.len() as i32);
                }
                for (field1, field2) in data.field.iter().zip(other.field.iter()) {
                    let cmp = field1.compare_dependency(field2);
                    if cmp != 0 {
                        return cmp;
                    }
                }
                if data.bitfield.len() != other.bitfield.len() {
                    return (other.bitfield.len() as i32).wrapping_sub(data.bitfield.len() as i32);
                }
                for (bit1, bit2) in data.bitfield.iter().zip(other.bitfield.iter()) {
                    let cmp = bit1.compare_dependency(bit2);
                    if cmp != 0 {
                        return cmp;
                    }
                }
                0
            }
            TypeKind::Union(data) => {
                let res = self.compare_base(op);
                if res != 0 {
                    return res;
                }
                let TypeKind::Union(other) = &op.kind else {
                    return 0;
                };
                if data.field.len() != other.field.len() {
                    return (other.field.len() as i32).wrapping_sub(data.field.len() as i32);
                }
                for (field1, field2) in data.field.iter().zip(other.field.iter()) {
                    if field1.name != field2.name {
                        return order_code(&field1.name, &field2.name);
                    }
                    if field1.tp != field2.tp {
                        return order_code(field1.tp, field2.tp);
                    }
                }
                0
            }
            TypeKind::PartialEnum(_) | TypeKind::PartialStruct(_) | TypeKind::PartialUnion(_) => {
                if self.submeta != op.get_sub_meta() {
                    return order_code(self.submeta, op.get_sub_meta());
                }
                let (offset, parent) = self.partial_parts().expect("partial data-type");
                if let Some((other_offset, other_parent)) = op.partial_parts() {
                    if parent != other_parent {
                        return order_code(parent, other_parent);
                    }
                    if offset != other_offset {
                        return order_code(offset, other_offset);
                    }
                }
                op.get_size().wrapping_sub(self.size)
            }
            TypeKind::Code(_) => {
                let res = self.compare_base(op);
                if res != 0 {
                    return res;
                }
                let res = self.compare_basic(op);
                if res != 2 {
                    return res;
                }
                let sig1 = self.code_signature().expect("code data-type without prototype");
                let sig2 = op.code_signature().expect("code data-type without prototype");
                for (param1, param2) in sig1.params.iter().zip(sig2.params.iter()) {
                    if param1 != param2 {
                        return order_code(param1, param2);
                    }
                }
                match (sig1.output, sig2.output) {
                    (None, None) => 0,
                    (None, Some(_)) => 1,
                    (Some(_), None) => -1,
                    (Some(otype), Some(opotype)) => {
                        if otype != opotype {
                            return order_code(otype, opotype);
                        }
                        0
                    }
                }
            }
            TypeKind::Spacebase(data) => {
                let res = self.compare_base(op);
                if res != 0 {
                    return res;
                }
                let TypeKind::Spacebase(other) = &op.kind else {
                    return 0;
                };
                let space1 = space_order_index(&data.spaceid);
                let space2 = space_order_index(&other.spaceid);
                if space1 != space2 {
                    return order_code(space1, space2);
                }
                if data.scope_id != other.scope_id {
                    return order_code(data.scope_id, other.scope_id);
                }
                0
            }
            _ => self.compare_base(op),
        }
    }

    pub fn compare_basic(&self, op: &Datatype) -> i32 {
        let sig1 = self.code_signature();
        let sig2 = op.code_signature();
        let Some(sig1) = sig1 else {
            if sig2.is_none() {
                return 0;
            }
            return 1;
        };
        let Some(sig2) = sig2 else {
            return -1;
        };
        match (&sig1.model_name, &sig2.model_name) {
            (None, Some(_)) => return 1,
            (Some(_), None) => return -1,
            (Some(model1), Some(model2)) => {
                if model1 != model2 {
                    return order_code(model1, model2);
                }
            }
            (None, None) => {}
        }
        let nump = sig1.params.len();
        let opnump = sig2.params.len();
        if nump != opnump {
            return if opnump < nump { -1 } else { 1 };
        }
        let myflags = sig1.comparable_flags;
        let opflags = sig2.comparable_flags;
        if myflags != opflags {
            return order_code(myflags, opflags);
        }
        2
    }

    pub fn encode(&self, encoder: &mut dyn Encoder, glb: &Architecture) -> Result<()> {
        let types = types_of(glb);
        let has_typedef = self.typedef_imm.is_some();
        match &self.kind {
            TypeKind::Char => {
                if has_typedef {
                    return self.encode_typedef(encoder, glb);
                }
                encoder.open_element(ELEM_TYPE);
                self.encode_basic(self.metatype, -1, encoder)?;
                encoder.write_bool(ATTRIB_CHAR, true);
                encoder.close_element(ELEM_TYPE);
            }
            TypeKind::Unicode => {
                if has_typedef {
                    return self.encode_typedef(encoder, glb);
                }
                encoder.open_element(ELEM_TYPE);
                self.encode_basic(self.metatype, -1, encoder)?;
                encoder.write_bool(ATTRIB_UTF, true);
                encoder.close_element(ELEM_TYPE);
            }
            TypeKind::Void => {
                if has_typedef {
                    return self.encode_typedef(encoder, glb);
                }
                encoder.open_element(ELEM_VOID);
                encoder.close_element(ELEM_VOID);
            }
            TypeKind::Pointer(data) => {
                if has_typedef {
                    return self.encode_typedef(encoder, glb);
                }
                encoder.open_element(ELEM_TYPE);
                self.encode_basic(self.metatype, -1, encoder)?;
                if data.wordsize != 1 {
                    encoder.write_unsigned_integer(ATTRIB_WORDSIZE, data.wordsize as u64);
                }
                if let Some(spc) = &data.spaceid {
                    encoder.write_space(ATTRIB_SPACE, spc);
                }
                types
                    .get(data.ptrto.expect("pointer without target"))
                    .encode_ref(encoder, glb)?;
                encoder.close_element(ELEM_TYPE);
            }
            TypeKind::Array(data) => {
                if has_typedef {
                    return self.encode_typedef(encoder, glb);
                }
                encoder.open_element(ELEM_TYPE);
                self.encode_basic(self.metatype, -1, encoder)?;
                encoder.write_signed_integer(ATTRIB_ARRAYSIZE, data.arraysize as i64);
                types
                    .get(data.arrayof.expect("array without element type"))
                    .encode_ref(encoder, glb)?;
                encoder.close_element(ELEM_TYPE);
            }
            TypeKind::Enum(data) => {
                if has_typedef {
                    return self.encode_typedef(encoder, glb);
                }
                encoder.open_element(ELEM_TYPE);
                let meta = if self.metatype == TypeMetatype::Int {
                    TypeMetatype::EnumInt
                } else {
                    TypeMetatype::EnumUint
                };
                self.encode_basic(meta, -1, encoder)?;
                for (value, name) in data.namemap.iter() {
                    encoder.open_element(ELEM_VAL);
                    encoder.write_string(ATTRIB_NAME, name);
                    encoder.write_unsigned_integer(ATTRIB_VALUE, *value);
                    encoder.close_element(ELEM_VAL);
                }
                encoder.close_element(ELEM_TYPE);
            }
            TypeKind::Struct(data) => {
                if has_typedef {
                    return self.encode_typedef(encoder, glb);
                }
                encoder.open_element(ELEM_TYPE);
                self.encode_basic(self.metatype, self.alignment, encoder)?;
                let mut field_index = 0;
                let mut bit_index = 0;
                while field_index < data.field.len() && bit_index < data.bitfield.len() {
                    if data.field[field_index].offset < data.bitfield[bit_index].bits.byte_offset {
                        data.field[field_index].encode(encoder, glb)?;
                        field_index += 1;
                    } else {
                        data.bitfield[bit_index].encode(encoder, glb)?;
                        bit_index += 1;
                    }
                }
                for field in data.field[field_index..].iter() {
                    field.encode(encoder, glb)?;
                }
                for bitfield in data.bitfield[bit_index..].iter() {
                    bitfield.encode(encoder, glb)?;
                }
                encoder.close_element(ELEM_TYPE);
            }
            TypeKind::Union(data) => {
                if has_typedef {
                    return self.encode_typedef(encoder, glb);
                }
                encoder.open_element(ELEM_TYPE);
                self.encode_basic(self.metatype, self.alignment, encoder)?;
                for field in data.field.iter() {
                    field.encode(encoder, glb)?;
                }
                encoder.close_element(ELEM_TYPE);
            }
            TypeKind::PartialEnum(data) => {
                encoder.open_element(ELEM_TYPE);
                self.encode_basic(TypeMetatype::PartialEnum, -1, encoder)?;
                encoder.write_signed_integer(ATTRIB_OFFSET, data.offset as i64);
                types.get(data.parent).encode_ref(encoder, glb)?;
                encoder.close_element(ELEM_TYPE);
            }
            TypeKind::PartialUnion(data) => {
                encoder.open_element(ELEM_TYPE);
                self.encode_basic(self.metatype, -1, encoder)?;
                encoder.write_signed_integer(ATTRIB_OFFSET, data.offset as i64);
                types.get(data.container).encode_ref(encoder, glb)?;
                encoder.close_element(ELEM_TYPE);
            }
            TypeKind::PointerRel(data) => {
                encoder.open_element(ELEM_TYPE);
                self.encode_basic(TypeMetatype::PtrRel, -1, encoder)?;
                if data.pointer.wordsize != 1 {
                    encoder.write_unsigned_integer(ATTRIB_WORDSIZE, data.pointer.wordsize as u64);
                }
                types
                    .get(data.pointer.ptrto.expect("pointer without target"))
                    .encode(encoder, glb)?;
                types
                    .get(data.parent.expect("relative pointer without parent"))
                    .encode_ref(encoder, glb)?;
                encoder.open_element(ELEM_OFF);
                encoder.write_signed_integer(ATTRIB_CONTENT, data.offset as i64);
                encoder.close_element(ELEM_OFF);
                encoder.close_element(ELEM_TYPE);
            }
            TypeKind::Code(data) => {
                if has_typedef {
                    return self.encode_typedef(encoder, glb);
                }
                encoder.open_element(ELEM_TYPE);
                self.encode_basic(self.metatype, -1, encoder)?;
                if let Some(proto) = &data.proto {
                    proto.encode(encoder, glb)?;
                }
                encoder.close_element(ELEM_TYPE);
            }
            TypeKind::Spacebase(data) => {
                if has_typedef {
                    return self.encode_typedef(encoder, glb);
                }
                encoder.open_element(ELEM_TYPE);
                self.encode_basic(self.metatype, -1, encoder)?;
                encoder.write_space(
                    ATTRIB_SPACE,
                    data.spaceid.as_ref().expect("spacebase without address space"),
                );
                let mut localframe = Address::default();
                let scope = self.get_map(glb)?;
                let db = glb.symboltab.as_deref().expect("symbol table is not initialized");
                let scope_data = db.scope(scope);
                if !scope_data.is_global() {
                    localframe = scope_data.get_function().expect("local scope without function").clone();
                }
                localframe.encode(encoder)?;
                encoder.close_element(ELEM_TYPE);
            }
            TypeKind::Base | TypeKind::PartialStruct(_) => {
                encoder.open_element(ELEM_TYPE);
                self.encode_basic(self.metatype, -1, encoder)?;
                encoder.close_element(ELEM_TYPE);
            }
        }
        Ok(())
    }

    pub fn encode_basic(&self, meta: TypeMetatype, align: i32, encoder: &mut dyn Encoder) -> Result<()> {
        encoder.write_string(ATTRIB_NAME, &self.name);
        let save_id = self.get_unsized_id();
        if save_id != 0 {
            encoder.write_unsigned_integer(ATTRIB_ID, save_id);
        }
        encoder.write_signed_integer(ATTRIB_SIZE, self.size as i64);
        let metastring = metatype2string(meta)?;
        encoder.write_string(ATTRIB_METATYPE, &metastring);
        if align > 0 {
            encoder.write_signed_integer(ATTRIB_ALIGNMENT, align as i64);
        }
        if (self.flags & Datatype::CORETYPE) != 0 {
            encoder.write_bool(ATTRIB_CORE, true);
        }
        if self.is_variable_length() {
            encoder.write_bool(ATTRIB_VARLENGTH, true);
        }
        if (self.flags & Datatype::OPAQUE_STRING) != 0 {
            encoder.write_bool(ATTRIB_OPAQUESTRING, true);
        }
        let format = self.get_display_format();
        if format != 0 {
            encoder.write_string(ATTRIB_FORMAT, &Datatype::decode_integer_format(format)?);
        }
        Ok(())
    }

    pub fn encode_ref(&self, encoder: &mut dyn Encoder, glb: &Architecture) -> Result<()> {
        if self.id != 0 && self.metatype != TypeMetatype::Void {
            encoder.open_element(ELEM_TYPEREF);
            encoder.write_string(ATTRIB_NAME, &self.name);
            if self.is_variable_length() {
                encoder.write_unsigned_integer(ATTRIB_ID, Datatype::hash_size(self.id, self.size));
                encoder.write_signed_integer(ATTRIB_SIZE, self.size as i64);
            } else {
                encoder.write_unsigned_integer(ATTRIB_ID, self.id);
            }
            encoder.close_element(ELEM_TYPEREF);
            Ok(())
        } else {
            self.encode(encoder, glb)
        }
    }

    pub fn encode_typedef(&self, encoder: &mut dyn Encoder, glb: &Architecture) -> Result<()> {
        encoder.open_element(ELEM_DEF);
        encoder.write_string(ATTRIB_NAME, &self.name);
        encoder.write_unsigned_integer(ATTRIB_ID, self.id);
        let format = self.get_display_format();
        if format != 0 {
            encoder.write_string(ATTRIB_FORMAT, &Datatype::decode_integer_format(format)?);
        }
        let typedef_imm = self.typedef_imm.expect("typedef without underlying data-type");
        types_of(glb).get(typedef_imm).encode_ref(encoder, glb)?;
        encoder.close_element(ELEM_DEF);
        Ok(())
    }

    pub fn is_ptrsub_matching(&self, off: i64, extra: i64, multiplier: i64, glb: &Architecture) -> bool {
        self.ptrsub_matching(off, extra, multiplier, types_of(glb), Some(glb))
    }

    pub(crate) fn ptrsub_matching(
        &self,
        off: i64,
        extra: i64,
        multiplier: i64,
        types: &TypeFactory,
        glb: Option<&Architecture>,
    ) -> bool {
        match &self.kind {
            TypeKind::PointerRel(data) if data.stripped.is_none() => {
                let wordsize = data.pointer.wordsize;
                let mut int_off = AddrSpace::address_to_byte_int(off, wordsize) as i32;
                let extra = AddrSpace::address_to_byte_int(extra, wordsize);
                int_off = (int_off as i64).wrapping_add((data.offset as i64).wrapping_add(extra)) as i32;
                let parent = types.get(data.parent.expect("relative pointer without parent"));
                int_off >= 0 && int_off <= parent.get_size()
            }
            TypeKind::Pointer(_) | TypeKind::PointerRel(_) => {
                let data = self.pointer_data();
                let off = AddrSpace::address_to_byte_int(off, data.wordsize);
                let extra = AddrSpace::address_to_byte_int(extra, data.wordsize);
                let multiplier = AddrSpace::address_to_byte_int(multiplier, data.wordsize);
                let ptrto = types.get(data.ptrto.expect("pointer without target"));
                ptrto.offset_valid(off, extra, multiplier, types, glb)
            }
            _ => false,
        }
    }

    pub fn is_offset_valid(&self, off: i64, extra: i64, multiplier: i64, glb: &Architecture) -> bool {
        self.offset_valid(off, extra, multiplier, types_of(glb), Some(glb))
    }

    pub(crate) fn offset_valid(
        &self,
        off: i64,
        extra: i64,
        multiplier: i64,
        types: &TypeFactory,
        glb: Option<&Architecture>,
    ) -> bool {
        match &self.kind {
            TypeKind::Array(_) => {
                if off != 0 {
                    return false;
                }
                if multiplier >= self.get_align_size() as i64 {
                    return false;
                }
                true
            }
            TypeKind::Struct(_) => {
                if multiplier >= self.get_align_size() as i64 {
                    return false;
                }
                let mut newoff = off;
                let sub_type = self.sub_type(off, &mut newoff, types, glb);
                match sub_type {
                    Some(sub) => {
                        if newoff != 0 {
                            return false;
                        }
                        let sub_dt = types.get(sub);
                        if (extra < 0 || extra >= sub_dt.get_size() as i64) && !sub_dt.array_slack(extra, types, glb) {
                            return false;
                        }
                    }
                    None => {
                        let extra = extra + newoff;
                        if (extra < 0 || extra >= self.size as i64) && self.size != 0 {
                            return false;
                        }
                    }
                }
                true
            }
            TypeKind::Code(_) => extra >= 0,
            TypeKind::Spacebase(_) => {
                let mut newoff = off;
                let sub_type = self.sub_type(off, &mut newoff, types, glb);
                let Some(sub) = sub_type else {
                    return false;
                };
                if newoff != 0 {
                    return false;
                }
                let sub_dt = types.get(sub);
                if sub_dt.get_metatype() == TypeMetatype::Code {
                    if extra < 0 {
                        return false;
                    }
                } else if (extra < 0 || extra >= sub_dt.get_size() as i64) && !sub_dt.array_slack(extra, types, glb) {
                    return false;
                }
                true
            }
            _ => false,
        }
    }

    pub fn get_stripped(&self) -> Option<TypeId> {
        match &self.kind {
            TypeKind::PartialEnum(data) => Some(data.stripped),
            TypeKind::PartialStruct(data) => Some(data.stripped),
            TypeKind::PartialUnion(data) => Some(data.stripped),
            TypeKind::PointerRel(data) => data.stripped,
            _ => None,
        }
    }

    pub fn find_compatible_resolve(&self, ct: TypeId, types: &TypeFactory) -> i32 {
        let ct_dt = types.get(ct);
        match &self.kind {
            TypeKind::Pointer(_) | TypeKind::PointerRel(_) => {
                if ct_dt.get_metatype() == TypeMetatype::Ptr {
                    let ptrto = types.get(self.get_ptr_to());
                    return ptrto.find_compatible_resolve(ct_dt.get_ptr_to(), types);
                }
                -1
            }
            TypeKind::Array(data) => {
                let arrayof = data.arrayof.expect("array without element type");
                if ct_dt.needs_resolution()
                    && !types.get(arrayof).needs_resolution()
                    && ct_dt.find_compatible_resolve(arrayof, types) >= 0
                {
                    return 0;
                }
                if arrayof == ct {
                    return 0;
                }
                -1
            }
            TypeKind::Struct(data) => {
                let field_type = data.field[0].tp;
                if ct_dt.needs_resolution()
                    && !types.get(field_type).needs_resolution()
                    && ct_dt.find_compatible_resolve(field_type, types) >= 0
                {
                    return 0;
                }
                if field_type == ct {
                    return 0;
                }
                -1
            }
            TypeKind::Union(data) => {
                if !ct_dt.needs_resolution() {
                    for (index, field) in data.field.iter().enumerate() {
                        if field.tp == ct && field.offset == 0 {
                            return index as i32;
                        }
                    }
                } else {
                    for (index, field) in data.field.iter().enumerate() {
                        if field.offset != 0 {
                            continue;
                        }
                        let field_type = types.get(field.tp);
                        if field_type.get_size() != ct_dt.get_size() {
                            continue;
                        }
                        if field_type.needs_resolution() {
                            continue;
                        }
                        if ct_dt.find_compatible_resolve(field.tp, types) >= 0 {
                            return index as i32;
                        }
                    }
                }
                -1
            }
            TypeKind::PartialUnion(data) => types.get(data.container).find_compatible_resolve(ct, types),
            _ => -1,
        }
    }

    pub fn is_primitive_whole(&self, types: &TypeFactory) -> bool {
        if !self.is_piece_structured() {
            return true;
        }
        if (self.metatype == TypeMetatype::Array || self.metatype == TypeMetatype::Struct) && self.num_depend(types) > 0
        {
            let component = types.get(self.get_depend(0, types).expect("component data-type"));
            if component.get_size() == self.get_size() {
                return component.is_primitive_whole(types);
            }
        }
        false
    }

    pub fn nearest_arrayed_component(&self, off: i64, array_hint: u32, newoff: &mut i64, glb: &Architecture) -> bool {
        let types = types_of(glb);
        let mut before = Nearest::default();
        let mut after = Nearest::default();
        let type_before = self.nearest_backward(off, &mut before, types, Some(glb));
        let type_after = self.nearest_forward(off, &mut after, types, Some(glb));
        if !type_before && !type_after {
            return false;
        }
        if !type_before {
            *newoff = after.offset;
            return true;
        }
        if !type_after {
            *newoff = before.offset;
            return true;
        }
        if array_hint != 1 && before.el_size != after.el_size {
            if before.el_size as u32 == array_hint {
                *newoff = before.offset;
                return true;
            }
            if after.el_size as u32 == array_hint {
                *newoff = after.offset;
                return true;
            }
        }
        if self.sub_type(off, newoff, types, Some(glb)).is_some()
            && (*newoff == before.offset || *newoff == after.offset)
        {
            return true;
        }
        *newoff = if after.distance <= before.distance {
            after.offset
        } else {
            before.offset
        };
        true
    }

    pub fn test_for_array_slack(&self, off: i64, glb: &Architecture) -> bool {
        self.array_slack(off, types_of(glb), Some(glb))
    }

    pub(crate) fn array_slack(&self, off: i64, types: &TypeFactory, glb: Option<&Architecture>) -> bool {
        if self.metatype == TypeMetatype::Array {
            return true;
        }
        let mut comp = Nearest::default();
        if off < 0 {
            return self.nearest_forward(off, &mut comp, types, glb);
        }
        self.nearest_backward(off, &mut comp, types, glb)
    }

    pub fn find_smallest_container(ct: TypeId, off: i64, sz: i64, newoff: &mut i64, glb: &Architecture) -> TypeId {
        let types = types_of(glb);
        let mut res = ct;
        let mut next = ct;
        let mut off = off;
        let mut cur_off = off;
        loop {
            let mut sub_off = cur_off;
            let Some(sub) = types.get(next).sub_type(cur_off, &mut sub_off, types, Some(glb)) else {
                break;
            };
            cur_off = sub_off;
            next = sub;
            if cur_off + sz > types.get(next).get_size() as i64 {
                break;
            }
            res = next;
            off = cur_off;
        }
        *newoff = off;
        res
    }

    pub fn encode_integer_format(val: &str) -> Result<u32> {
        match val {
            "hex" => Ok(1),
            "dec" => Ok(2),
            "oct" => Ok(3),
            "bin" => Ok(4),
            "char" => Ok(5),
            _ => Err(Error::Lowlevel(format!("Unrecognized integer format: {}", val))),
        }
    }

    pub fn decode_integer_format(val: u32) -> Result<String> {
        let res = match val {
            1 => "hex",
            2 => "dec",
            3 => "oct",
            4 => "bin",
            5 => "char",
            _ => return Err(Error::Lowlevel("Unrecognized integer format encoding".to_string())),
        };
        Ok(res.to_string())
    }

    pub fn decode_basic(&mut self, decoder: &mut dyn Decoder) -> Result<()> {
        self.size = -1;
        self.metatype = TypeMetatype::Void;
        self.id = 0;
        loop {
            let attrib = decoder.get_next_attribute_id()?;
            if attrib == 0 {
                break;
            }
            if attrib == ATTRIB_NAME {
                self.name = decoder.read_string()?;
            } else if attrib == ATTRIB_SIZE {
                self.size = decoder.read_signed_integer()? as i32;
            } else if attrib == ATTRIB_METATYPE {
                self.metatype = string2metatype(&decoder.read_string()?)?;
            } else if attrib == ATTRIB_CORE {
                if decoder.read_bool()? {
                    self.flags |= Datatype::CORETYPE;
                }
            } else if attrib == ATTRIB_ID {
                self.id = decoder.read_unsigned_integer()?;
            } else if attrib == ATTRIB_VARLENGTH {
                if decoder.read_bool()? {
                    self.flags |= Datatype::VARIABLE_LENGTH;
                }
            } else if attrib == ATTRIB_ALIGNMENT {
                self.alignment = decoder.read_signed_integer()? as i32;
            } else if attrib == ATTRIB_OPAQUESTRING {
                if decoder.read_bool()? {
                    self.flags |= Datatype::OPAQUE_STRING;
                }
            } else if attrib == ATTRIB_FORMAT {
                let val = Datatype::encode_integer_format(&decoder.read_string()?)?;
                self.set_display_format(val);
            } else if attrib == ATTRIB_LABEL {
                self.display_name = decoder.read_string()?;
            } else if attrib == ATTRIB_INCOMPLETE && decoder.read_bool()? {
                self.flags |= Datatype::TYPE_INCOMPLETE;
            }
        }
        if self.size < 0 {
            return Err(Error::Lowlevel(format!("Bad size for type {}", self.name)));
        }
        self.align_size = self.size;
        self.submeta = BASE2SUB[self.metatype as usize];
        if self.id == 0 && !self.name.is_empty() {
            self.id = Datatype::hash_name(&self.name);
        }
        if self.is_variable_length() {
            self.id = Datatype::hash_size(self.id, self.size);
        }
        if self.display_name.is_empty() {
            self.display_name = self.name.clone();
        }
        Ok(())
    }

    pub fn decode_char(&mut self, decoder: &mut dyn Decoder) -> Result<()> {
        self.decode_basic(decoder)?;
        self.submeta = if self.metatype == TypeMetatype::Int {
            SubMetatype::IntChar
        } else {
            SubMetatype::UintChar
        };
        Ok(())
    }

    pub fn decode_unicode(&mut self, decoder: &mut dyn Decoder) -> Result<()> {
        self.decode_basic(decoder)?;
        self.set_unicode_flags();
        self.submeta = if self.metatype == TypeMetatype::Int {
            SubMetatype::IntUnicode
        } else {
            SubMetatype::UintUnicode
        };
        Ok(())
    }

    pub fn decode_void(&mut self, decoder: &mut dyn Decoder) -> Result<()> {
        loop {
            let attrib = decoder.get_next_attribute_id()?;
            if attrib == 0 {
                break;
            }
            if attrib == ATTRIB_ID {
                self.id = decoder.read_unsigned_integer()?;
            }
        }
        Ok(())
    }

    fn decode_pointer_attributes(&mut self, decoder: &mut dyn Decoder) -> Result<()> {
        decoder.rewind_attributes();
        loop {
            let attrib = decoder.get_next_attribute_id()?;
            if attrib == 0 {
                break;
            }
            if attrib == ATTRIB_WORDSIZE {
                self.pointer_data_mut().wordsize = decoder.read_unsigned_integer()? as u32;
            } else if attrib == ATTRIB_SPACE {
                self.pointer_data_mut().spaceid = Some(decoder.read_space()?);
            }
        }
        Ok(())
    }

    pub fn decode_pointer(&mut self, decoder: &mut dyn Decoder, glb: &mut Architecture) -> Result<()> {
        self.decode_basic(decoder)?;
        self.decode_pointer_attributes(decoder)?;
        let ptrto = TypeFactory::decode_type(glb, decoder)?;
        self.pointer_data_mut().ptrto = Some(ptrto);
        let types = types_of_mut(glb);
        self.calc_submeta(types);
        if self.name.is_empty() {
            self.flags |= types.get(ptrto).inherit_for_pointer();
        }
        self.calc_truncate_local(types)
    }

    pub fn calc_submeta(&mut self, types: &TypeFactory) {
        let ptrto = types.get(self.get_ptr_to());
        let ptrto_meta = ptrto.get_metatype();
        let ptrto_needs_resolution = ptrto.needs_resolution();
        if ptrto_meta == TypeMetatype::Struct {
            if ptrto_needs_resolution {
                self.submeta = SubMetatype::Ptr;
            } else {
                self.submeta = SubMetatype::PtrStruct;
            }
        } else if ptrto_meta == TypeMetatype::Union {
            self.submeta = SubMetatype::PtrStruct;
        } else if ptrto_meta == TypeMetatype::Array {
            self.flags |= Datatype::POINTER_TO_ARRAY;
        }
        if ptrto_needs_resolution && ptrto_meta != TypeMetatype::Ptr {
            self.flags |= Datatype::NEEDS_RESOLUTION;
        }
    }

    pub fn calc_truncate(ct: TypeId, types: &mut TypeFactory) -> Result<()> {
        let dt = types.get(ct);
        if dt.get_truncate().is_some() || dt.size != types.get_size_of_alt_pointer() {
            return Ok(());
        }
        let ptrto = dt.get_ptr_to();
        let wordsize = dt.get_word_size();
        let new_size = types.get_size_of_pointer();
        let truncate = types.resize_pointer_parts(ptrto, wordsize, new_size)?;
        let big_endian = types.default_data_space_big_endian();
        let dt = types.get_mut(ct);
        dt.pointer_data_mut().truncate = Some(truncate);
        if big_endian {
            dt.flags |= Datatype::TRUNCATE_BIGENDIAN;
        }
        Ok(())
    }

    pub fn calc_truncate_local(&mut self, types: &mut TypeFactory) -> Result<()> {
        if self.get_truncate().is_some() || self.size != types.get_size_of_alt_pointer() {
            return Ok(());
        }
        let new_size = types.get_size_of_pointer();
        let truncate = types.resize_pointer_parts(self.get_ptr_to(), self.get_word_size(), new_size)?;
        self.pointer_data_mut().truncate = Some(truncate);
        if types.default_data_space_big_endian() {
            self.flags |= Datatype::TRUNCATE_BIGENDIAN;
        }
        Ok(())
    }

    pub fn down_chain(
        ct: TypeId,
        off: &mut i64,
        par: &mut Option<TypeId>,
        par_off: &mut i64,
        allow_array_wrap: bool,
        glb: &mut Architecture,
    ) -> Result<Option<TypeId>> {
        let dt = types_of(glb).get(ct);
        if let TypeKind::PointerRel(data) = &dt.kind {
            let ptrto = data.pointer.ptrto.expect("pointer without target");
            let parent = data.parent.expect("relative pointer without parent");
            let offset = data.offset;
            let wordsize = data.pointer.wordsize;
            let size = dt.size;
            let types = types_of(glb);
            let ptrto_dt = types.get(ptrto);
            let ptrto_meta = ptrto_dt.get_metatype();
            if *off >= 0
                && *off < ptrto_dt.get_size() as i64
                && (ptrto_meta == TypeMetatype::Struct || ptrto_meta == TypeMetatype::Array)
            {
                return Datatype::pointer_down_chain(ct, off, par, par_off, allow_array_wrap, glb);
            }
            let rel_off = (off.wrapping_add(offset as i64) as u64 & calc_mask(size)) as i64;
            if rel_off < 0 || rel_off >= types.get(parent).get_size() as i64 {
                return Ok(None);
            }
            let orig_pointer = types_of_mut(glb).get_type_pointer(size, parent, wordsize)?;
            *off = rel_off;
            if rel_off == 0 && offset != 0 {
                return Ok(Some(orig_pointer));
            }
            return Datatype::pointer_down_chain(orig_pointer, off, par, par_off, allow_array_wrap, glb);
        }
        Datatype::pointer_down_chain(ct, off, par, par_off, allow_array_wrap, glb)
    }

    fn pointer_down_chain(
        ct: TypeId,
        off: &mut i64,
        par: &mut Option<TypeId>,
        par_off: &mut i64,
        allow_array_wrap: bool,
        glb: &mut Architecture,
    ) -> Result<Option<TypeId>> {
        let types = types_of(glb);
        let dt = types.get(ct);
        let size = dt.size;
        let wordsize = dt.get_word_size();
        let ptrto = dt.get_ptr_to();
        let ptrto_dt = types.get(ptrto);
        let ptrto_size = ptrto_dt.get_align_size();
        if (*off < 0 || *off >= ptrto_size as i64) && ptrto_size != 0 && !ptrto_dt.is_variable_length() {
            if !allow_array_wrap {
                return Ok(None);
            }
            let mut sign_off = sign_extend(*off, size * 8 - 1);
            sign_off %= ptrto_size as i64;
            if sign_off < 0 {
                sign_off += ptrto_size as i64;
            }
            *off = sign_off;
            if *off == 0 {
                return Ok(Some(ct));
            }
        }
        if ptrto_dt.is_enum_type() {
            let types = types_of_mut(glb);
            let tmp = types.get_base(1, TypeMetatype::Uint)?;
            *off = 0;
            return Ok(Some(types.get_type_pointer(size, tmp, wordsize)?));
        }
        let meta = ptrto_dt.get_metatype();
        let is_array = meta == TypeMetatype::Array;
        if is_array || meta == TypeMetatype::Struct {
            *par = Some(ct);
            *par_off = *off;
        }
        let mut newoff = *off;
        let pt = ptrto_dt.sub_type(*off, &mut newoff, types, Some(glb));
        *off = newoff;
        let Some(pt) = pt else {
            return Ok(None);
        };
        let types = types_of_mut(glb);
        if !is_array {
            return Ok(Some(types.get_type_pointer_strip_array(size, pt, wordsize)?));
        }
        Ok(Some(types.get_type_pointer(size, pt, wordsize)?))
    }

    pub fn get_sub_entry(
        &self,
        off: i32,
        sz: i32,
        newoff: &mut i32,
        el: &mut i32,
        types: &TypeFactory,
    ) -> Option<TypeId> {
        let arrayof = self.get_base();
        let align_size = types.get(arrayof).get_align_size();
        let noff = off % align_size;
        let nel = off / align_size;
        if noff + sz > align_size {
            return None;
        }
        *newoff = noff;
        *el = nel;
        Some(arrayof)
    }

    pub fn decode_array(&mut self, decoder: &mut dyn Decoder, glb: &mut Architecture) -> Result<()> {
        self.decode_basic(decoder)?;
        let mut arraysize = -1;
        decoder.rewind_attributes();
        loop {
            let attrib = decoder.get_next_attribute_id()?;
            if attrib == 0 {
                break;
            }
            if attrib == ATTRIB_ARRAYSIZE {
                arraysize = decoder.read_signed_integer()? as i32;
            }
        }
        let arrayof = TypeFactory::decode_type(glb, decoder)?;
        if let TypeKind::Array(data) = &mut self.kind {
            data.arraysize = arraysize;
            data.arrayof = Some(arrayof);
        }
        let element = types_of(glb).get(arrayof);
        if arraysize <= 0 || arraysize.wrapping_mul(element.get_align_size()) != self.size {
            return Err(Error::Lowlevel(format!(
                "Bad size for array of type {}",
                element.get_name()
            )));
        }
        self.alignment = element.get_alignment();
        if arraysize == 1 {
            self.flags |= Datatype::NEEDS_RESOLUTION;
        }
        Ok(())
    }

    pub fn decode_enum(&mut self, decoder: &mut dyn Decoder) -> Result<String> {
        self.decode_basic(decoder)?;
        self.metatype = if self.metatype == TypeMetatype::EnumInt {
            TypeMetatype::Int
        } else {
            TypeMetatype::Uint
        };
        let mut nmap: BTreeMap<u64, String> = BTreeMap::new();
        let mut warning = String::new();
        loop {
            let child_id = decoder.open_element()?;
            if child_id == 0 {
                break;
            }
            let mut val: u64 = 0;
            let mut nm = String::new();
            loop {
                let attrib = decoder.get_next_attribute_id()?;
                if attrib == 0 {
                    break;
                }
                if attrib == ATTRIB_VALUE {
                    let valsign = decoder.read_signed_integer()?;
                    val = (valsign as u64) & calc_mask(self.size);
                } else if attrib == ATTRIB_NAME {
                    nm = decoder.read_string()?;
                }
            }
            if nm.is_empty() {
                return Err(Error::Lowlevel(format!(
                    "{}: TypeEnum field missing name attribute",
                    self.name
                )));
            }
            if let std::collections::btree_map::Entry::Vacant(e) = nmap.entry(val) {
                e.insert(nm);
            } else {
                if warning.is_empty() {
                    warning = format!("Enum \"{}\": Some values do not have unique names", self.name);
                }
            }
            decoder.close_element(child_id)?;
        }
        self.set_name_map(&nmap);
        Ok(warning)
    }

    pub fn has_named_value(&self, val: u64, types: &TypeFactory) -> bool {
        match &self.kind {
            TypeKind::PartialEnum(data) => {
                let val = val.wrapping_shl((8 * data.offset) as u32);
                types.get(data.parent).has_named_value(val, types)
            }
            _ => self.enum_data().namemap.contains_key(&val),
        }
    }

    pub fn get_matches(&self, val: u64, rep: &mut EnumRepresentation, types: &TypeFactory) {
        if let TypeKind::PartialEnum(data) = &self.kind {
            let val = val.wrapping_shl((8 * data.offset) as u32);
            rep.shift_amount = data.offset * 8;
            types.get(data.parent).get_matches(val, rep, types);
            return;
        }
        let namemap = &self.enum_data().namemap;
        let mut val = val;
        for count in 0..2 {
            let allmatch;
            if val == 0 {
                match namemap.get(&val) {
                    Some(name) => {
                        rep.matchname.push(name.clone());
                        allmatch = true;
                    }
                    None => allmatch = false,
                }
            } else {
                let mut bitsleft = val;
                let mut target = val;
                while target != 0 {
                    let Some((curval, name)) = namemap.range(..=target).next_back() else {
                        break;
                    };
                    let curval = *curval;
                    let diff = coveringmask(bitsleft ^ curval);
                    if diff >= bitsleft {
                        break;
                    }
                    if (curval & diff) == 0 {
                        rep.matchname.push(name.clone());
                        bitsleft ^= curval;
                        target = bitsleft;
                    } else {
                        target = curval & !diff;
                    }
                }
                allmatch = bitsleft == 0;
            }
            if allmatch {
                rep.complement = count == 1;
                return;
            }
            val ^= calc_mask(self.size);
            rep.matchname.clear();
        }
    }

    pub fn assign_values(
        nmap: &mut BTreeMap<u64, String>,
        namelist: &[String],
        vallist: &mut [u64],
        assignlist: &[bool],
        te: &Datatype,
    ) -> Result<()> {
        let mask = calc_mask(te.get_size());
        let mut maxval: u64 = 0;
        for index in 0..namelist.len() {
            if assignlist[index] {
                let mut val = vallist[index];
                if val > maxval {
                    maxval = val;
                }
                val &= mask;
                if nmap.contains_key(&val) {
                    return Err(Error::Lowlevel(format!(
                        "Enum \"{}\": \"{}\" is a duplicate value",
                        te.name, namelist[index]
                    )));
                }
                nmap.insert(val, namelist[index].clone());
            }
        }
        for index in 0..namelist.len() {
            if !assignlist[index] {
                let mut val;
                loop {
                    maxval = maxval.wrapping_add(1);
                    val = maxval & mask;
                    if !nmap.contains_key(&val) {
                        break;
                    }
                }
                nmap.insert(val, namelist[index].clone());
            }
        }
        Ok(())
    }

    pub fn get_component_for_ptr(&self, types: &TypeFactory) -> TypeId {
        let TypeKind::PartialStruct(data) = &self.kind else {
            panic!("data-type is not a partial structure");
        };
        let container = types.get(data.container);
        if container.get_metatype() == TypeMetatype::Array {
            let eltype = container.get_base();
            let eltype_dt = types.get(eltype);
            if eltype_dt.get_metatype() != TypeMetatype::Unknown && (data.offset % eltype_dt.get_align_size()) == 0 {
                return eltype;
            }
        }
        data.stripped
    }

    pub fn decode_pointer_rel(&mut self, decoder: &mut dyn Decoder, glb: &mut Architecture) -> Result<()> {
        self.flags |= Datatype::IS_PTRREL;
        self.decode_basic(decoder)?;
        self.metatype = TypeMetatype::Ptr;
        self.decode_pointer_attributes(decoder)?;
        let ptrto = TypeFactory::decode_type(glb, decoder)?;
        let parent = TypeFactory::decode_type(glb, decoder)?;
        let sub_id = decoder.open_element_expect(ELEM_OFF)?;
        let offset = decoder.read_signed_integer_attr(ATTRIB_CONTENT)? as i32;
        decoder.close_element(sub_id)?;
        if let TypeKind::PointerRel(data) = &mut self.kind {
            data.pointer.ptrto = Some(ptrto);
            data.parent = Some(parent);
            data.offset = offset;
        }
        if offset == 0 {
            return Err(Error::Lowlevel(
                "For metatype=\"ptrstruct\", <off> tag must not be zero".to_string(),
            ));
        }
        self.submeta = SubMetatype::PtrRel;
        if self.name.is_empty() {
            self.mark_ephemeral(types_of_mut(glb))?;
        }
        Ok(())
    }

    pub fn evaluate_thru_parent(&self, addr_off: u64, types: &TypeFactory) -> bool {
        let data = self.pointer_rel_data();
        let mut byte_off = AddrSpace::address_to_byte(addr_off, data.pointer.wordsize);
        let ptrto = types.get(data.pointer.ptrto.expect("pointer without target"));
        if ptrto.get_metatype() == TypeMetatype::Struct && byte_off < ptrto.get_size() as i64 as u64 {
            return false;
        }
        byte_off = byte_off.wrapping_add(data.offset as i64 as u64) & calc_mask(self.size);
        let parent = types.get(data.parent.expect("relative pointer without parent"));
        byte_off < parent.get_size() as i64 as u64
    }

    pub fn get_ptr_to_from_parent(base: TypeId, off: i32, types: &mut TypeFactory) -> Result<TypeId> {
        if off > 0 {
            let mut curoff = off as i64;
            let mut cur = Some(base);
            loop {
                let current = cur.expect("sub-type chain");
                let mut newoff = curoff;
                cur = types.get(current).sub_type(curoff, &mut newoff, types, None);
                curoff = newoff;
                if !(curoff != 0 && cur.is_some()) {
                    break;
                }
            }
            match cur {
                Some(res) => Ok(res),
                None => types.get_base(1, TypeMetatype::Unknown),
            }
        } else {
            types.get_base(1, TypeMetatype::Unknown)
        }
    }

    fn code_data_mut(&mut self) -> &mut super::TypeCodeData {
        match &mut self.kind {
            TypeKind::Code(data) => data,
            _ => panic!("data-type is not a code data-type"),
        }
    }

    pub fn compute_code_signature(proto: &mut FuncProto, glb: &Architecture) -> CodeSignature {
        let model_name = if proto.has_model() {
            Some(proto.get_model_name(glb).to_string())
        } else {
            None
        };
        let nump = proto.num_params(glb);
        let mut params = Vec::with_capacity(nump.max(0) as usize);
        for index in 0..nump {
            let param = proto.get_param(index, glb).expect("prototype parameter");
            params.push(param.get_type(glb));
        }
        let output = proto.get_output_ref().map(|param| param.get_type(glb));
        CodeSignature {
            model_name,
            params,
            output,
            comparable_flags: proto.get_comparable_flags(),
        }
    }

    pub fn set_prototype_pieces(
        &mut self,
        sig: &PrototypePieces,
        voidtype: TypeId,
        glb: &mut Architecture,
    ) -> Result<()> {
        self.flags |= Datatype::VARIABLE_LENGTH;
        let mut proto = FuncProto::new();
        proto.set_internal_model_option(sig.model, voidtype, glb);
        proto.update_all_types(sig, glb)?;
        proto.set_input_lock(true, glb);
        proto.set_output_lock(true, glb);
        let signature = Datatype::compute_code_signature(&mut proto, glb);
        let data = self.code_data_mut();
        data.factory = true;
        data.proto = Some(Box::new(proto));
        data.signature = Some(signature);
        Ok(())
    }

    pub fn set_prototype_copy(&mut self, fp: super::TypeCodeData) {
        let data = self.code_data_mut();
        if data.proto.is_some() {
            data.proto = None;
            data.signature = None;
            data.factory = false;
        }
        if fp.proto.is_some() {
            data.factory = true;
            data.proto = fp.proto;
            data.signature = fp.signature;
        }
    }

    pub fn decode_stub(&mut self, decoder: &mut dyn Decoder) -> Result<()> {
        if decoder.peek_element()? != 0 {
            self.flags |= Datatype::VARIABLE_LENGTH;
        }
        self.decode_basic(decoder)
    }

    pub fn decode_prototype(
        &mut self,
        decoder: &mut dyn Decoder,
        is_constructor: bool,
        is_destructor: bool,
        glb: &mut Architecture,
    ) -> Result<()> {
        if decoder.peek_element()? != 0 {
            let mut proto = FuncProto::new();
            let voidtype = types_of_mut(glb).get_type_void()?;
            let defaultfp = glb.defaultfp;
            proto.set_internal_model_option(defaultfp, voidtype, glb);
            proto.decode(decoder, glb)?;
            proto.set_constructor(is_constructor);
            proto.set_destructor(is_destructor);
            let signature = Datatype::compute_code_signature(&mut proto, glb);
            let data = self.code_data_mut();
            data.factory = true;
            data.proto = Some(Box::new(proto));
            data.signature = Some(signature);
        }
        self.mark_complete();
        Ok(())
    }

    pub fn get_map(&self, glb: &Architecture) -> Result<ScopeId> {
        let TypeKind::Spacebase(data) = &self.kind else {
            panic!("data-type is not a spacebase");
        };
        let scope = glb.symboltab.as_deref().and_then(|db| db.resolve_scope(data.scope_id));
        scope.ok_or_else(|| Error::Lowlevel("Trying to get scope from unattached Typespacebase".to_string()))
    }

    pub fn get_address(&self, off: u64, sz: i32, point: &Address, glb: &Architecture) -> Address {
        let TypeKind::Spacebase(data) = &self.kind else {
            panic!("data-type is not a spacebase");
        };
        let mut full_encoding = 0u64;
        let sz = if data.scope_id == 0 { -1 } else { sz };
        let spaceid = data.spaceid.as_ref().expect("spacebase without address space");
        glb.manager
            .resolve_constant(spaceid, off, sz, point, &mut full_encoding)
    }

    pub fn decode_spacebase(&mut self, decoder: &mut dyn Decoder, glb: &mut Architecture) -> Result<()> {
        self.decode_basic(decoder)?;
        let spaceid = decoder.read_space_attr(ATTRIB_SPACE)?;
        let localframe = Address::decode(decoder)?;
        let db = glb.symboltab.as_deref().expect("symbol table is not initialized");
        let mut res = db.get_global_scope().expect("global scope is not initialized");
        if !localframe.is_invalid()
            && let Some(symbol) = db.scope_query_function(res, &localframe)
            && let Some(local) = Datatype::function_local_scope(glb, res, symbol, &localframe)
        {
            res = local;
        }
        let scope_id = db.scope(res).get_id();
        if let TypeKind::Spacebase(data) = &mut self.kind {
            data.spaceid = Some(spaceid);
            data.scope_id = scope_id;
        }
        Ok(())
    }

    fn function_local_scope(
        glb: &Architecture,
        global: ScopeId,
        symbol: crate::database::SymbolId,
        localframe: &Address,
    ) -> Option<ScopeId> {
        let db = glb.symboltab.as_deref()?;
        if let crate::database::SymbolKind::Function { fd: Some(fd), .. } = &db.symbol(symbol).kind {
            return fd.get_scope_local();
        }
        db.scope(global)
            .children
            .values()
            .copied()
            .find(|child| db.scope(*child).get_function() == Some(localframe))
    }
}
