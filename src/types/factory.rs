use std::collections::{BTreeMap, BTreeSet};
use std::fmt::Write as _;

use super::{
    ATTRIB_ALIGNMENT, ATTRIB_CHAR, ATTRIB_SIGNED, ATTRIB_UTF, Datatype, ELEM_CHAR_SIZE, ELEM_CORETYPES,
    ELEM_DATA_ORGANIZATION, ELEM_DEF, ELEM_ENTRY, ELEM_ENUM, ELEM_INTEGER_SIZE, ELEM_LONG_SIZE, ELEM_POINTER_SIZE,
    ELEM_SIZE_ALIGNMENT_MAP, ELEM_TYPEGRP, ELEM_TYPEREF, ELEM_WCHAR_SIZE, TypeBitField, TypeCodeData, TypeFactory,
    TypeField, TypeId, TypeKind, TypeMetatype, datatype_compare, string2metatype, types_of_mut,
};
use crate::architecture::Architecture;
use crate::arena::Arena;
use crate::error::{Error, Result};
use crate::fspec::PrototypePieces;
use crate::marshal::{
    ATTRIB_FORMAT, ATTRIB_ID, ATTRIB_METATYPE, ATTRIB_NAME, ATTRIB_SIZE, ATTRIB_VALUE, Decoder, ELEM_VOID, Encoder,
};
use crate::space::SpaceRef;

impl Default for TypeFactory {
    fn default() -> TypeFactory {
        TypeFactory::new()
    }
}

impl TypeFactory {
    pub fn new() -> TypeFactory {
        let mut res = TypeFactory {
            size_of_int: 0,
            size_of_long: 0,
            size_of_char: 0,
            size_of_wchar: 0,
            size_of_pointer: 0,
            size_of_alt_pointer: 0,
            enumsize: 0,
            enumtype: TypeMetatype::EnumUint,
            align_map: Vec::new(),
            arena: Arena::new(),
            tree: Vec::new(),
            nametree: BTreeMap::new(),
            typecache: [[None; 8]; 9],
            typecache10: None,
            typecache16: None,
            type_nochar: None,
            charcache: [None; 5],
            warnings: BTreeMap::new(),
            incomplete_typedef: Vec::new(),
            default_data_space: None,
            max_basetype_size: 0,
        };
        res.clear_cache();
        res
    }

    pub fn get(&self, id: TypeId) -> &Datatype {
        self.arena.get(id)
    }

    pub fn get_mut(&mut self, id: TypeId) -> &mut Datatype {
        self.arena.get_mut(id)
    }

    pub fn set_arch_properties(&mut self, default_data_space: Option<SpaceRef>, max_basetype_size: i32) {
        self.default_data_space = default_data_space;
        self.max_basetype_size = max_basetype_size;
    }

    pub fn single_field_fills(fd: &[TypeField], size: i32, types: &TypeFactory) -> bool {
        fd.len() == 1 && types.get(fd[0].tp).get_size() == size
    }

    pub(crate) fn default_data_space_big_endian(&self) -> bool {
        self.default_data_space
            .as_ref()
            .expect("default data space is not set")
            .is_big_endian()
    }

    fn tree_find(&self, ct: &Datatype) -> std::result::Result<usize, usize> {
        self.tree
            .binary_search_by(|probe| datatype_compare(self.arena.get(*probe), ct, self))
    }

    fn tree_erase(&mut self, ct: TypeId) {
        if let Ok(pos) = self.tree_find(self.arena.get(ct))
            && self.tree[pos] == ct
        {
            self.tree.remove(pos);
        }
    }

    fn tree_insert(&mut self, ct: TypeId) -> bool {
        match self.tree_find(self.arena.get(ct)) {
            Ok(_) => false,
            Err(pos) => {
                self.tree.insert(pos, ct);
                true
            }
        }
    }

    fn nametree_key(dt: &Datatype) -> (String, u64) {
        (dt.name.clone(), dt.id)
    }

    fn nametree_insert(&mut self, ct: TypeId) {
        let key = TypeFactory::nametree_key(self.arena.get(ct));
        self.nametree.entry(key).or_insert(ct);
    }

    fn nametree_erase(&mut self, ct: TypeId) {
        let key = TypeFactory::nametree_key(self.arena.get(ct));
        self.nametree.remove(&key);
    }

    pub fn tree_ids(&self) -> &[TypeId] {
        &self.tree
    }

    fn find_no_name(&self, ct: &Datatype) -> Option<TypeId> {
        match self.tree_find(ct) {
            Ok(pos) => Some(self.tree[pos]),
            Err(_) => None,
        }
    }

    fn insert(&mut self, newtype: Datatype) -> Result<TypeId> {
        match self.tree_find(&newtype) {
            Ok(pos) => {
                let existing = self.tree[pos];
                let mut text = String::new();
                let _ = writeln!(text, "Shared type id: {:x}", newtype.get_id());
                text.push_str("  ");
                newtype.print_raw(&mut text, self);
                text.push_str(" : ");
                self.get(existing).print_raw(&mut text, self);
                Err(Error::Lowlevel(text))
            }
            Err(pos) => {
                let has_id = newtype.id != 0;
                let id = self.arena.alloc(newtype);
                self.tree.insert(pos, id);
                if has_id {
                    self.nametree_insert(id);
                }
                Ok(id)
            }
        }
    }

    pub fn find_add(&mut self, ct: &Datatype) -> Result<TypeId> {
        if !ct.name.is_empty() {
            if ct.id == 0 {
                return Err(Error::Lowlevel(format!("Datatype must have a valid id: {}", ct.name)));
            }
            if let Some(res) = self.find_by_id_local(&ct.name, ct.id) {
                if self.get(res).compare_dependency(ct, self) != 0 {
                    return Err(Error::Lowlevel(format!(
                        "Trying to alter definition of type: {}",
                        ct.name
                    )));
                }
                return Ok(res);
            }
        } else if let Some(res) = self.find_no_name(ct) {
            return Ok(res);
        }
        let mut newtype = ct.clone_type(self)?;
        if newtype.alignment < 0 {
            newtype.align_size = self.get_primitive_align_size(newtype.size as u32)?;
            newtype.alignment = self.get_alignment(newtype.align_size as u32)?;
        }
        self.insert(newtype)
    }

    fn order_recurse(&self, deporder: &mut Vec<TypeId>, mark: &mut BTreeSet<TypeId>, ct: TypeId) {
        if !mark.insert(ct) {
            return;
        }
        let dt = self.get(ct);
        if let Some(typedef_imm) = dt.typedef_imm {
            self.order_recurse(deporder, mark, typedef_imm);
        }
        let size = dt.num_depend(self);
        for index in 0..size {
            if let Some(depend) = dt.get_depend(index, self) {
                self.order_recurse(deporder, mark, depend);
            }
        }
        deporder.push(ct);
    }

    fn decode_alignment_map(&mut self, decoder: &mut dyn Decoder) -> Result<()> {
        self.align_map.clear();
        loop {
            let map_id = decoder.open_element()?;
            if map_id != ELEM_ENTRY {
                break;
            }
            let sz = decoder.read_signed_integer_attr(ATTRIB_SIZE)? as i32;
            let val = decoder.read_signed_integer_attr(ATTRIB_ALIGNMENT)? as i32;
            while self.align_map.len() as i64 <= sz as i64 {
                self.align_map.push(-1);
            }
            self.align_map[sz as usize] = val;
            decoder.close_element(map_id)?;
        }
        if self.align_map.is_empty() {
            return Err(Error::Lowlevel("Alignment map empty".to_string()));
        }
        self.align_map[0] = 1;
        let mut cur_align = 1;
        for sz in 1..self.align_map.len() {
            let tmp_align = self.align_map[sz];
            if tmp_align == -1 {
                self.align_map[sz] = cur_align;
            } else {
                cur_align = tmp_align;
            }
        }
        Ok(())
    }

    fn set_default_alignment_map(&mut self) {
        self.align_map.resize(9, 1);
        self.align_map[1] = 1;
        self.align_map[2] = 2;
        self.align_map[3] = 2;
        self.align_map[4] = 4;
        self.align_map[5] = 4;
        self.align_map[6] = 4;
        self.align_map[7] = 4;
        self.align_map[8] = 8;
    }

    fn decode_typedef(glb: &mut Architecture, decoder: &mut dyn Decoder) -> Result<TypeId> {
        let mut id: u64 = 0;
        let mut nm = String::new();
        let mut format: u32 = 0;
        loop {
            let attrib_id = decoder.get_next_attribute_id()?;
            if attrib_id == 0 {
                break;
            }
            if attrib_id == ATTRIB_ID {
                id = decoder.read_unsigned_integer()?;
            } else if attrib_id == ATTRIB_NAME {
                nm = decoder.read_string()?;
            } else if attrib_id == ATTRIB_FORMAT {
                format = Datatype::encode_integer_format(&decoder.read_string()?)?;
            }
        }
        if id == 0 {
            id = Datatype::hash_name(&nm);
        }
        let defed_type = TypeFactory::decode_type(glb, decoder)?;
        let types = types_of_mut(glb);
        let defed = types.get(defed_type);
        if defed.is_variable_length() {
            id = Datatype::hash_size(id, defed.size);
        }
        let defed_meta = defed.get_metatype();
        if (defed_meta == TypeMetatype::Struct || defed_meta == TypeMetatype::Union)
            && let Some(prev) = types.find_by_id_local(&nm, id)
        {
            let prev_dt = types.get(prev);
            if Some(defed_type) != prev_dt.get_typedef() {
                return Err(Error::Lowlevel(format!(
                    "Trying to create typedef of existing type: {}",
                    prev_dt.name
                )));
            }
            let defed = types.get(defed_type);
            if prev_dt.get_metatype() == TypeMetatype::Struct {
                if prev_dt.get_fields().len() != defed.get_fields().len() {
                    let fields = defed.get_fields().to_vec();
                    let bitfields = defed.struct_data().bitfield.clone();
                    let (size, alignment, flags) = (defed.size, defed.alignment, defed.flags);
                    types.set_fields_struct(&fields, &bitfields, prev, size, alignment, flags)?;
                }
            } else if prev_dt.get_fields().len() != defed.get_fields().len() {
                let fields = defed.get_fields().to_vec();
                let (size, alignment, flags) = (defed.size, defed.alignment, defed.flags);
                types.set_fields_union(&fields, prev, size, alignment, flags)?;
            }
            return Ok(prev);
        }
        types.get_typedef(defed_type, &nm, id, format)
    }

    fn decode_enum(glb: &mut Architecture, decoder: &mut dyn Decoder, forcecore: bool) -> Result<TypeId> {
        let mut te = Datatype::new_enum(1, TypeMetatype::EnumInt)?;
        let warning = te.decode_enum(decoder)?;
        if forcecore {
            te.flags |= Datatype::CORETYPE;
        }
        let types = types_of_mut(glb);
        let res = types.find_add(&te)?;
        if !warning.is_empty() {
            types.insert_warning(res, warning)?;
        }
        Ok(res)
    }

    fn decode_struct(glb: &mut Architecture, decoder: &mut dyn Decoder, forcecore: bool) -> Result<TypeId> {
        let mut ts = Datatype::new_struct()?;
        ts.decode_basic(decoder)?;
        if forcecore {
            ts.flags |= Datatype::CORETYPE;
        }
        let types = types_of_mut(glb);
        let ct = match types.find_by_id_local(&ts.name, ts.id) {
            None => types.find_add(&ts)?,
            Some(ct) => {
                if types.get(ct).get_metatype() != TypeMetatype::Struct {
                    return Err(Error::Lowlevel(format!("Trying to redefine type: {}", ts.name)));
                }
                ct
            }
        };
        let warning = ts.decode_fields_struct(decoder, glb)?;
        let types = types_of_mut(glb);
        if !types.get(ct).is_incomplete() {
            if types.get(ct).compare_dependency(&ts, types) != 0 {
                return Err(Error::Lowlevel(format!("Redefinition of structure: {}", ts.name)));
            }
        } else {
            let fields = ts.get_fields().to_vec();
            let bitfields = ts.struct_data().bitfield.clone();
            types.set_fields_struct(&fields, &bitfields, ct, ts.size, ts.alignment, ts.flags)?;
        }
        if !warning.is_empty() {
            types.insert_warning(ct, warning)?;
        }
        types.resolve_incomplete_typedefs()?;
        Ok(ct)
    }

    fn decode_union(glb: &mut Architecture, decoder: &mut dyn Decoder, forcecore: bool) -> Result<TypeId> {
        let mut tu = Datatype::new_union()?;
        tu.decode_basic(decoder)?;
        if forcecore {
            tu.flags |= Datatype::CORETYPE;
        }
        let types = types_of_mut(glb);
        let ct = match types.find_by_id_local(&tu.name, tu.id) {
            None => types.find_add(&tu)?,
            Some(ct) => {
                if types.get(ct).get_metatype() != TypeMetatype::Union {
                    return Err(Error::Lowlevel(format!("Trying to redefine type: {}", tu.name)));
                }
                ct
            }
        };
        tu.decode_fields_union(decoder, glb)?;
        let types = types_of_mut(glb);
        if !types.get(ct).is_incomplete() {
            if types.get(ct).compare_dependency(&tu, types) != 0 {
                return Err(Error::Lowlevel(format!("Redefinition of union: {}", tu.name)));
            }
        } else {
            let fields = tu.get_fields().to_vec();
            types.set_fields_union(&fields, ct, tu.size, tu.alignment, tu.flags)?;
        }
        types.resolve_incomplete_typedefs()?;
        Ok(ct)
    }

    fn decode_code(
        glb: &mut Architecture,
        decoder: &mut dyn Decoder,
        is_constructor: bool,
        is_destructor: bool,
        forcecore: bool,
    ) -> Result<TypeId> {
        let mut tc = Datatype::new_code()?;
        tc.decode_stub(decoder)?;
        if tc.get_metatype() != TypeMetatype::Code {
            return Err(Error::Lowlevel("Expecting metatype=\"code\"".to_string()));
        }
        if forcecore {
            tc.flags |= Datatype::CORETYPE;
        }
        let types = types_of_mut(glb);
        let ct = match types.find_by_id_local(&tc.name, tc.id) {
            None => types.find_add(&tc)?,
            Some(ct) => {
                if types.get(ct).get_metatype() != TypeMetatype::Code {
                    return Err(Error::Lowlevel(format!("Trying to redefine type: {}", tc.name)));
                }
                ct
            }
        };
        tc.decode_prototype(decoder, is_constructor, is_destructor, glb)?;
        let types = types_of_mut(glb);
        if !types.get(ct).is_incomplete() {
            if types.get(ct).compare_dependency(&tc, types) != 0 {
                return Err(Error::Lowlevel(format!("Redefinition of code data-type: {}", tc.name)));
            }
        } else {
            let flags = tc.flags;
            let data = match &mut tc.kind {
                TypeKind::Code(data) => TypeCodeData {
                    proto: data.proto.take(),
                    signature: data.signature.take(),
                    factory: data.factory,
                },
                _ => unreachable!("code data-type"),
            };
            types.set_prototype(data, ct, flags)?;
        }
        types.resolve_incomplete_typedefs()?;
        Ok(ct)
    }

    fn decode_type_no_ref(glb: &mut Architecture, decoder: &mut dyn Decoder, forcecore: bool) -> Result<TypeId> {
        let elem_id = decoder.open_element()?;
        if elem_id == ELEM_VOID {
            let ct = types_of_mut(glb).get_type_void()?;
            decoder.close_element(elem_id)?;
            return Ok(ct);
        }
        if elem_id == ELEM_DEF {
            let ct = TypeFactory::decode_typedef(glb, decoder)?;
            decoder.close_element(elem_id)?;
            return Ok(ct);
        }
        let meta = string2metatype(&decoder.read_string_attr(ATTRIB_METATYPE)?)?;
        let ct = match meta {
            TypeMetatype::Ptr => {
                let mut tp = Datatype::new_pointer_empty()?;
                tp.decode_pointer(decoder, glb)?;
                if forcecore {
                    tp.flags |= Datatype::CORETYPE;
                }
                types_of_mut(glb).find_add(&tp)?
            }
            TypeMetatype::PtrRel => {
                let mut tp = Datatype::new_pointer_rel_empty()?;
                tp.decode_pointer_rel(decoder, glb)?;
                if forcecore {
                    tp.flags |= Datatype::CORETYPE;
                }
                types_of_mut(glb).find_add(&tp)?
            }
            TypeMetatype::Array => {
                let mut ta = Datatype::new_array_empty()?;
                ta.decode_array(decoder, glb)?;
                if forcecore {
                    ta.flags |= Datatype::CORETYPE;
                }
                types_of_mut(glb).find_add(&ta)?
            }
            TypeMetatype::EnumInt | TypeMetatype::EnumUint => TypeFactory::decode_enum(glb, decoder, forcecore)?,
            TypeMetatype::Struct => TypeFactory::decode_struct(glb, decoder, forcecore)?,
            TypeMetatype::Union => TypeFactory::decode_union(glb, decoder, forcecore)?,
            TypeMetatype::Spacebase => {
                let mut tsb = Datatype::new_spacebase_empty()?;
                tsb.decode_spacebase(decoder, glb)?;
                if forcecore {
                    tsb.flags |= Datatype::CORETYPE;
                }
                types_of_mut(glb).find_add(&tsb)?
            }
            TypeMetatype::Code => TypeFactory::decode_code(glb, decoder, false, false, forcecore)?,
            TypeMetatype::Void => {
                let mut void_type = Datatype::new_void()?;
                void_type.decode_void(decoder)?;
                types_of_mut(glb).find_add(&void_type)?
            }
            _ => {
                loop {
                    let attrib_id = decoder.get_next_attribute_id()?;
                    if attrib_id == 0 {
                        break;
                    }
                    if attrib_id == ATTRIB_CHAR && decoder.read_bool()? {
                        let mut tc = Datatype::new_char(&decoder.read_string_attr(ATTRIB_NAME)?)?;
                        decoder.rewind_attributes();
                        tc.decode_char(decoder)?;
                        if forcecore {
                            tc.flags |= Datatype::CORETYPE;
                        }
                        let ct = types_of_mut(glb).find_add(&tc)?;
                        decoder.close_element(elem_id)?;
                        return Ok(ct);
                    } else if attrib_id == ATTRIB_UTF && decoder.read_bool()? {
                        let mut tu = Datatype::new_unicode_empty()?;
                        decoder.rewind_attributes();
                        tu.decode_unicode(decoder)?;
                        if forcecore {
                            tu.flags |= Datatype::CORETYPE;
                        }
                        let ct = types_of_mut(glb).find_add(&tu)?;
                        decoder.close_element(elem_id)?;
                        return Ok(ct);
                    }
                }
                decoder.rewind_attributes();
                let mut tb = Datatype::new_base(0, TypeMetatype::Unknown)?;
                tb.decode_basic(decoder)?;
                if forcecore {
                    tb.flags |= Datatype::CORETYPE;
                }
                types_of_mut(glb).find_add(&tb)?
            }
        };
        decoder.close_element(elem_id)?;
        Ok(ct)
    }

    fn clear_cache(&mut self) {
        for row in self.typecache.iter_mut() {
            for slot in row.iter_mut() {
                *slot = None;
            }
        }
        self.typecache10 = None;
        self.typecache16 = None;
        self.type_nochar = None;
        for slot in self.charcache.iter_mut() {
            *slot = None;
        }
    }

    fn get_type_char_named(&mut self, name: &str) -> Result<TypeId> {
        let mut tc = Datatype::new_char(name)?;
        tc.id = Datatype::hash_name(name);
        self.find_add(&tc)
    }

    fn get_type_unicode(&mut self, nm: &str, sz: i32, metatype: TypeMetatype) -> Result<TypeId> {
        let mut tu = Datatype::new_unicode(nm, sz, metatype)?;
        tu.id = Datatype::hash_name(nm);
        self.find_add(&tu)
    }

    fn get_type_code_named(&mut self, name: &str) -> Result<TypeId> {
        if name.is_empty() {
            return self.get_type_code();
        }
        let mut tmp = Datatype::new_code()?;
        tmp.name = name.to_string();
        tmp.display_name = name.to_string();
        tmp.id = Datatype::hash_name(name);
        tmp.mark_complete();
        self.find_add(&tmp)
    }

    fn recalc_pointer_submeta(&mut self, base: TypeId, sub: super::SubMetatype) -> Result<()> {
        let mut top = Datatype::new_pointer(1, base, 0, self)?;
        let cur_sub = top.submeta;
        if cur_sub == sub {
            return Ok(());
        }
        top.submeta = sub;
        let mut pos = self
            .tree
            .partition_point(|probe| datatype_compare(self.arena.get(*probe), &top, self) == std::cmp::Ordering::Less);
        while pos < self.tree.len() {
            let dt_id = self.tree[pos];
            let dt = self.get(dt_id);
            if dt.get_metatype() != TypeMetatype::Ptr {
                break;
            }
            if dt.pointer_data_option().and_then(|data| data.ptrto) != Some(base) {
                break;
            }
            pos += 1;
            if dt.submeta == sub {
                let next = self.tree.get(pos).copied();
                self.tree_erase(dt_id);
                self.get_mut(dt_id).submeta = cur_sub;
                self.tree_insert(dt_id);
                pos = match next {
                    Some(next_id) => match self.tree_find(self.arena.get(next_id)) {
                        Ok(found) => found,
                        Err(_) => self.tree.len(),
                    },
                    None => self.tree.len(),
                };
            }
        }
        Ok(())
    }

    fn insert_warning(&mut self, dt: TypeId, warn: String) -> Result<()> {
        if self.get(dt).get_id() == 0 {
            return Err(Error::Lowlevel(
                "Can only issue warnings for named data-types".to_string(),
            ));
        }
        self.get_mut(dt).flags |= Datatype::WARNING_ISSUED;
        self.warnings.insert(dt, warn);
        Ok(())
    }

    fn remove_warning(&mut self, dt: TypeId) {
        self.warnings.remove(&dt);
    }

    fn resolve_incomplete_typedefs(&mut self) -> Result<()> {
        let mut index = 0;
        while index < self.incomplete_typedef.len() {
            let dt = self.incomplete_typedef[index];
            let defed_type = self
                .get(dt)
                .get_typedef()
                .expect("typedef without underlying data-type");
            let defed = self.get(defed_type);
            if defed.is_incomplete() {
                index += 1;
                continue;
            }
            match self.get(dt).get_metatype() {
                TypeMetatype::Struct => {
                    let fields = defed.get_fields().to_vec();
                    let bitfields = defed.struct_data().bitfield.clone();
                    let (size, alignment, flags) = (defed.size, defed.alignment, defed.flags);
                    self.set_fields_struct(&fields, &bitfields, dt, size, alignment, flags)?;
                    self.incomplete_typedef.remove(index);
                }
                TypeMetatype::Union => {
                    let fields = defed.get_fields().to_vec();
                    let (size, alignment, flags) = (defed.size, defed.alignment, defed.flags);
                    self.set_fields_union(&fields, dt, size, alignment, flags)?;
                    self.incomplete_typedef.remove(index);
                }
                TypeMetatype::Code => {
                    let flags = defed.flags;
                    let data = match &defed.kind {
                        TypeKind::Code(data) => data.copy_data()?,
                        _ => TypeCodeData {
                            proto: None,
                            signature: None,
                            factory: false,
                        },
                    };
                    self.set_prototype(data, dt, flags)?;
                    self.incomplete_typedef.remove(index);
                }
                _ => index += 1,
            }
        }
        Ok(())
    }

    fn set_fields_struct(
        &mut self,
        fd: &[TypeField],
        bit: &[TypeBitField],
        ot: TypeId,
        new_size: i32,
        new_align: i32,
        flags: u32,
    ) -> Result<()> {
        if !self.get(ot).is_incomplete() {
            return Err(Error::Lowlevel(
                "Can only set fields on an incomplete structure".to_string(),
            ));
        }
        let single_fill = TypeFactory::single_field_fills(fd, new_size, self);
        self.tree_erase(ot);
        let dt = self.get_mut(ot);
        dt.set_fields_struct(fd, bit, new_size, new_align, single_fill);
        dt.flags &= !Datatype::TYPE_INCOMPLETE;
        dt.flags |= flags
            & (Datatype::OPAQUE_STRING
                | Datatype::VARIABLE_LENGTH
                | Datatype::TYPE_INCOMPLETE
                | Datatype::HAS_BITFIELDS);
        self.tree_insert(ot);
        self.recalc_pointer_submeta(ot, super::SubMetatype::Ptr)?;
        self.recalc_pointer_submeta(ot, super::SubMetatype::PtrStruct)?;
        Ok(())
    }

    fn set_fields_union(
        &mut self,
        fd: &[TypeField],
        ot: TypeId,
        new_size: i32,
        new_align: i32,
        flags: u32,
    ) -> Result<()> {
        if !self.get(ot).is_incomplete() {
            return Err(Error::Lowlevel(
                "Can only set fields on an incomplete union".to_string(),
            ));
        }
        self.tree_erase(ot);
        let dt = self.get_mut(ot);
        dt.set_fields_union(fd, new_size, new_align);
        dt.flags &= !Datatype::TYPE_INCOMPLETE;
        dt.flags |= flags & (Datatype::VARIABLE_LENGTH | Datatype::TYPE_INCOMPLETE);
        self.tree_insert(ot);
        Ok(())
    }

    pub fn find_by_id_local(&self, nm: &str, id: u64) -> Option<TypeId> {
        if id != 0 {
            return self.nametree.get(&(nm.to_string(), id)).copied();
        }
        let (key, res) = self.nametree.range((nm.to_string(), 0u64)..).next()?;
        if key.0 != nm {
            return None;
        }
        Some(*res)
    }

    pub fn find_by_id(&mut self, name: &str, id: u64, sz: i32) -> Option<TypeId> {
        let mut id = id;
        if sz > 0 {
            id = Datatype::hash_size(id, sz);
        }
        self.find_by_id_local(name, id)
    }

    pub fn setup_sizes(glb: &mut Architecture) -> Result<()> {
        let stack_int_size = match glb.manager.get_stack_space() {
            Some(spc) => Some(spc.get_spacebase(0)?.size as i32),
            None => None,
        };
        let default_data_space = glb.manager.get_default_data_space();
        let data_addr_size = default_data_space.as_ref().map(|spc| spc.get_addr_size() as i32);
        let segment = match &default_data_space {
            Some(spc) => glb.get_segment_op(spc),
            None => None,
        };
        let far_pointer = segment
            .as_ref()
            .and_then(|op| op.as_segment())
            .filter(|seg| seg.has_far_pointer_support())
            .map(|seg| (seg.get_inner_size(), seg.get_base_size()));
        let default_size = glb.manager.get_default_size();
        let types = types_of_mut(glb);
        if types.size_of_int == 0 {
            types.size_of_int = 1;
            if let Some(size) = stack_int_size {
                types.size_of_int = size;
                if types.size_of_int > 4 {
                    types.size_of_int = 4;
                }
            }
        }
        if types.size_of_long == 0 {
            types.size_of_long = if types.size_of_int == 4 { 8 } else { types.size_of_int };
        }
        if types.size_of_char == 0 {
            types.size_of_char = 1;
        }
        if types.size_of_wchar == 0 {
            types.size_of_wchar = 2;
        }
        if types.size_of_pointer == 0 {
            types.size_of_pointer = data_addr_size.expect("default data space is not set");
        }
        if let Some((inner_size, base_size)) = far_pointer {
            types.size_of_pointer = inner_size;
            types.size_of_alt_pointer = types.size_of_pointer + base_size;
        }
        if types.align_map.is_empty() {
            types.set_default_alignment_map();
        }
        if types.enumsize == 0 {
            types.enumsize = default_size;
            types.enumtype = TypeMetatype::EnumUint;
        }
        Ok(())
    }

    pub fn clear(&mut self) {
        self.arena.clear();
        self.tree.clear();
        self.nametree.clear();
        self.clear_cache();
        self.warnings.clear();
        self.incomplete_typedef.clear();
    }

    pub fn clear_noncore(&mut self) {
        let mut pos = 0;
        while pos < self.tree.len() {
            let ct = self.tree[pos];
            if self.get(ct).is_core_type() {
                pos += 1;
                continue;
            }
            self.nametree_erase(ct);
            self.tree.remove(pos);
            self.arena.remove(ct);
        }
        self.warnings.clear();
        self.incomplete_typedef.clear();
    }

    pub fn get_alignment(&self, size: u32) -> Result<i32> {
        if size as usize >= self.align_map.len() {
            if self.align_map.is_empty() {
                return Err(Error::Lowlevel("TypeFactory alignment map not initialized".to_string()));
            }
            return Ok(self.align_map[self.align_map.len() - 1]);
        }
        Ok(self.align_map[size as usize])
    }

    pub fn get_primitive_align_size(&self, size: u32) -> Result<i32> {
        let align = self.get_alignment(size)?;
        let mut size = size;
        let modulus = size % align as u32;
        if modulus != 0 {
            size = size.wrapping_add((align as u32).wrapping_sub(modulus));
        }
        Ok(size as i32)
    }

    pub fn get_size_of_int(&self) -> i32 {
        self.size_of_int
    }

    pub fn get_size_of_long(&self) -> i32 {
        self.size_of_long
    }

    pub fn get_size_of_char(&self) -> i32 {
        self.size_of_char
    }

    pub fn get_size_of_wchar(&self) -> i32 {
        self.size_of_wchar
    }

    pub fn get_size_of_pointer(&self) -> i32 {
        self.size_of_pointer
    }

    pub fn get_size_of_alt_pointer(&self) -> i32 {
        self.size_of_alt_pointer
    }

    pub fn find_by_name(&mut self, name: &str) -> Option<TypeId> {
        self.find_by_id(name, 0, 0)
    }

    pub fn set_name(&mut self, ct: TypeId, name: &str) -> Result<TypeId> {
        if self.get(ct).id != 0 {
            self.nametree_erase(ct);
        }
        self.tree_erase(ct);
        let dt = self.get_mut(ct);
        dt.name = name.to_string();
        dt.display_name = name.to_string();
        if dt.id == 0 {
            dt.id = Datatype::hash_name(name);
        }
        self.tree_insert(ct);
        self.nametree_insert(ct);
        Ok(ct)
    }

    pub fn set_display_format(&mut self, ct: TypeId, format: u32) {
        self.get_mut(ct).set_display_format(format);
    }

    pub fn set_prototype(&mut self, fp: TypeCodeData, new_code: TypeId, flags: u32) -> Result<()> {
        if !self.get(new_code).is_incomplete() {
            return Err(Error::Lowlevel(
                "Can only set prototype on incomplete data-type".to_string(),
            ));
        }
        self.tree_erase(new_code);
        let dt = self.get_mut(new_code);
        dt.set_prototype_copy(fp);
        dt.flags &= !Datatype::TYPE_INCOMPLETE;
        dt.flags |= flags & (Datatype::VARIABLE_LENGTH | Datatype::TYPE_INCOMPLETE);
        self.tree_insert(new_code);
        Ok(())
    }

    pub fn set_enum_values(&mut self, nmap: &BTreeMap<u64, String>, te: TypeId) {
        self.tree_erase(te);
        self.get_mut(te).set_name_map(nmap);
        self.tree_insert(te);
    }

    pub fn decode_type(glb: &mut Architecture, decoder: &mut dyn Decoder) -> Result<TypeId> {
        let elem_id = decoder.peek_element()?;
        if ELEM_TYPEREF == elem_id {
            let elem_id = decoder.open_element()?;
            let mut newid: u64 = 0;
            let mut size: i32 = -1;
            loop {
                let attrib_id = decoder.get_next_attribute_id()?;
                if attrib_id == 0 {
                    break;
                }
                if attrib_id == ATTRIB_ID {
                    newid = decoder.read_unsigned_integer()?;
                } else if attrib_id == ATTRIB_SIZE {
                    size = decoder.read_signed_integer()? as i32;
                }
            }
            let newname = decoder.read_string_attr(ATTRIB_NAME)?;
            if newid == 0 {
                newid = Datatype::hash_name(&newname);
            }
            let ct = types_of_mut(glb).find_by_id(&newname, newid, size);
            let Some(ct) = ct else {
                return Err(Error::Lowlevel(format!("Unable to resolve type: {}", newname)));
            };
            decoder.close_element(elem_id)?;
            return Ok(ct);
        }
        TypeFactory::decode_type_no_ref(glb, decoder, false)
    }

    pub fn decode_type_with_code_flags(
        glb: &mut Architecture,
        decoder: &mut dyn Decoder,
        is_constructor: bool,
        is_destructor: bool,
    ) -> Result<TypeId> {
        let mut tp = Datatype::new_pointer_empty()?;
        let elem_id = decoder.open_element()?;
        tp.decode_basic(decoder)?;
        if tp.get_metatype() != TypeMetatype::Ptr {
            return Err(Error::Lowlevel("Special type decode does not see pointer".to_string()));
        }
        loop {
            let attrib_id = decoder.get_next_attribute_id()?;
            if attrib_id == 0 {
                break;
            }
            if attrib_id == crate::marshal::ATTRIB_WORDSIZE {
                tp.pointer_data_mut().wordsize = decoder.read_unsigned_integer()? as u32;
            }
        }
        let ptrto = TypeFactory::decode_code(glb, decoder, is_constructor, is_destructor, false)?;
        tp.pointer_data_mut().ptrto = Some(ptrto);
        decoder.close_element(elem_id)?;
        let types = types_of_mut(glb);
        tp.calc_truncate_local(types)?;
        types.find_add(&tp)
    }

    pub fn get_type_void(&mut self) -> Result<TypeId> {
        if let Some(ct) = self.typecache[0][TypeMetatype::Void.cache_index()] {
            return Ok(ct);
        }
        let mut tv = Datatype::new_void()?;
        tv.id = Datatype::hash_name(&tv.name);
        let newtype = tv.clone_type(self)?;
        let ct = self.arena.alloc(newtype);
        self.tree_insert(ct);
        self.nametree_insert(ct);
        self.typecache[0][TypeMetatype::Void.cache_index()] = Some(ct);
        Ok(ct)
    }

    pub fn get_base_no_char(&mut self, size: i32, metatype: TypeMetatype) -> Result<TypeId> {
        if size == 1
            && metatype == TypeMetatype::Int
            && let Some(nochar) = self.type_nochar
        {
            return Ok(nochar);
        }
        self.get_base(size, metatype)
    }

    pub fn get_base(&mut self, size: i32, metatype: TypeMetatype) -> Result<TypeId> {
        if (size as u32) < 9 {
            if metatype >= TypeMetatype::Float
                && let Some(ct) = self.typecache[size as usize][metatype.cache_index()]
            {
                return Ok(ct);
            }
        } else if metatype == TypeMetatype::Float {
            if size == 10 {
                return self
                    .typecache10
                    .ok_or_else(|| Error::Lowlevel("no cached 10-byte float data-type".to_string()));
            }
            if size == 16 {
                return self
                    .typecache16
                    .ok_or_else(|| Error::Lowlevel("no cached 16-byte float data-type".to_string()));
            }
        }
        if size > self.max_basetype_size {
            let unknown = self.typecache[1][TypeMetatype::Unknown.cache_index()]
                .ok_or_else(|| Error::Lowlevel("no cached undefined1 data-type".to_string()))?;
            return self.get_type_array(size, unknown);
        }
        let tmp = Datatype::new_base(size, metatype)?;
        self.find_add(&tmp)
    }

    pub(crate) fn find_base_existing(&self, size: i32, metatype: TypeMetatype) -> Option<TypeId> {
        if (size as u32) < 9 {
            if metatype >= TypeMetatype::Float
                && let Some(ct) = self.typecache[size as usize][metatype.cache_index()]
            {
                return Some(ct);
            }
        } else if metatype == TypeMetatype::Float {
            if size == 10 {
                return self.typecache10;
            }
            if size == 16 {
                return self.typecache16;
            }
        }
        if size > self.max_basetype_size {
            let unknown = self.typecache[1][TypeMetatype::Unknown.cache_index()]?;
            let tmp = Datatype::new_array(size, unknown, self).ok()?;
            return self.find_no_name(&tmp);
        }
        let tmp = Datatype::new_base(size, metatype).ok()?;
        self.find_no_name(&tmp)
    }

    pub fn get_base_named(&mut self, size: i32, metatype: TypeMetatype, name: &str) -> Result<TypeId> {
        let mut tmp = Datatype::new_base_named(size, metatype, name)?;
        tmp.id = Datatype::hash_name(name);
        self.find_add(&tmp)
    }

    pub fn get_type_char(&mut self, size: i32) -> Result<TypeId> {
        if (size as u32) < 5
            && let Some(res) = self.charcache[size as usize]
        {
            return Ok(res);
        }
        Err(Error::Lowlevel(
            "Request for unsupported character data-type".to_string(),
        ))
    }

    pub fn get_type_code(&mut self) -> Result<TypeId> {
        if let Some(ct) = self.typecache[1][TypeMetatype::Code.cache_index()] {
            return Ok(ct);
        }
        let mut tmp = Datatype::new_code()?;
        tmp.mark_complete();
        self.find_add(&tmp)
    }

    pub fn get_type_pointer_strip_array(&mut self, size: i32, pt: TypeId, ws: u32) -> Result<TypeId> {
        let mut pt = pt;
        if self.get(pt).has_stripped() {
            pt = self.get(pt).get_stripped().expect("stripped data-type");
        }
        if self.get(pt).get_metatype() == TypeMetatype::Array {
            pt = self.get(pt).get_base();
        }
        let tmp = Datatype::new_pointer(size, pt, ws, self)?;
        let res = self.find_add(&tmp)?;
        Datatype::calc_truncate(res, self)?;
        Ok(res)
    }

    pub fn get_type_pointer(&mut self, size: i32, pt: TypeId, ws: u32) -> Result<TypeId> {
        let mut pt = pt;
        if self.get(pt).has_stripped() {
            pt = self.get(pt).get_stripped().expect("stripped data-type");
        }
        let tmp = Datatype::new_pointer(size, pt, ws, self)?;
        let res = self.find_add(&tmp)?;
        Datatype::calc_truncate(res, self)?;
        Ok(res)
    }

    pub fn get_type_pointer_named(&mut self, size: i32, pt: TypeId, ws: u32, name: &str) -> Result<TypeId> {
        let mut pt = pt;
        if self.get(pt).has_stripped() {
            pt = self.get(pt).get_stripped().expect("stripped data-type");
        }
        let mut tmp = Datatype::new_pointer(size, pt, ws, self)?;
        tmp.name = name.to_string();
        tmp.display_name = name.to_string();
        tmp.id = Datatype::hash_name(name);
        let res = self.find_add(&tmp)?;
        Datatype::calc_truncate(res, self)?;
        Ok(res)
    }

    pub fn get_type_array(&mut self, as_size: i32, ao: TypeId) -> Result<TypeId> {
        let mut ao = ao;
        if self.get(ao).has_stripped() {
            ao = self.get(ao).get_stripped().expect("stripped data-type");
        }
        let tmp = Datatype::new_array(as_size, ao, self)?;
        self.find_add(&tmp)
    }

    pub fn get_type_struct(&mut self, name: &str) -> Result<TypeId> {
        let mut tmp = Datatype::new_struct()?;
        tmp.name = name.to_string();
        tmp.display_name = name.to_string();
        tmp.id = Datatype::hash_name(name);
        self.find_add(&tmp)
    }

    pub fn get_type_partial_struct(&mut self, contain: TypeId, off: i32, sz: i32) -> Result<TypeId> {
        let strip = self.get_base(sz, TypeMetatype::Unknown)?;
        let tps = Datatype::new_partial_struct(contain, off, sz, strip, self)?;
        self.find_add(&tps)
    }

    pub fn get_type_union(&mut self, name: &str) -> Result<TypeId> {
        let mut tmp = Datatype::new_union()?;
        tmp.name = name.to_string();
        tmp.display_name = name.to_string();
        tmp.id = Datatype::hash_name(name);
        self.find_add(&tmp)
    }

    pub fn get_type_partial_union(&mut self, contain: TypeId, off: i32, sz: i32) -> Result<TypeId> {
        let strip = self.get_base(sz, TypeMetatype::Unknown)?;
        let tpu = Datatype::new_partial_union(contain, off, sz, strip, self)?;
        self.find_add(&tpu)
    }

    pub fn get_type_enum(&mut self, name: &str) -> Result<TypeId> {
        let mut tmp = Datatype::new_enum_named(self.enumsize, self.enumtype, name)?;
        tmp.id = Datatype::hash_name(name);
        self.find_add(&tmp)
    }

    pub fn get_type_partial_enum(&mut self, contain: TypeId, off: i32, sz: i32) -> Result<TypeId> {
        let strip = self.get_base(sz, TypeMetatype::Unknown)?;
        let tpe = Datatype::new_partial_enum(contain, off, sz, strip, self)?;
        self.find_add(&tpe)
    }

    pub fn get_type_spacebase(&mut self, spc: &SpaceRef, scope: u64) -> Result<TypeId> {
        let tsb = Datatype::new_spacebase(spc, scope)?;
        self.find_add(&tsb)
    }

    pub fn get_type_code_proto(glb: &mut Architecture, proto: &PrototypePieces) -> Result<TypeId> {
        let mut tc = Datatype::new_code()?;
        let voidtype = types_of_mut(glb).get_type_void()?;
        tc.set_prototype_pieces(proto, voidtype, glb)?;
        tc.mark_complete();
        types_of_mut(glb).find_add(&tc)
    }

    pub fn get_typedef(&mut self, ct: TypeId, name: &str, id: u64, format: u32) -> Result<TypeId> {
        let mut id = id;
        if id == 0 {
            id = Datatype::hash_name(name);
        }
        if let Some(res) = self.find_by_id_local(name, id) {
            if Some(ct) != self.get(res).get_typedef() {
                return Err(Error::Lowlevel(format!(
                    "Trying to create typedef of existing type: {}",
                    name
                )));
            }
            return Ok(res);
        }
        let mut res = self.get(ct).clone_type(self)?;
        res.name = name.to_string();
        res.display_name = name.to_string();
        res.id = id;
        res.flags &= !Datatype::CORETYPE;
        res.typedef_imm = Some(ct);
        res.set_display_format(format);
        let incomplete = res.is_incomplete();
        let res = self.insert(res)?;
        if incomplete {
            self.incomplete_typedef.push(res);
        }
        Ok(res)
    }

    pub fn get_type_pointer_rel(&mut self, parent_ptr: TypeId, ptr_to: TypeId, off: i32) -> Result<TypeId> {
        let parent = self.get(parent_ptr);
        let size = parent.size;
        let wordsize = parent.get_word_size();
        let parent_to = parent.get_ptr_to();
        let mut tp = Datatype::new_pointer_rel(size, ptr_to, wordsize, parent_to, off, self)?;
        tp.mark_ephemeral(self)?;
        self.find_add(&tp)
    }

    pub fn get_type_pointer_rel_named(
        &mut self,
        sz: i32,
        parent: TypeId,
        ptr_to: TypeId,
        ws: i32,
        off: i32,
        nm: &str,
    ) -> Result<TypeId> {
        let mut tp = Datatype::new_pointer_rel(sz, ptr_to, ws as u32, parent, off, self)?;
        tp.name = nm.to_string();
        tp.display_name = nm.to_string();
        tp.id = Datatype::hash_name(nm);
        self.find_add(&tp)
    }

    pub fn get_type_pointer_with_space(&mut self, ptr_to: TypeId, spc: &SpaceRef, nm: &str) -> Result<TypeId> {
        let mut tp = Datatype::new_pointer_space(ptr_to, spc, self)?;
        tp.name = nm.to_string();
        tp.display_name = nm.to_string();
        tp.id = Datatype::hash_name(nm);
        let res = self.find_add(&tp)?;
        Datatype::calc_truncate(res, self)?;
        Ok(res)
    }

    pub fn resize_pointer(&mut self, ptr: TypeId, new_size: i32) -> Result<TypeId> {
        let dt = self.get(ptr);
        let ptrto = dt.get_ptr_to();
        let wordsize = dt.get_word_size();
        self.resize_pointer_parts(ptrto, wordsize, new_size)
    }

    pub(crate) fn resize_pointer_parts(&mut self, ptrto: TypeId, wordsize: u32, new_size: i32) -> Result<TypeId> {
        let mut pt = ptrto;
        if self.get(pt).has_stripped() {
            pt = self.get(pt).get_stripped().expect("stripped data-type");
        }
        let tmp = Datatype::new_pointer(new_size, pt, wordsize, self)?;
        self.find_add(&tmp)
    }

    pub fn resize_integer(&mut self, ct: TypeId, new_size: i32) -> Result<TypeId> {
        let dt = self.get(ct);
        if new_size == dt.get_size() {
            return Ok(ct);
        }
        let mut meta = dt.get_metatype();
        if meta != TypeMetatype::Int && meta != TypeMetatype::Uint {
            meta = TypeMetatype::Uint;
        }
        if dt.is_char_print() {
            return self.get_base(new_size, meta);
        }
        self.get_base_no_char(new_size, meta)
    }

    pub fn get_exact_piece(&mut self, ct: TypeId, offset: i32, size: i32) -> Result<Option<TypeId>> {
        let mut last_type: Option<TypeId> = None;
        let mut last_off: i64 = 0;
        let mut cur_off: i64 = offset as i64;
        let mut cur = ct;
        loop {
            let dt = self.get(cur);
            if (dt.get_size() as i64) < size as i64 + cur_off {
                break;
            }
            if dt.get_size() == size {
                return Ok(Some(cur));
            }
            last_type = Some(cur);
            last_off = cur_off;
            let mut newoff = cur_off;
            let next = dt.sub_type(cur_off, &mut newoff, self, None);
            cur_off = newoff;
            match next {
                Some(next) => cur = next,
                None => break,
            }
        }
        if let Some(last) = last_type {
            let last_dt = self.get(last);
            let meta = last_dt.get_metatype();
            if meta == TypeMetatype::Struct || meta == TypeMetatype::Array || meta == TypeMetatype::PartialStruct {
                return Ok(Some(self.get_type_partial_struct(last, last_off as i32, size)?));
            } else if meta == TypeMetatype::Union {
                return Ok(Some(self.get_type_partial_union(last, last_off as i32, size)?));
            } else if meta == TypeMetatype::PartialUnion {
                let parent = last_dt.get_parent_union();
                let partial_offset = last_dt.get_offset();
                return Ok(Some(self.get_type_partial_union(
                    parent,
                    (last_off + partial_offset as i64) as i32,
                    size,
                )?));
            } else if last_dt.is_enum_type() && !last_dt.has_stripped() {
                return Ok(Some(self.get_type_partial_enum(last, last_off as i32, size)?));
            }
        }
        Ok(None)
    }

    pub fn assign_raw_fields_struct(
        &mut self,
        ct: TypeId,
        fd: &mut [TypeField],
        bit: &mut [TypeBitField],
    ) -> Result<()> {
        let mut new_size = 0;
        let mut new_align = 0;
        let mut flags = 0;
        Datatype::assign_field_offsets_struct(
            fd,
            bit,
            &mut new_size,
            &mut new_align,
            &mut flags,
            Some(self.get(ct)),
            self,
        )?;
        self.set_fields_struct(fd, bit, ct, new_size, new_align, flags)
    }

    pub fn assign_raw_fields_union(&mut self, ct: TypeId, fd: &mut [TypeField]) -> Result<()> {
        let mut new_size = 0;
        let mut new_align = 0;
        let mut flags = 0;
        Datatype::assign_field_offsets_union(fd, &mut new_size, &mut new_align, &mut flags, Some(self.get(ct)), self)?;
        self.set_fields_union(fd, ct, new_size, new_align, flags)
    }

    pub fn destroy_type(&mut self, ct: TypeId) -> Result<()> {
        let dt = self.get(ct);
        if dt.is_core_type() {
            return Err(Error::Lowlevel("Cannot destroy core type".to_string()));
        }
        if dt.has_warning() {
            self.remove_warning(ct);
        }
        self.nametree_erase(ct);
        self.tree_erase(ct);
        self.arena.remove(ct);
        Ok(())
    }

    pub fn concretize(&mut self, ct: TypeId) -> Result<TypeId> {
        let dt = self.get(ct);
        if dt.get_metatype() == TypeMetatype::Code {
            if dt.get_size() != 1 {
                return Err(Error::Lowlevel(
                    "Primitive code data-type that is not size 1".to_string(),
                ));
            }
            return self.get_base(1, TypeMetatype::Unknown);
        }
        Ok(ct)
    }

    pub fn dependent_order(&self, deporder: &mut Vec<TypeId>) {
        let mut mark: BTreeSet<TypeId> = BTreeSet::new();
        for ct in self.tree.iter() {
            self.order_recurse(deporder, &mut mark, *ct);
        }
    }

    pub fn encode(&self, encoder: &mut dyn Encoder, glb: &Architecture) -> Result<()> {
        let mut deporder = Vec::new();
        self.dependent_order(&mut deporder);
        encoder.open_element(ELEM_TYPEGRP);
        for ct in deporder.iter() {
            let dt = self.get(*ct);
            if dt.get_name().is_empty() {
                continue;
            }
            if dt.is_core_type() {
                let meta = dt.get_metatype();
                if meta != TypeMetatype::Ptr
                    && meta != TypeMetatype::Array
                    && meta != TypeMetatype::Struct
                    && meta != TypeMetatype::Union
                {
                    continue;
                }
            }
            dt.encode(encoder, glb)?;
        }
        encoder.close_element(ELEM_TYPEGRP);
        Ok(())
    }

    pub fn encode_core_types(&self, encoder: &mut dyn Encoder, glb: &Architecture) -> Result<()> {
        encoder.open_element(ELEM_CORETYPES);
        for ct in self.tree.iter() {
            let dt = self.get(*ct);
            if !dt.is_core_type() {
                continue;
            }
            let meta = dt.get_metatype();
            if meta == TypeMetatype::Ptr
                || meta == TypeMetatype::Array
                || meta == TypeMetatype::Struct
                || meta == TypeMetatype::Union
            {
                continue;
            }
            dt.encode(encoder, glb)?;
        }
        encoder.close_element(ELEM_CORETYPES);
        Ok(())
    }

    pub fn decode(glb: &mut Architecture, decoder: &mut dyn Decoder) -> Result<()> {
        let elem_id = decoder.open_element_expect(ELEM_TYPEGRP)?;
        while decoder.peek_element()? != 0 {
            TypeFactory::decode_type_no_ref(glb, decoder, false)?;
        }
        decoder.close_element(elem_id)
    }

    pub fn decode_core_types(glb: &mut Architecture, decoder: &mut dyn Decoder) -> Result<()> {
        types_of_mut(glb).clear();
        let elem_id = decoder.open_element_expect(ELEM_CORETYPES)?;
        while decoder.peek_element()? != 0 {
            TypeFactory::decode_type_no_ref(glb, decoder, true)?;
        }
        decoder.close_element(elem_id)?;
        types_of_mut(glb).cache_core_types()
    }

    pub fn decode_data_organization(&mut self, decoder: &mut dyn Decoder) -> Result<()> {
        let elem_id = decoder.open_element_expect(ELEM_DATA_ORGANIZATION)?;
        loop {
            let sub_id = decoder.open_element()?;
            if sub_id == 0 {
                break;
            }
            if sub_id == ELEM_INTEGER_SIZE {
                self.size_of_int = decoder.read_signed_integer_attr(ATTRIB_VALUE)? as i32;
            } else if sub_id == ELEM_LONG_SIZE {
                self.size_of_long = decoder.read_signed_integer_attr(ATTRIB_VALUE)? as i32;
            } else if sub_id == ELEM_POINTER_SIZE {
                self.size_of_pointer = decoder.read_signed_integer_attr(ATTRIB_VALUE)? as i32;
            } else if sub_id == ELEM_CHAR_SIZE {
                self.size_of_char = decoder.read_signed_integer_attr(ATTRIB_VALUE)? as i32;
            } else if sub_id == ELEM_WCHAR_SIZE {
                self.size_of_wchar = decoder.read_signed_integer_attr(ATTRIB_VALUE)? as i32;
            } else if sub_id == ELEM_SIZE_ALIGNMENT_MAP {
                self.decode_alignment_map(decoder)?;
            } else {
                decoder.close_element_skipping(sub_id)?;
                continue;
            }
            decoder.close_element(sub_id)?;
        }
        decoder.close_element(elem_id)
    }

    pub fn parse_enum_config(&mut self, decoder: &mut dyn Decoder) -> Result<()> {
        let elem_id = decoder.open_element_expect(ELEM_ENUM)?;
        self.enumsize = decoder.read_signed_integer_attr(ATTRIB_SIZE)? as i32;
        if decoder.read_bool_attr(ATTRIB_SIGNED)? {
            self.enumtype = TypeMetatype::EnumInt;
        } else {
            self.enumtype = TypeMetatype::EnumUint;
        }
        decoder.close_element(elem_id)
    }

    pub fn set_core_type(&mut self, name: &str, size: i32, meta: TypeMetatype, chartp: bool) -> Result<()> {
        let ct = if chartp {
            if size == 1 {
                self.get_type_char_named(name)?
            } else {
                self.get_type_unicode(name, size, meta)?
            }
        } else if meta == TypeMetatype::Code {
            self.get_type_code_named(name)?
        } else if meta == TypeMetatype::Void {
            self.get_type_void()?
        } else {
            self.get_base_named(size, meta, name)?
        };
        self.get_mut(ct).flags |= Datatype::CORETYPE;
        Ok(())
    }

    pub fn cache_core_types(&mut self) -> Result<()> {
        for pos in 0..self.tree.len() {
            let ct = self.tree[pos];
            let dt = self.get(ct);
            if !dt.is_core_type() {
                continue;
            }
            let size = dt.get_size();
            let meta = dt.get_metatype();
            let is_ascii = dt.is_ascii();
            let is_enum = dt.is_enum_type();
            let is_char_print = dt.is_char_print();
            if size > 8 {
                if meta == TypeMetatype::Float {
                    if size == 10 {
                        self.typecache10 = Some(ct);
                    } else if size == 16 {
                        self.typecache16 = Some(ct);
                    }
                }
                continue;
            }
            let mut fill_generic = false;
            match meta {
                TypeMetatype::Int | TypeMetatype::Uint => {
                    if meta == TypeMetatype::Int && size == 1 && !is_ascii {
                        self.type_nochar = Some(ct);
                    }
                    if is_enum {
                    } else if is_char_print {
                        if size < 5 {
                            self.charcache[size as usize] = Some(ct);
                        }
                        if is_ascii {
                            self.typecache[size as usize][meta.cache_index()] = Some(ct);
                        }
                    } else {
                        fill_generic = true;
                    }
                }
                TypeMetatype::Void
                | TypeMetatype::Unknown
                | TypeMetatype::Bool
                | TypeMetatype::Code
                | TypeMetatype::Float => fill_generic = true,
                _ => {}
            }
            if fill_generic && self.typecache[size as usize][meta.cache_index()].is_none() {
                self.typecache[size as usize][meta.cache_index()] = Some(ct);
            }
        }
        Ok(())
    }

    pub fn find_warning(&self, dt: TypeId) -> String {
        let mut dt = dt;
        while self.get(dt).get_metatype() == TypeMetatype::Ptr {
            dt = self.get(dt).get_ptr_to();
        }
        while let Some(typedef_imm) = self.get(dt).get_typedef() {
            dt = typedef_imm;
        }
        if let Some(base) = self.get(dt).get_partial_base() {
            dt = base;
        }
        match self.warnings.get(&dt) {
            Some(warning) => warning.clone(),
            None => String::new(),
        }
    }
}
