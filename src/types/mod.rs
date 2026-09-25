use std::cmp::Ordering;
use std::collections::BTreeMap;
use std::fmt::Write as _;

use crate::address::{Address, BitRange};
use crate::architecture::Architecture;
use crate::arena::Arena;
use crate::define_id;
use crate::error::{Error, Result};
use crate::fspec::FuncProto;
use crate::marshal::{AttributeId, ElementId};
use crate::space::{AddrSpace, SpaceRef};

mod compound;
mod datatype;
mod factory;
mod resolve;

pub const ATTRIB_ALIGNMENT: AttributeId = AttributeId::new("alignment", 47);
pub const ATTRIB_ARRAYSIZE: AttributeId = AttributeId::new("arraysize", 48);
pub const ATTRIB_CHAR: AttributeId = AttributeId::new("char", 49);
pub const ATTRIB_CORE: AttributeId = AttributeId::new("core", 50);
pub const ATTRIB_INCOMPLETE: AttributeId = AttributeId::new("incomplete", 52);
pub const ATTRIB_OPAQUESTRING: AttributeId = AttributeId::new("opaquestring", 56);
pub const ATTRIB_SIGNED: AttributeId = AttributeId::new("signed", 57);
pub const ATTRIB_STRUCTALIGN: AttributeId = AttributeId::new("structalign", 58);
pub const ATTRIB_UTF: AttributeId = AttributeId::new("utf", 59);
pub const ATTRIB_VARLENGTH: AttributeId = AttributeId::new("varlength", 60);
pub const ELEM_CHAR_SIZE: ElementId = ElementId::new("char_size", 39);
pub const ELEM_CORETYPES: ElementId = ElementId::new("coretypes", 41);
pub const ELEM_DATA_ORGANIZATION: ElementId = ElementId::new("data_organization", 42);
pub const ELEM_DEF: ElementId = ElementId::new("def", 43);
pub const ELEM_ENTRY: ElementId = ElementId::new("entry", 47);
pub const ELEM_ENUM: ElementId = ElementId::new("enum", 48);
pub const ELEM_FIELD: ElementId = ElementId::new("field", 49);
pub const ELEM_INTEGER_SIZE: ElementId = ElementId::new("integer_size", 51);
pub const ELEM_LONG_SIZE: ElementId = ElementId::new("long_size", 54);
pub const ELEM_POINTER_SIZE: ElementId = ElementId::new("pointer_size", 57);
pub const ELEM_SIZE_ALIGNMENT_MAP: ElementId = ElementId::new("size_alignment_map", 59);
pub const ELEM_TYPE: ElementId = ElementId::new("type", 60);
pub const ELEM_TYPEGRP: ElementId = ElementId::new("typegrp", 62);
pub const ELEM_TYPEREF: ElementId = ElementId::new("typeref", 63);
pub const ELEM_WCHAR_SIZE: ElementId = ElementId::new("wchar_size", 65);
pub const ELEM_BITFIELD: ElementId = ElementId::new("bitfield", 289);

define_id!(TypeId);

#[repr(i32)]
#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum TypeMetatype {
    PartialUnion = 0,
    PartialStruct = 1,
    PartialEnum = 2,
    Union = 3,
    Struct = 4,
    EnumInt = 5,
    EnumUint = 6,
    Array = 7,
    PtrRel = 8,
    Ptr = 9,
    Float = 10,
    Code = 11,
    Bool = 12,
    Uint = 13,
    Int = 14,
    Unknown = 15,
    Spacebase = 16,
    Void = 17,
}

impl TypeMetatype {
    pub(crate) fn cache_index(self) -> usize {
        (self as i32 - TypeMetatype::Float as i32) as usize
    }
}

#[repr(i32)]
#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum SubMetatype {
    PartialUnion = 0,
    Union = 1,
    Struct = 2,
    Array = 3,
    PtrStruct = 4,
    PtrRel = 5,
    Ptr = 6,
    PtrRelUnk = 7,
    Float = 8,
    Code = 9,
    Bool = 10,
    UintUnicode = 11,
    IntUnicode = 12,
    UintEnum = 13,
    UintPartialEnum = 14,
    IntEnum = 15,
    UintPlain = 16,
    IntPlain = 17,
    UintChar = 18,
    IntChar = 19,
    PartialStruct = 20,
    Unknown = 21,
    Spacebase = 22,
    Void = 23,
}

#[repr(i32)]
#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum TypeClass {
    General = 0,
    Float = 1,
    Ptr = 2,
    HiddenRet = 3,
    Vector = 4,
    Class1 = 100,
    Class2 = 101,
    Class3 = 102,
    Class4 = 103,
}

pub const BASE2SUB: [SubMetatype; 18] = [
    SubMetatype::PartialUnion,
    SubMetatype::PartialStruct,
    SubMetatype::UintPartialEnum,
    SubMetatype::Union,
    SubMetatype::Struct,
    SubMetatype::IntEnum,
    SubMetatype::UintEnum,
    SubMetatype::Array,
    SubMetatype::PtrRel,
    SubMetatype::Ptr,
    SubMetatype::Float,
    SubMetatype::Code,
    SubMetatype::Bool,
    SubMetatype::UintPlain,
    SubMetatype::IntPlain,
    SubMetatype::Unknown,
    SubMetatype::Spacebase,
    SubMetatype::Void,
];

pub fn types_of(glb: &Architecture) -> &TypeFactory {
    glb.types.as_deref().expect("type factory is not initialized")
}

pub fn types_of_mut(glb: &mut Architecture) -> &mut TypeFactory {
    glb.types.as_deref_mut().expect("type factory is not initialized")
}

fn is_print_byte(byte: u8) -> bool {
    (0x20..0x7f).contains(&byte)
}

pub fn print_data(out: &mut String, buffer: Option<&[u8]>, size: i32, baseaddr: &Address) {
    let Some(buffer) = buffer else {
        out.push_str("Address not present in binary image\n");
        return;
    };
    let addr = baseaddr.get_offset();
    let endaddr = addr.wrapping_add(size as i64 as u64);
    let mut start = addr & !0xfu64;
    while start < endaddr {
        let _ = write!(out, "{:08x}: ", start);
        for index in 0..16u64 {
            let cur = start.wrapping_add(index);
            if cur < addr || cur >= endaddr {
                out.push_str("   ");
            } else {
                let _ = write!(out, "{:02x} ", buffer[(cur - addr) as usize]);
            }
        }
        out.push_str("  ");
        for index in 0..16u64 {
            let cur = start.wrapping_add(index);
            if cur < addr || cur >= endaddr {
                out.push(' ');
            } else {
                let byte = buffer[(cur - addr) as usize];
                if is_print_byte(byte) {
                    out.push(byte as char);
                } else {
                    out.push('.');
                }
            }
        }
        out.push('\n');
        start = start.wrapping_add(16);
    }
}

pub fn metatype2string(metatype: TypeMetatype) -> Result<String> {
    let res = match metatype {
        TypeMetatype::Void => "void",
        TypeMetatype::Ptr => "ptr",
        TypeMetatype::PtrRel => "ptrrel",
        TypeMetatype::Array => "array",
        TypeMetatype::PartialEnum => "partenum",
        TypeMetatype::PartialStruct => "partstruct",
        TypeMetatype::PartialUnion => "partunion",
        TypeMetatype::EnumInt => "enum_int",
        TypeMetatype::EnumUint => "enum_uint",
        TypeMetatype::Struct => "struct",
        TypeMetatype::Union => "union",
        TypeMetatype::Spacebase => "spacebase",
        TypeMetatype::Unknown => "unknown",
        TypeMetatype::Uint => "uint",
        TypeMetatype::Int => "int",
        TypeMetatype::Bool => "bool",
        TypeMetatype::Code => "code",
        TypeMetatype::Float => "float",
    };
    Ok(res.to_string())
}

pub fn string2metatype(metastring: &str) -> Result<TypeMetatype> {
    let first = metastring.as_bytes().first().copied().unwrap_or(0);
    match first {
        b'p' => {
            if metastring == "ptr" {
                return Ok(TypeMetatype::Ptr);
            } else if metastring == "ptrrel" {
                return Ok(TypeMetatype::PtrRel);
            } else if metastring == "partunion" {
                return Ok(TypeMetatype::PartialUnion);
            } else if metastring == "partstruct" {
                return Ok(TypeMetatype::PartialStruct);
            }
        }
        b'a' if metastring == "array" => {
            return Ok(TypeMetatype::Array);
        }
        b'e' => {
            if metastring == "enum_int" {
                return Ok(TypeMetatype::EnumInt);
            } else if metastring == "enum_uint" {
                return Ok(TypeMetatype::EnumUint);
            }
        }
        b's' => {
            if metastring == "struct" {
                return Ok(TypeMetatype::Struct);
            }
            if metastring == "spacebase" {
                return Ok(TypeMetatype::Spacebase);
            }
        }
        b'u' => {
            if metastring == "unknown" {
                return Ok(TypeMetatype::Unknown);
            } else if metastring == "uint" {
                return Ok(TypeMetatype::Uint);
            } else if metastring == "union" {
                return Ok(TypeMetatype::Union);
            }
        }
        b'i' if metastring == "int" => {
            return Ok(TypeMetatype::Int);
        }
        b'f' if metastring == "float" => {
            return Ok(TypeMetatype::Float);
        }
        b'b' if metastring == "bool" => {
            return Ok(TypeMetatype::Bool);
        }
        b'c' if metastring == "code" => {
            return Ok(TypeMetatype::Code);
        }
        b'v' if metastring == "void" => {
            return Ok(TypeMetatype::Void);
        }
        _ => {}
    }
    Err(Error::Lowlevel(format!("Unknown metatype: {}", metastring)))
}

pub fn string2typeclass(classstring: &str) -> Result<TypeClass> {
    let first = classstring.as_bytes().first().copied().unwrap_or(0);
    match first {
        b'c' => {
            if classstring == "class1" {
                return Ok(TypeClass::Class1);
            } else if classstring == "class2" {
                return Ok(TypeClass::Class2);
            } else if classstring == "class3" {
                return Ok(TypeClass::Class3);
            } else if classstring == "class4" {
                return Ok(TypeClass::Class4);
            }
        }
        b'g' if classstring == "general" => {
            return Ok(TypeClass::General);
        }
        b'h' if classstring == "hiddenret" => {
            return Ok(TypeClass::HiddenRet);
        }
        b'f' if classstring == "float" => {
            return Ok(TypeClass::Float);
        }
        b'p' if (classstring == "ptr" || classstring == "pointer") => {
            return Ok(TypeClass::Ptr);
        }
        b'v' if classstring == "vector" => {
            return Ok(TypeClass::Vector);
        }
        b'u' if classstring == "unknown" => {
            return Ok(TypeClass::General);
        }
        _ => {}
    }
    Err(Error::Lowlevel(format!("Unknown data-type class: {}", classstring)))
}

pub fn metatype2typeclass(meta: TypeMetatype) -> TypeClass {
    match meta {
        TypeMetatype::Float => TypeClass::Float,
        TypeMetatype::Ptr => TypeClass::Ptr,
        _ => TypeClass::General,
    }
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct Nearest {
    pub distance: i64,
    pub offset: i64,
    pub el_size: i32,
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct EnumRepresentation {
    pub matchname: Vec<String>,
    pub complement: bool,
    pub shift_amount: i32,
}

impl EnumRepresentation {
    pub fn new() -> EnumRepresentation {
        EnumRepresentation {
            matchname: Vec::new(),
            complement: false,
            shift_amount: 0,
        }
    }
}

#[derive(Clone, Debug, Default)]
pub struct FieldAccum {
    pub last_off: i32,
    pub calc_size: i32,
    pub calc_align: i32,
    pub warning: String,
}

#[derive(Clone, Debug)]
pub struct TypePointerData {
    pub ptrto: Option<TypeId>,
    pub spaceid: Option<SpaceRef>,
    pub truncate: Option<TypeId>,
    pub wordsize: u32,
}

#[derive(Clone, Debug)]
pub struct TypeArrayData {
    pub arrayof: Option<TypeId>,
    pub arraysize: i32,
}

#[derive(Clone, Debug, Default)]
pub struct TypeEnumData {
    pub namemap: BTreeMap<u64, String>,
}

#[derive(Clone, Debug, Default)]
pub struct TypeStructData {
    pub field: Vec<TypeField>,
    pub bitfield: Vec<TypeBitField>,
}

#[derive(Clone, Debug, Default)]
pub struct TypeUnionData {
    pub field: Vec<TypeField>,
}

#[derive(Clone, Debug)]
pub struct TypePartialEnumData {
    pub enum_data: TypeEnumData,
    pub stripped: TypeId,
    pub parent: TypeId,
    pub offset: i32,
}

#[derive(Clone, Debug)]
pub struct TypePartialStructData {
    pub stripped: TypeId,
    pub container: TypeId,
    pub offset: i32,
}

#[derive(Clone, Debug)]
pub struct TypePartialUnionData {
    pub stripped: TypeId,
    pub container: TypeId,
    pub offset: i32,
}

#[derive(Clone, Debug)]
pub struct TypePointerRelData {
    pub pointer: TypePointerData,
    pub stripped: Option<TypeId>,
    pub parent: Option<TypeId>,
    pub offset: i32,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CodeSignature {
    pub model_name: Option<String>,
    pub params: Vec<TypeId>,
    pub output: Option<TypeId>,
    pub comparable_flags: u32,
}

pub struct TypeCodeData {
    pub proto: Option<Box<FuncProto>>,
    pub signature: Option<CodeSignature>,
    pub factory: bool,
}

#[derive(Clone, Debug)]
pub struct TypeSpacebaseData {
    pub spaceid: Option<SpaceRef>,
    pub scope_id: u64,
}

pub enum TypeKind {
    Base,
    Char,
    Unicode,
    Void,
    Pointer(TypePointerData),
    Array(TypeArrayData),
    Enum(TypeEnumData),
    Struct(TypeStructData),
    Union(TypeUnionData),
    PartialEnum(TypePartialEnumData),
    PartialStruct(TypePartialStructData),
    PartialUnion(TypePartialUnionData),
    PointerRel(TypePointerRelData),
    Code(TypeCodeData),
    Spacebase(TypeSpacebaseData),
}

pub struct Datatype {
    pub(crate) id: u64,
    pub(crate) size: i32,
    pub(crate) flags: u32,
    pub(crate) name: String,
    pub(crate) display_name: String,
    pub(crate) metatype: TypeMetatype,
    pub(crate) submeta: SubMetatype,
    pub(crate) typedef_imm: Option<TypeId>,
    pub(crate) alignment: i32,
    pub(crate) align_size: i32,
    pub kind: TypeKind,
}

impl Datatype {
    pub const CORETYPE: u32 = 1;
    pub const CHARTYPE: u32 = 2;
    pub const ENUMTYPE: u32 = 4;
    pub const POWEROFTWO: u32 = 8;
    pub const UTF16: u32 = 16;
    pub const UTF32: u32 = 32;
    pub const OPAQUE_STRING: u32 = 64;
    pub const VARIABLE_LENGTH: u32 = 128;
    pub const HAS_STRIPPED: u32 = 0x100;
    pub const IS_PTRREL: u32 = 0x200;
    pub const TYPE_INCOMPLETE: u32 = 0x400;
    pub const NEEDS_RESOLUTION: u32 = 0x800;
    pub const FORCE_FORMAT: u32 = 0x7000;
    pub const TRUNCATE_BIGENDIAN: u32 = 0x8000;
    pub const POINTER_TO_ARRAY: u32 = 0x10000;
    pub const WARNING_ISSUED: u32 = 0x20000;
    pub const HAS_BITFIELDS: u32 = 0x40000;

    pub const MAX_ARRAY_SLACK_FORWARD: i32 = 128;
    pub const MAX_ARRAY_SLACK_BACKWARD: i32 = 8;

    pub fn new(size_2: i32, align: i32, metatype_2: TypeMetatype) -> Result<Datatype> {
        if size_2 < 0 {
            return Err(Error::Lowlevel("Bad data-type size".to_string()));
        }
        Ok(Datatype {
            id: 0,
            size: size_2,
            flags: 0,
            name: String::new(),
            display_name: String::new(),
            metatype: metatype_2,
            submeta: BASE2SUB[metatype_2 as usize],
            typedef_imm: None,
            alignment: align,
            align_size: size_2,
            kind: TypeKind::Base,
        })
    }

    pub fn new_base(size: i32, metatype: TypeMetatype) -> Result<Datatype> {
        Datatype::new(size, -1, metatype)
    }

    pub fn new_base_named(size: i32, metatype: TypeMetatype, name: &str) -> Result<Datatype> {
        let mut res = Datatype::new(size, -1, metatype)?;
        res.name = name.to_string();
        res.display_name = name.to_string();
        Ok(res)
    }

    pub fn new_char(name: &str) -> Result<Datatype> {
        let mut res = Datatype::new_base_named(1, TypeMetatype::Int, name)?;
        res.kind = TypeKind::Char;
        res.flags |= Datatype::CHARTYPE;
        res.submeta = SubMetatype::IntChar;
        Ok(res)
    }

    pub fn new_unicode_empty() -> Result<Datatype> {
        let mut res = Datatype::new_base(0, TypeMetatype::Int)?;
        res.kind = TypeKind::Unicode;
        Ok(res)
    }

    pub fn new_unicode(nm: &str, sz: i32, metatype: TypeMetatype) -> Result<Datatype> {
        let mut res = Datatype::new_base_named(sz, metatype, nm)?;
        res.kind = TypeKind::Unicode;
        res.set_unicode_flags();
        res.submeta = if metatype == TypeMetatype::Int {
            SubMetatype::IntUnicode
        } else {
            SubMetatype::UintUnicode
        };
        Ok(res)
    }

    pub fn new_void() -> Result<Datatype> {
        let mut res = Datatype::new(0, 1, TypeMetatype::Void)?;
        res.kind = TypeKind::Void;
        res.name = "void".to_string();
        res.display_name = res.name.clone();
        res.flags |= Datatype::CORETYPE;
        Ok(res)
    }

    pub fn new_pointer_empty() -> Result<Datatype> {
        let mut res = Datatype::new(0, -1, TypeMetatype::Ptr)?;
        res.kind = TypeKind::Pointer(TypePointerData {
            ptrto: None,
            spaceid: None,
            truncate: None,
            wordsize: 1,
        });
        Ok(res)
    }

    pub fn new_pointer(size: i32, pt: TypeId, ws: u32, types: &TypeFactory) -> Result<Datatype> {
        let mut res = Datatype::new(size, -1, TypeMetatype::Ptr)?;
        res.flags = types.get(pt).inherit_for_pointer();
        res.kind = TypeKind::Pointer(TypePointerData {
            ptrto: Some(pt),
            spaceid: None,
            truncate: None,
            wordsize: ws,
        });
        res.calc_submeta(types);
        Ok(res)
    }

    pub fn new_pointer_space(pt: TypeId, spc: &SpaceRef, types: &TypeFactory) -> Result<Datatype> {
        let mut res = Datatype::new(spc.get_addr_size() as i32, -1, TypeMetatype::Ptr)?;
        res.flags = types.get(pt).inherit_for_pointer();
        res.kind = TypeKind::Pointer(TypePointerData {
            ptrto: Some(pt),
            spaceid: Some(spc.clone()),
            truncate: None,
            wordsize: spc.get_word_size(),
        });
        res.calc_submeta(types);
        Ok(res)
    }

    pub fn new_array_empty() -> Result<Datatype> {
        let mut res = Datatype::new(0, -1, TypeMetatype::Array)?;
        res.kind = TypeKind::Array(TypeArrayData {
            arrayof: None,
            arraysize: 0,
        });
        Ok(res)
    }

    pub fn new_array(count: i32, ao: TypeId, types: &TypeFactory) -> Result<Datatype> {
        let element = types.get(ao);
        let mut res = Datatype::new(
            count.wrapping_mul(element.get_align_size()),
            element.get_alignment(),
            TypeMetatype::Array,
        )?;
        res.kind = TypeKind::Array(TypeArrayData {
            arrayof: Some(ao),
            arraysize: count,
        });
        if count == 1 {
            res.flags |= Datatype::NEEDS_RESOLUTION;
        }
        Ok(res)
    }

    pub fn new_enum(size: i32, metatype: TypeMetatype) -> Result<Datatype> {
        let mut res = Datatype::new_base(size, metatype)?;
        res.kind = TypeKind::Enum(TypeEnumData::default());
        res.flags |= Datatype::ENUMTYPE;
        res.metatype = if metatype == TypeMetatype::EnumInt {
            TypeMetatype::Int
        } else {
            TypeMetatype::Uint
        };
        Ok(res)
    }

    pub fn new_enum_named(size: i32, metatype: TypeMetatype, nm: &str) -> Result<Datatype> {
        let mut res = Datatype::new_base_named(size, metatype, nm)?;
        res.kind = TypeKind::Enum(TypeEnumData::default());
        res.flags |= Datatype::ENUMTYPE;
        res.metatype = if metatype == TypeMetatype::EnumInt {
            TypeMetatype::Int
        } else {
            TypeMetatype::Uint
        };
        Ok(res)
    }

    pub fn new_struct() -> Result<Datatype> {
        let mut res = Datatype::new(0, -1, TypeMetatype::Struct)?;
        res.kind = TypeKind::Struct(TypeStructData::default());
        res.flags |= Datatype::TYPE_INCOMPLETE;
        Ok(res)
    }

    pub fn new_union() -> Result<Datatype> {
        let mut res = Datatype::new(0, -1, TypeMetatype::Union)?;
        res.kind = TypeKind::Union(TypeUnionData::default());
        res.flags |= Datatype::TYPE_INCOMPLETE | Datatype::NEEDS_RESOLUTION;
        Ok(res)
    }

    pub fn new_partial_enum(par: TypeId, off: i32, sz: i32, strip: TypeId, types: &TypeFactory) -> Result<Datatype> {
        let mut res = Datatype::new_enum(sz, TypeMetatype::PartialEnum)?;
        res.flags |= types.get(par).inherit_for_partial();
        res.flags |= Datatype::HAS_STRIPPED;
        res.kind = TypeKind::PartialEnum(TypePartialEnumData {
            enum_data: TypeEnumData::default(),
            stripped: strip,
            parent: par,
            offset: off,
        });
        Ok(res)
    }

    pub fn new_partial_struct(
        contain: TypeId,
        off: i32,
        sz: i32,
        strip: TypeId,
        types: &TypeFactory,
    ) -> Result<Datatype> {
        let mut res = Datatype::new(sz, 1, TypeMetatype::PartialStruct)?;
        let mut container = contain;
        let mut offset = off;
        if let TypeKind::PartialStruct(partial) = &types.get(container).kind {
            container = partial.container;
            offset += partial.offset;
        }
        let container_type = types.get(container);
        res.flags |= container_type.inherit_for_partial();
        res.flags |= Datatype::HAS_STRIPPED;
        if container_type.has_bitfields() && container_type.has_bit_fields_in_range(offset, sz, types) {
            res.flags |= Datatype::HAS_BITFIELDS;
        }
        res.kind = TypeKind::PartialStruct(TypePartialStructData {
            stripped: strip,
            container,
            offset,
        });
        Ok(res)
    }

    pub fn new_partial_union(
        contain: TypeId,
        off: i32,
        sz: i32,
        strip: TypeId,
        types: &TypeFactory,
    ) -> Result<Datatype> {
        let mut res = Datatype::new(sz, 1, TypeMetatype::PartialUnion)?;
        res.flags |= types.get(contain).inherit_for_partial();
        res.flags |= Datatype::NEEDS_RESOLUTION | Datatype::HAS_STRIPPED;
        res.kind = TypeKind::PartialUnion(TypePartialUnionData {
            stripped: strip,
            container: contain,
            offset: off,
        });
        Ok(res)
    }

    pub fn new_pointer_rel_empty() -> Result<Datatype> {
        let mut res = Datatype::new(0, -1, TypeMetatype::Ptr)?;
        res.kind = TypeKind::PointerRel(TypePointerRelData {
            pointer: TypePointerData {
                ptrto: None,
                spaceid: None,
                truncate: None,
                wordsize: 1,
            },
            stripped: None,
            parent: None,
            offset: 0,
        });
        res.submeta = SubMetatype::PtrRel;
        Ok(res)
    }

    pub fn new_pointer_rel(
        sz: i32,
        pt: TypeId,
        ws: u32,
        par: TypeId,
        off: i32,
        types: &TypeFactory,
    ) -> Result<Datatype> {
        let mut res = Datatype::new_pointer(sz, pt, ws, types)?;
        let pointer = match res.kind {
            TypeKind::Pointer(pointer) => pointer,
            _ => unreachable!("new_pointer builds a pointer kind"),
        };
        res.kind = TypeKind::PointerRel(TypePointerRelData {
            pointer,
            stripped: None,
            parent: Some(par),
            offset: off,
        });
        res.flags |= Datatype::IS_PTRREL;
        res.submeta = SubMetatype::PtrRel;
        Ok(res)
    }

    pub fn new_code() -> Result<Datatype> {
        let mut res = Datatype::new(1, 1, TypeMetatype::Code)?;
        res.kind = TypeKind::Code(TypeCodeData {
            proto: None,
            signature: None,
            factory: false,
        });
        res.flags |= Datatype::TYPE_INCOMPLETE;
        Ok(res)
    }

    pub fn new_spacebase_empty() -> Result<Datatype> {
        let mut res = Datatype::new(0, 1, TypeMetatype::Spacebase)?;
        res.kind = TypeKind::Spacebase(TypeSpacebaseData {
            spaceid: None,
            scope_id: 0,
        });
        Ok(res)
    }

    pub fn new_spacebase(id: &SpaceRef, scope: u64) -> Result<Datatype> {
        let mut res = Datatype::new(0, 1, TypeMetatype::Spacebase)?;
        res.kind = TypeKind::Spacebase(TypeSpacebaseData {
            spaceid: Some(id.clone()),
            scope_id: scope,
        });
        Ok(res)
    }

    pub fn clone_type(&self, types: &TypeFactory) -> Result<Datatype> {
        let mut extra_flags = 0;
        let kind = match &self.kind {
            TypeKind::Base => TypeKind::Base,
            TypeKind::Char => {
                extra_flags |= Datatype::CHARTYPE;
                TypeKind::Char
            }
            TypeKind::Unicode => TypeKind::Unicode,
            TypeKind::Void => {
                extra_flags |= Datatype::CORETYPE;
                TypeKind::Void
            }
            TypeKind::Pointer(pointer) => TypeKind::Pointer(pointer.clone()),
            TypeKind::Array(array) => TypeKind::Array(array.clone()),
            TypeKind::PointerRel(pointer_rel) => TypeKind::PointerRel(pointer_rel.clone()),
            TypeKind::Spacebase(spacebase) => TypeKind::Spacebase(spacebase.clone()),
            TypeKind::Enum(data) => TypeKind::Enum(data.clone()),
            TypeKind::Struct(data) => {
                if TypeFactory::single_field_fills(&data.field, self.size, types) {
                    extra_flags |= Datatype::NEEDS_RESOLUTION;
                }
                TypeKind::Struct(data.clone())
            }
            TypeKind::Union(data) => TypeKind::Union(data.clone()),
            TypeKind::PartialEnum(data) => TypeKind::PartialEnum(data.clone()),
            TypeKind::PartialStruct(data) => TypeKind::PartialStruct(data.clone()),
            TypeKind::PartialUnion(data) => TypeKind::PartialUnion(data.clone()),
            TypeKind::Code(data) => TypeKind::Code(data.copy_data()?),
        };
        Ok(Datatype {
            id: self.id,
            size: self.size,
            flags: self.flags | extra_flags,
            name: self.name.clone(),
            display_name: self.display_name.clone(),
            metatype: self.metatype,
            submeta: self.submeta,
            typedef_imm: self.typedef_imm,
            alignment: self.alignment,
            align_size: self.align_size,
            kind,
        })
    }

    pub fn mark_complete(&mut self) {
        self.flags &= !Datatype::TYPE_INCOMPLETE;
    }

    pub fn set_display_format(&mut self, format: u32) {
        self.flags &= !Datatype::FORCE_FORMAT;
        self.flags |= format << 12;
    }

    pub fn hash_name(nm: &str) -> u64 {
        let mut res: u64 = 123;
        for byte in nm.bytes() {
            res = res.rotate_left(8);
            res = res.wrapping_add(byte as i8 as i64 as u64);
            if (res & 1) == 0 {
                res ^= 0xfeabfeab;
            }
        }
        res |= 0xC000000000000000;
        res
    }

    pub fn hash_size(id: u64, size: i32) -> u64 {
        let size_hash = (size as i64 as u64).wrapping_mul(0x98251033aecbabaf);
        id ^ size_hash
    }

    pub fn calc_align_size(sz: i32, align: i32) -> i32 {
        let modulus = sz % align;
        if modulus != 0 {
            return sz + (align - modulus);
        }
        sz
    }

    pub fn is_core_type(&self) -> bool {
        (self.flags & Datatype::CORETYPE) != 0
    }

    pub fn is_char_print(&self) -> bool {
        (self.flags & (Datatype::CHARTYPE | Datatype::UTF16 | Datatype::UTF32 | Datatype::OPAQUE_STRING)) != 0
    }

    pub fn is_enum_type(&self) -> bool {
        (self.flags & Datatype::ENUMTYPE) != 0
    }

    pub fn is_ascii(&self) -> bool {
        (self.flags & Datatype::CHARTYPE) != 0
    }

    pub fn is_utf16(&self) -> bool {
        (self.flags & Datatype::UTF16) != 0
    }

    pub fn is_utf32(&self) -> bool {
        (self.flags & Datatype::UTF32) != 0
    }

    pub fn is_variable_length(&self) -> bool {
        (self.flags & Datatype::VARIABLE_LENGTH) != 0
    }

    pub fn has_same_variable_base(&self, ct: &Datatype) -> bool {
        if !self.is_variable_length() {
            return false;
        }
        if !ct.is_variable_length() {
            return false;
        }
        let this_id = Datatype::hash_size(self.id, self.size);
        let them_id = Datatype::hash_size(ct.id, ct.size);
        this_id == them_id
    }

    pub fn is_opaque_string(&self) -> bool {
        (self.flags & Datatype::OPAQUE_STRING) != 0
    }

    pub fn is_pointer_to_array(&self) -> bool {
        (self.flags & Datatype::POINTER_TO_ARRAY) != 0
    }

    pub fn is_pointer_rel(&self) -> bool {
        (self.flags & Datatype::IS_PTRREL) != 0
    }

    pub fn is_formal_pointer_rel(&self) -> bool {
        (self.flags & (Datatype::IS_PTRREL | Datatype::HAS_STRIPPED)) == Datatype::IS_PTRREL
    }

    pub fn has_stripped(&self) -> bool {
        (self.flags & Datatype::HAS_STRIPPED) != 0
    }

    pub fn is_incomplete(&self) -> bool {
        (self.flags & Datatype::TYPE_INCOMPLETE) != 0
    }

    pub fn needs_resolution(&self) -> bool {
        (self.flags & Datatype::NEEDS_RESOLUTION) != 0
    }

    pub fn has_warning(&self) -> bool {
        (self.flags & Datatype::WARNING_ISSUED) != 0
    }

    pub fn has_bitfields(&self) -> bool {
        (self.flags & Datatype::HAS_BITFIELDS) != 0
    }

    pub fn inherit_for_pointer(&self) -> u32 {
        self.flags & (Datatype::CORETYPE | Datatype::WARNING_ISSUED)
    }

    pub fn inherit_for_partial(&self) -> u32 {
        self.flags & Datatype::WARNING_ISSUED
    }

    pub fn get_display_format(&self) -> u32 {
        (self.flags & Datatype::FORCE_FORMAT) >> 12
    }

    pub fn get_metatype(&self) -> TypeMetatype {
        self.metatype
    }

    pub fn get_sub_meta(&self) -> SubMetatype {
        self.submeta
    }

    pub fn get_id(&self) -> u64 {
        self.id
    }

    pub fn get_unsized_id(&self) -> u64 {
        if (self.flags & Datatype::VARIABLE_LENGTH) != 0 {
            return Datatype::hash_size(self.id, self.size);
        }
        self.id
    }

    pub fn get_size(&self) -> i32 {
        self.size
    }

    pub fn get_align_size(&self) -> i32 {
        self.align_size
    }

    pub fn get_alignment(&self) -> i32 {
        self.alignment
    }

    pub fn get_name(&self) -> &str {
        &self.name
    }

    pub fn get_display_name(&self) -> &str {
        &self.display_name
    }

    pub fn get_typedef(&self) -> Option<TypeId> {
        self.typedef_imm
    }

    pub fn get_flags(&self) -> u32 {
        self.flags
    }

    pub fn get_partial_base(&self) -> Option<TypeId> {
        match &self.kind {
            TypeKind::PartialEnum(data) => Some(data.parent),
            TypeKind::PartialStruct(data) => Some(data.container),
            TypeKind::PartialUnion(data) => Some(data.container),
            _ => None,
        }
    }

    pub fn type_order(&self, op: &Datatype, types: &TypeFactory) -> i32 {
        if std::ptr::eq(self, op) {
            return 0;
        }
        self.compare(op, 10, types)
    }

    pub fn type_order_formal(&self, op: &Datatype, types: &TypeFactory) -> i32 {
        if std::ptr::eq(self, op) {
            return 0;
        }
        if self.metatype == TypeMetatype::PartialUnion {
            return 1;
        }
        if op.metatype == TypeMetatype::PartialUnion {
            return -1;
        }
        if self.metatype == TypeMetatype::Bool {
            return 1;
        }
        if op.metatype == TypeMetatype::Bool {
            return -1;
        }
        self.compare(op, 10, types)
    }

    pub fn is_piece_structured(&self) -> bool {
        self.metatype <= TypeMetatype::Array
    }

    pub fn set_unicode_flags(&mut self) {
        if self.size == 2 {
            self.flags |= Datatype::UTF16;
        } else if self.size == 4 {
            self.flags |= Datatype::UTF32;
        } else if self.size == 1 {
            self.flags |= Datatype::CHARTYPE;
        }
    }

    fn pointer_data(&self) -> &TypePointerData {
        match &self.kind {
            TypeKind::Pointer(data) => data,
            TypeKind::PointerRel(data) => &data.pointer,
            _ => panic!("data-type is not a pointer"),
        }
    }

    fn pointer_data_mut(&mut self) -> &mut TypePointerData {
        match &mut self.kind {
            TypeKind::Pointer(data) => data,
            TypeKind::PointerRel(data) => &mut data.pointer,
            _ => panic!("data-type is not a pointer"),
        }
    }

    pub(crate) fn pointer_data_option(&self) -> Option<&TypePointerData> {
        match &self.kind {
            TypeKind::Pointer(data) => Some(data),
            TypeKind::PointerRel(data) => Some(&data.pointer),
            _ => None,
        }
    }

    pub fn get_ptr_to(&self) -> TypeId {
        self.pointer_data().ptrto.expect("pointer without target")
    }

    pub fn get_word_size(&self) -> u32 {
        self.pointer_data().wordsize
    }

    pub fn get_space(&self) -> Option<&SpaceRef> {
        self.pointer_data().spaceid.as_ref()
    }

    pub fn get_truncate(&self) -> Option<TypeId> {
        self.pointer_data().truncate
    }

    fn array_data(&self) -> &TypeArrayData {
        match &self.kind {
            TypeKind::Array(data) => data,
            _ => panic!("data-type is not an array"),
        }
    }

    pub fn get_base(&self) -> TypeId {
        self.array_data().arrayof.expect("array without element type")
    }

    pub fn num_elements(&self) -> i32 {
        self.array_data().arraysize
    }

    fn enum_data(&self) -> &TypeEnumData {
        match &self.kind {
            TypeKind::Enum(data) => data,
            TypeKind::PartialEnum(data) => &data.enum_data,
            _ => panic!("data-type is not an enumeration"),
        }
    }

    pub fn set_name_map(&mut self, nmap: &BTreeMap<u64, String>) {
        match &mut self.kind {
            TypeKind::Enum(data) => data.namemap = nmap.clone(),
            TypeKind::PartialEnum(data) => data.enum_data.namemap = nmap.clone(),
            _ => panic!("data-type is not an enumeration"),
        }
    }

    pub fn get_enum_map(&self) -> &BTreeMap<u64, String> {
        &self.enum_data().namemap
    }

    fn struct_data(&self) -> &TypeStructData {
        match &self.kind {
            TypeKind::Struct(data) => data,
            _ => panic!("data-type is not a structure"),
        }
    }

    pub fn get_fields(&self) -> &[TypeField] {
        match &self.kind {
            TypeKind::Struct(data) => &data.field,
            TypeKind::Union(data) => &data.field,
            _ => panic!("data-type has no fields"),
        }
    }

    pub fn num_bit_fields(&self) -> i32 {
        self.struct_data().bitfield.len() as i32
    }

    pub fn get_bit_field(&self, index: i32) -> &TypeBitField {
        &self.struct_data().bitfield[index as usize]
    }

    pub fn get_field(&self, index: i32) -> &TypeField {
        match &self.kind {
            TypeKind::Union(data) => &data.field[index as usize],
            _ => panic!("data-type is not a union"),
        }
    }

    pub fn get_offset(&self) -> i32 {
        match &self.kind {
            TypeKind::PartialEnum(data) => data.offset,
            TypeKind::PartialStruct(data) => data.offset,
            TypeKind::PartialUnion(data) => data.offset,
            _ => panic!("data-type is not a partial data-type"),
        }
    }

    pub fn get_parent(&self) -> TypeId {
        match &self.kind {
            TypeKind::PartialEnum(data) => data.parent,
            TypeKind::PartialStruct(data) => data.container,
            TypeKind::PointerRel(data) => data.parent.expect("relative pointer without parent"),
            _ => panic!("data-type has no parent"),
        }
    }

    pub fn get_parent_union(&self) -> TypeId {
        match &self.kind {
            TypeKind::PartialUnion(data) => data.container,
            _ => panic!("data-type is not a partial union"),
        }
    }

    fn pointer_rel_data(&self) -> &TypePointerRelData {
        match &self.kind {
            TypeKind::PointerRel(data) => data,
            _ => panic!("data-type is not a relative pointer"),
        }
    }

    pub fn mark_ephemeral(&mut self, types: &mut TypeFactory) -> Result<()> {
        let size = self.size;
        let ptrto = self.get_ptr_to();
        let wordsize = self.get_word_size();
        let stripped = types.get_type_pointer(size, ptrto, wordsize)?;
        match &mut self.kind {
            TypeKind::PointerRel(data) => data.stripped = Some(stripped),
            _ => panic!("data-type is not a relative pointer"),
        }
        self.flags |= Datatype::HAS_STRIPPED;
        if types.get(ptrto).get_metatype() == TypeMetatype::Unknown {
            self.submeta = SubMetatype::PtrRelUnk;
        }
        Ok(())
    }

    pub fn get_address_offset(&self) -> i32 {
        let data = self.pointer_rel_data();
        AddrSpace::byte_to_address_int(data.offset as i64, data.pointer.wordsize) as i32
    }

    pub fn get_byte_offset(&self) -> i32 {
        self.pointer_rel_data().offset
    }

    pub fn get_prototype(&self) -> Option<&FuncProto> {
        match &self.kind {
            TypeKind::Code(data) => data.proto.as_deref(),
            _ => panic!("data-type is not a code data-type"),
        }
    }

    pub(crate) fn code_signature(&self) -> Option<&CodeSignature> {
        match &self.kind {
            TypeKind::Code(data) => data.signature.as_ref(),
            _ => None,
        }
    }
}

impl TypeCodeData {
    pub fn copy_data(&self) -> Result<TypeCodeData> {
        let proto = match &self.proto {
            Some(proto) => {
                let mut copy = FuncProto::new();
                copy.copy(proto)?;
                Some(Box::new(copy))
            }
            None => None,
        };
        Ok(TypeCodeData {
            proto,
            signature: self.signature.clone(),
            factory: self.factory,
        })
    }
}

#[derive(Clone, Debug)]
pub struct TypeField {
    pub ident: i32,
    pub offset: i32,
    pub name: String,
    pub tp: TypeId,
}

impl TypeField {
    pub fn new(id: i32, off: i32, nm: &str, ct: TypeId) -> TypeField {
        TypeField {
            ident: id,
            offset: off,
            name: nm.to_string(),
            tp: ct,
        }
    }

    pub fn compare(&self, op2: &TypeField, types: &TypeFactory) -> i32 {
        if self.offset != op2.offset {
            return if self.offset < op2.offset { -1 } else { 1 };
        }
        if self.name != op2.name {
            return if self.name < op2.name { -1 } else { 1 };
        }
        let meta1 = types.get(self.tp).get_metatype();
        let meta2 = types.get(op2.tp).get_metatype();
        if meta1 != meta2 {
            return if meta1 < meta2 { -1 } else { 1 };
        }
        0
    }

    pub fn compare_dependency(&self, op2: &TypeField) -> i32 {
        if self.offset != op2.offset {
            return if self.offset < op2.offset { -1 } else { 1 };
        }
        if self.name != op2.name {
            return if self.name < op2.name { -1 } else { 1 };
        }
        if self.tp != op2.tp {
            return if self.tp < op2.tp { -1 } else { 1 };
        }
        0
    }

    pub fn compare_max_byte(off: i32, field: &TypeField, types: &TypeFactory) -> bool {
        off < field.offset + types.get(field.tp).get_size()
    }
}

#[derive(Clone, Debug)]
pub struct TypeBitField {
    pub name: String,
    pub tp: TypeId,
    pub bits: BitRange,
    pub ident: i32,
}

impl TypeBitField {
    pub fn new(id: i32, num_bits: i32, is_big_endian: bool, nm: &str, ct: TypeId) -> TypeBitField {
        TypeBitField {
            name: nm.to_string(),
            tp: ct,
            bits: BitRange::new(0, (num_bits + 7) / 8, 0, num_bits, is_big_endian),
            ident: id,
        }
    }

    pub fn compare(&self, op2: &TypeBitField, types: &TypeFactory) -> i32 {
        let res = self.bits.compare(&op2.bits);
        if res != 0 {
            return res;
        }
        if self.name != op2.name {
            return if self.name < op2.name { -1 } else { 1 };
        }
        let meta1 = types.get(self.tp).get_metatype();
        let meta2 = types.get(op2.tp).get_metatype();
        if meta1 != meta2 {
            return if meta1 < meta2 { -1 } else { 1 };
        }
        0
    }

    pub fn compare_dependency(&self, op2: &TypeBitField) -> i32 {
        let res = self.bits.compare(&op2.bits);
        if res != 0 {
            return res;
        }
        if self.name != op2.name {
            return if self.name < op2.name { -1 } else { 1 };
        }
        if self.tp != op2.tp {
            return if self.tp < op2.tp { -1 } else { 1 };
        }
        0
    }

    pub fn compare_max_byte(off: i32, bitfield: &TypeBitField) -> bool {
        off < bitfield.bits.byte_offset + bitfield.bits.byte_size
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct BitFieldTriple {
    pub immed_container: TypeId,
    pub bitfield: usize,
    pub offset: i32,
}

impl BitFieldTriple {
    pub fn new(contain: TypeId, bits: usize, off: i32) -> BitFieldTriple {
        BitFieldTriple {
            immed_container: contain,
            bitfield: bits,
            offset: off,
        }
    }

    pub fn get_bit_field<'a>(&self, types: &'a TypeFactory) -> &'a TypeBitField {
        types.get(self.immed_container).get_bit_field(self.bitfield as i32)
    }

    pub fn compare(op1: &BitFieldTriple, op2: &BitFieldTriple, types: &TypeFactory) -> bool {
        let bits1 = &op1.get_bit_field(types).bits;
        let bits2 = &op2.get_bit_field(types).bits;
        let is_big_endian = bits1.is_big_endian;
        let byte_off1 = op1.offset + bits1.byte_offset;
        let byte_off2 = op2.offset + bits2.byte_offset;
        if byte_off1 != byte_off2 {
            if is_big_endian {
                return byte_off1 > byte_off2;
            }
            return byte_off1 < byte_off2;
        }
        let lsb1 = bits1.least_sig_bit;
        let lsb2 = bits2.least_sig_bit;
        if lsb1 != lsb2 {
            return lsb1 < lsb2;
        }
        false
    }
}

pub fn datatype_compare(first: &Datatype, second: &Datatype, types: &TypeFactory) -> Ordering {
    let res = first.compare_dependency(second, types);
    if res != 0 {
        return if res < 0 { Ordering::Less } else { Ordering::Greater };
    }
    first.get_id().cmp(&second.get_id())
}

pub fn datatype_name_compare(first: &Datatype, second: &Datatype) -> Ordering {
    match first.get_name().cmp(second.get_name()) {
        Ordering::Equal => first.get_id().cmp(&second.get_id()),
        other => other,
    }
}

pub struct TypeFactory {
    pub(crate) size_of_int: i32,
    pub(crate) size_of_long: i32,
    pub(crate) size_of_char: i32,
    pub(crate) size_of_wchar: i32,
    pub(crate) size_of_pointer: i32,
    pub(crate) size_of_alt_pointer: i32,
    pub(crate) enumsize: i32,
    pub(crate) enumtype: TypeMetatype,
    pub(crate) align_map: Vec<i32>,
    pub(crate) arena: Arena<TypeId, Datatype>,
    pub(crate) tree: Vec<TypeId>,
    pub(crate) nametree: BTreeMap<(String, u64), TypeId>,
    pub(crate) typecache: [[Option<TypeId>; 8]; 9],
    pub(crate) typecache10: Option<TypeId>,
    pub(crate) typecache16: Option<TypeId>,
    pub(crate) type_nochar: Option<TypeId>,
    pub(crate) charcache: [Option<TypeId>; 5],
    pub(crate) warnings: BTreeMap<TypeId, String>,
    pub(crate) incomplete_typedef: Vec<TypeId>,
    pub(crate) default_data_space: Option<SpaceRef>,
    pub(crate) max_basetype_size: i32,
}
