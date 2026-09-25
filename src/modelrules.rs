use std::collections::BTreeSet;

use crate::address::{ATTRIB_FIRST, ATTRIB_LAST};
use crate::architecture::{ATTRIB_REVERSEJUSTIFY, ELEM_RULE};
use crate::cpool::{ATTRIB_A, ATTRIB_B};
use crate::error::{Error, Result};
use crate::fspec::{
    ATTRIB_MAXSIZE, ATTRIB_MINSIZE, ATTRIB_STRATEGY, ATTRIB_VOIDLOCK, P_REGISTER_OUT, P_STANDARD_OUT, ParamActive,
    ParamListStandard, ParameterPieces, PrototypePieces,
};
use crate::istream::{Basefield, extract_i32};
use crate::marshal::{
    ATTRIB_ALIGN, ATTRIB_INDEX, ATTRIB_NAME, ATTRIB_STACKSPILL, ATTRIB_STORAGE, AttributeId, Decoder, ElementId,
};
use crate::pcoderaw::VarnodeData;
use crate::space::SpaceRef;
use crate::translate::{AddrSpaceManager, Translate};
use crate::types::{
    TypeClass, TypeFactory, TypeId, TypeMetatype, metatype2typeclass, string2metatype, string2typeclass,
};

pub const ATTRIB_SIZES: AttributeId = AttributeId::new("sizes", 151);
pub const ATTRIB_MAX_PRIMITIVES: AttributeId = AttributeId::new("maxprimitives", 153);
pub const ATTRIB_REVERSESIGNIF: AttributeId = AttributeId::new("reversesignif", 154);
pub const ATTRIB_MATCHSIZE: AttributeId = AttributeId::new("matchsize", 155);
pub const ATTRIB_AFTER_BYTES: AttributeId = AttributeId::new("afterbytes", 156);
pub const ATTRIB_AFTER_STORAGE: AttributeId = AttributeId::new("afterstorage", 157);
pub const ATTRIB_FILL_ALTERNATE: AttributeId = AttributeId::new("fillalternate", 158);
pub const ELEM_DATATYPE: ElementId = ElementId::new("datatype", 273);
pub const ELEM_CONSUME: ElementId = ElementId::new("consume", 274);
pub const ELEM_CONSUME_EXTRA: ElementId = ElementId::new("consume_extra", 275);
pub const ELEM_CONVERT_TO_PTR: ElementId = ElementId::new("convert_to_ptr", 276);
pub const ELEM_GOTO_STACK: ElementId = ElementId::new("goto_stack", 277);
pub const ELEM_JOIN: ElementId = ElementId::new("join", 278);
pub const ELEM_DATATYPE_AT: ElementId = ElementId::new("datatype_at", 279);
pub const ELEM_POSITION: ElementId = ElementId::new("position", 280);
pub const ELEM_VARARGS: ElementId = ElementId::new("varargs", 281);
pub const ELEM_HIDDEN_RETURN: ElementId = ElementId::new("hidden_return", 282);
pub const ELEM_JOIN_PER_PRIMITIVE: ElementId = ElementId::new("join_per_primitive", 283);
pub const ELEM_JOIN_DUAL_CLASS: ElementId = ElementId::new("join_dual_class", 285);
pub const ELEM_EXTRA_STACK: ElementId = ElementId::new("extra_stack", 287);
pub const ELEM_CONSUME_REMAINING: ElementId = ElementId::new("consume_remaining", 288);

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Primitive {
    pub dt: TypeId,
    pub offset: i32,
}

impl Primitive {
    pub fn new(dt: TypeId, off: i32) -> Primitive {
        Primitive { dt, offset: off }
    }
}

#[derive(Clone, Debug)]
pub struct PrimitiveExtractor {
    primitives: Vec<Primitive>,
    flags: u32,
}

impl PrimitiveExtractor {
    pub const UNKNOWN_ELEMENT: u32 = 1;
    pub const UNALIGNED: u32 = 2;
    pub const EXTRA_SPACE: u32 = 4;
    pub const INVALID: u32 = 8;
    pub const UNION_INVALID: u32 = 16;

    pub fn new(dt: TypeId, union_illegal: bool, offset: i32, max: i32, types: &TypeFactory) -> PrimitiveExtractor {
        let mut extractor = PrimitiveExtractor {
            primitives: Vec::new(),
            flags: if union_illegal {
                PrimitiveExtractor::UNION_INVALID
            } else {
                0
            },
        };
        if !extractor.extract(dt, max, offset, types) {
            extractor.flags |= PrimitiveExtractor::INVALID;
        }
        extractor
    }

    pub fn check_overlap(
        res: &mut Vec<Primitive>,
        small: &[Primitive],
        point: i32,
        big: &Primitive,
        types: &TypeFactory,
    ) -> i32 {
        let mut point = point;
        let end_off = big.offset + types.get(big.dt).get_align_size();
        let use_small = types.get(big.dt).get_metatype() == TypeMetatype::Float;
        while (point as usize) < small.len() {
            let mut cur_off = small[point as usize].offset;
            if cur_off >= end_off {
                break;
            }
            cur_off += types.get(small[point as usize].dt).get_align_size();
            if cur_off > end_off {
                return -1;
            }
            if use_small {
                res.push(small[point as usize]);
            }
            point += 1;
        }
        if !use_small {
            res.push(*big);
        }
        point
    }

    pub fn common_refinement(first: &mut Vec<Primitive>, second: &[Primitive], types: &TypeFactory) -> bool {
        let mut first_point: i32 = 0;
        let mut second_point: i32 = 0;
        let mut common: Vec<Primitive> = Vec::new();
        while (first_point as usize) < first.len() && (second_point as usize) < second.len() {
            let first_element = first[first_point as usize];
            let second_element = second[second_point as usize];
            if first_element.offset < second_element.offset
                && first_element.offset + types.get(first_element.dt).get_align_size() <= second_element.offset
            {
                common.push(first_element);
                first_point += 1;
                continue;
            }
            if second_element.offset < first_element.offset
                && second_element.offset + types.get(second_element.dt).get_align_size() <= first_element.offset
            {
                common.push(second_element);
                second_point += 1;
                continue;
            }
            if types.get(first_element.dt).get_align_size() >= types.get(second_element.dt).get_align_size() {
                second_point =
                    PrimitiveExtractor::check_overlap(&mut common, second, second_point, &first_element, types);
                if second_point < 0 {
                    return false;
                }
                first_point += 1;
            } else {
                first_point =
                    PrimitiveExtractor::check_overlap(&mut common, first, first_point, &second_element, types);
                if first_point < 0 {
                    return false;
                }
                second_point += 1;
            }
        }
        while (first_point as usize) < first.len() {
            common.push(first[first_point as usize]);
            first_point += 1;
        }
        while (second_point as usize) < second.len() {
            common.push(second[second_point as usize]);
            second_point += 1;
        }
        std::mem::swap(first, &mut common);
        true
    }

    pub fn handle_union(&mut self, dt: TypeId, max: i32, offset: i32, types: &TypeFactory) -> bool {
        if (self.flags & PrimitiveExtractor::UNION_INVALID) != 0 {
            return false;
        }
        let union_type = types.get(dt);
        let num = union_type.num_depend(types);
        if num == 0 {
            return false;
        }
        let cur_field = union_type.get_field(0);
        let mut common = PrimitiveExtractor::new(cur_field.tp, false, offset + cur_field.offset, max, types);
        if !common.is_valid() {
            return false;
        }
        for index in 1..num {
            let cur_field = union_type.get_field(index);
            let next = PrimitiveExtractor::new(cur_field.tp, false, offset + cur_field.offset, max, types);
            if !next.is_valid() {
                return false;
            }
            if !PrimitiveExtractor::common_refinement(&mut common.primitives, &next.primitives, types) {
                return false;
            }
        }
        if (self.primitives.len() + common.primitives.len()) as i32 > max {
            return false;
        }
        self.primitives.extend_from_slice(&common.primitives);
        true
    }

    pub fn extract(&mut self, dt: TypeId, max: i32, offset: i32, types: &TypeFactory) -> bool {
        let datatype = types.get(dt);
        match datatype.get_metatype() {
            TypeMetatype::Unknown
            | TypeMetatype::Int
            | TypeMetatype::Uint
            | TypeMetatype::Bool
            | TypeMetatype::Code
            | TypeMetatype::Float
            | TypeMetatype::Ptr
            | TypeMetatype::PtrRel => {
                if datatype.get_metatype() == TypeMetatype::Unknown {
                    self.flags |= PrimitiveExtractor::UNKNOWN_ELEMENT;
                }
                if self.primitives.len() as i32 >= max {
                    return false;
                }
                self.primitives.push(Primitive::new(dt, offset));
                return true;
            }
            TypeMetatype::Array => {
                let num_els = datatype.num_elements();
                let base = datatype.get_base();
                let mut offset = offset;
                for _ in 0..num_els {
                    if !self.extract(base, max, offset, types) {
                        return false;
                    }
                    offset += types.get(base).get_align_size();
                }
                return true;
            }
            TypeMetatype::Union => {
                return self.handle_union(dt, max, offset, types);
            }
            TypeMetatype::Struct => {}
            _ => return false,
        }
        let mut expected_off = offset;
        for field in datatype.get_fields() {
            let comp_dt = field.tp;
            let cur_off = field.offset + offset;
            let align = types.get(comp_dt).get_alignment();
            if cur_off % align != 0 {
                self.flags |= PrimitiveExtractor::UNALIGNED;
            }
            let rem = expected_off % align;
            if rem != 0 {
                expected_off += align - rem;
            }
            if expected_off != cur_off {
                self.flags |= PrimitiveExtractor::EXTRA_SPACE;
            }
            if !self.extract(comp_dt, max, cur_off, types) {
                return false;
            }
            expected_off = cur_off + types.get(comp_dt).get_align_size();
        }
        true
    }

    pub fn size(&self) -> i32 {
        self.primitives.len() as i32
    }

    pub fn get(&self, index: i32) -> &Primitive {
        &self.primitives[index as usize]
    }

    pub fn is_valid(&self) -> bool {
        (self.flags & PrimitiveExtractor::INVALID) == 0
    }

    pub fn contains_unknown(&self) -> bool {
        (self.flags & PrimitiveExtractor::UNKNOWN_ELEMENT) != 0
    }

    pub fn is_aligned(&self) -> bool {
        (self.flags & PrimitiveExtractor::UNALIGNED) == 0
    }

    pub fn contains_holes(&self) -> bool {
        (self.flags & PrimitiveExtractor::EXTRA_SPACE) != 0
    }
}

pub trait DatatypeFilter: Send {
    fn clone_filter(&self) -> Box<dyn DatatypeFilter>;

    fn filter(&self, dt: TypeId, types: &TypeFactory) -> bool;

    fn decode(&mut self, decoder: &mut dyn Decoder) -> Result<()>;
}

pub fn decode_datatype_filter(decoder: &mut dyn Decoder) -> Result<Box<dyn DatatypeFilter>> {
    let elem_id = decoder.open_element_expect(ELEM_DATATYPE)?;
    let name = decoder.read_string_attr(ATTRIB_NAME)?;
    let mut filter: Box<dyn DatatypeFilter> = if name == "any" {
        Box::new(SizeRestrictedFilter::new_default())
    } else if name == "homogeneous-float-aggregate" {
        Box::new(HomogeneousAggregate::new_sized(TypeMetatype::Float, 4, 0, 0))
    } else {
        let meta = string2metatype(&name)?;
        Box::new(MetaTypeFilter::new(meta))
    };
    filter.decode(decoder)?;
    decoder.close_element(elem_id)?;
    Ok(filter)
}

#[derive(Clone, Debug, Default)]
pub struct SizeRestrictedFilter {
    min_size: i32,
    max_size: i32,
    sizes: BTreeSet<i32>,
}

impl SizeRestrictedFilter {
    pub fn new_default() -> SizeRestrictedFilter {
        SizeRestrictedFilter {
            min_size: 0,
            max_size: 0,
            sizes: BTreeSet::new(),
        }
    }

    pub fn new(min: i32, max: i32) -> SizeRestrictedFilter {
        let mut filter = SizeRestrictedFilter {
            min_size: min,
            max_size: max,
            sizes: BTreeSet::new(),
        };
        if filter.max_size == 0 && filter.min_size >= 0 {
            filter.max_size = 0x7fffffff;
        }
        filter
    }

    pub fn init_from_size_list(&mut self, text: &str) -> Result<()> {
        let bytes = text.as_bytes();
        let is_space = |byte: u8| matches!(byte, b' ' | b'\t' | b'\n' | 0x0b | 0x0c | b'\r');
        let mut pos = 0usize;
        let mut stream_failed = false;
        loop {
            let mut val: i32 = -1;
            if !stream_failed {
                while pos < bytes.len() && is_space(bytes[pos]) {
                    pos += 1;
                }
                if pos >= bytes.len() {
                    break;
                }
                if bytes[pos] == b',' {
                    pos += 1;
                    while pos < bytes.len() && is_space(bytes[pos]) {
                        pos += 1;
                    }
                }
                match extract_i32(&text[pos..], Basefield::Dec) {
                    None => {
                        val = 0;
                        pos = bytes.len();
                        stream_failed = true;
                    }
                    Some(extraction) => {
                        val = extraction.value as u32 as i32;
                        pos += extraction.consumed;
                        if extraction.failed {
                            stream_failed = true;
                            if pos >= bytes.len() && val > 0 {
                                self.sizes.insert(val);
                                break;
                            }
                        }
                    }
                }
            }
            if val <= 0 {
                return Err(Error::Decoder("Bad filter size".to_string()));
            }
            self.sizes.insert(val);
        }
        if let (Some(first), Some(last)) = (self.sizes.first(), self.sizes.last()) {
            self.min_size = *first;
            self.max_size = *last;
        }
        Ok(())
    }

    pub fn filter_on_size(&self, dt: TypeId, types: &TypeFactory) -> bool {
        if self.max_size == 0 {
            return true;
        }
        let size = types.get(dt).get_size();
        if !self.sizes.is_empty() {
            return self.sizes.contains(&size);
        }
        size >= self.min_size && size <= self.max_size
    }

    fn decode_sizes(&mut self, decoder: &mut dyn Decoder) -> Result<()> {
        loop {
            let attrib_id = decoder.get_next_attribute_id()?;
            if attrib_id == 0 {
                break;
            }
            if attrib_id == ATTRIB_MINSIZE {
                if !self.sizes.is_empty() {
                    return Err(Error::Decoder(
                        "Mixing \"sizes\" with \"minsize\" and \"maxsize\"".to_string(),
                    ));
                }
                self.min_size = decoder.read_unsigned_integer()? as i32;
            } else if attrib_id == ATTRIB_MAXSIZE {
                if !self.sizes.is_empty() {
                    return Err(Error::Decoder(
                        "Mixing \"sizes\" with \"minsize\" and \"maxsize\"".to_string(),
                    ));
                }
                self.max_size = decoder.read_unsigned_integer()? as i32;
            } else if attrib_id == ATTRIB_SIZES {
                if self.min_size != 0 || self.max_size != 0 {
                    return Err(Error::Decoder(
                        "Mixing \"sizes\" with \"minsize\" and \"maxsize\"".to_string(),
                    ));
                }
                let size_list = decoder.read_string()?;
                self.init_from_size_list(&size_list)?;
            }
        }
        if self.max_size == 0 && self.min_size >= 0 {
            self.max_size = 0x7fffffff;
        }
        Ok(())
    }
}

impl DatatypeFilter for SizeRestrictedFilter {
    fn clone_filter(&self) -> Box<dyn DatatypeFilter> {
        Box::new(self.clone())
    }

    fn filter(&self, dt: TypeId, types: &TypeFactory) -> bool {
        self.filter_on_size(dt, types)
    }

    fn decode(&mut self, decoder: &mut dyn Decoder) -> Result<()> {
        self.decode_sizes(decoder)
    }
}

#[derive(Clone, Debug)]
pub struct MetaTypeFilter {
    base: SizeRestrictedFilter,
    meta_type: TypeMetatype,
}

impl MetaTypeFilter {
    pub fn new(meta: TypeMetatype) -> MetaTypeFilter {
        MetaTypeFilter {
            base: SizeRestrictedFilter::new_default(),
            meta_type: meta,
        }
    }

    pub fn new_sized(meta: TypeMetatype, min: i32, max: i32) -> MetaTypeFilter {
        MetaTypeFilter {
            base: SizeRestrictedFilter::new(min, max),
            meta_type: meta,
        }
    }
}

impl DatatypeFilter for MetaTypeFilter {
    fn clone_filter(&self) -> Box<dyn DatatypeFilter> {
        Box::new(self.clone())
    }

    fn filter(&self, dt: TypeId, types: &TypeFactory) -> bool {
        if types.get(dt).get_metatype() != self.meta_type {
            return false;
        }
        self.base.filter_on_size(dt, types)
    }

    fn decode(&mut self, decoder: &mut dyn Decoder) -> Result<()> {
        self.base.decode_sizes(decoder)
    }
}

#[derive(Clone, Debug)]
pub struct HomogeneousAggregate {
    base: SizeRestrictedFilter,
    meta_type: TypeMetatype,
    max_primitives: i32,
}

impl HomogeneousAggregate {
    pub fn new(meta: TypeMetatype) -> HomogeneousAggregate {
        HomogeneousAggregate {
            base: SizeRestrictedFilter::new_default(),
            meta_type: meta,
            max_primitives: 4,
        }
    }

    pub fn new_sized(meta: TypeMetatype, max_prim: i32, min_size: i32, max_size: i32) -> HomogeneousAggregate {
        HomogeneousAggregate {
            base: SizeRestrictedFilter::new(min_size, max_size),
            meta_type: meta,
            max_primitives: max_prim,
        }
    }
}

impl DatatypeFilter for HomogeneousAggregate {
    fn clone_filter(&self) -> Box<dyn DatatypeFilter> {
        Box::new(self.clone())
    }

    fn filter(&self, dt: TypeId, types: &TypeFactory) -> bool {
        let meta = types.get(dt).get_metatype();
        if meta != TypeMetatype::Array && meta != TypeMetatype::Struct {
            return false;
        }
        let primitives = PrimitiveExtractor::new(dt, true, 0, self.max_primitives, types);
        if !primitives.is_valid()
            || primitives.size() == 0
            || primitives.contains_unknown()
            || !primitives.is_aligned()
            || primitives.contains_holes()
        {
            return false;
        }
        let base = primitives.get(0).dt;
        if types.get(base).get_metatype() != self.meta_type {
            return false;
        }
        for index in 1..primitives.size() {
            if primitives.get(index).dt != base {
                return false;
            }
        }
        true
    }

    fn decode(&mut self, decoder: &mut dyn Decoder) -> Result<()> {
        self.base.decode_sizes(decoder)?;
        decoder.rewind_attributes();
        loop {
            let attrib_id = decoder.get_next_attribute_id()?;
            if attrib_id == 0 {
                break;
            }
            if attrib_id == ATTRIB_MAX_PRIMITIVES {
                let xml_max_prim = decoder.read_unsigned_integer()? as u32;
                if xml_max_prim > 0 {
                    self.max_primitives = xml_max_prim as i32;
                }
            }
        }
        Ok(())
    }
}

pub trait QualifierFilter: Send {
    fn clone_filter(&self) -> Box<dyn QualifierFilter>;

    fn filter(&self, proto: &PrototypePieces, pos: i32, types: &TypeFactory) -> bool;

    fn decode(&mut self, _decoder: &mut dyn Decoder) -> Result<()> {
        Ok(())
    }
}

pub fn decode_qualifier_filter(decoder: &mut dyn Decoder) -> Result<Option<Box<dyn QualifierFilter>>> {
    let elem_id = decoder.peek_element()?;
    let mut filter: Box<dyn QualifierFilter> = if elem_id == ELEM_VARARGS {
        Box::new(VarargsFilter::new())
    } else if elem_id == ELEM_POSITION {
        Box::new(PositionMatchFilter::new(-1))
    } else if elem_id == ELEM_DATATYPE_AT {
        Box::new(DatatypeMatchFilter::new())
    } else {
        return Ok(None);
    };
    filter.decode(decoder)?;
    Ok(Some(filter))
}

pub struct AndFilter {
    sub_qualifiers: Vec<Box<dyn QualifierFilter>>,
}

impl AndFilter {
    pub fn new(filters: Vec<Box<dyn QualifierFilter>>) -> AndFilter {
        AndFilter {
            sub_qualifiers: filters,
        }
    }
}

impl QualifierFilter for AndFilter {
    fn clone_filter(&self) -> Box<dyn QualifierFilter> {
        let new_filters: Vec<Box<dyn QualifierFilter>> =
            self.sub_qualifiers.iter().map(|filter| filter.clone_filter()).collect();
        Box::new(AndFilter::new(new_filters))
    }

    fn filter(&self, proto: &PrototypePieces, pos: i32, types: &TypeFactory) -> bool {
        for filter in &self.sub_qualifiers {
            if !filter.filter(proto, pos, types) {
                return false;
            }
        }
        true
    }

    fn decode(&mut self, _decoder: &mut dyn Decoder) -> Result<()> {
        Ok(())
    }
}

#[derive(Clone, Debug)]
pub struct VarargsFilter {
    first_pos: i32,
    last_pos: i32,
}

impl VarargsFilter {
    pub fn new() -> VarargsFilter {
        VarargsFilter {
            first_pos: i32::MIN,
            last_pos: i32::MAX,
        }
    }

    pub fn new_range(first: i32, last: i32) -> VarargsFilter {
        VarargsFilter {
            first_pos: first,
            last_pos: last,
        }
    }
}

impl Default for VarargsFilter {
    fn default() -> VarargsFilter {
        VarargsFilter::new()
    }
}

impl QualifierFilter for VarargsFilter {
    fn clone_filter(&self) -> Box<dyn QualifierFilter> {
        Box::new(VarargsFilter::new_range(self.first_pos, self.last_pos))
    }

    fn filter(&self, proto: &PrototypePieces, pos: i32, _types: &TypeFactory) -> bool {
        if proto.first_var_arg_slot < 0 {
            return false;
        }
        let pos = pos.wrapping_sub(proto.first_var_arg_slot);
        pos >= self.first_pos && pos <= self.last_pos
    }

    fn decode(&mut self, decoder: &mut dyn Decoder) -> Result<()> {
        let elem_id = decoder.open_element_expect(ELEM_VARARGS)?;
        loop {
            let attrib_id = decoder.get_next_attribute_id()?;
            if attrib_id == 0 {
                break;
            }
            if attrib_id == ATTRIB_FIRST {
                self.first_pos = decoder.read_signed_integer()? as i32;
            } else if attrib_id == ATTRIB_LAST {
                self.last_pos = decoder.read_signed_integer()? as i32;
            }
        }
        decoder.close_element(elem_id)?;
        Ok(())
    }
}

#[derive(Clone, Debug)]
pub struct PositionMatchFilter {
    position: i32,
}

impl PositionMatchFilter {
    pub fn new(pos: i32) -> PositionMatchFilter {
        PositionMatchFilter { position: pos }
    }
}

impl QualifierFilter for PositionMatchFilter {
    fn clone_filter(&self) -> Box<dyn QualifierFilter> {
        Box::new(PositionMatchFilter::new(self.position))
    }

    fn filter(&self, _proto: &PrototypePieces, pos: i32, _types: &TypeFactory) -> bool {
        pos == self.position
    }

    fn decode(&mut self, decoder: &mut dyn Decoder) -> Result<()> {
        let elem_id = decoder.open_element_expect(ELEM_POSITION)?;
        self.position = decoder.read_signed_integer_attr(ATTRIB_INDEX)? as i32;
        decoder.close_element(elem_id)?;
        Ok(())
    }
}

pub struct DatatypeMatchFilter {
    position: i32,
    type_filter: Option<Box<dyn DatatypeFilter>>,
}

impl DatatypeMatchFilter {
    pub fn new() -> DatatypeMatchFilter {
        DatatypeMatchFilter {
            position: -1,
            type_filter: None,
        }
    }
}

impl Default for DatatypeMatchFilter {
    fn default() -> DatatypeMatchFilter {
        DatatypeMatchFilter::new()
    }
}

impl QualifierFilter for DatatypeMatchFilter {
    fn clone_filter(&self) -> Box<dyn QualifierFilter> {
        Box::new(DatatypeMatchFilter {
            position: self.position,
            type_filter: Some(
                self.type_filter
                    .as_ref()
                    .expect("datatype match filter has no type filter")
                    .clone_filter(),
            ),
        })
    }

    fn filter(&self, proto: &PrototypePieces, _pos: i32, types: &TypeFactory) -> bool {
        let dt = if self.position < 0 {
            proto.outtype.expect("prototype pieces have no output data-type")
        } else {
            if self.position as usize >= proto.intypes.len() {
                return false;
            }
            proto.intypes[self.position as usize]
        };
        self.type_filter
            .as_ref()
            .expect("datatype match filter has no type filter")
            .filter(dt, types)
    }

    fn decode(&mut self, decoder: &mut dyn Decoder) -> Result<()> {
        let elem_id = decoder.open_element_expect(ELEM_DATATYPE_AT)?;
        self.position = decoder.read_signed_integer_attr(ATTRIB_INDEX)? as i32;
        self.type_filter = Some(decode_datatype_filter(decoder)?);
        decoder.close_element(elem_id)?;
        Ok(())
    }
}

pub const SUCCESS: u32 = 0;
pub const FAIL: u32 = 1;
pub const NO_ASSIGNMENT: u32 = 2;
pub const HIDDENRET_PTRPARAM: u32 = 3;
pub const HIDDENRET_SPECIALREG: u32 = 4;
pub const HIDDENRET_SPECIALREG_VOID: u32 = 5;

#[derive(Clone, Copy, Debug, Default)]
pub struct AssignActionBase {
    pub fillin_output_active: bool,
}

pub struct AssignEnv<'a> {
    pub manager: &'a AddrSpaceManager,
    pub translate: &'a dyn Translate,
}

pub trait AssignAction: Send {
    fn base(&self) -> &AssignActionBase;

    fn base_mut(&mut self) -> &mut AssignActionBase;

    fn can_affect_fillin_output(&self) -> bool {
        self.base().fillin_output_active
    }

    fn clone_action(&self, new_resource: &ParamListStandard) -> Result<Box<dyn AssignAction>>;

    fn assign_address(
        &self,
        dt: TypeId,
        proto: &PrototypePieces,
        pos: i32,
        tlist: &mut TypeFactory,
        status: &mut Vec<i32>,
        res: &mut ParameterPieces,
        resource: &ParamListStandard,
        env: &AssignEnv<'_>,
    ) -> Result<u32>;

    fn fillin_output_map(&self, _active: &mut ParamActive, _resource: &ParamListStandard) -> bool {
        false
    }

    fn decode(&mut self, decoder: &mut dyn Decoder, resource: &ParamListStandard) -> Result<()>;
}

pub fn decode_action(decoder: &mut dyn Decoder, res: &ParamListStandard) -> Result<Box<dyn AssignAction>> {
    let elem_id = decoder.peek_element()?;
    let mut action: Box<dyn AssignAction> = if elem_id == ELEM_GOTO_STACK {
        Box::new(GotoStack::new_with_value(res, 0))
    } else if elem_id == ELEM_JOIN {
        Box::new(MultiSlotAssign::new(res))
    } else if elem_id == ELEM_CONSUME {
        Box::new(ConsumeAs::new(TypeClass::General, res))
    } else if elem_id == ELEM_CONVERT_TO_PTR {
        Box::new(ConvertToPointer::new(res))
    } else if elem_id == ELEM_HIDDEN_RETURN {
        Box::new(HiddenReturnAssign::new(res, HIDDENRET_SPECIALREG))
    } else if elem_id == ELEM_JOIN_PER_PRIMITIVE {
        Box::new(MultiMemberAssign::new(
            TypeClass::General,
            false,
            res.is_big_endian(),
            res,
        ))
    } else if elem_id == ELEM_JOIN_DUAL_CLASS {
        Box::new(MultiSlotDualAssign::new(res))
    } else {
        return Err(Error::Decoder("Expecting model rule action".to_string()));
    };
    action.decode(decoder, res)?;
    Ok(action)
}

pub fn decode_precondition(
    decoder: &mut dyn Decoder,
    res: &ParamListStandard,
) -> Result<Option<Box<dyn AssignAction>>> {
    let elem_id = decoder.peek_element()?;
    let mut action: Box<dyn AssignAction> = if elem_id == ELEM_CONSUME_EXTRA {
        Box::new(ConsumeExtra::new(res))
    } else {
        return Ok(None);
    };
    action.decode(decoder, res)?;
    Ok(Some(action))
}

pub fn decode_sideeffect(decoder: &mut dyn Decoder, res: &ParamListStandard) -> Result<Box<dyn AssignAction>> {
    let elem_id = decoder.peek_element()?;
    let mut action: Box<dyn AssignAction> = if elem_id == ELEM_CONSUME_EXTRA {
        Box::new(ConsumeExtra::new(res))
    } else if elem_id == ELEM_EXTRA_STACK {
        Box::new(ExtraStack::new(res))
    } else if elem_id == ELEM_CONSUME_REMAINING {
        Box::new(ConsumeRemaining::new(res))
    } else {
        return Err(Error::Decoder("Expecting model rule sideeffect".to_string()));
    };
    action.decode(decoder, res)?;
    Ok(action)
}

pub fn justify_pieces(
    pieces: &mut [VarnodeData],
    offset: i32,
    is_big_endian: bool,
    consume_most_sig: bool,
    justify_right: bool,
) {
    let add_offset = is_big_endian ^ consume_most_sig ^ justify_right;
    let pos = if justify_right { 0 } else { pieces.len() - 1 };
    let vndata = &mut pieces[pos];
    if add_offset {
        vndata.offset = vndata.offset.wrapping_add(offset as i64 as u64);
    }
    vndata.size = vndata.size.wrapping_sub(offset as u32);
}

fn piece_from_address(addr: &crate::address::Address, size: i32) -> VarnodeData {
    VarnodeData {
        space: addr.get_space().cloned(),
        offset: addr.get_offset(),
        size: size as u32,
    }
}

pub struct GotoStack {
    base: AssignActionBase,
    stack_entry: Option<usize>,
}

impl GotoStack {
    pub fn initialize_entry(&mut self, resource: &ParamListStandard) -> Result<()> {
        self.stack_entry = resource.get_stack_entry();
        if self.stack_entry.is_none() {
            return Err(Error::Lowlevel(
                "Cannot find matching <pentry> for action: goto_stack".to_string(),
            ));
        }
        Ok(())
    }

    pub fn new_with_value(_res: &ParamListStandard, _val: i32) -> GotoStack {
        GotoStack {
            base: AssignActionBase {
                fillin_output_active: true,
            },
            stack_entry: None,
        }
    }

    pub fn new(res: &ParamListStandard) -> Result<GotoStack> {
        let mut action = GotoStack {
            base: AssignActionBase {
                fillin_output_active: true,
            },
            stack_entry: None,
        };
        action.initialize_entry(res)?;
        Ok(action)
    }
}

impl AssignAction for GotoStack {
    fn base(&self) -> &AssignActionBase {
        &self.base
    }

    fn base_mut(&mut self) -> &mut AssignActionBase {
        &mut self.base
    }

    fn clone_action(&self, new_resource: &ParamListStandard) -> Result<Box<dyn AssignAction>> {
        Ok(Box::new(GotoStack::new(new_resource)?))
    }

    fn assign_address(
        &self,
        dt: TypeId,
        _proto: &PrototypePieces,
        _pos: i32,
        tlist: &mut TypeFactory,
        status: &mut Vec<i32>,
        res: &mut ParameterPieces,
        resource: &ParamListStandard,
        env: &AssignEnv<'_>,
    ) -> Result<u32> {
        let stack_entry = &resource.get_entry()[self.stack_entry.expect("goto_stack action has no stack entry")];
        let grp = stack_entry.get_group();
        res.tp = Some(dt);
        let datatype = tlist.get(dt);
        res.addr = stack_entry.get_addr_by_slot(
            &mut status[grp as usize],
            datatype.get_size(),
            datatype.get_alignment(),
            env.manager,
        )?;
        res.flags = 0;
        Ok(SUCCESS)
    }

    fn fillin_output_map(&self, active: &mut ParamActive, _resource: &ParamListStandard) -> bool {
        let mut count = 0;
        for index in 0..active.get_num_trials() {
            let trial = active.get_trial(index);
            let Some(entry) = trial.get_entry() else {
                break;
            };
            if Some(entry) != self.stack_entry {
                return false;
            }
            count += 1;
            if count > 1 {
                return false;
            }
        }
        count == 1
    }

    fn decode(&mut self, decoder: &mut dyn Decoder, resource: &ParamListStandard) -> Result<()> {
        let elem_id = decoder.open_element_expect(ELEM_GOTO_STACK)?;
        decoder.close_element(elem_id)?;
        self.initialize_entry(resource)
    }
}

pub struct ConvertToPointer {
    base: AssignActionBase,
    space: Option<SpaceRef>,
}

impl ConvertToPointer {
    pub fn new(res: &ParamListStandard) -> ConvertToPointer {
        ConvertToPointer {
            base: AssignActionBase::default(),
            space: res.get_spacebase().cloned(),
        }
    }
}

impl AssignAction for ConvertToPointer {
    fn base(&self) -> &AssignActionBase {
        &self.base
    }

    fn base_mut(&mut self) -> &mut AssignActionBase {
        &mut self.base
    }

    fn clone_action(&self, new_resource: &ParamListStandard) -> Result<Box<dyn AssignAction>> {
        Ok(Box::new(ConvertToPointer::new(new_resource)))
    }

    fn assign_address(
        &self,
        dt: TypeId,
        proto: &PrototypePieces,
        pos: i32,
        tlist: &mut TypeFactory,
        status: &mut Vec<i32>,
        res: &mut ParameterPieces,
        resource: &ParamListStandard,
        env: &AssignEnv<'_>,
    ) -> Result<u32> {
        let spc = match &self.space {
            Some(spc) => spc.clone(),
            None => env.manager.get_default_data_space().expect("no default data space"),
        };
        let pointersize = spc.get_addr_size() as i32;
        let wordsize = spc.get_word_size();
        let pointertp = tlist.get_type_pointer(pointersize, dt, wordsize)?;
        let response_code = resource.assign_address(pointertp, proto, pos, tlist, status, res, env)?;
        res.flags = ParameterPieces::INDIRECTSTORAGE;
        Ok(response_code)
    }

    fn decode(&mut self, decoder: &mut dyn Decoder, _resource: &ParamListStandard) -> Result<()> {
        let elem_id = decoder.open_element_expect(ELEM_CONVERT_TO_PTR)?;
        decoder.close_element(elem_id)?;
        Ok(())
    }
}

pub struct MultiSlotAssign {
    base: AssignActionBase,
    resource_type: TypeClass,
    is_big_endian: bool,
    consume_from_stack: bool,
    consume_most_sig: bool,
    enforce_alignment: bool,
    justify_right: bool,
    tiles: Vec<usize>,
    stack_entry: Option<usize>,
}

impl MultiSlotAssign {
    pub fn initialize_entries(&mut self, resource: &ParamListStandard) -> Result<()> {
        resource.extract_tiles(&mut self.tiles, self.resource_type);
        self.stack_entry = resource.get_stack_entry();
        if self.tiles.is_empty() {
            return Err(Error::Lowlevel(
                "Could not find matching resources for action: join".to_string(),
            ));
        }
        if self.consume_from_stack && self.stack_entry.is_none() {
            return Err(Error::Lowlevel(
                "Cannot find matching <pentry> for action: join".to_string(),
            ));
        }
        Ok(())
    }

    pub fn new(res: &ParamListStandard) -> MultiSlotAssign {
        let is_big_endian = res.is_big_endian();
        let list_type = res.get_type();
        let mut action = MultiSlotAssign {
            base: AssignActionBase {
                fillin_output_active: true,
            },
            resource_type: TypeClass::General,
            is_big_endian,
            consume_from_stack: list_type != P_REGISTER_OUT && list_type != P_STANDARD_OUT,
            consume_most_sig: false,
            enforce_alignment: false,
            justify_right: false,
            tiles: Vec::new(),
            stack_entry: None,
        };
        if is_big_endian {
            action.consume_most_sig = true;
            action.justify_right = true;
        }
        action
    }

    pub fn new_with(
        store: TypeClass,
        stack: bool,
        most_sig: bool,
        align: bool,
        just_right: bool,
        res: &ParamListStandard,
    ) -> Result<MultiSlotAssign> {
        let mut action = MultiSlotAssign {
            base: AssignActionBase {
                fillin_output_active: true,
            },
            resource_type: store,
            is_big_endian: res.is_big_endian(),
            consume_from_stack: stack,
            consume_most_sig: most_sig,
            enforce_alignment: align,
            justify_right: just_right,
            tiles: Vec::new(),
            stack_entry: None,
        };
        action.initialize_entries(res)?;
        Ok(action)
    }
}

fn fillin_join_output_map(
    active: &mut ParamActive,
    resource_filter: impl Fn(TypeClass) -> bool,
    justify_right: bool,
    consume_most_sig: bool,
    adopt_first_type: bool,
) -> bool {
    let mut count = 0;
    let mut cur_group = -1;
    let mut partial: i32 = -1;
    let mut resource_type = TypeClass::General;
    for index in 0..active.get_num_trials() {
        let trial = active.get_trial(index);
        let Some(entry) = trial.get_entry_data() else {
            break;
        };
        if adopt_first_type {
            if count == 0 {
                resource_type = entry.get_type();
                if !resource_filter(resource_type) {
                    return false;
                }
            } else if entry.get_type() != resource_type {
                return false;
            }
        } else if !resource_filter(entry.get_type()) {
            return false;
        }
        if count == 0 {
            if !entry.is_first_in_class() {
                return false;
            }
        } else if entry.get_group() != cur_group + 1 {
            return false;
        }
        cur_group = entry.get_group();
        if trial.get_size() != entry.get_size() {
            if partial != -1 {
                return false;
            }
            partial = index;
        }
        count += 1;
    }
    if partial != -1 {
        if justify_right {
            if partial != 0 {
                return false;
            }
        } else if partial != count - 1 {
            return false;
        }
        let trial = active.get_trial(partial);
        if justify_right == consume_most_sig {
            if trial.get_offset() != 0 {
                return false;
            }
        } else {
            let entry_size = trial
                .get_entry_data()
                .expect("partial trial has no param entry")
                .get_size();
            if trial.get_offset() + trial.get_size() != entry_size {
                return false;
            }
        }
    }
    if count == 0 {
        return false;
    }
    if consume_most_sig {
        active.set_join_reverse();
    }
    true
}

impl AssignAction for MultiSlotAssign {
    fn base(&self) -> &AssignActionBase {
        &self.base
    }

    fn base_mut(&mut self) -> &mut AssignActionBase {
        &mut self.base
    }

    fn clone_action(&self, new_resource: &ParamListStandard) -> Result<Box<dyn AssignAction>> {
        Ok(Box::new(MultiSlotAssign::new_with(
            self.resource_type,
            self.consume_from_stack,
            self.consume_most_sig,
            self.enforce_alignment,
            self.justify_right,
            new_resource,
        )?))
    }

    fn assign_address(
        &self,
        dt: TypeId,
        _proto: &PrototypePieces,
        _pos: i32,
        tlist: &mut TypeFactory,
        status: &mut Vec<i32>,
        res: &mut ParameterPieces,
        resource: &ParamListStandard,
        env: &AssignEnv<'_>,
    ) -> Result<u32> {
        let entries = resource.get_entry();
        let mut tmp_status = status.clone();
        let mut pieces: Vec<VarnodeData> = Vec::new();
        let dt_size = tlist.get(dt).get_size();
        let mut size_left = dt_size;
        let mut align = tlist.get(dt).get_alignment();
        let mut iter = 0usize;
        if self.enforce_alignment {
            let mut resources_consumed = 0;
            while iter != self.tiles.len() {
                let entry = &entries[self.tiles[iter]];
                if tmp_status[entry.get_group() as usize] == 0 {
                    let reg_size = entry.get_size();
                    if align <= reg_size || (resources_consumed % align) == 0 {
                        break;
                    }
                    tmp_status[entry.get_group() as usize] = -1;
                }
                resources_consumed += entry.get_size();
                iter += 1;
            }
        }
        while size_left > 0 && iter != self.tiles.len() {
            let entry = &entries[self.tiles[iter]];
            iter += 1;
            if tmp_status[entry.get_group() as usize] != 0 {
                continue;
            }
            let trial_size = entry.get_size();
            let addr = entry.get_addr_by_slot(
                &mut tmp_status[entry.get_group() as usize],
                trial_size,
                align,
                env.manager,
            )?;
            tmp_status[entry.get_group() as usize] = -1;
            pieces.push(piece_from_address(&addr, trial_size));
            size_left -= trial_size;
            align = 1;
        }
        if size_left > 0 {
            if !self.consume_from_stack {
                return Ok(FAIL);
            }
            let stack_entry = &entries[self.stack_entry.expect("join action has no stack entry")];
            let grp = stack_entry.get_group();
            let addr = stack_entry.get_addr_by_slot_justified(
                &mut tmp_status[grp as usize],
                size_left,
                align,
                self.justify_right,
                env.manager,
            )?;
            if addr.is_invalid() {
                return Ok(FAIL);
            }
            pieces.push(piece_from_address(&addr, size_left));
        } else if size_left < 0 {
            if self.resource_type == TypeClass::Float && pieces.len() == 1 {
                let tmp = &mut pieces[0];
                let addr = env
                    .manager
                    .construct_float_extension_address(&tmp.get_addr(), tmp.size as i32, dt_size)?;
                tmp.space = addr.get_space().cloned();
                tmp.offset = addr.get_offset();
                tmp.size = dt_size as u32;
            } else {
                justify_pieces(
                    &mut pieces,
                    -size_left,
                    self.is_big_endian,
                    self.consume_most_sig,
                    self.justify_right,
                );
            }
        }
        *status = tmp_status;
        res.flags = 0;
        res.tp = Some(dt);
        res.assign_address_from_pieces(&mut pieces, self.consume_most_sig, env.manager, env.translate)?;
        Ok(SUCCESS)
    }

    fn fillin_output_map(&self, active: &mut ParamActive, _resource: &ParamListStandard) -> bool {
        let resource_type = self.resource_type;
        fillin_join_output_map(
            active,
            |tp| tp == resource_type,
            self.justify_right,
            self.consume_most_sig,
            false,
        )
    }

    fn decode(&mut self, decoder: &mut dyn Decoder, resource: &ParamListStandard) -> Result<()> {
        let elem_id = decoder.open_element_expect(ELEM_JOIN)?;
        loop {
            let attrib_id = decoder.get_next_attribute_id()?;
            if attrib_id == 0 {
                break;
            }
            if attrib_id == ATTRIB_REVERSEJUSTIFY {
                if decoder.read_bool()? {
                    self.justify_right = !self.justify_right;
                }
            } else if attrib_id == ATTRIB_REVERSESIGNIF {
                if decoder.read_bool()? {
                    self.consume_most_sig = !self.consume_most_sig;
                }
            } else if attrib_id == ATTRIB_STORAGE {
                self.resource_type = string2typeclass(&decoder.read_string()?)?;
            } else if attrib_id == ATTRIB_ALIGN {
                self.enforce_alignment = decoder.read_bool()?;
            } else if attrib_id == ATTRIB_STACKSPILL {
                self.consume_from_stack = decoder.read_bool()?;
            }
        }
        decoder.close_element(elem_id)?;
        self.initialize_entries(resource)
    }
}

pub struct MultiMemberAssign {
    base: AssignActionBase,
    resource_type: TypeClass,
    consume_from_stack: bool,
    consume_most_sig: bool,
}

impl MultiMemberAssign {
    pub fn new(store: TypeClass, stack: bool, most_sig: bool, _res: &ParamListStandard) -> MultiMemberAssign {
        MultiMemberAssign {
            base: AssignActionBase {
                fillin_output_active: true,
            },
            resource_type: store,
            consume_from_stack: stack,
            consume_most_sig: most_sig,
        }
    }
}

impl AssignAction for MultiMemberAssign {
    fn base(&self) -> &AssignActionBase {
        &self.base
    }

    fn base_mut(&mut self) -> &mut AssignActionBase {
        &mut self.base
    }

    fn clone_action(&self, new_resource: &ParamListStandard) -> Result<Box<dyn AssignAction>> {
        Ok(Box::new(MultiMemberAssign::new(
            self.resource_type,
            self.consume_from_stack,
            self.consume_most_sig,
            new_resource,
        )))
    }

    fn assign_address(
        &self,
        dt: TypeId,
        _proto: &PrototypePieces,
        _pos: i32,
        tlist: &mut TypeFactory,
        status: &mut Vec<i32>,
        res: &mut ParameterPieces,
        resource: &ParamListStandard,
        env: &AssignEnv<'_>,
    ) -> Result<u32> {
        let mut tmp_status = status.clone();
        let mut pieces: Vec<VarnodeData> = Vec::new();
        let primitives = PrimitiveExtractor::new(dt, false, 0, 16, tlist);
        if !primitives.is_valid()
            || primitives.size() == 0
            || primitives.contains_unknown()
            || !primitives.is_aligned()
            || primitives.contains_holes()
        {
            return Ok(FAIL);
        }
        let mut param = ParameterPieces::default();
        for index in 0..primitives.size() {
            let cur_type = primitives.get(index).dt;
            if resource.assign_address_fallback(
                self.resource_type,
                cur_type,
                !self.consume_from_stack,
                &mut tmp_status,
                &mut param,
                tlist,
                env.manager,
            )? == FAIL
            {
                return Ok(FAIL);
            }
            pieces.push(piece_from_address(&param.addr, tlist.get(cur_type).get_size()));
        }
        *status = tmp_status;
        res.flags = 0;
        res.tp = Some(dt);
        res.assign_address_from_pieces(&mut pieces, self.consume_most_sig, env.manager, env.translate)?;
        Ok(SUCCESS)
    }

    fn fillin_output_map(&self, active: &mut ParamActive, _resource: &ParamListStandard) -> bool {
        let mut count = 0;
        let mut cur_group = -1;
        for index in 0..active.get_num_trials() {
            let trial = active.get_trial(index);
            let Some(entry) = trial.get_entry_data() else {
                break;
            };
            if entry.get_type() != self.resource_type {
                return false;
            }
            if count == 0 {
                if !entry.is_first_in_class() {
                    return false;
                }
            } else if entry.get_group() != cur_group + 1 {
                return false;
            }
            cur_group = entry.get_group();
            if trial.get_offset() != 0 {
                return false;
            }
            count += 1;
        }
        if count == 0 {
            return false;
        }
        if self.consume_most_sig {
            active.set_join_reverse();
        }
        true
    }

    fn decode(&mut self, decoder: &mut dyn Decoder, _resource: &ParamListStandard) -> Result<()> {
        let elem_id = decoder.open_element_expect(ELEM_JOIN_PER_PRIMITIVE)?;
        loop {
            let attrib_id = decoder.get_next_attribute_id()?;
            if attrib_id == 0 {
                break;
            }
            if attrib_id == ATTRIB_STORAGE {
                self.resource_type = string2typeclass(&decoder.read_string()?)?;
            }
        }
        decoder.close_element(elem_id)?;
        Ok(())
    }
}

pub struct MultiSlotDualAssign {
    base: AssignActionBase,
    base_type: TypeClass,
    alt_type: TypeClass,
    is_big_endian: bool,
    consume_from_stack: bool,
    consume_most_sig: bool,
    justify_right: bool,
    fill_alternate: bool,
    tile_size: i32,
    base_tiles: Vec<usize>,
    alt_tiles: Vec<usize>,
    stack_entry: Option<usize>,
}

impl MultiSlotDualAssign {
    pub fn initialize_entries(&mut self, resource: &ParamListStandard) -> Result<()> {
        resource.extract_tiles(&mut self.base_tiles, self.base_type);
        resource.extract_tiles(&mut self.alt_tiles, self.alt_type);
        self.stack_entry = resource.get_stack_entry();
        if self.base_tiles.is_empty() || self.alt_tiles.is_empty() {
            return Err(Error::Lowlevel(
                "Could not find matching resources for action: join_dual_class".to_string(),
            ));
        }
        let entries = resource.get_entry();
        self.tile_size = entries[self.base_tiles[0]].get_size();
        if self.tile_size != entries[self.alt_tiles[0]].get_size() {
            return Err(Error::Lowlevel(
                "Storage class register sizes do not match for action: join_dual_class".to_string(),
            ));
        }
        if self.consume_from_stack && self.stack_entry.is_none() {
            return Err(Error::Lowlevel(
                "Cannot find matching stack resource for action: join_dual_class".to_string(),
            ));
        }
        Ok(())
    }

    pub fn get_first_unused(&self, iter: i32, tiles: &[usize], status: &[i32], resource: &ParamListStandard) -> i32 {
        let entries = resource.get_entry();
        let mut iter = iter;
        while (iter as usize) != tiles.len() {
            let entry = &entries[tiles[iter as usize]];
            if status[entry.get_group() as usize] != 0 {
                iter += 1;
                continue;
            }
            return iter;
        }
        tiles.len() as i32
    }

    pub fn get_tile_class(
        &self,
        primitives: &PrimitiveExtractor,
        off: i32,
        index: &mut i32,
        types: &TypeFactory,
    ) -> i32 {
        let mut res = 1;
        let mut count = 0;
        let end_boundary = off + self.tile_size;
        if *index >= primitives.size() {
            return -1;
        }
        let first_primitive = *primitives.get(*index);
        while *index < primitives.size() {
            let element = primitives.get(*index);
            if element.offset < off {
                return -1;
            }
            if element.offset >= end_boundary {
                break;
            }
            if element.offset + types.get(element.dt).get_size() > end_boundary {
                return -1;
            }
            count += 1;
            *index += 1;
            let storage = metatype2typeclass(types.get(element.dt).get_metatype());
            if storage != self.alt_type {
                res = 0;
            }
        }
        if count == 0 {
            return -1;
        }
        if self.fill_alternate {
            if count > 1 {
                res = 0;
            }
            if types.get(first_primitive.dt).get_size() != self.tile_size {
                res = 0;
            }
        }
        res
    }

    pub fn new(res: &ParamListStandard) -> MultiSlotDualAssign {
        let is_big_endian = res.is_big_endian();
        let mut action = MultiSlotDualAssign {
            base: AssignActionBase {
                fillin_output_active: true,
            },
            base_type: TypeClass::General,
            alt_type: TypeClass::Float,
            is_big_endian,
            consume_from_stack: false,
            consume_most_sig: false,
            justify_right: false,
            fill_alternate: false,
            tile_size: 0,
            base_tiles: Vec::new(),
            alt_tiles: Vec::new(),
            stack_entry: None,
        };
        if is_big_endian {
            action.consume_most_sig = true;
            action.justify_right = true;
        }
        action
    }

    pub fn new_with(
        base_store: TypeClass,
        alt_store: TypeClass,
        stack: bool,
        most_sig: bool,
        just_right: bool,
        fill_alt: bool,
        res: &ParamListStandard,
    ) -> Result<MultiSlotDualAssign> {
        let mut action = MultiSlotDualAssign {
            base: AssignActionBase {
                fillin_output_active: true,
            },
            base_type: base_store,
            alt_type: alt_store,
            is_big_endian: res.is_big_endian(),
            consume_from_stack: stack,
            consume_most_sig: most_sig,
            justify_right: just_right,
            fill_alternate: fill_alt,
            tile_size: 0,
            base_tiles: Vec::new(),
            alt_tiles: Vec::new(),
            stack_entry: None,
        };
        action.initialize_entries(res)?;
        Ok(action)
    }
}

impl AssignAction for MultiSlotDualAssign {
    fn base(&self) -> &AssignActionBase {
        &self.base
    }

    fn base_mut(&mut self) -> &mut AssignActionBase {
        &mut self.base
    }

    fn clone_action(&self, new_resource: &ParamListStandard) -> Result<Box<dyn AssignAction>> {
        Ok(Box::new(MultiSlotDualAssign::new_with(
            self.base_type,
            self.alt_type,
            self.consume_from_stack,
            self.consume_most_sig,
            self.justify_right,
            self.fill_alternate,
            new_resource,
        )?))
    }

    fn assign_address(
        &self,
        dt: TypeId,
        _proto: &PrototypePieces,
        _pos: i32,
        tlist: &mut TypeFactory,
        status: &mut Vec<i32>,
        res: &mut ParameterPieces,
        resource: &ParamListStandard,
        env: &AssignEnv<'_>,
    ) -> Result<u32> {
        let entries = resource.get_entry();
        let primitives = PrimitiveExtractor::new(dt, false, 0, 1024, tlist);
        if !primitives.is_valid() || primitives.size() == 0 || primitives.contains_holes() {
            return Ok(FAIL);
        }
        let mut primitive_index = 0;
        let mut tmp_status = status.clone();
        let mut pieces: Vec<VarnodeData> = Vec::new();
        let type_size = tlist.get(dt).get_size();
        let align = tlist.get(dt).get_alignment();
        let mut size_left = type_size;
        let mut iter_base = 0;
        let mut iter_alt = 0;
        while size_left > 0 {
            let iter_type = self.get_tile_class(&primitives, type_size - size_left, &mut primitive_index, tlist);
            if iter_type < 0 {
                return Ok(FAIL);
            }
            let entry = if iter_type == 0 {
                iter_base = self.get_first_unused(iter_base, &self.base_tiles, &tmp_status, resource);
                if iter_base as usize == self.base_tiles.len() {
                    if !self.consume_from_stack {
                        return Ok(FAIL);
                    }
                    break;
                }
                &entries[self.base_tiles[iter_base as usize]]
            } else {
                iter_alt = self.get_first_unused(iter_alt, &self.alt_tiles, &tmp_status, resource);
                if iter_alt as usize == self.alt_tiles.len() {
                    if !self.consume_from_stack {
                        return Ok(FAIL);
                    }
                    break;
                }
                &entries[self.alt_tiles[iter_alt as usize]]
            };
            let trial_size = entry.get_size();
            let addr =
                entry.get_addr_by_slot(&mut tmp_status[entry.get_group() as usize], trial_size, 1, env.manager)?;
            tmp_status[entry.get_group() as usize] = -1;
            pieces.push(piece_from_address(&addr, trial_size));
            size_left -= trial_size;
        }
        if size_left > 0 {
            if !self.consume_from_stack {
                return Ok(FAIL);
            }
            let stack_entry = &entries[self.stack_entry.expect("join_dual_class action has no stack entry")];
            let grp = stack_entry.get_group();
            let addr = stack_entry.get_addr_by_slot_justified(
                &mut tmp_status[grp as usize],
                size_left,
                align,
                self.justify_right,
                env.manager,
            )?;
            if addr.is_invalid() {
                return Ok(FAIL);
            }
            pieces.push(piece_from_address(&addr, size_left));
        }
        if size_left < 0 {
            justify_pieces(
                &mut pieces,
                -size_left,
                self.is_big_endian,
                self.consume_most_sig,
                self.justify_right,
            );
        }
        *status = tmp_status;
        res.flags = 0;
        res.tp = Some(dt);
        res.assign_address_from_pieces(&mut pieces, self.consume_most_sig, env.manager, env.translate)?;
        Ok(SUCCESS)
    }

    fn fillin_output_map(&self, active: &mut ParamActive, _resource: &ParamListStandard) -> bool {
        let base_type = self.base_type;
        let alt_type = self.alt_type;
        fillin_join_output_map(
            active,
            |tp| tp == base_type || tp == alt_type,
            self.justify_right,
            self.consume_most_sig,
            true,
        )
    }

    fn decode(&mut self, decoder: &mut dyn Decoder, resource: &ParamListStandard) -> Result<()> {
        let elem_id = decoder.open_element_expect(ELEM_JOIN_DUAL_CLASS)?;
        loop {
            let attrib_id = decoder.get_next_attribute_id()?;
            if attrib_id == 0 {
                break;
            }
            if attrib_id == ATTRIB_REVERSEJUSTIFY {
                if decoder.read_bool()? {
                    self.justify_right = !self.justify_right;
                }
            } else if attrib_id == ATTRIB_REVERSESIGNIF {
                if decoder.read_bool()? {
                    self.consume_most_sig = !self.consume_most_sig;
                }
            } else if attrib_id == ATTRIB_STORAGE || attrib_id == ATTRIB_A {
                self.base_type = string2typeclass(&decoder.read_string()?)?;
            } else if attrib_id == ATTRIB_B {
                self.alt_type = string2typeclass(&decoder.read_string()?)?;
            } else if attrib_id == ATTRIB_STACKSPILL {
                self.consume_from_stack = decoder.read_bool()?;
            } else if attrib_id == ATTRIB_FILL_ALTERNATE {
                self.fill_alternate = decoder.read_bool()?;
            }
        }
        decoder.close_element(elem_id)?;
        self.initialize_entries(resource)
    }
}

pub struct ConsumeAs {
    base: AssignActionBase,
    resource_type: TypeClass,
}

impl ConsumeAs {
    pub fn new(store: TypeClass, _res: &ParamListStandard) -> ConsumeAs {
        ConsumeAs {
            base: AssignActionBase {
                fillin_output_active: true,
            },
            resource_type: store,
        }
    }
}

impl AssignAction for ConsumeAs {
    fn base(&self) -> &AssignActionBase {
        &self.base
    }

    fn base_mut(&mut self) -> &mut AssignActionBase {
        &mut self.base
    }

    fn clone_action(&self, new_resource: &ParamListStandard) -> Result<Box<dyn AssignAction>> {
        Ok(Box::new(ConsumeAs::new(self.resource_type, new_resource)))
    }

    fn assign_address(
        &self,
        dt: TypeId,
        _proto: &PrototypePieces,
        _pos: i32,
        tlist: &mut TypeFactory,
        status: &mut Vec<i32>,
        res: &mut ParameterPieces,
        resource: &ParamListStandard,
        env: &AssignEnv<'_>,
    ) -> Result<u32> {
        resource.assign_address_fallback(self.resource_type, dt, true, status, res, tlist, env.manager)
    }

    fn fillin_output_map(&self, active: &mut ParamActive, _resource: &ParamListStandard) -> bool {
        let mut count = 0;
        for index in 0..active.get_num_trials() {
            let trial = active.get_trial(index);
            let Some(entry) = trial.get_entry_data() else {
                break;
            };
            if entry.get_type() != self.resource_type {
                return false;
            }
            if !entry.is_first_in_class() {
                return false;
            }
            count += 1;
            if count > 1 {
                return false;
            }
            if trial.get_offset() != 0 {
                return false;
            }
        }
        count > 0
    }

    fn decode(&mut self, decoder: &mut dyn Decoder, _resource: &ParamListStandard) -> Result<()> {
        let elem_id = decoder.open_element_expect(ELEM_CONSUME)?;
        self.resource_type = string2typeclass(&decoder.read_string_attr(ATTRIB_STORAGE)?)?;
        decoder.close_element(elem_id)?;
        Ok(())
    }
}

pub struct HiddenReturnAssign {
    base: AssignActionBase,
    ret_code: u32,
}

impl HiddenReturnAssign {
    pub fn new(_res: &ParamListStandard, code: u32) -> HiddenReturnAssign {
        HiddenReturnAssign {
            base: AssignActionBase::default(),
            ret_code: code,
        }
    }
}

impl AssignAction for HiddenReturnAssign {
    fn base(&self) -> &AssignActionBase {
        &self.base
    }

    fn base_mut(&mut self) -> &mut AssignActionBase {
        &mut self.base
    }

    fn clone_action(&self, new_resource: &ParamListStandard) -> Result<Box<dyn AssignAction>> {
        Ok(Box::new(HiddenReturnAssign::new(new_resource, self.ret_code)))
    }

    fn assign_address(
        &self,
        _dt: TypeId,
        _proto: &PrototypePieces,
        _pos: i32,
        _tlist: &mut TypeFactory,
        _status: &mut Vec<i32>,
        _res: &mut ParameterPieces,
        _resource: &ParamListStandard,
        _env: &AssignEnv<'_>,
    ) -> Result<u32> {
        Ok(self.ret_code)
    }

    fn decode(&mut self, decoder: &mut dyn Decoder, _resource: &ParamListStandard) -> Result<()> {
        self.ret_code = HIDDENRET_SPECIALREG;
        let elem_id = decoder.open_element_expect(ELEM_HIDDEN_RETURN)?;
        loop {
            let attrib_id = decoder.get_next_attribute_id()?;
            if attrib_id == ATTRIB_VOIDLOCK {
                self.ret_code = HIDDENRET_SPECIALREG_VOID;
            } else if attrib_id == ATTRIB_STRATEGY {
                let strategy_string = decoder.read_string()?;
                if strategy_string == "normalparam" {
                    self.ret_code = HIDDENRET_PTRPARAM;
                } else if strategy_string == "special" {
                    self.ret_code = HIDDENRET_SPECIALREG;
                } else {
                    return Err(Error::Decoder(format!(
                        "Bad <hidden_return> strategy: {}",
                        strategy_string
                    )));
                }
            } else {
                break;
            }
        }
        decoder.close_element(elem_id)?;
        Ok(())
    }
}

pub struct ConsumeExtra {
    base: AssignActionBase,
    resource_type: TypeClass,
    match_size: bool,
    tiles: Vec<usize>,
}

impl ConsumeExtra {
    pub fn initialize_entries(&mut self, resource: &ParamListStandard) -> Result<()> {
        resource.extract_tiles(&mut self.tiles, self.resource_type);
        if self.tiles.is_empty() {
            return Err(Error::Lowlevel(
                "Could not find matching resources for action: consume_extra".to_string(),
            ));
        }
        Ok(())
    }

    pub fn new(_res: &ParamListStandard) -> ConsumeExtra {
        ConsumeExtra {
            base: AssignActionBase::default(),
            resource_type: TypeClass::General,
            match_size: true,
            tiles: Vec::new(),
        }
    }

    pub fn new_with(store: TypeClass, matched: bool, res: &ParamListStandard) -> Result<ConsumeExtra> {
        let mut action = ConsumeExtra {
            base: AssignActionBase::default(),
            resource_type: store,
            match_size: matched,
            tiles: Vec::new(),
        };
        action.initialize_entries(res)?;
        Ok(action)
    }
}

impl AssignAction for ConsumeExtra {
    fn base(&self) -> &AssignActionBase {
        &self.base
    }

    fn base_mut(&mut self) -> &mut AssignActionBase {
        &mut self.base
    }

    fn clone_action(&self, new_resource: &ParamListStandard) -> Result<Box<dyn AssignAction>> {
        Ok(Box::new(ConsumeExtra::new_with(
            self.resource_type,
            self.match_size,
            new_resource,
        )?))
    }

    fn assign_address(
        &self,
        dt: TypeId,
        _proto: &PrototypePieces,
        _pos: i32,
        tlist: &mut TypeFactory,
        status: &mut Vec<i32>,
        _res: &mut ParameterPieces,
        resource: &ParamListStandard,
        _env: &AssignEnv<'_>,
    ) -> Result<u32> {
        let entries = resource.get_entry();
        let mut iter = 0usize;
        let mut size_left = tlist.get(dt).get_size();
        while size_left > 0 && iter != self.tiles.len() {
            let entry = &entries[self.tiles[iter]];
            iter += 1;
            if status[entry.get_group() as usize] != 0 {
                continue;
            }
            status[entry.get_group() as usize] = -1;
            size_left -= entry.get_size();
            if !self.match_size {
                break;
            }
        }
        Ok(SUCCESS)
    }

    fn decode(&mut self, decoder: &mut dyn Decoder, resource: &ParamListStandard) -> Result<()> {
        let elem_id = decoder.open_element_expect(ELEM_CONSUME_EXTRA)?;
        loop {
            let attrib_id = decoder.get_next_attribute_id()?;
            if attrib_id == 0 {
                break;
            } else if attrib_id == ATTRIB_STORAGE {
                self.resource_type = string2typeclass(&decoder.read_string()?)?;
            } else if attrib_id == ATTRIB_MATCHSIZE {
                self.match_size = decoder.read_bool()?;
            }
        }
        decoder.close_element(elem_id)?;
        self.initialize_entries(resource)
    }
}

pub struct ExtraStack {
    base: AssignActionBase,
    after_bytes: i32,
    after_storage: TypeClass,
    stack_entry: Option<usize>,
}

impl ExtraStack {
    pub fn initialize_entry(&mut self, resource: &ParamListStandard) -> Result<()> {
        self.stack_entry = resource.get_stack_entry();
        if self.stack_entry.is_none() {
            return Err(Error::Lowlevel(
                "Cannot find matching <pentry> for action: extra_stack".to_string(),
            ));
        }
        Ok(())
    }

    pub fn new(_res: &ParamListStandard) -> ExtraStack {
        ExtraStack {
            base: AssignActionBase::default(),
            after_bytes: -1,
            after_storage: TypeClass::General,
            stack_entry: None,
        }
    }

    pub fn new_with(storage: TypeClass, offset: i32, res: &ParamListStandard) -> Result<ExtraStack> {
        let mut action = ExtraStack {
            base: AssignActionBase::default(),
            after_bytes: offset,
            after_storage: storage,
            stack_entry: None,
        };
        action.initialize_entry(res)?;
        Ok(action)
    }
}

impl AssignAction for ExtraStack {
    fn base(&self) -> &AssignActionBase {
        &self.base
    }

    fn base_mut(&mut self) -> &mut AssignActionBase {
        &mut self.base
    }

    fn clone_action(&self, new_resource: &ParamListStandard) -> Result<Box<dyn AssignAction>> {
        Ok(Box::new(ExtraStack::new_with(
            self.after_storage,
            self.after_bytes,
            new_resource,
        )?))
    }

    fn assign_address(
        &self,
        dt: TypeId,
        _proto: &PrototypePieces,
        _pos: i32,
        tlist: &mut TypeFactory,
        status: &mut Vec<i32>,
        res: &mut ParameterPieces,
        resource: &ParamListStandard,
        env: &AssignEnv<'_>,
    ) -> Result<u32> {
        let entries = resource.get_entry();
        let stack_entry = &entries[self.stack_entry.expect("extra_stack action has no stack entry")];
        let same_space = match (res.addr.get_space(), stack_entry.get_space()) {
            (Some(left), Some(right)) => left.get_index() == right.get_index(),
            (None, None) => true,
            _ => false,
        };
        if same_space {
            return Ok(SUCCESS);
        }
        let grp = stack_entry.get_group();
        if self.after_bytes > 0 {
            let mut bytes_consumed = 0;
            for entry in entries.iter() {
                if entry.get_group() == grp || entry.get_type() != self.after_storage {
                    continue;
                }
                if status[entry.get_group() as usize] != 0 {
                    bytes_consumed += entry.get_size();
                }
            }
            if bytes_consumed < self.after_bytes {
                return Ok(SUCCESS);
            }
        }
        let datatype = tlist.get(dt);
        stack_entry.get_addr_by_slot(
            &mut status[grp as usize],
            datatype.get_size(),
            datatype.get_alignment(),
            env.manager,
        )?;
        Ok(SUCCESS)
    }

    fn decode(&mut self, decoder: &mut dyn Decoder, resource: &ParamListStandard) -> Result<()> {
        let elem_id = decoder.open_element_expect(ELEM_EXTRA_STACK)?;
        loop {
            let attrib_id = decoder.get_next_attribute_id()?;
            if attrib_id == 0 {
                break;
            } else if attrib_id == ATTRIB_AFTER_BYTES {
                self.after_bytes = decoder.read_unsigned_integer()? as i32;
            } else if attrib_id == ATTRIB_AFTER_STORAGE {
                self.after_storage = string2typeclass(&decoder.read_string()?)?;
            }
        }
        decoder.close_element(elem_id)?;
        self.initialize_entry(resource)
    }
}

pub struct ConsumeRemaining {
    base: AssignActionBase,
    resource_type: TypeClass,
    tiles: Vec<usize>,
}

impl ConsumeRemaining {
    pub fn initialize_entries(&mut self, resource: &ParamListStandard) -> Result<()> {
        resource.extract_tiles(&mut self.tiles, self.resource_type);
        if self.tiles.is_empty() {
            return Err(Error::Lowlevel(
                "Could not find matching resources for action: consume_remaining".to_string(),
            ));
        }
        Ok(())
    }

    pub fn new(_res: &ParamListStandard) -> ConsumeRemaining {
        ConsumeRemaining {
            base: AssignActionBase::default(),
            resource_type: TypeClass::General,
            tiles: Vec::new(),
        }
    }

    pub fn new_with(store: TypeClass, res: &ParamListStandard) -> Result<ConsumeRemaining> {
        let mut action = ConsumeRemaining {
            base: AssignActionBase::default(),
            resource_type: store,
            tiles: Vec::new(),
        };
        action.initialize_entries(res)?;
        Ok(action)
    }
}

impl AssignAction for ConsumeRemaining {
    fn base(&self) -> &AssignActionBase {
        &self.base
    }

    fn base_mut(&mut self) -> &mut AssignActionBase {
        &mut self.base
    }

    fn clone_action(&self, new_resource: &ParamListStandard) -> Result<Box<dyn AssignAction>> {
        Ok(Box::new(ConsumeRemaining::new_with(self.resource_type, new_resource)?))
    }

    fn assign_address(
        &self,
        _dt: TypeId,
        _proto: &PrototypePieces,
        _pos: i32,
        _tlist: &mut TypeFactory,
        status: &mut Vec<i32>,
        _res: &mut ParameterPieces,
        resource: &ParamListStandard,
        _env: &AssignEnv<'_>,
    ) -> Result<u32> {
        let entries = resource.get_entry();
        for tile in &self.tiles {
            let entry = &entries[*tile];
            if status[entry.get_group() as usize] != 0 {
                continue;
            }
            status[entry.get_group() as usize] = -1;
        }
        Ok(SUCCESS)
    }

    fn decode(&mut self, decoder: &mut dyn Decoder, resource: &ParamListStandard) -> Result<()> {
        let elem_id = decoder.open_element_expect(ELEM_CONSUME_REMAINING)?;
        self.resource_type = string2typeclass(&decoder.read_string_attr(ATTRIB_STORAGE)?)?;
        decoder.close_element(elem_id)?;
        self.initialize_entries(resource)
    }
}

#[derive(Default)]
pub struct ModelRule {
    filter: Option<Box<dyn DatatypeFilter>>,
    qualifier: Option<Box<dyn QualifierFilter>>,
    assign: Option<Box<dyn AssignAction>>,
    preconditions: Vec<Box<dyn AssignAction>>,
    sideeffects: Vec<Box<dyn AssignAction>>,
}

impl ModelRule {
    pub fn new() -> ModelRule {
        ModelRule {
            filter: None,
            qualifier: None,
            assign: None,
            preconditions: Vec::new(),
            sideeffects: Vec::new(),
        }
    }

    pub fn new_copy(op2: &ModelRule, res: &ParamListStandard) -> Result<ModelRule> {
        let filter = op2.filter.as_ref().map(|filter| filter.clone_filter());
        let qualifier = op2.qualifier.as_ref().map(|qualifier| qualifier.clone_filter());
        let assign = match &op2.assign {
            Some(action) => Some(action.clone_action(res)?),
            None => None,
        };
        let mut preconditions = Vec::new();
        for action in &op2.preconditions {
            preconditions.push(action.clone_action(res)?);
        }
        let mut sideeffects = Vec::new();
        for action in &op2.sideeffects {
            sideeffects.push(action.clone_action(res)?);
        }
        Ok(ModelRule {
            filter,
            qualifier,
            assign,
            preconditions,
            sideeffects,
        })
    }

    pub fn new_from(
        type_filter: &dyn DatatypeFilter,
        action: &dyn AssignAction,
        res: &ParamListStandard,
    ) -> Result<ModelRule> {
        Ok(ModelRule {
            filter: Some(type_filter.clone_filter()),
            qualifier: None,
            assign: Some(action.clone_action(res)?),
            preconditions: Vec::new(),
            sideeffects: Vec::new(),
        })
    }

    fn assign_ref(&self) -> &dyn AssignAction {
        self.assign.as_deref().expect("model rule has no assign action")
    }

    pub fn assign_address(
        &self,
        dt: TypeId,
        proto: &PrototypePieces,
        pos: i32,
        tlist: &mut TypeFactory,
        status: &mut Vec<i32>,
        res: &mut ParameterPieces,
        resource: &ParamListStandard,
        env: &AssignEnv<'_>,
    ) -> Result<u32> {
        if !self
            .filter
            .as_ref()
            .expect("model rule has no data-type filter")
            .filter(dt, tlist)
        {
            return Ok(FAIL);
        }
        if let Some(qualifier) = &self.qualifier
            && !qualifier.filter(proto, pos, tlist)
        {
            return Ok(FAIL);
        }
        let mut tmp_status = status.clone();
        for precondition in &self.preconditions {
            precondition.assign_address(dt, proto, pos, tlist, &mut tmp_status, res, resource, env)?;
        }
        let response = self
            .assign_ref()
            .assign_address(dt, proto, pos, tlist, &mut tmp_status, res, resource, env)?;
        if response != FAIL {
            *status = tmp_status;
            for sideeffect in &self.sideeffects {
                sideeffect.assign_address(dt, proto, pos, tlist, status, res, resource, env)?;
            }
        }
        Ok(response)
    }

    pub fn fillin_output_map(&self, active: &mut ParamActive, resource: &ParamListStandard) -> bool {
        self.assign_ref().fillin_output_map(active, resource)
    }

    pub fn can_affect_fillin_output(&self) -> bool {
        self.assign_ref().can_affect_fillin_output()
    }

    pub fn decode(&mut self, decoder: &mut dyn Decoder, res: &ParamListStandard) -> Result<()> {
        let mut qualifiers: Vec<Box<dyn QualifierFilter>> = Vec::new();
        let elem_id = decoder.open_element_expect(ELEM_RULE)?;
        self.filter = Some(decode_datatype_filter(decoder)?);
        while let Some(qual) = decode_qualifier_filter(decoder)? {
            qualifiers.push(qual);
        }
        self.qualifier = if qualifiers.is_empty() {
            None
        } else if qualifiers.len() == 1 {
            qualifiers.pop()
        } else {
            Some(Box::new(AndFilter::new(qualifiers)))
        };
        while let Some(precond) = decode_precondition(decoder, res)? {
            self.preconditions.push(precond);
        }
        self.assign = Some(decode_action(decoder, res)?);
        while decoder.peek_element()? != 0 {
            self.sideeffects.push(decode_sideeffect(decoder, res)?);
        }
        decoder.close_element(elem_id)?;
        Ok(())
    }
}
