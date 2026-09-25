use super::{
    BitFieldTriple, Datatype, ELEM_BITFIELD, ELEM_FIELD, FieldAccum, TypeBitField, TypeFactory, TypeField, TypeId,
    TypeKind, TypeMetatype, types_of, types_of_mut,
};
use crate::address::BitRange;
use crate::architecture::Architecture;
use crate::error::{Error, Result};
use crate::marshal::{ATTRIB_ID, ATTRIB_NAME, ATTRIB_OFFSET, ATTRIB_SIZE, Decoder, Encoder};

use crate::address::ATTRIB_FIRST;

impl TypeField {
    pub fn decode(decoder: &mut dyn Decoder, glb: &mut Architecture) -> Result<TypeField> {
        let elem_id = decoder.open_element_expect(ELEM_FIELD)?;
        let mut ident = -1;
        let mut offset = -1;
        let mut name = String::new();
        loop {
            let attrib = decoder.get_next_attribute_id()?;
            if attrib == 0 {
                break;
            }
            if attrib == ATTRIB_NAME {
                name = decoder.read_string()?;
            } else if attrib == ATTRIB_OFFSET {
                offset = decoder.read_signed_integer()? as i32;
            } else if attrib == ATTRIB_ID {
                ident = decoder.read_signed_integer()? as i32;
            }
        }
        let tp = TypeFactory::decode_type(glb, decoder)?;
        if name.is_empty() {
            return Err(Error::Lowlevel(
                "name attribute must not be empty in <field> tag".to_string(),
            ));
        }
        if offset < 0 {
            return Err(Error::Lowlevel("offset attribute invalid for <field> tag".to_string()));
        }
        if ident < 0 {
            ident = offset;
        }
        decoder.close_element(elem_id)?;
        Ok(TypeField {
            ident,
            offset,
            name,
            tp,
        })
    }

    pub fn encode(&self, encoder: &mut dyn Encoder, glb: &Architecture) -> Result<()> {
        encoder.open_element(ELEM_FIELD);
        encoder.write_string(ATTRIB_NAME, &self.name);
        encoder.write_signed_integer(ATTRIB_OFFSET, self.offset as i64);
        if self.ident != self.offset {
            encoder.write_signed_integer(ATTRIB_ID, self.ident as i64);
        }
        types_of(glb).get(self.tp).encode_ref(encoder, glb)?;
        encoder.close_element(ELEM_FIELD);
        Ok(())
    }
}

impl TypeBitField {
    pub fn decode(decoder: &mut dyn Decoder, glb: &mut Architecture) -> Result<TypeBitField> {
        let mut ident = -1;
        let mut name = String::new();
        let mut bits = BitRange::default();
        let elem_id = decoder.open_element_expect(ELEM_BITFIELD)?;
        loop {
            let attrib = decoder.get_next_attribute_id()?;
            if attrib == 0 {
                break;
            }
            if attrib == ATTRIB_NAME {
                name = decoder.read_string()?;
            } else if attrib == ATTRIB_ID {
                ident = decoder.read_signed_integer()? as i32;
            } else if attrib == ATTRIB_OFFSET {
                bits.byte_offset = decoder.read_signed_integer()? as i32;
            } else if attrib == ATTRIB_SIZE {
                bits.num_bits = decoder.read_signed_integer()? as i32;
            } else if attrib == ATTRIB_FIRST {
                bits.least_sig_bit = decoder.read_signed_integer()? as i32;
            }
        }
        let tp = TypeFactory::decode_type(glb, decoder)?;
        if name.is_empty() {
            return Err(Error::Lowlevel(
                "<bitfield> name attribute must not be empty".to_string(),
            ));
        }
        if ident < 0 {
            return Err(Error::Lowlevel("<bitfield> id attribute must not be empty".to_string()));
        }
        if bits.byte_offset < 0 || bits.least_sig_bit < 0 || bits.num_bits < 0 {
            return Err(Error::Lowlevel(
                "<bitfield> missing offset/size/first attributes".to_string(),
            ));
        }
        bits.byte_size = (bits.least_sig_bit + bits.num_bits + 7) / 8;
        decoder.close_element(elem_id)?;
        bits.is_big_endian = glb
            .manager
            .get_default_data_space()
            .expect("default data space is not set")
            .is_big_endian();
        Ok(TypeBitField { name, tp, bits, ident })
    }

    pub fn encode(&self, encoder: &mut dyn Encoder, glb: &Architecture) -> Result<()> {
        encoder.open_element(ELEM_BITFIELD);
        encoder.write_string(ATTRIB_NAME, &self.name);
        encoder.write_signed_integer(ATTRIB_OFFSET, self.bits.byte_offset as i64);
        encoder.write_signed_integer(ATTRIB_SIZE, self.bits.num_bits as i64);
        encoder.write_signed_integer(ATTRIB_FIRST, self.bits.least_sig_bit as i64);
        types_of(glb).get(self.tp).encode_ref(encoder, glb)?;
        encoder.close_element(ELEM_BITFIELD);
        Ok(())
    }
}

impl Datatype {
    fn struct_data_mut(&mut self) -> &mut super::TypeStructData {
        match &mut self.kind {
            TypeKind::Struct(data) => data,
            _ => panic!("data-type is not a structure"),
        }
    }

    fn union_data_mut(&mut self) -> &mut super::TypeUnionData {
        match &mut self.kind {
            TypeKind::Union(data) => data,
            _ => panic!("data-type is not a union"),
        }
    }

    pub fn set_fields_struct(
        &mut self,
        fd: &[TypeField],
        bit: &[TypeBitField],
        new_size: i32,
        new_align: i32,
        single_fill: bool,
    ) {
        let data = self.struct_data_mut();
        data.field = fd.to_vec();
        data.bitfield = bit.to_vec();
        self.size = new_size;
        self.alignment = new_align;
        if single_fill {
            self.flags |= Datatype::NEEDS_RESOLUTION;
        }
        self.align_size = Datatype::calc_align_size(self.size, self.alignment);
    }

    pub fn get_field_iter(&self, off: i32, types: &TypeFactory) -> i32 {
        let field = &self.struct_data().field;
        let mut min: i32 = 0;
        let mut max: i32 = field.len() as i32 - 1;
        while min <= max {
            let mid = (min + max) / 2;
            let curfield = &field[mid as usize];
            if curfield.offset > off {
                max = mid - 1;
            } else {
                if curfield.offset + types.get(curfield.tp).get_size() > off {
                    return mid;
                }
                min = mid + 1;
            }
        }
        -1
    }

    pub fn get_lower_bound_field(&self, off: i32) -> i32 {
        let field = &self.struct_data().field;
        if field.is_empty() {
            return -1;
        }
        let mut min: i32 = 0;
        let mut max: i32 = field.len() as i32 - 1;
        while min < max {
            let mid = (min + max + 1) / 2;
            if field[mid as usize].offset > off {
                max = mid - 1;
            } else {
                min = mid;
            }
        }
        if min == max && field[min as usize].offset <= off {
            return min;
        }
        -1
    }

    pub fn find_matching_bit_field(&self, range: &BitRange) -> Option<&TypeBitField> {
        let bitfield = &self.struct_data().bitfield;
        let mut min: i32 = 0;
        let mut max: i32 = bitfield.len() as i32 - 1;
        while min <= max {
            let mid = (min + max) / 2;
            let curfield = &bitfield[mid as usize];
            let code = range.overlap_test(&curfield.bits);
            if code == 0 {
                return Some(curfield);
            }
            if code == -1 {
                max = mid - 1;
            } else if code == 1 {
                min = mid + 1;
            } else {
                break;
            }
        }
        None
    }

    pub fn collect_bit_fields(
        ct: TypeId,
        base_offset: i32,
        res: &mut Vec<BitFieldTriple>,
        offset: i32,
        sz: i32,
        types: &TypeFactory,
    ) {
        let data = types.get(ct).struct_data();
        let start = data
            .bitfield
            .partition_point(|bitfield| !TypeBitField::compare_max_byte(offset, bitfield));
        if start < data.bitfield.len() {
            let range = BitRange::new_bytes(offset, sz, data.bitfield[start].bits.is_big_endian);
            for (index, cur_bit_field) in data.bitfield.iter().enumerate().skip(start) {
                let code = cur_bit_field.bits.overlap_test(&range);
                if code == 1 {
                    break;
                }
                if code == -1 {
                    continue;
                }
                res.push(BitFieldTriple::new(ct, index, base_offset));
            }
        }
        let fstart = data
            .field
            .partition_point(|field| !TypeField::compare_max_byte(offset, field, types));
        for cur_field in data.field[fstart..].iter() {
            if cur_field.offset >= offset + sz {
                break;
            }
            let field_type = types.get(cur_field.tp);
            if field_type.get_metatype() != TypeMetatype::Struct {
                continue;
            }
            if !field_type.has_bitfields() {
                continue;
            }
            Datatype::collect_bit_fields(
                cur_field.tp,
                base_offset + cur_field.offset,
                res,
                offset - cur_field.offset,
                sz,
                types,
            );
        }
    }

    pub fn has_bit_fields_in_range(&self, offset: i32, sz: i32, types: &TypeFactory) -> bool {
        let data = self.struct_data();
        let start = data
            .bitfield
            .partition_point(|bitfield| !TypeBitField::compare_max_byte(offset, bitfield));
        if start < data.bitfield.len() {
            let range = BitRange::new_bytes(offset, sz, data.bitfield[start].bits.is_big_endian);
            for cur_bit_field in data.bitfield[start..].iter() {
                let code = cur_bit_field.bits.overlap_test(&range);
                if code == 1 {
                    break;
                }
                if code == -1 {
                    continue;
                }
                return true;
            }
        }
        let fstart = data
            .field
            .partition_point(|field| !TypeField::compare_max_byte(offset, field, types));
        for cur_field in data.field[fstart..].iter() {
            if cur_field.offset >= offset + sz {
                break;
            }
            let field_type = types.get(cur_field.tp);
            if field_type.get_metatype() != TypeMetatype::Struct {
                continue;
            }
            if !field_type.has_bitfields() {
                continue;
            }
            if field_type.has_bit_fields_in_range(offset - cur_field.offset, sz, types) {
                return true;
            }
        }
        false
    }

    pub fn decode_field(
        &mut self,
        decoder: &mut dyn Decoder,
        glb: &mut Architecture,
        accum: &mut FieldAccum,
    ) -> Result<()> {
        let cur_field = TypeField::decode(decoder, glb)?;
        let types = types_of(glb);
        let field_type = types.get(cur_field.tp);
        if field_type.get_metatype() == TypeMetatype::Void {
            return Err(Error::Lowlevel(format!(
                "Bad field data-type for structure: {}",
                self.name
            )));
        }
        if cur_field.name.is_empty() {
            return Err(Error::Lowlevel(format!("Bad field name for structure: {}", self.name)));
        }
        if cur_field.offset < accum.last_off {
            return Err(Error::Lowlevel("Fields are out of order".to_string()));
        }
        if cur_field.offset < accum.calc_size {
            if accum.warning.is_empty() {
                accum.warning = format!(
                    "Struct \"{}\": ignoring overlapping field \"{}\"",
                    self.name, cur_field.name
                );
            } else {
                accum.warning = format!("Struct \"{}\": ignoring multiple overlapping fields", self.name);
            }
            return Ok(());
        }
        if field_type.has_bitfields() {
            self.flags |= Datatype::HAS_BITFIELDS;
        }
        accum.last_off = cur_field.offset;
        accum.calc_size = cur_field.offset + field_type.get_size();
        if accum.calc_size > self.size {
            return Err(Error::Lowlevel(format!(
                "Field {} does not fit in structure {}",
                cur_field.name, self.name
            )));
        }
        let cur_align = field_type.get_alignment();
        if cur_align > accum.calc_align {
            accum.calc_align = cur_align;
        }
        self.struct_data_mut().field.push(cur_field);
        Ok(())
    }

    pub fn decode_bit_field(
        &mut self,
        decoder: &mut dyn Decoder,
        glb: &mut Architecture,
        accum: &mut FieldAccum,
    ) -> Result<()> {
        let mut cur_bit_field = TypeBitField::decode(decoder, glb)?;
        if cur_bit_field.name.is_empty() {
            return Err(Error::Lowlevel(format!(
                "Bad bitfield name for structure: {}",
                self.name
            )));
        }
        let meta = types_of(glb).get(cur_bit_field.tp).get_metatype();
        if meta != TypeMetatype::Int
            && meta != TypeMetatype::Uint
            && meta != TypeMetatype::Bool
            && meta != TypeMetatype::EnumInt
            && meta != TypeMetatype::EnumUint
        {
            return Err(Error::Lowlevel(format!(
                "Non integer data-type for bitfield \"{}\" in structure: {}",
                cur_bit_field.name, self.name
            )));
        }
        if cur_bit_field.bits.byte_offset < accum.last_off {
            return Err(Error::Lowlevel(format!(
                "Bitfields are out of order in structure: {}",
                self.name
            )));
        }
        if cur_bit_field.bits.byte_offset < accum.calc_size {
            let previous_overlaps = match self.struct_data().bitfield.last() {
                None => true,
                Some(previous) => previous.bits.overlap_test(&cur_bit_field.bits) != -1,
            };
            if previous_overlaps {
                if accum.warning.is_empty() {
                    accum.warning = format!(
                        "Struct \"{}\": ignoring overlapping bit field \"{}\"",
                        self.name, cur_bit_field.name
                    );
                } else {
                    accum.warning = format!("Struct \"{}\": ignoring multiple overlapping fields", self.name);
                }
                return Ok(());
            }
        }
        accum.last_off = cur_bit_field.bits.byte_offset;
        accum.calc_size = cur_bit_field.bits.byte_offset + cur_bit_field.bits.byte_size;
        if accum.calc_size > self.size {
            return Err(Error::Lowlevel(format!(
                "Bitfield {} does not fit in structure {}",
                cur_bit_field.name, self.name
            )));
        }
        if cur_bit_field.bits.is_byte_range() {
            cur_bit_field.bits.minimize_container();
            let mut dt = cur_bit_field.tp;
            let dt_data = types_of(glb).get(dt);
            if dt_data.get_size() != cur_bit_field.bits.byte_size {
                let mut meta = dt_data.get_metatype();
                if meta != TypeMetatype::Int && meta != TypeMetatype::Uint {
                    meta = TypeMetatype::Unknown;
                }
                dt = types_of_mut(glb).get_base(cur_bit_field.bits.byte_size, meta)?;
            }
            let byte_offset = cur_bit_field.bits.byte_offset;
            self.struct_data_mut()
                .field
                .push(TypeField::new(byte_offset, byte_offset, &cur_bit_field.name, dt));
            return Ok(());
        }
        self.struct_data_mut().bitfield.push(cur_bit_field);
        Ok(())
    }

    pub fn decode_fields_struct(&mut self, decoder: &mut dyn Decoder, glb: &mut Architecture) -> Result<String> {
        let mut accum = FieldAccum {
            last_off: -1,
            calc_size: 0,
            calc_align: 1,
            warning: String::new(),
        };
        loop {
            let el = decoder.peek_element()?;
            if el == 0 {
                break;
            }
            if el == ELEM_FIELD {
                self.decode_field(decoder, glb, &mut accum)?;
            } else if el == ELEM_BITFIELD {
                self.decode_bit_field(decoder, glb, &mut accum)?;
            } else {
                return Err(Error::Decoder("Expecting <field> or <bitfield>".to_string()));
            }
        }
        if self.size == 0 {
            self.flags |= Datatype::TYPE_INCOMPLETE;
        }
        let data = self.struct_data();
        let has_fields = !data.field.is_empty() || !data.bitfield.is_empty();
        let has_bits = !data.bitfield.is_empty();
        let single_fill = TypeFactory::single_field_fills(&data.field, self.size, types_of(glb));
        if has_fields {
            self.mark_complete();
        }
        if has_bits {
            self.flags |= Datatype::HAS_BITFIELDS;
        }
        if single_fill {
            self.flags |= Datatype::NEEDS_RESOLUTION;
        }
        if self.alignment < 1 {
            self.alignment = accum.calc_align;
        }
        self.align_size = Datatype::calc_align_size(self.size, self.alignment);
        Ok(accum.warning)
    }

    pub fn assign_contiguous_bitfields(
        bitlist: &mut [TypeBitField],
        pos: &mut i32,
        offset: &mut i32,
        new_align: &mut i32,
        types: &TypeFactory,
    ) {
        let mut total_size = 0;
        let start_ind = *pos;
        let next_bit_pos = bitlist[*pos as usize].ident;
        while (*pos as usize) < bitlist.len() && bitlist[*pos as usize].ident == next_bit_pos {
            total_size += bitlist[*pos as usize].bits.num_bits;
            *pos += 1;
        }
        let mut align = types.get(bitlist[start_ind as usize].tp).get_alignment();
        if align > *new_align {
            *new_align = align;
        }
        align -= 1;
        if align > 0 && (*offset & align) != 0 {
            *offset = *offset - (*offset & align) + (align + 1);
        }
        total_size = (total_size + 7) / 8;
        let mut lsb = 0;
        for index in start_ind..*pos {
            let bitfield = &mut bitlist[index as usize];
            bitfield.bits.byte_offset = *offset;
            bitfield.bits.byte_size = total_size;
            bitfield.bits.least_sig_bit = lsb;
            lsb += bitfield.bits.num_bits;
            bitfield.ident = index;
        }
        *offset += total_size;
        if bitlist[start_ind as usize].bits.is_big_endian && (*pos - start_ind) > 1 {
            bitlist[start_ind as usize..*pos as usize].reverse();
        }
    }

    pub fn assign_field_offsets_struct(
        list: &mut [TypeField],
        bitlist: &mut [TypeBitField],
        new_size: &mut i32,
        new_align: &mut i32,
        flags: &mut u32,
        st: Option<&Datatype>,
        types: &TypeFactory,
    ) -> Result<()> {
        let struct_name = st.map(|dt| dt.get_name().to_string()).unwrap_or_default();
        let mut next_bit_pos: i32 = -1;
        let mut cur_bit_ind: i32 = -1;
        if !bitlist.is_empty() {
            cur_bit_ind = 0;
            next_bit_pos = bitlist[0].ident;
        }
        let mut offset = 0;
        *new_align = 1;
        *flags = 0;
        for pos in 0..list.len() {
            if pos as i32 == next_bit_pos {
                Datatype::assign_contiguous_bitfields(bitlist, &mut cur_bit_ind, &mut offset, new_align, types);
                if (cur_bit_ind as usize) < bitlist.len() {
                    next_bit_pos = bitlist[cur_bit_ind as usize].ident;
                }
            }
            let cur_field = &mut list[pos];
            let field_type = types.get(cur_field.tp);
            if field_type.get_metatype() == TypeMetatype::Void {
                return Err(Error::Lowlevel(format!(
                    "Illegal field void in structure: {}",
                    struct_name
                )));
            }
            if cur_field.offset != -1 {
                continue;
            }
            let cursize = field_type.get_align_size();
            let mut align = field_type.get_alignment();
            if align > *new_align {
                *new_align = align;
            }
            align -= 1;
            if align > 0 && (offset & align) != 0 {
                offset = offset - (offset & align) + (align + 1);
            }
            cur_field.offset = offset;
            cur_field.ident = offset;
            offset += cursize;
            if field_type.has_bitfields() {
                *flags |= Datatype::HAS_BITFIELDS;
            }
        }
        if next_bit_pos >= 0 && list.len() == next_bit_pos as usize {
            Datatype::assign_contiguous_bitfields(bitlist, &mut cur_bit_ind, &mut offset, new_align, types);
        }
        if !bitlist.is_empty() && cur_bit_ind as usize != bitlist.len() {
            return Err(Error::Lowlevel(format!(
                "Malformed bitfield description in structure: {}",
                struct_name
            )));
        }
        if !bitlist.is_empty() {
            *flags |= Datatype::HAS_BITFIELDS;
        }
        *new_size = Datatype::calc_align_size(offset, *new_align);
        Ok(())
    }

    pub fn set_fields_union(&mut self, fd: &[TypeField], new_size: i32, new_align: i32) {
        self.union_data_mut().field = fd.to_vec();
        self.size = new_size;
        self.alignment = new_align;
        self.align_size = Datatype::calc_align_size(self.size, self.alignment);
    }

    pub fn decode_fields_union(&mut self, decoder: &mut dyn Decoder, glb: &mut Architecture) -> Result<()> {
        let mut calc_align = 1;
        while decoder.peek_element()? != 0 {
            let field = TypeField::decode(decoder, glb)?;
            let field_type = types_of(glb).get(field.tp);
            if field.offset + field_type.get_size() > self.size {
                return Err(Error::Lowlevel(format!(
                    "Field {} does not fit in union {}",
                    field.name, self.name
                )));
            }
            let cur_align = field_type.get_alignment();
            if cur_align > calc_align {
                calc_align = cur_align;
            }
            self.union_data_mut().field.push(field);
        }
        if self.size == 0 {
            self.flags |= Datatype::TYPE_INCOMPLETE;
        }
        if !self.get_fields().is_empty() {
            self.mark_complete();
        }
        if self.alignment < 1 {
            self.alignment = calc_align;
        }
        self.align_size = Datatype::calc_align_size(self.size, self.alignment);
        Ok(())
    }

    pub fn assign_field_offsets_union(
        list: &mut [TypeField],
        new_size: &mut i32,
        new_align: &mut i32,
        flags: &mut u32,
        tu: Option<&Datatype>,
        types: &TypeFactory,
    ) -> Result<()> {
        let union_name = tu.map(|dt| dt.get_name().to_string()).unwrap_or_default();
        *new_size = 0;
        *new_align = 1;
        *flags = 0;
        for field in list.iter_mut() {
            let ct = types.get(field.tp);
            if ct.get_metatype() == TypeMetatype::Void {
                return Err(Error::Lowlevel(format!(
                    "Bad field data-type for union: {}",
                    union_name
                )));
            } else if field.name.is_empty() {
                return Err(Error::Lowlevel(format!("Bad field name for union: {}", union_name)));
            }
            field.offset = 0;
            let end = ct.get_size();
            if end > *new_size {
                *new_size = end;
            }
            let cur_align = ct.get_alignment();
            if cur_align > *new_align {
                *new_align = cur_align;
            }
        }
        Ok(())
    }
}
