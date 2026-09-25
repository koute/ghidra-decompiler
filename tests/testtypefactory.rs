use std::cmp::Ordering;
use std::collections::BTreeMap;

use ghidra_decompiler::cast::{CastStrategy, CastStrategyC};
use ghidra_decompiler::cpool::{CPoolRecord, ConstantPool, ConstantPoolInternal};
use ghidra_decompiler::marshal::{Decoder, Encoder, XmlDecode, XmlEncode};
use ghidra_decompiler::stringmanage::StringManagerBase;
use ghidra_decompiler::types::{
    Datatype, EnumRepresentation, SubMetatype, TypeFactory, TypeField, TypeId, TypeMetatype, datatype_compare,
};

const DATA_ORGANIZATION: &str = "<data_organization><integer_size value=\"4\"/><long_size value=\"8\"/>\
<pointer_size value=\"8\"/><size_alignment_map><entry size=\"1\" alignment=\"1\"/>\
<entry size=\"2\" alignment=\"2\"/><entry size=\"4\" alignment=\"4\"/><entry size=\"8\" alignment=\"8\"/>\
</size_alignment_map></data_organization>";

fn build_factory() -> TypeFactory {
    let mut types = TypeFactory::new();
    let mut decoder = XmlDecode::new(None, 0);
    decoder
        .ingest_stream(DATA_ORGANIZATION.as_bytes())
        .expect("invalid data organization document");
    types
        .decode_data_organization(&mut decoder)
        .expect("data organization does not decode");
    let mut enum_decoder = XmlDecode::new(None, 0);
    enum_decoder
        .ingest_stream(b"<enum size=\"4\" signed=\"false\"/>")
        .expect("invalid enum configuration document");
    types
        .parse_enum_config(&mut enum_decoder)
        .expect("enum configuration does not decode");
    types.set_arch_properties(None, 10);
    let core: [(&str, i32, TypeMetatype, bool); 19] = [
        ("void", 1, TypeMetatype::Void, false),
        ("uint1", 1, TypeMetatype::Uint, false),
        ("uint2", 2, TypeMetatype::Uint, false),
        ("uint4", 4, TypeMetatype::Uint, false),
        ("uint8", 8, TypeMetatype::Uint, false),
        ("int1", 1, TypeMetatype::Int, false),
        ("int2", 2, TypeMetatype::Int, false),
        ("int4", 4, TypeMetatype::Int, false),
        ("int8", 8, TypeMetatype::Int, false),
        ("float4", 4, TypeMetatype::Float, false),
        ("float8", 8, TypeMetatype::Float, false),
        ("float10", 10, TypeMetatype::Float, false),
        ("bool", 1, TypeMetatype::Bool, false),
        ("code", 1, TypeMetatype::Code, false),
        ("char", 1, TypeMetatype::Int, true),
        ("wchar2", 2, TypeMetatype::Int, true),
        ("undefined", 1, TypeMetatype::Unknown, false),
        ("undefined4", 4, TypeMetatype::Unknown, false),
        ("undefined8", 8, TypeMetatype::Unknown, false),
    ];
    for (name, size, meta, chartp) in core.iter() {
        types
            .set_core_type(name, *size, *meta, *chartp)
            .expect("core type creation failed");
    }
    types.cache_core_types().expect("core type caching failed");
    types
}

fn raw(types: &TypeFactory, ct: TypeId) -> String {
    let mut s = String::new();
    types.get(ct).print_raw(&mut s, types);
    s
}

fn assert_tree_sorted(types: &TypeFactory) {
    let tree = types.tree_ids();
    for pair in tree.windows(2) {
        assert_eq!(
            datatype_compare(types.get(pair[0]), types.get(pair[1]), types),
            Ordering::Less
        );
    }
}

#[test]
fn hash_name_matches_reference() {
    assert_eq!(Datatype::hash_name("int4"), 0xc000fe2ec290219f);
    assert_eq!(Datatype::hash_name("undefined"), 0xc56465666a6c6d2f);
    assert_eq!(Datatype::hash_name("void"), 0xc0feab8523c497cf);
    assert_eq!(Datatype::hash_name("mystruct"), 0xd32c2621d97563ef);
    assert_eq!(Datatype::hash_name("\u{e9}t\u{e9}"), 0xc000846957dec2a9);
    assert_eq!(Datatype::hash_name(""), 0xc00000000000007b);
    assert_eq!(
        Datatype::hash_size(Datatype::hash_name("mystruct"), 16),
        0x517d251b35cfd91f
    );
    assert_eq!(Datatype::hash_size(5, -3), 0x3790cf64f39cfcf6);
}

#[test]
fn core_type_cache() {
    let mut types = build_factory();
    let int4 = types.get_base(4, TypeMetatype::Int).expect("int4");
    assert_eq!(types.get(int4).get_name(), "int4");
    let char1 = types.get_base(1, TypeMetatype::Int).expect("char");
    assert_eq!(types.get(char1).get_name(), "char");
    let int1 = types.get_base_no_char(1, TypeMetatype::Int).expect("int1");
    assert_eq!(types.get(int1).get_name(), "int1");
    let int2 = types.get_base(2, TypeMetatype::Int).expect("int2");
    assert_eq!(types.get(int2).get_name(), "int2");
    let float10 = types.get_base(10, TypeMetatype::Float).expect("float10");
    assert_eq!(types.get(float10).get_name(), "float10");
    let wchar = types.get_type_char(2).expect("wchar");
    assert_eq!(types.get(wchar).get_name(), "wchar2");
    assert!(types.get(wchar).is_utf16());
    assert_eq!(types.get(wchar).get_sub_meta(), SubMetatype::IntUnicode);
    assert!(types.get_type_char(3).is_err());
    let void = types.get_type_void().expect("void");
    assert_eq!(types.get(void).get_name(), "void");
    assert!(types.get(void).is_core_type());
    assert_eq!(
        types.find_by_name("uint4"),
        Some(types.get_base(4, TypeMetatype::Uint).expect("uint4"))
    );
    assert_tree_sorted(&types);
}

#[test]
fn unnamed_base_and_large_base() {
    let mut types = build_factory();
    let unk3 = types.get_base(3, TypeMetatype::Unknown).expect("undefined3");
    assert_eq!(raw(&types, unk3), "unkbyte3");
    assert_eq!(types.get(unk3).get_align_size(), 4);
    assert_eq!(types.get(unk3).get_alignment(), 4);
    assert_eq!(types.get_base(3, TypeMetatype::Unknown).expect("undefined3"), unk3);
    let big = types.get_base(12, TypeMetatype::Unknown).expect("large unknown");
    assert_eq!(types.get(big).get_metatype(), TypeMetatype::Array);
    assert_eq!(raw(&types, big), "undefined [12]");
    assert_eq!(types.get(big).num_elements(), 12);
    assert_tree_sorted(&types);
}

#[test]
fn struct_layout_and_pieces() {
    let mut types = build_factory();
    let int4 = types.get_base(4, TypeMetatype::Int).expect("int4");
    let char1 = types.get_base(1, TypeMetatype::Int).expect("char");
    let int8 = types.get_base(8, TypeMetatype::Int).expect("int8");
    let st = types.get_type_struct("mystruct").expect("struct");
    assert!(types.get(st).is_incomplete());
    let mut fields = vec![
        TypeField::new(-1, -1, "a", int4),
        TypeField::new(-1, -1, "b", char1),
        TypeField::new(-1, -1, "c", int8),
    ];
    let mut bitfields = Vec::new();
    types
        .assign_raw_fields_struct(st, &mut fields, &mut bitfields)
        .expect("struct layout");
    let dt = types.get(st);
    assert!(!dt.is_incomplete());
    assert_eq!(dt.get_size(), 16);
    assert_eq!(dt.get_alignment(), 8);
    let offsets: Vec<i32> = dt.get_fields().iter().map(|field| field.offset).collect();
    assert_eq!(offsets, vec![0, 4, 8]);
    let mut newoff = 0i64;
    assert_eq!(dt.get_sub_type_local(9, &mut newoff, &types), Some(int8));
    assert_eq!(newoff, 1);
    assert_eq!(dt.get_hole_size(5, &types), 3);
    assert_eq!(dt.get_hole_size(0, &types), 0);
    assert_eq!(types.get_exact_piece(st, 4, 1).expect("exact piece"), Some(char1));
    let partial = types
        .get_exact_piece(st, 2, 4)
        .expect("exact piece")
        .expect("partial structure");
    assert_eq!(raw(&types, partial), "mystruct[off=2,sz=4]");
    assert_eq!(types.get(partial).get_metatype(), TypeMetatype::PartialStruct);
    let ptr = types.get_type_pointer(8, st, 1).expect("pointer");
    assert_eq!(types.get(ptr).get_sub_meta(), SubMetatype::PtrStruct);
    assert_eq!(raw(&types, ptr), "mystruct *");
    let ptr_int = types.get_type_pointer(8, int4, 1).expect("pointer");
    assert_eq!(types.get(ptr_int).get_sub_meta(), SubMetatype::Ptr);
    assert!(types.get(ptr).type_order(types.get(ptr_int), &types) < 0);
    let mut deporder = Vec::new();
    types.dependent_order(&mut deporder);
    let st_pos = deporder.iter().position(|ct| *ct == st).expect("struct in order");
    let int8_pos = deporder.iter().position(|ct| *ct == int8).expect("int8 in order");
    assert!(int8_pos < st_pos);
    assert_tree_sorted(&types);
}

#[test]
fn enum_matches() {
    let mut types = build_factory();
    let te = types.get_type_enum("flags").expect("enum");
    let mut nmap = BTreeMap::new();
    let namelist = vec!["A".to_string(), "B".to_string(), "C".to_string()];
    let mut vallist = vec![1u64, 2, 4];
    let assignlist = vec![true, true, true];
    Datatype::assign_values(&mut nmap, &namelist, &mut vallist, &assignlist, types.get(te)).expect("enum values");
    types.set_enum_values(&nmap, te);
    let dt = types.get(te);
    assert!(dt.is_enum_type());
    assert!(dt.has_named_value(2, &types));
    assert!(!dt.has_named_value(3, &types));
    let mut rep = EnumRepresentation::new();
    dt.get_matches(3, &mut rep, &types);
    assert_eq!(rep.matchname, vec!["B".to_string(), "A".to_string()]);
    assert!(!rep.complement);
    let mut rep = EnumRepresentation::new();
    dt.get_matches(0xfffffffe, &mut rep, &types);
    assert_eq!(rep.matchname, vec!["A".to_string()]);
    assert!(rep.complement);
    let mut rep = EnumRepresentation::new();
    dt.get_matches(8, &mut rep, &types);
    assert!(rep.matchname.is_empty());
    let mut nmap2 = BTreeMap::new();
    let mut vallist2 = vec![5u64, 0, 0];
    let assignlist2 = vec![true, false, false];
    Datatype::assign_values(&mut nmap2, &namelist, &mut vallist2, &assignlist2, types.get(te)).expect("enum values");
    let assigned: Vec<(u64, String)> = nmap2.into_iter().collect();
    assert_eq!(
        assigned,
        vec![(5, "A".to_string()), (6, "B".to_string()), (7, "C".to_string())]
    );
    let mut nmap3 = BTreeMap::new();
    let mut vallist3 = vec![1u64, 1, 0];
    let assignlist3 = vec![true, true, false];
    let err = Datatype::assign_values(&mut nmap3, &namelist, &mut vallist3, &assignlist3, types.get(te))
        .expect_err("duplicate enum value");
    assert_eq!(err.explain(), "Enum \"flags\": \"B\" is a duplicate value");
    let partial = types.get_type_partial_enum(te, 0, 1).expect("partial enum");
    assert_eq!(raw(&types, partial), "flags[off=0,sz=1]");
    assert!(types.get(partial).has_named_value(4, &types));
}

#[test]
fn typedef_and_rename() {
    let mut types = build_factory();
    let int4 = types.get_base(4, TypeMetatype::Int).expect("int4");
    let myint = types.get_typedef(int4, "myint", 0, 1).expect("typedef");
    assert_eq!(types.get(myint).get_typedef(), Some(int4));
    assert_eq!(types.get(myint).get_display_format(), 1);
    assert!(!types.get(myint).is_core_type());
    assert_eq!(types.find_by_name("myint"), Some(myint));
    assert_eq!(types.get_typedef(int4, "myint", 0, 1).expect("typedef"), myint);
    let uint4 = types.get_base(4, TypeMetatype::Uint).expect("uint4");
    assert!(types.get_typedef(uint4, "myint", 0, 0).is_err());
    let anon = types.get_base(3, TypeMetatype::Int).expect("int3");
    types.set_name(anon, "int3").expect("rename");
    assert_eq!(types.find_by_name("int3"), Some(anon));
    assert_eq!(types.get(anon).get_id(), Datatype::hash_name("int3"));
    assert_tree_sorted(&types);
}

#[test]
fn encode_basic_attributes() {
    let mut types = build_factory();
    let int4 = types.get_base(4, TypeMetatype::Int).expect("int4");
    let mut encoder = XmlEncode::new(false);
    encoder.open_element(ghidra_decompiler::types::ELEM_TYPE);
    types
        .get(int4)
        .encode_basic(TypeMetatype::Int, -1, &mut encoder)
        .expect("encode");
    encoder.close_element(ghidra_decompiler::types::ELEM_TYPE);
    assert_eq!(
        encoder.into_string(),
        "<type name=\"int4\" id=\"0xc000fe2ec290219f\" size=\"4\" metatype=\"int\" core=\"true\"/>"
    );
}

#[test]
fn cast_standard_rules() {
    let mut types = build_factory();
    let int4 = types.get_base(4, TypeMetatype::Int).expect("int4");
    let uint4 = types.get_base(4, TypeMetatype::Uint).expect("uint4");
    let int8 = types.get_base(8, TypeMetatype::Int).expect("int8");
    let float4 = types.get_base(4, TypeMetatype::Float).expect("float4");
    let ptr_int = types.get_type_pointer(8, int4, 1).expect("pointer");
    let ptr_uint = types.get_type_pointer(8, uint4, 1).expect("pointer");
    let mut strategy = CastStrategyC::new();
    strategy.set_type_factory(&types);
    assert_eq!(strategy.base().promote_size, 4);
    assert_eq!(strategy.cast_standard(int4, uint4, false, false, &types), None);
    assert_eq!(strategy.cast_standard(int4, uint4, true, false, &types), Some(int4));
    assert_eq!(strategy.cast_standard(int8, int4, false, false, &types), Some(int8));
    assert_eq!(strategy.cast_standard(int4, float4, false, false, &types), Some(int4));
    assert_eq!(
        strategy.cast_standard(ptr_int, ptr_uint, false, false, &types),
        Some(ptr_int)
    );
    assert!(strategy.is_zext_cast(int8, uint4, &types));
    assert!(!strategy.is_zext_cast(int8, int4, &types));
    assert!(strategy.is_sext_cast(int8, int4, &types));
    assert!(strategy.is_subpiece_cast(int4, int8, 0, &types));
    assert!(!strategy.is_subpiece_cast(int4, int8, 4, &types));
    assert!(strategy.is_subpiece_cast_endian(int4, int8, 7, true, &types));
}

#[test]
fn string_codepoints() {
    let mut out = Vec::new();
    StringManagerBase::write_utf8(&mut out, 0x41).expect("ascii");
    StringManagerBase::write_utf8(&mut out, 0xe9).expect("two bytes");
    StringManagerBase::write_utf8(&mut out, 0x20ac).expect("three bytes");
    StringManagerBase::write_utf8(&mut out, 0x1f600).expect("four bytes");
    assert_eq!(out, "A\u{e9}\u{20ac}\u{1f600}".as_bytes());
    assert!(StringManagerBase::write_utf8(&mut out, -1).is_err());
    let utf16 = [0x3d, 0xd8, 0x00, 0xde, 0x41, 0x00, 0x00, 0x00];
    let mut skip = 0;
    assert_eq!(StringManagerBase::get_codepoint(&utf16, 2, false, &mut skip), 0x1f600);
    assert_eq!(skip, 4);
    assert_eq!(StringManagerBase::check_characters(&utf16, 8, 2, false), 2);
    assert!(StringManagerBase::has_char_terminator(&utf16, 8, 2));
    let bad = [0x00, 0xdc, 0x41, 0x00];
    assert_eq!(StringManagerBase::check_characters(&bad, 4, 2, false), -1);
    let utf8 = "h\u{e9}llo\0".as_bytes();
    assert_eq!(
        StringManagerBase::check_characters(utf8, utf8.len() as i32, 1, false),
        5
    );
}

#[test]
fn constant_pool_records() {
    let mut types = build_factory();
    let int4 = types.get_base(4, TypeMetatype::Int).expect("int4");
    let mut pool = ConstantPoolInternal::new();
    assert!(pool.empty());
    pool.put_record(&[1, 2], CPoolRecord::STRING_LITERAL, "hello", Some(int4))
        .expect("record");
    let record = pool.get_record(&[1, 2]).expect("record present");
    assert_eq!(record.get_token(), "hello");
    assert_eq!(record.get_tag(), CPoolRecord::STRING_LITERAL);
    assert!(pool.get_record(&[1]).is_none());
    let err = pool
        .put_record(&[1, 2], 0, "other", None)
        .expect_err("duplicate record");
    assert_eq!(err.explain(), "Creating duplicate entry in constant pool: hello");
}
