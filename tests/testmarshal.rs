mod common;

use common::{AnyEncoder, Format, marshal_manager, new_decoder};
use ghidra_decompiler::address::ELEM_ADDR;
use ghidra_decompiler::error::Error;
use ghidra_decompiler::marshal::*;
use ghidra_decompiler::translate::AddrSpaceManager;

fn test_signed_attributes(format: Format, manager: &AddrSpaceManager) {
    let mut any = AnyEncoder::new(format);
    let encoder = any.encoder();
    encoder.open_element(ELEM_ADDR);
    encoder.write_signed_integer(ATTRIB_ALIGN, 3);
    encoder.write_signed_integer(ATTRIB_BIGENDIAN, -0x100);
    encoder.write_signed_integer(ATTRIB_CONSTRUCTOR, 0x1fffff);
    encoder.write_signed_integer(ATTRIB_DESTRUCTOR, -0xabcdefa);
    encoder.write_signed_integer(ATTRIB_EXTRAPOP, 0x300000000);
    encoder.write_signed_integer(ATTRIB_FORMAT, -0x30101010101);
    encoder.write_signed_integer(ATTRIB_ID, 0x123456789011);
    encoder.write_signed_integer(ATTRIB_INDEX, -0xf0f0f0f0f0f0f0);
    encoder.write_signed_integer(ATTRIB_METATYPE, 0x7fffffffffffffff);
    encoder.close_element(ELEM_ADDR);
    let mut decoder = new_decoder(format, manager);
    decoder.ingest_stream(&any.bytes()).expect("ingest");
    let el = decoder.open_element_expect(ELEM_ADDR).expect("open addr");
    let mut flags = 0u32;
    loop {
        let attrib_id = decoder.get_next_attribute_id().expect("attribute id");
        if attrib_id == 0 {
            break;
        }
        let expected: [(AttributeId, i64, u32); 9] = [
            (ATTRIB_ALIGN, 3, 1),
            (ATTRIB_BIGENDIAN, -0x100, 2),
            (ATTRIB_CONSTRUCTOR, 0x1fffff, 4),
            (ATTRIB_DESTRUCTOR, -0xabcdefa, 8),
            (ATTRIB_EXTRAPOP, 0x300000000, 0x10),
            (ATTRIB_FORMAT, -0x30101010101, 0x20),
            (ATTRIB_ID, 0x123456789011, 0x40),
            (ATTRIB_INDEX, -0xf0f0f0f0f0f0f0, 0x80),
            (ATTRIB_METATYPE, 0x7fffffffffffffff, 0x100),
        ];
        for (attrib, value, bit) in expected {
            if attrib_id == attrib {
                let val = decoder.read_signed_integer().expect("signed");
                flags |= bit;
                assert_eq!(val, value);
            }
        }
    }
    decoder.close_element(el).expect("close");
    assert_eq!(flags, 0x1ff);
}

fn test_unsigned_attributes(format: Format, manager: &AddrSpaceManager) {
    let mut any = AnyEncoder::new(format);
    let encoder = any.encoder();
    encoder.open_element(ELEM_ADDR);
    encoder.write_unsigned_integer(ATTRIB_ALIGN, 3);
    encoder.write_unsigned_integer(ATTRIB_BIGENDIAN, 0x100);
    encoder.write_unsigned_integer(ATTRIB_CONSTRUCTOR, 0x1fffff);
    encoder.write_unsigned_integer(ATTRIB_DESTRUCTOR, 0xabcdefa);
    encoder.write_unsigned_integer(ATTRIB_EXTRAPOP, 0x300000000);
    encoder.write_unsigned_integer(ATTRIB_FORMAT, 0x30101010101);
    encoder.write_unsigned_integer(ATTRIB_ID, 0x123456789011);
    encoder.write_unsigned_integer(ATTRIB_INDEX, 0xf0f0f0f0f0f0f0);
    encoder.write_unsigned_integer(ATTRIB_METATYPE, 0x7fffffffffffffff);
    encoder.write_unsigned_integer(ATTRIB_MODEL, 0x8000000000000000);
    encoder.close_element(ELEM_ADDR);
    let mut decoder = new_decoder(format, manager);
    decoder.ingest_stream(&any.bytes()).expect("ingest");
    let el = decoder.open_element_expect(ELEM_ADDR).expect("open addr");
    let expected: [(AttributeId, u64); 10] = [
        (ATTRIB_ALIGN, 3),
        (ATTRIB_BIGENDIAN, 0x100),
        (ATTRIB_CONSTRUCTOR, 0x1fffff),
        (ATTRIB_DESTRUCTOR, 0xabcdefa),
        (ATTRIB_EXTRAPOP, 0x300000000),
        (ATTRIB_FORMAT, 0x30101010101),
        (ATTRIB_ID, 0x123456789011),
        (ATTRIB_INDEX, 0xf0f0f0f0f0f0f0),
        (ATTRIB_METATYPE, 0x7fffffffffffffff),
        (ATTRIB_MODEL, 0x8000000000000000),
    ];
    for (attrib, value) in expected {
        assert_eq!(decoder.read_unsigned_integer_attr(attrib).expect("unsigned"), value);
    }
    decoder.close_element(el).expect("close");
}

#[test]
fn marshal_signed_packed() {
    test_signed_attributes(Format::Packed, &marshal_manager());
}

#[test]
fn marshal_signed_xml() {
    test_signed_attributes(Format::Xml, &marshal_manager());
}

#[test]
fn marshal_unsigned_packed() {
    test_unsigned_attributes(Format::Packed, &marshal_manager());
}

#[test]
fn marshal_unsigned_xml() {
    test_unsigned_attributes(Format::Xml, &marshal_manager());
}

fn test_mixed_attributes(format: Format, manager: &AddrSpaceManager) {
    let mut any = AnyEncoder::new(format);
    let encoder = any.encoder();
    encoder.open_element(ELEM_ADDR);
    encoder.write_signed_integer(ATTRIB_ALIGN, 456);
    encoder.write_string(ATTRIB_EXTRAPOP, "unknown");
    encoder.close_element(ELEM_ADDR);
    let mut decoder = new_decoder(format, manager);
    decoder.ingest_stream(&any.bytes()).expect("ingest");
    let mut align_val = -1;
    let mut extrapop_val = -1;
    let el = decoder.open_element_expect(ELEM_ADDR).expect("open addr");
    loop {
        let attrib_id = decoder.get_next_attribute_id().expect("attribute id");
        if attrib_id == 0 {
            break;
        }
        if attrib_id == ATTRIB_ALIGN {
            align_val = decoder.read_signed_integer_expect_string("00blah", 700).expect("align");
        } else if attrib_id == ATTRIB_EXTRAPOP {
            extrapop_val = decoder
                .read_signed_integer_expect_string("unknown", 800)
                .expect("extrapop");
        }
    }
    decoder.close_element(el).expect("close");
    assert_eq!(align_val, 456);
    assert_eq!(extrapop_val, 800);
}

#[test]
fn marshal_mixed_packed() {
    test_mixed_attributes(Format::Packed, &marshal_manager());
}

#[test]
fn marshal_mixed_xml() {
    test_mixed_attributes(Format::Xml, &marshal_manager());
}

const LONG_STRING: &str = "one to three four five six seven eight nine ten eleven twelve thirteen \
fourteen fifteen sixteen seventeen eighteen nineteen twenty twenty one \
blahblahblahblahblahblahblahblahblahblahblahblahblahblahblahblahblahblah";

const SPECIAL_STRING: &str = "<<\u{20ac}>>&\"bl a  h'\\bleh\n\t";

fn test_attributes(format: Format, manager: &AddrSpaceManager) {
    let mut any = AnyEncoder::new(format);
    let encoder = any.encoder();
    encoder.open_element(ELEM_DATA);
    encoder.write_bool(ATTRIB_ALIGN, true);
    encoder.write_bool(ATTRIB_BIGENDIAN, false);
    let spc = manager.get_space(3).expect("space 3");
    encoder.write_space(ATTRIB_SPACE, &spc);
    encoder.write_string(ATTRIB_VAL, "");
    encoder.write_string(ATTRIB_VALUE, "hello");
    encoder.write_string(ATTRIB_CONSTRUCTOR, SPECIAL_STRING);
    encoder.write_string(ATTRIB_DESTRUCTOR, LONG_STRING);
    encoder.close_element(ELEM_DATA);
    let mut decoder = new_decoder(format, manager);
    decoder.ingest_stream(&any.bytes()).expect("ingest");
    let el = decoder.open_element_expect(ELEM_DATA).expect("open data");
    assert!(decoder.read_bool_attr(ATTRIB_ALIGN).expect("align"));
    assert!(!decoder.read_bool_attr(ATTRIB_BIGENDIAN).expect("bigendian"));
    let read_space = decoder.read_space_attr(ATTRIB_SPACE).expect("space");
    assert!(std::sync::Arc::ptr_eq(&read_space, &spc));
    assert_eq!(decoder.read_string_attr(ATTRIB_VAL).expect("val"), "");
    assert_eq!(decoder.read_string_attr(ATTRIB_VALUE).expect("value"), "hello");
    assert_eq!(
        decoder.read_string_attr(ATTRIB_CONSTRUCTOR).expect("constructor"),
        SPECIAL_STRING
    );
    assert_eq!(
        decoder.read_string_attr(ATTRIB_DESTRUCTOR).expect("destructor"),
        LONG_STRING
    );
    decoder.close_element(el).expect("close");
}

#[test]
fn marshal_attribs_packed() {
    test_attributes(Format::Packed, &marshal_manager());
}

#[test]
fn marshal_attribs_xml() {
    test_attributes(Format::Xml, &marshal_manager());
}

fn test_hierarchy(format: Format, manager: &AddrSpaceManager) {
    let mut any = AnyEncoder::new(format);
    let encoder = any.encoder();
    encoder.open_element(ELEM_DATA);
    encoder.write_bool(ATTRIB_CONTENT, true);
    encoder.open_element(ELEM_INPUT);
    encoder.open_element(ELEM_OUTPUT);
    encoder.write_signed_integer(ATTRIB_ID, 0x1000);
    encoder.open_element(ELEM_DATA);
    encoder.open_element(ELEM_DATA);
    encoder.open_element(ELEM_OFF);
    encoder.close_element(ELEM_OFF);
    encoder.open_element(ELEM_OFF);
    encoder.write_string(ATTRIB_ID, "blahblah");
    encoder.close_element(ELEM_OFF);
    encoder.open_element(ELEM_OFF);
    encoder.close_element(ELEM_OFF);
    encoder.close_element(ELEM_DATA);
    encoder.close_element(ELEM_DATA);
    encoder.open_element(ELEM_SYMBOL);
    encoder.write_unsigned_integer(ATTRIB_ID, 17);
    encoder.open_element(ELEM_TARGET);
    encoder.close_element(ELEM_TARGET);
    encoder.close_element(ELEM_SYMBOL);
    encoder.close_element(ELEM_OUTPUT);
    encoder.close_element(ELEM_INPUT);
    for _ in 0..6 {
        encoder.open_element(ELEM_INPUT);
        encoder.close_element(ELEM_INPUT);
    }
    encoder.close_element(ELEM_DATA);
    let mut decoder = new_decoder(format, manager);
    decoder.ingest_stream(&any.bytes()).expect("ingest");
    let el1 = decoder.open_element_expect(ELEM_DATA).expect("el1");
    let el2 = decoder.open_element_expect(ELEM_INPUT).expect("el2");
    let el3 = decoder.open_element_expect(ELEM_OUTPUT).expect("el3");
    let val = decoder.read_signed_integer_attr(ATTRIB_ID).expect("id");
    assert_eq!(val, 0x1000);
    let el4 = decoder.peek_element().expect("peek");
    assert_eq!(el4, ELEM_DATA.get_id());
    decoder.open_element().expect("open el4");
    let el5 = decoder.open_element().expect("open el5");
    assert_eq!(el5, ELEM_DATA.get_id());
    for _ in 0..3 {
        let el6 = decoder.open_element_expect(ELEM_OFF).expect("el6");
        decoder.close_element(el6).expect("close el6");
    }
    decoder.close_element(el5).expect("close el5");
    decoder.close_element(el4).expect("close el4");
    decoder.close_element_skipping(el3).expect("skip el3");
    decoder.close_element(el2).expect("close el2");
    let el2 = decoder.open_element_expect(ELEM_INPUT).expect("el2 again");
    decoder.close_element(el2).expect("close el2 again");
    let el2 = decoder.open_element_expect(ELEM_INPUT).expect("el2 third");
    decoder.close_element(el2).expect("close el2 third");
    decoder.close_element_skipping(el1).expect("skip el1");
}

#[test]
fn marshal_hierarchy_packed() {
    test_hierarchy(Format::Packed, &marshal_manager());
}

#[test]
fn marshal_hierarchy_xml() {
    test_hierarchy(Format::Xml, &marshal_manager());
}

fn test_unexpected_eof(format: Format, manager: &AddrSpaceManager) {
    let mut any = AnyEncoder::new(format);
    let encoder = any.encoder();
    encoder.open_element(ELEM_DATA);
    encoder.open_element(ELEM_INPUT);
    encoder.write_string(ATTRIB_NAME, "hello");
    encoder.close_element(ELEM_INPUT);
    let mut decoder = new_decoder(format, manager);
    let outcome = (|| -> ghidra_decompiler::error::Result<()> {
        decoder.ingest_stream(&any.bytes())?;
        let el1 = decoder.open_element_expect(ELEM_DATA)?;
        let el2 = decoder.open_element_expect(ELEM_INPUT)?;
        decoder.close_element(el2)?;
        decoder.close_element(el1)?;
        Ok(())
    })();
    assert!(matches!(outcome, Err(Error::Decoder(_))));
}

#[test]
fn marshal_unexpected_packed() {
    test_unexpected_eof(Format::Packed, &marshal_manager());
}

#[test]
fn marshal_unexpected_xml() {
    test_unexpected_eof(Format::Xml, &marshal_manager());
}

fn encode_input_off(format: Format) -> AnyEncoder {
    let mut any = AnyEncoder::new(format);
    let encoder = any.encoder();
    encoder.open_element(ELEM_INPUT);
    encoder.open_element(ELEM_OFF);
    encoder.close_element(ELEM_OFF);
    encoder.close_element(ELEM_INPUT);
    any
}

fn test_noremaining(format: Format, manager: &AddrSpaceManager) {
    let any = encode_input_off(format);
    let mut decoder = new_decoder(format, manager);
    decoder.ingest_stream(&any.bytes()).expect("ingest");
    decoder.open_element_expect(ELEM_INPUT).expect("input");
    let el2 = decoder.open_element_expect(ELEM_OFF).expect("off");
    decoder.close_element(el2).expect("close off");
    assert!(matches!(decoder.open_element_expect(ELEM_OFF), Err(Error::Decoder(_))));
}

fn test_openmismatch(format: Format, manager: &AddrSpaceManager) {
    let any = encode_input_off(format);
    let mut decoder = new_decoder(format, manager);
    decoder.ingest_stream(&any.bytes()).expect("ingest");
    decoder.open_element_expect(ELEM_INPUT).expect("input");
    assert!(matches!(
        decoder.open_element_expect(ELEM_OUTPUT),
        Err(Error::Decoder(_))
    ));
}

fn test_closemismatch(format: Format, manager: &AddrSpaceManager) {
    let any = encode_input_off(format);
    let mut decoder = new_decoder(format, manager);
    decoder.ingest_stream(&any.bytes()).expect("ingest");
    let el1 = decoder.open_element_expect(ELEM_INPUT).expect("input");
    assert!(matches!(decoder.close_element(el1), Err(Error::Decoder(_))));
}

#[test]
fn marshal_noremaining_packed() {
    test_noremaining(Format::Packed, &marshal_manager());
}

#[test]
fn marshal_noremaining_xml() {
    test_noremaining(Format::Xml, &marshal_manager());
}

#[test]
fn marshal_openmismatch_packed() {
    test_openmismatch(Format::Packed, &marshal_manager());
}

#[test]
fn marshal_openmismatch_xml() {
    test_openmismatch(Format::Xml, &marshal_manager());
}

#[test]
fn marshal_closemismatch_packed() {
    test_closemismatch(Format::Packed, &marshal_manager());
}

#[test]
fn marshal_bufferpad() {
    assert_eq!(PackedDecode::BUFFER_SIZE, 1024);
    let mut encoder = PackedEncode::new();
    encoder.open_element(ELEM_INPUT);
    for index in 0..511 {
        encoder.write_bool(ATTRIB_CONTENT, (index & 1) == 0);
    }
    encoder.close_element(ELEM_INPUT);
    assert_eq!(encoder.as_bytes().len(), 1024);
    let manager = marshal_manager();
    let mut decoder = PackedDecode::new(Some(&manager));
    decoder.ingest_stream(encoder.as_bytes()).expect("ingest");
    let el = decoder.open_element_expect(ELEM_INPUT).expect("input");
    for index in 0..511 {
        let attrib_id = decoder.get_next_attribute_id().expect("attribute id");
        assert_eq!(attrib_id, ATTRIB_CONTENT.get_id());
        let val = decoder.read_bool().expect("bool");
        assert_eq!(val, (index & 1) == 0);
    }
    let nextel = decoder.peek_element().expect("peek");
    assert_eq!(nextel, 0);
    decoder.close_element(el).expect("close");
}
