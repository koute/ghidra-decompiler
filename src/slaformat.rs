use crate::compression::Decompress;
use crate::error::{Error, Result};
use crate::marshal::{AttributeId, ElementId, PackedDecode};
use crate::translate::AddrSpaceManager;

pub const FORMAT_SCOPE: i32 = 1;
pub const FORMAT_VERSION: i32 = 4;

pub const ATTRIB_VAL: AttributeId = AttributeId::new("val", 2);
pub const ATTRIB_ID: AttributeId = AttributeId::new("id", 3);
pub const ATTRIB_SPACE: AttributeId = AttributeId::new("space", 4);
pub const ATTRIB_S: AttributeId = AttributeId::new("s", 5);
pub const ATTRIB_OFF: AttributeId = AttributeId::new("off", 6);
pub const ATTRIB_CODE: AttributeId = AttributeId::new("code", 7);
pub const ATTRIB_MASK: AttributeId = AttributeId::new("mask", 8);
pub const ATTRIB_INDEX: AttributeId = AttributeId::new("index", 9);
pub const ATTRIB_NONZERO: AttributeId = AttributeId::new("nonzero", 10);
pub const ATTRIB_PIECE: AttributeId = AttributeId::new("piece", 11);
pub const ATTRIB_NAME: AttributeId = AttributeId::new("name", 12);
pub const ATTRIB_SCOPE: AttributeId = AttributeId::new("scope", 13);
pub const ATTRIB_STARTBIT: AttributeId = AttributeId::new("startbit", 14);
pub const ATTRIB_SIZE: AttributeId = AttributeId::new("size", 15);
pub const ATTRIB_TABLE: AttributeId = AttributeId::new("table", 16);
pub const ATTRIB_CT: AttributeId = AttributeId::new("ct", 17);
pub const ATTRIB_MINLEN: AttributeId = AttributeId::new("minlen", 18);
pub const ATTRIB_BASE: AttributeId = AttributeId::new("base", 19);
pub const ATTRIB_NUMBER: AttributeId = AttributeId::new("number", 20);
pub const ATTRIB_CONTEXT: AttributeId = AttributeId::new("context", 21);
pub const ATTRIB_PARENT: AttributeId = AttributeId::new("parent", 22);
pub const ATTRIB_SUBSYM: AttributeId = AttributeId::new("subsym", 23);
pub const ATTRIB_LINE: AttributeId = AttributeId::new("line", 24);
pub const ATTRIB_SOURCE: AttributeId = AttributeId::new("source", 25);
pub const ATTRIB_LENGTH: AttributeId = AttributeId::new("length", 26);
pub const ATTRIB_FIRST: AttributeId = AttributeId::new("first", 27);
pub const ATTRIB_PLUS: AttributeId = AttributeId::new("plus", 28);
pub const ATTRIB_SHIFT: AttributeId = AttributeId::new("shift", 29);
pub const ATTRIB_ENDBIT: AttributeId = AttributeId::new("endbit", 30);
pub const ATTRIB_SIGNBIT: AttributeId = AttributeId::new("signbit", 31);
pub const ATTRIB_ENDBYTE: AttributeId = AttributeId::new("endbyte", 32);
pub const ATTRIB_STARTBYTE: AttributeId = AttributeId::new("startbyte", 33);
pub const ATTRIB_VERSION: AttributeId = AttributeId::new("version", 34);
pub const ATTRIB_BIGENDIAN: AttributeId = AttributeId::new("bigendian", 35);
pub const ATTRIB_ALIGN: AttributeId = AttributeId::new("align", 36);
pub const ATTRIB_UNIQBASE: AttributeId = AttributeId::new("uniqbase", 37);
pub const ATTRIB_MAXDELAY: AttributeId = AttributeId::new("maxdelay", 38);
pub const ATTRIB_UNIQMASK: AttributeId = AttributeId::new("uniqmask", 39);
pub const ATTRIB_NUMSECTIONS: AttributeId = AttributeId::new("numsections", 40);
pub const ATTRIB_DEFAULTSPACE: AttributeId = AttributeId::new("defaultspace", 41);
pub const ATTRIB_DELAY: AttributeId = AttributeId::new("delay", 42);
pub const ATTRIB_WORDSIZE: AttributeId = AttributeId::new("wordsize", 43);
pub const ATTRIB_PHYSICAL: AttributeId = AttributeId::new("physical", 44);
pub const ATTRIB_SCOPESIZE: AttributeId = AttributeId::new("scopesize", 45);
pub const ATTRIB_SYMBOLSIZE: AttributeId = AttributeId::new("symbolsize", 46);
pub const ATTRIB_VARNODE: AttributeId = AttributeId::new("varnode", 47);
pub const ATTRIB_LOW: AttributeId = AttributeId::new("low", 48);
pub const ATTRIB_HIGH: AttributeId = AttributeId::new("high", 49);
pub const ATTRIB_FLOW: AttributeId = AttributeId::new("flow", 50);
pub const ATTRIB_CONTAIN: AttributeId = AttributeId::new("contain", 51);
pub const ATTRIB_I: AttributeId = AttributeId::new("i", 52);
pub const ATTRIB_NUMCT: AttributeId = AttributeId::new("numct", 53);
pub const ATTRIB_SECTION: AttributeId = AttributeId::new("section", 54);
pub const ATTRIB_LABELS: AttributeId = AttributeId::new("labels", 55);

pub const ELEM_CONST_REAL: ElementId = ElementId::new("const_real", 1);
pub const ELEM_VARNODE_TPL: ElementId = ElementId::new("varnode_tpl", 2);
pub const ELEM_CONST_SPACEID: ElementId = ElementId::new("const_spaceid", 3);
pub const ELEM_CONST_HANDLE: ElementId = ElementId::new("const_handle", 4);
pub const ELEM_OP_TPL: ElementId = ElementId::new("op_tpl", 5);
pub const ELEM_MASK_WORD: ElementId = ElementId::new("mask_word", 6);
pub const ELEM_PAT_BLOCK: ElementId = ElementId::new("pat_block", 7);
pub const ELEM_PRINT: ElementId = ElementId::new("print", 8);
pub const ELEM_PAIR: ElementId = ElementId::new("pair", 9);
pub const ELEM_CONTEXT_PAT: ElementId = ElementId::new("context_pat", 10);
pub const ELEM_NULL: ElementId = ElementId::new("null", 11);
pub const ELEM_OPERAND_EXP: ElementId = ElementId::new("operand_exp", 12);
pub const ELEM_OPERAND_SYM: ElementId = ElementId::new("operand_sym", 13);
pub const ELEM_OPERAND_SYM_HEAD: ElementId = ElementId::new("operand_sym_head", 14);
pub const ELEM_OPER: ElementId = ElementId::new("oper", 15);
pub const ELEM_DECISION: ElementId = ElementId::new("decision", 16);
pub const ELEM_OPPRINT: ElementId = ElementId::new("opprint", 17);
pub const ELEM_INSTRUCT_PAT: ElementId = ElementId::new("instruct_pat", 18);
pub const ELEM_COMBINE_PAT: ElementId = ElementId::new("combine_pat", 19);
pub const ELEM_CONSTRUCTOR: ElementId = ElementId::new("constructor", 20);
pub const ELEM_CONSTRUCT_TPL: ElementId = ElementId::new("construct_tpl", 21);
pub const ELEM_SCOPE: ElementId = ElementId::new("scope", 22);
pub const ELEM_VARNODE_SYM: ElementId = ElementId::new("varnode_sym", 23);
pub const ELEM_VARNODE_SYM_HEAD: ElementId = ElementId::new("varnode_sym_head", 24);
pub const ELEM_USEROP: ElementId = ElementId::new("userop", 25);
pub const ELEM_USEROP_HEAD: ElementId = ElementId::new("userop_head", 26);
pub const ELEM_TOKENFIELD: ElementId = ElementId::new("tokenfield", 27);
pub const ELEM_VAR: ElementId = ElementId::new("var", 28);
pub const ELEM_CONTEXTFIELD: ElementId = ElementId::new("contextfield", 29);
pub const ELEM_HANDLE_TPL: ElementId = ElementId::new("handle_tpl", 30);
pub const ELEM_CONST_RELATIVE: ElementId = ElementId::new("const_relative", 31);
pub const ELEM_CONTEXT_OP: ElementId = ElementId::new("context_op", 32);
pub const ELEM_SLEIGH: ElementId = ElementId::new("sleigh", 33);
pub const ELEM_SPACES: ElementId = ElementId::new("spaces", 34);
pub const ELEM_SOURCEFILES: ElementId = ElementId::new("sourcefiles", 35);
pub const ELEM_SOURCEFILE: ElementId = ElementId::new("sourcefile", 36);
pub const ELEM_SPACE: ElementId = ElementId::new("space", 37);
pub const ELEM_SYMBOL_TABLE: ElementId = ElementId::new("symbol_table", 38);
pub const ELEM_VALUE_SYM: ElementId = ElementId::new("value_sym", 39);
pub const ELEM_VALUE_SYM_HEAD: ElementId = ElementId::new("value_sym_head", 40);
pub const ELEM_CONTEXT_SYM: ElementId = ElementId::new("context_sym", 41);
pub const ELEM_CONTEXT_SYM_HEAD: ElementId = ElementId::new("context_sym_head", 42);
pub const ELEM_END_SYM: ElementId = ElementId::new("end_sym", 43);
pub const ELEM_END_SYM_HEAD: ElementId = ElementId::new("end_sym_head", 44);
pub const ELEM_SPACE_OTHER: ElementId = ElementId::new("space_other", 45);
pub const ELEM_SPACE_UNIQUE: ElementId = ElementId::new("space_unique", 46);
pub const ELEM_AND_EXP: ElementId = ElementId::new("and_exp", 47);
pub const ELEM_DIV_EXP: ElementId = ElementId::new("div_exp", 48);
pub const ELEM_LSHIFT_EXP: ElementId = ElementId::new("lshift_exp", 49);
pub const ELEM_MINUS_EXP: ElementId = ElementId::new("minus_exp", 50);
pub const ELEM_MULT_EXP: ElementId = ElementId::new("mult_exp", 51);
pub const ELEM_NOT_EXP: ElementId = ElementId::new("not_exp", 52);
pub const ELEM_OR_EXP: ElementId = ElementId::new("or_exp", 53);
pub const ELEM_PLUS_EXP: ElementId = ElementId::new("plus_exp", 54);
pub const ELEM_RSHIFT_EXP: ElementId = ElementId::new("rshift_exp", 55);
pub const ELEM_SUB_EXP: ElementId = ElementId::new("sub_exp", 56);
pub const ELEM_XOR_EXP: ElementId = ElementId::new("xor_exp", 57);
pub const ELEM_INTB: ElementId = ElementId::new("intb", 58);
pub const ELEM_END_EXP: ElementId = ElementId::new("end_exp", 59);
pub const ELEM_NEXT2_EXP: ElementId = ElementId::new("next2_exp", 60);
pub const ELEM_START_EXP: ElementId = ElementId::new("start_exp", 61);
pub const ELEM_EPSILON_SYM: ElementId = ElementId::new("epsilon_sym", 62);
pub const ELEM_EPSILON_SYM_HEAD: ElementId = ElementId::new("epsilon_sym_head", 63);
pub const ELEM_NAME_SYM: ElementId = ElementId::new("name_sym", 64);
pub const ELEM_NAME_SYM_HEAD: ElementId = ElementId::new("name_sym_head", 65);
pub const ELEM_NAMETAB: ElementId = ElementId::new("nametab", 66);
pub const ELEM_NEXT2_SYM: ElementId = ElementId::new("next2_sym", 67);
pub const ELEM_NEXT2_SYM_HEAD: ElementId = ElementId::new("next2_sym_head", 68);
pub const ELEM_START_SYM: ElementId = ElementId::new("start_sym", 69);
pub const ELEM_START_SYM_HEAD: ElementId = ElementId::new("start_sym_head", 70);
pub const ELEM_SUBTABLE_SYM: ElementId = ElementId::new("subtable_sym", 71);
pub const ELEM_SUBTABLE_SYM_HEAD: ElementId = ElementId::new("subtable_sym_head", 72);
pub const ELEM_VALUEMAP_SYM: ElementId = ElementId::new("valuemap_sym", 73);
pub const ELEM_VALUEMAP_SYM_HEAD: ElementId = ElementId::new("valuemap_sym_head", 74);
pub const ELEM_VALUETAB: ElementId = ElementId::new("valuetab", 75);
pub const ELEM_VARLIST_SYM: ElementId = ElementId::new("varlist_sym", 76);
pub const ELEM_VARLIST_SYM_HEAD: ElementId = ElementId::new("varlist_sym_head", 77);
pub const ELEM_OR_PAT: ElementId = ElementId::new("or_pat", 78);
pub const ELEM_COMMIT: ElementId = ElementId::new("commit", 79);
pub const ELEM_CONST_START: ElementId = ElementId::new("const_start", 80);
pub const ELEM_CONST_NEXT: ElementId = ElementId::new("const_next", 81);
pub const ELEM_CONST_NEXT2: ElementId = ElementId::new("const_next2", 82);
pub const ELEM_CONST_CURSPACE: ElementId = ElementId::new("const_curspace", 83);
pub const ELEM_CONST_CURSPACE_SIZE: ElementId = ElementId::new("const_curspace_size", 84);
pub const ELEM_CONST_FLOWREF: ElementId = ElementId::new("const_flowref", 85);
pub const ELEM_CONST_FLOWREF_SIZE: ElementId = ElementId::new("const_flowref_size", 86);
pub const ELEM_CONST_FLOWDEST: ElementId = ElementId::new("const_flowdest", 87);
pub const ELEM_CONST_FLOWDEST_SIZE: ElementId = ElementId::new("const_flowdest_size", 88);

const IN_BUFFER_SIZE: usize = 4096;

pub fn is_sla_format(data: &[u8]) -> bool {
    if data.len() < 4 {
        return false;
    }
    if data[0] != b's' || data[1] != b'l' || data[2] != b'a' {
        return false;
    }
    data[3] as i32 == FORMAT_VERSION
}

pub fn write_sla_header(out: &mut Vec<u8>) {
    out.extend_from_slice(b"sla");
    out.push(FORMAT_VERSION as u8);
}

const XZ_MAGIC: &[u8] = &[0xfd, b'7', b'z', b'X', b'Z', 0x00];

pub fn decompress_sla(data: &[u8]) -> Result<Option<Vec<u8>>> {
    if !is_sla_format(data) {
        return Err(Error::Lowlevel("Missing SLA format header".to_string()));
    }
    if data[4..].starts_with(XZ_MAGIC) {
        return decompress_xz_payload(&data[4..]);
    }
    let buffer_size = PackedDecode::BUFFER_SIZE as usize;
    let mut decompressor = Decompress::new();
    let mut output: Vec<u8> = Vec::new();
    let mut chunk_count = 0usize;
    let mut out_avail = 0usize;
    let mut position = 4usize;
    while !decompressor.is_finished() {
        let end = (position + IN_BUFFER_SIZE).min(data.len());
        let gcount = end - position;
        if gcount == 0 {
            break;
        }
        decompressor.input(&data[position..end]);
        position = end;
        loop {
            if out_avail == 0 {
                output.resize((chunk_count + 1) * buffer_size, 0);
                chunk_count += 1;
                out_avail = buffer_size;
            }
            let start = chunk_count * buffer_size - out_avail;
            let limit = chunk_count * buffer_size;
            out_avail = decompressor.inflate(&mut output[start..limit])? as usize;
            if out_avail != 0 {
                break;
            }
        }
    }
    if chunk_count == 0 {
        return Ok(None);
    }
    output.truncate(chunk_count * buffer_size - out_avail);
    Ok(Some(output))
}

fn decompress_xz_payload(mut payload: &[u8]) -> Result<Option<Vec<u8>>> {
    let mut output = Vec::new();
    lzma_rs::xz_decompress(&mut payload, &mut output)
        .map_err(|error| Error::Lowlevel(format!("invalid xz payload in .sla file: {error}")))?;
    Ok(if output.is_empty() { None } else { Some(output) })
}

pub fn format_decode<'a>(manager: &'a AddrSpaceManager, data: &[u8]) -> Result<PackedDecode<'a>> {
    let mut decoder = PackedDecode::new(Some(manager));
    let bytes = decompress_sla(data)?;
    decoder.end_ingest(bytes)?;
    Ok(decoder)
}
