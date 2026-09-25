use std::io::Cursor;
use std::path::PathBuf;

use ghidra_decompiler::architecture::{Architecture, ArchitectureCapability, ErrorStream};
use ghidra_decompiler::error::Result;
use ghidra_decompiler::grammar::parse_c;
use ghidra_decompiler::printlanguage::PrintContext;
use ghidra_decompiler::xml::DocumentStorage;
use ghidra_decompiler::xml_arch::XML_ARCHITECTURE_CAPABILITY;

fn data_path(name: &str) -> PathBuf {
    let mut path = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    path.push("tests");
    path.push("printtypes_data");
    path.push(name);
    path
}

fn escape(text: &[u8]) -> String {
    let mut result = String::new();
    for byte in text {
        if *byte < 0x20 || *byte >= 0x7f || *byte == b'%' {
            result.push_str(&format!("%{:02x}", byte));
        } else {
            result.push(*byte as char);
        }
    }
    result
}

fn build_arch() -> Box<Architecture> {
    let mut store = DocumentStorage::new();
    let doc = store
        .parse_document(b"<binaryimage arch=\"x86:LE:64:default:gcc\"></binaryimage>")
        .expect("invalid binaryimage document");
    store.register_tag(doc.get_root());
    let estream: ErrorStream = std::sync::Arc::new(std::sync::Mutex::new(String::new()));
    let mut glb = XML_ARCHITECTURE_CAPABILITY
        .build_architecture("", "", Some(estream))
        .expect("xml architecture construction failed");
    glb.init(&mut store).expect("architecture initialization failed");
    glb
}

fn run_case(line: &str) -> Result<Vec<u8>> {
    let fields: Vec<&str> = line.splitn(7, ' ').collect();
    let markup = fields[0] != "0";
    let width: i32 = fields[1].parse().expect("invalid width");
    let indent: i32 = fields[2].parse().expect("invalid indent");
    let language = fields[3];
    let comments = fields[4];
    let integers = fields[5];
    let rest = format!(" {}", fields.get(6).copied().unwrap_or(""));
    let mut glb = build_arch();
    if language == "java" {
        glb.set_print_language("java-language")?;
    }
    for definition in rest.split('|') {
        if definition.trim().is_empty() {
            continue;
        }
        let mut stream = Cursor::new(definition.as_bytes().to_vec());
        parse_c(&mut glb, &mut stream)?;
    }
    let index = glb.print;
    glb.with_print_language(index, |lang, glb| {
        lang.set_output_stream(Vec::new());
        if markup {
            lang.set_markup(true);
            lang.set_packed_output(false);
        }
        lang.set_max_line_size(width)?;
        lang.set_indent_increment(indent);
        lang.set_comment_style(comments)?;
        lang.set_integer_format(integers)?;
        let mut ctx = PrintContext::new(glb, None);
        let id = lang.base_mut().emit.begin_document()?;
        lang.doc_type_definitions(&mut ctx)?;
        lang.base_mut().emit.end_document(id)?;
        lang.base_mut().emit.flush()?;
        Ok(lang.take_output_stream())
    })
}

#[test]
fn print_type_definitions_match_reference() {
    let cases_path = std::env::var("PRINTTYPES_CASES")
        .map(PathBuf::from)
        .unwrap_or_else(|_| data_path("cases.txt"));
    let expected_path = std::env::var("PRINTTYPES_EXPECTED")
        .map(PathBuf::from)
        .unwrap_or_else(|_| data_path("expected.txt"));
    let cases = std::fs::read_to_string(cases_path).expect("missing print cases");
    let expected = std::fs::read_to_string(expected_path).expect("missing print expected output");
    let mut compared = 0;
    for (line, wanted) in cases.lines().zip(expected.lines()) {
        let actual = match run_case(line) {
            Ok(output) => format!("OUT {}", escape(&output)),
            Err(err) => format!("ERR {}", escape(err.explain().as_bytes())),
        };
        assert_eq!(actual, wanted, "mismatch for case {}", line);
        compared += 1;
    }
    assert!(compared >= 150);
}
