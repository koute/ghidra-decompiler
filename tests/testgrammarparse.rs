use std::io::Cursor;
use std::path::PathBuf;

use ghidra_decompiler::architecture::{Architecture, ArchitectureCapability, ErrorStream};
use ghidra_decompiler::fspec::PrototypePieces;
use ghidra_decompiler::grammar::{parse_c, parse_protopieces, parse_type};
use ghidra_decompiler::types::{TypeId, TypeKind, TypeMetatype};
use ghidra_decompiler::xml::DocumentStorage;
use ghidra_decompiler::xml_arch::XML_ARCHITECTURE_CAPABILITY;

fn data_path(name: &str) -> PathBuf {
    let mut path = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    path.push("tests");
    path.push("grammarparse_data");
    path.push(name);
    path
}

fn escape(text: &str) -> String {
    let mut result = String::new();
    for byte in text.bytes() {
        if !(0x20..0x7f).contains(&byte) || byte == b'%' {
            result.push_str(&format!("%{:02x}", byte));
        } else {
            result.push(byte as char);
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

fn describe(glb: &Architecture, ct: Option<TypeId>, depth: i32) -> String {
    let Some(ct) = ct else {
        return "null".to_string();
    };
    let types = glb.types.as_deref().expect("type factory is not initialized");
    let datatype = types.get(ct);
    let mut text = format!(
        "{}:{}:{}",
        datatype.get_name(),
        datatype.get_metatype() as i32,
        datatype.get_size()
    );
    if depth > 3 {
        return text;
    }
    match datatype.get_metatype() {
        TypeMetatype::Ptr => {
            text.push_str("->");
            text.push_str(&describe(glb, Some(datatype.get_ptr_to()), depth + 1));
        }
        TypeMetatype::Array => {
            text.push_str(&format!("[{}]", datatype.num_elements()));
            text.push_str(&describe(glb, Some(datatype.get_base()), depth + 1));
        }
        TypeMetatype::Struct => {
            text.push('{');
            for field in datatype.get_fields() {
                text.push_str(&format!(
                    "{}@{}={};",
                    field.name,
                    field.offset,
                    describe(glb, Some(field.tp), depth + 1)
                ));
            }
            text.push('}');
        }
        TypeMetatype::Code => {
            if let TypeKind::Code(code) = &datatype.kind
                && let Some(proto) = code.proto.as_deref()
            {
                text.push_str(&format!(
                    "({}{})->{}",
                    proto.num_params(glb),
                    if proto.is_dotdotdot() { "..." } else { "" },
                    describe(glb, Some(proto.get_output_type(glb)), depth + 1)
                ));
            }
        }
        _ => {}
    }
    text
}

fn run_case(glb: &mut Architecture, line: &str) -> String {
    let kind = line.as_bytes()[0];
    let text = line.as_bytes()[2..].to_vec();
    let mut stream = Cursor::new(text);
    match kind {
        b'T' => {
            let mut name = String::new();
            match parse_type(&mut stream, &mut name, glb) {
                Ok(ct) => format!("OK {} {}", name, escape(&describe(glb, Some(ct), 0))),
                Err(err) => format!("ERR {}", escape(err.explain())),
            }
        }
        b'P' => {
            let mut pieces = PrototypePieces::default();
            match parse_protopieces(&mut pieces, &mut stream, glb) {
                Ok(()) => {
                    let model = match pieces.model {
                        Some(model) => glb.proto_models[model].get_name().to_string(),
                        None => "none".to_string(),
                    };
                    let mut out = format!(
                        "OK {} {} {} {}",
                        model,
                        pieces.name,
                        escape(&describe(glb, pieces.outtype, 0)),
                        pieces.first_var_arg_slot
                    );
                    for (name, tp) in pieces.innames.iter().zip(pieces.intypes.iter()) {
                        out.push_str(&format!(" {}={}", name, escape(&describe(glb, Some(*tp), 0))));
                    }
                    out
                }
                Err(err) => format!("ERR {}", escape(err.explain())),
            }
        }
        _ => match parse_c(glb, &mut stream) {
            Ok(()) => "OK".to_string(),
            Err(err) => format!("ERR {}", escape(err.explain())),
        },
    }
}

#[test]
fn grammar_parser_matches_reference() {
    let cases_path = std::env::var("PARSE_CASES")
        .map(PathBuf::from)
        .unwrap_or_else(|_| data_path("cases.txt"));
    let expected_path = std::env::var("PARSE_EXPECTED")
        .map(PathBuf::from)
        .unwrap_or_else(|_| data_path("expected.txt"));
    let cases = std::fs::read_to_string(cases_path).expect("missing parser cases");
    let expected = std::fs::read_to_string(expected_path).expect("missing parser expected output");
    let mut glb = build_arch();
    let mut compared = 0;
    for (line, wanted) in cases.lines().zip(expected.lines()) {
        let actual = run_case(&mut glb, line);
        assert_eq!(actual, wanted, "mismatch for case {}", line);
        compared += 1;
    }
    assert!(compared > 2000);
}
