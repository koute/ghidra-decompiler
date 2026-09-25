use std::fmt::Write as _;

use ghidra_decompiler::error::Error;
use ghidra_decompiler::xml::{Element, xml_tree};

fn hex_bytes(bytes: &[u8]) -> String {
    let mut text = String::new();
    for byte in bytes {
        let _ = write!(text, "{byte:02x}");
    }
    text
}

fn decode_hex(line: &str) -> Vec<u8> {
    (0..line.len() / 2)
        .map(|index| u8::from_str_radix(&line[index * 2..index * 2 + 2], 16).expect("valid hex digit pair"))
        .collect()
}

fn dump_string(out: &mut String, text: &str) {
    let _ = write!(out, "{}:{}", text.len(), hex_bytes(text.as_bytes()));
}

fn dump_element(out: &mut String, el: &Element) {
    out.push('(');
    dump_string(out, el.get_name());
    let _ = write!(out, " {}", el.get_num_attributes());
    for index in 0..el.get_num_attributes() {
        out.push(' ');
        dump_string(out, el.get_attribute_name(index));
        out.push(' ');
        dump_string(out, el.get_attribute_value_index(index));
    }
    out.push(' ');
    dump_string(out, el.get_content());
    let _ = write!(out, " {}", el.get_children().len());
    for child in el.get_children() {
        dump_element(out, child);
    }
    out.push(')');
}

fn dump_case(input: &[u8]) -> String {
    let mut out = String::new();
    match xml_tree(input) {
        Ok(doc) => dump_element(&mut out, doc.get_root()),
        Err(Error::Decoder(message)) => {
            out.push_str("ERROR ");
            dump_string(&mut out, &message);
        }
        Err(other) => panic!("unexpected error kind {other:?}"),
    }
    out
}

fn normalize_expected(line: &str) -> String {
    let bytes = line.as_bytes();
    let mut out = String::new();
    let mut pos = 0;
    while pos < bytes.len() {
        let start = pos;
        while pos < bytes.len() && bytes[pos].is_ascii_digit() {
            pos += 1;
        }
        if pos > start && pos < bytes.len() && bytes[pos] == b':' {
            let length: usize = line[start..pos].parse().expect("length prefix");
            let hex = &line[pos + 1..pos + 1 + length * 2];
            let raw = decode_hex(hex);
            let text = String::from_utf8_lossy(&raw).into_owned();
            let _ = write!(out, "{}:{}", text.len(), hex_bytes(text.as_bytes()));
            pos += 1 + length * 2;
        } else if pos > start {
            out.push_str(&line[start..pos]);
        } else {
            out.push(bytes[pos] as char);
            pos += 1;
        }
    }
    out
}

fn data_path(name: &str) -> String {
    format!("{}/tests/core_data/{}", env!("CARGO_MANIFEST_DIR"), name)
}

#[test]
fn xml_parser_matches_reference() {
    let cases_path = std::env::var("XML_CASES").unwrap_or_else(|_| data_path("xml_cases.txt"));
    let expected_path = std::env::var("XML_EXPECTED").unwrap_or_else(|_| data_path("xml_expected.txt"));
    let cases = std::fs::read_to_string(&cases_path).expect("readable xml cases file");
    let expected = std::fs::read_to_string(&expected_path).expect("readable xml expected file");
    let mut failures = 0;
    let mut total = 0;
    for (case, want) in cases.lines().zip(expected.lines()) {
        total += 1;
        let got = dump_case(&decode_hex(case));
        let want = normalize_expected(want);
        if got != want {
            failures += 1;
            if failures <= 10 {
                eprintln!("case {case}\n  want {want}\n  got  {got}");
            }
        }
    }
    assert!(total > 0);
    assert_eq!(
        failures, 0,
        "{failures} of {total} xml cases differ from the C++ reference"
    );
}

#[test]
fn xml_nesting_depth_matches_reference() {
    let accepted = [1, 3, 4, 6, 7, 10];
    let mut index = 0;
    for depth in 4996..=5001 {
        for prolog in ["", " "] {
            for leaf in ["", "<b c=\"&lt;\"/>", "<!-- x -->"] {
                index += 1;
                let text = format!("{}{}{}{}\n", prolog, "<a>".repeat(depth), leaf, "</a>".repeat(depth));
                let outcome = xml_tree(text.as_bytes());
                if accepted.contains(&index) {
                    assert!(outcome.is_ok(), "case {index} should parse");
                } else {
                    assert_eq!(
                        outcome.err(),
                        Some(Error::Decoder("memory exhausted".to_string())),
                        "case {index}"
                    );
                }
            }
        }
    }
}
