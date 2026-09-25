use std::path::PathBuf;

use ghidra_decompiler::printc::{print_char_hex_escape, print_unicode_c_style};
use ghidra_decompiler::printjava::print_unicode_java_style;
use ghidra_decompiler::printlanguage::{format_binary, most_natural_base, unicode_needs_escape};

fn data_path(name: &str) -> PathBuf {
    let mut path = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    path.push("tests");
    path.push("printlang_data");
    path.push(name);
    path
}

fn run_command(line: &str) -> Option<String> {
    let fields: Vec<&str> = line.split_whitespace().collect();
    if fields.is_empty() {
        return None;
    }
    let result = match fields[0] {
        "base" => {
            let value = u64::from_str_radix(fields[1], 16).expect("invalid hex value");
            format!("base {}", most_natural_base(value))
        }
        "bin" => {
            let value = u64::from_str_radix(fields[1], 16).expect("invalid hex value");
            let mut text = String::new();
            format_binary(&mut text, value);
            format!("bin {}", text)
        }
        "escape" => {
            let first: i32 = fields[1].parse().expect("invalid first codepoint");
            let last: i32 = fields[2].parse().expect("invalid last codepoint");
            let mut current = unicode_needs_escape(first);
            let mut text = format!("escape {}:{}", first, current as i32);
            for codepoint in first + 1..=last {
                let value = unicode_needs_escape(codepoint);
                if value != current {
                    current = value;
                    text.push_str(&format!(" {}:{}", codepoint, current as i32));
                }
            }
            text
        }
        "hexesc" => {
            let value: i32 = fields[1].parse().expect("invalid value");
            let mut text = String::new();
            print_char_hex_escape(&mut text, value);
            format!("hexesc {}", text)
        }
        "uc" => {
            let value: i32 = fields[1].parse().expect("invalid value");
            let mut text = String::new();
            print_unicode_c_style(&mut text, value);
            format!("uc {}", text)
        }
        "uj" => {
            let value: i32 = fields[1].parse().expect("invalid value");
            let mut text = String::new();
            print_unicode_java_style(&mut text, value);
            format!("uj {}", text)
        }
        other => panic!("unknown command {}", other),
    };
    Some(result)
}

#[test]
fn print_language_helpers_match_reference() {
    let cases = std::fs::read_to_string(data_path("cases.txt")).expect("missing printlang cases");
    let expected = std::fs::read_to_string(data_path("expected.txt")).expect("missing printlang expected output");
    let mut expected_lines = expected.lines();
    let mut count = 0;
    for line in cases.lines() {
        let Some(actual) = run_command(line) else {
            continue;
        };
        let wanted = expected_lines.next().expect("expected output is too short");
        assert_eq!(actual, wanted, "mismatch for case {}", line);
        count += 1;
    }
    assert!(count > 5000);
}
