use std::path::PathBuf;

use ghidra_decompiler::grammar::{GrammarLexer, GrammarToken, TokenValue};

fn data_path(name: &str) -> PathBuf {
    let mut path = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    path.push("tests");
    path.push("grammarlex_data");
    path.push(name);
    path
}

fn unescape(text: &str) -> Vec<u8> {
    let bytes = text.as_bytes();
    let mut result = Vec::new();
    let mut pos = 0;
    while pos < bytes.len() {
        if bytes[pos] == b'%' && pos + 2 < bytes.len() {
            let hex = std::str::from_utf8(&bytes[pos + 1..pos + 3]).expect("invalid escape");
            result.push(u8::from_str_radix(hex, 16).expect("invalid escape"));
            pos += 3;
        } else {
            result.push(bytes[pos]);
            pos += 1;
        }
    }
    result
}

fn escape(text: &str) -> String {
    let mut result = String::new();
    for byte in text.bytes() {
        if !(0x21..0x7f).contains(&byte) || byte == b'%' {
            result.push_str(&format!("%{:02x}", byte));
        } else {
            result.push(byte as char);
        }
    }
    result
}

fn run_case(maxbuf: i32, input: &[u8]) -> String {
    let mut reader: &[u8] = input;
    let mut lexer = GrammarLexer::new(maxbuf);
    lexer.push_file("stream", Box::new(&mut reader));
    let mut out = String::new();
    for _ in 0..200 {
        let mut token = GrammarToken::new();
        lexer.get_next_token(&mut token).expect("lexer failure");
        let tp = token.get_type();
        out.push_str(&format!("{}:{}:{}", tp, token.get_line_no(), token.get_col_no()));
        if tp == GrammarToken::INTEGER || tp == GrammarToken::CHARCONSTANT {
            out.push_str(&format!(":{:x}", token.get_integer()));
        } else if tp == GrammarToken::IDENTIFIER || tp == GrammarToken::STRINGVAL {
            let text = match &token.value {
                TokenValue::Text(text) => text.clone(),
                _ => String::new(),
            };
            out.push_str(&format!(":{}", escape(&text)));
        }
        out.push(' ');
        if tp == GrammarToken::ENDOFFILE || tp == GrammarToken::BADTOKEN {
            break;
        }
    }
    out.push_str("| ");
    out.push_str(lexer.get_error());
    out
}

#[test]
fn grammar_lexer_matches_reference() {
    let cases = std::fs::read_to_string(
        std::env::var("LEX_CASES")
            .map(PathBuf::from)
            .unwrap_or_else(|_| data_path("cases.txt")),
    )
    .expect("missing lexer cases");
    let expected = std::fs::read_to_string(
        std::env::var("LEX_EXPECTED")
            .map(PathBuf::from)
            .unwrap_or_else(|_| data_path("expected.txt")),
    )
    .expect("missing lexer expected output");
    let mut compared = 0;
    for (line, wanted) in cases.lines().zip(expected.lines()) {
        if wanted == "CRASH" {
            continue;
        }
        let space = line.find(' ').expect("missing buffer size");
        let maxbuf: i32 = line[..space].parse().expect("invalid buffer size");
        let input = unescape(&line[space + 1..]);
        let actual = run_case(maxbuf, &input);
        assert_eq!(actual.trim_end(), wanted.trim_end(), "mismatch for case {}", line);
        compared += 1;
    }
    assert!(compared > 2000);
}
