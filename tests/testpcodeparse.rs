use std::collections::BTreeMap;
use std::path::PathBuf;
use std::sync::{Arc, Mutex};

use ghidra_decompiler::address::Address;
use ghidra_decompiler::error::{Error, Result};
use ghidra_decompiler::globalcontext::ContextInternal;
use ghidra_decompiler::loadimage::LoadImage;
use ghidra_decompiler::marshal::XmlEncode;
use ghidra_decompiler::pcodeparse::PcodeSnippet;
use ghidra_decompiler::sleigh::{SharedContextDatabase, Sleigh};

struct NullLoadImage;

impl LoadImage for NullLoadImage {
    fn get_file_name(&self) -> &str {
        "null"
    }

    fn load_fill(&self, ptr: &mut [u8], _addr: &Address) -> Result<()> {
        ptr.fill(0);
        Ok(())
    }

    fn get_arch_type(&self) -> String {
        "null".to_string()
    }

    fn adjust_vma(&mut self, _adjust: i64) {}
}

fn unescape(text: &str) -> Vec<u8> {
    let bytes = text.as_bytes();
    let mut res = Vec::new();
    let mut position = 0;
    while position < bytes.len() {
        if bytes[position] == b'\\' && position + 3 < bytes.len() && bytes[position + 1] == b'x' {
            let digits = std::str::from_utf8(&bytes[position + 2..position + 4]).expect("invalid escape");
            res.push(u8::from_str_radix(digits, 16).expect("invalid escape digits"));
            position += 4;
        } else {
            res.push(bytes[position]);
            position += 1;
        }
    }
    res
}

fn escape(text: &str) -> String {
    let mut res = String::new();
    for byte in text.bytes() {
        if !(0x20..0x7f).contains(&byte) || byte == b'\\' {
            res.push_str(&format!("\\x{byte:02x}"));
        } else {
            res.push(byte as char);
        }
    }
    res
}

fn load_sleigh(path: &PathBuf) -> Sleigh {
    let context: SharedContextDatabase = Arc::new(Mutex::new(ContextInternal::new()));
    let mut sleigh = Sleigh::new(Arc::new(NullLoadImage), context);
    let data = std::fs::read(path).expect("missing sla file");
    sleigh.initialize_from_sla(&data).expect("sla file does not load");
    sleigh
}

fn run_case(sleigh: &Sleigh, base: u32, operands: &str, snippet: &[u8]) -> String {
    let mut compiler = PcodeSnippet::new(sleigh.base());
    if operands != "-" {
        for (index, name) in operands.split(',').enumerate() {
            compiler.add_operand(name, index as i32);
        }
    }
    compiler.set_unique_base(base);
    match compiler.parse_stream(snippet) {
        Err(err) => format!("EXC\t{}", escape(err.explain())),
        Ok(false) => format!("ERR\t{}", escape(compiler.get_error_message())),
        Ok(true) => {
            let tpl = compiler.release_result().expect("missing parse result");
            let mut encoder = XmlEncode::new(false);
            tpl.encode(&mut encoder, -1);
            format!(
                "OK\t{:x}\t{}\t{}",
                compiler.get_unique_base(),
                escape(compiler.get_error_message()),
                encoder.as_str()
            )
        }
    }
}

#[test]
fn pcodeparse_matches_reference() {
    let crate_dir = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let data = crate_dir.join("tests/pcodeparse_data");
    let cases = std::fs::read(data.join("cases.txt")).expect("missing cases");
    let expected = std::fs::read(data.join("expected.txt")).expect("missing expected output");
    let cases = String::from_utf8(cases).expect("cases are ascii");
    let expected = String::from_utf8(expected).expect("expected output is ascii");
    let mut languages: BTreeMap<String, Sleigh> = BTreeMap::new();
    let mut failures = Vec::new();
    let mut total = 0;
    for (line, expected_line) in cases.lines().zip(expected.lines()) {
        let fields: Vec<&str> = line.split('\t').collect();
        let sleigh = languages
            .entry(fields[0].to_string())
            .or_insert_with(|| load_sleigh(&crate_dir.join("languages").join(fields[0])));
        let base = u32::from_str_radix(fields[1], 16).expect("invalid unique base");
        let actual = run_case(sleigh, base, fields[2], &unescape(fields[3]));
        total += 1;
        if actual != expected_line {
            failures.push(format!(
                "case {total}: {line}\n  expected: {expected_line}\n  actual:   {actual}"
            ));
        }
    }
    assert_eq!(total, expected.lines().count(), "case and expected line counts differ");
    for failure in failures.iter().take(20) {
        eprintln!("{failure}");
    }
    assert!(failures.is_empty(), "{} of {total} cases differ", failures.len());
}

#[test]
fn lexer_tokens() {
    let mut lexer = ghidra_decompiler::pcodeparse::PcodeLexer::new();
    lexer.initialize(b"x s>> 0x10 f<= # comment\n 18446744073709551616 ;");
    let mut tokens = Vec::new();
    loop {
        let token = lexer.get_next_token();
        tokens.push(token);
        if token == 0 {
            break;
        }
    }
    use ghidra_decompiler::pcodeparse::*;
    assert_eq!(
        tokens,
        vec![
            STRING,
            OP_SRIGHT,
            INTEGER,
            OP_FLESSEQUAL,
            BADINTEGER,
            b';' as i32,
            ENDOFSTREAM,
            0
        ]
    );
    let _ = Error::Lowlevel(String::new());
}
