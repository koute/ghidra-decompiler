use std::path::{Path, PathBuf};

use ghidra_decompiler::program::Program;

fn regression_directory() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/data/fuzz")
}

fn decompiled_text(name: &str) -> (String, String) {
    let directory = regression_directory();
    let input = std::fs::read(directory.join(format!("{name}.bin"))).expect("missing regression input");
    let language = std::fs::read_to_string(directory.join(format!("{name}.language"))).expect("missing language");
    let expected =
        std::fs::read_to_string(directory.join(format!("{name}.expected"))).expect("missing expected output");
    let code = input[1..].to_vec();
    let actual = match Program::from_raw_bytes(code, language.trim(), 0).and_then(|mut program| program.decompile(0)) {
        Ok(text) => text,
        Err(error) => format!("error: {}\n", error.explain()),
    };
    (expected, actual)
}

#[test]
fn constant_output_ops_dropped() {
    let (expected, actual) = decompiled_text("constant_output");
    assert_eq!(actual, expected);
}

#[test]
fn undefined_operand_space_bad_data() {
    let (expected, actual) = decompiled_text("undefined_operand_space");
    assert_eq!(actual, expected);
    assert!(actual.contains("Bad instruction"));
}

#[test]
fn oscillating_rules_repeat_limit() {
    let (expected, actual) = decompiled_text("repeat_loop");
    assert_eq!(actual, expected);
    assert!(actual.contains("Exceeded maximum repeat count"));
}

#[test]
fn common_subexpression_self_match() {
    let (expected, actual) = decompiled_text("self_cse");
    assert_eq!(actual, expected);
}

#[test]
fn dead_free_join_varnode() {
    let (expected, actual) = decompiled_text("dead_join");
    assert_eq!(actual, expected);
    assert!(!actual.starts_with("error:"));
}
