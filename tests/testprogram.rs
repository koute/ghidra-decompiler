mod common;

use std::collections::BTreeMap;
use std::path::{Path, PathBuf};

use common::gunzip;
use ghidra_decompiler::program::Program;

fn data_directory() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/data")
}

fn corpus_binary(name: &str) -> PathBuf {
    data_directory().join("decomp/bin").join(name)
}

fn expected_c_output(binary: &str) -> BTreeMap<String, String> {
    let path = data_directory().join("decomp/expected").join(format!("{binary}.txt"));
    let text = std::fs::read_to_string(path).expect("unreadable expected decompiler output");
    let mut outputs = BTreeMap::new();
    for section in text.split("=== function ").skip(1) {
        let (name, body) = section.split_once('\n').expect("function section without body");
        let printed = body
            .split("[decomp]> print C\n")
            .nth(1)
            .and_then(|rest| rest.split("[decomp]> quit").next())
            .expect("transcript without print C output");
        outputs.insert(name.to_string(), printed.to_string());
    }
    outputs
}

fn decompilation_reference_check(binary: &str) {
    let mut program = Program::open(&corpus_binary(binary), None).expect("corpus binary does not load");
    let addresses: BTreeMap<String, u64> = program
        .functions()
        .expect("function list unavailable")
        .into_iter()
        .map(|function| (function.name, function.address))
        .collect();
    let expected = expected_c_output(binary);
    let mut mismatches = Vec::new();
    for (name, reference) in expected.iter() {
        let address = *addresses
            .get(name)
            .unwrap_or_else(|| panic!("function {name} missing from {binary}"));
        let actual = program
            .decompile(address)
            .unwrap_or_else(|error| format!("error: {error}"));
        if &actual != reference {
            mismatches.push(name.clone());
        }
    }
    assert!(
        mismatches.is_empty(),
        "{binary}: decompiler output differs for {mismatches:?}"
    );
}

#[test]
fn x86_64_decompilation_reference() {
    decompilation_reference_check("x86_64-O2");
}

#[test]
fn aarch64_decompilation_reference() {
    decompilation_reference_check("aarch64-O0");
}

#[test]
fn elf_language_detection() {
    let expectations = [
        ("x86_64-O0", "x86:LE:64:default:gcc"),
        ("i686-O0", "x86:LE:32:default:gcc"),
        ("aarch64-O0", "AARCH64:LE:64:v8A:default"),
        ("mips-O0", "MIPS:BE:32:default:default"),
        ("ppc-O0", "PowerPC:BE:32:default:default"),
        ("riscv64-O0", "RISCV:LE:64:default:gcc"),
    ];
    for (binary, language) in expectations {
        let program = Program::open(&corpus_binary(binary), None).expect("corpus binary does not load");
        assert_eq!(program.language_id(), language, "{binary}");
    }
}

struct DumpInstruction {
    address: u64,
    length: usize,
    mnemonic: String,
    operands: String,
    operations: Vec<String>,
}

fn reference_dump(corpus_name: &str, limit: usize) -> Vec<DumpInstruction> {
    let path = data_directory()
        .join("sleigh/expected")
        .join(format!("{corpus_name}.txt.gz"));
    let compressed = std::fs::read(path).expect("unreadable sleigh corpus");
    let text = String::from_utf8(gunzip(&compressed)).expect("sleigh corpus is not UTF-8");
    let mut instructions: Vec<DumpInstruction> = Vec::new();
    for line in text.lines() {
        let fields: Vec<&str> = line.splitn(5, '\t').collect();
        match fields[0] {
            "I" => {
                if instructions.len() == limit {
                    break;
                }
                instructions.push(DumpInstruction {
                    address: u64::from_str_radix(fields[1].trim_start_matches("0x"), 16).expect("bad address"),
                    length: fields[2].parse().expect("bad length"),
                    mnemonic: fields[3].to_string(),
                    operands: fields.get(4).copied().unwrap_or_default().to_string(),
                    operations: Vec::new(),
                });
            }
            "P" => instructions
                .last_mut()
                .expect("p-code before instruction")
                .operations
                .push(fields[1].to_string()),
            _ => {}
        }
    }
    instructions
}

#[test]
fn disassembly_and_pcode_reference() {
    let program = Program::open(&corpus_binary("x86_64-O2"), None).expect("corpus binary does not load");
    let reference = reference_dump("x86_LE_64_default.code-x86_64-O2", 300);
    let start = reference[0].address;
    let instructions = program.disassemble(start, reference.len()).expect("disassembly failed");
    let pcode = program.pcode(start, reference.len()).expect("p-code generation failed");
    for ((expected, instruction), operations) in reference.iter().zip(instructions.iter()).zip(pcode.iter()) {
        assert_eq!(instruction.address, expected.address);
        assert_eq!(instruction.length, expected.length, "length at {:#x}", expected.address);
        assert_eq!(
            instruction.mnemonic, expected.mnemonic,
            "mnemonic at {:#x}",
            expected.address
        );
        assert_eq!(
            instruction.operands, expected.operands,
            "operands at {:#x}",
            expected.address
        );
        let printed: Vec<String> = operations
            .operations
            .iter()
            .map(|operation| operation.to_string())
            .collect();
        assert_eq!(printed, expected.operations, "p-code at {:#x}", expected.address);
    }
}

#[test]
fn raw_bytes_disassembly() {
    let bytes = vec![0x55, 0x48, 0x89, 0xe5, 0xc3];
    let program = Program::from_raw_bytes(bytes, "x86:LE:64:default:gcc", 0x1000).expect("raw image does not load");
    let instructions = program.disassemble(0x1000, 3).expect("disassembly failed");
    let text: Vec<(u64, String, String)> = instructions
        .into_iter()
        .map(|instruction| (instruction.address, instruction.mnemonic, instruction.operands))
        .collect();
    assert_eq!(
        text,
        vec![
            (0x1000, "PUSH".to_string(), "RBP".to_string()),
            (0x1001, "MOV".to_string(), "RBP,RSP".to_string()),
            (0x1004, "RET".to_string(), String::new()),
        ]
    );
}

#[test]
fn call_graph_direct_calls() {
    let mut program = Program::open(&corpus_binary("x86_64-O0"), None).expect("corpus binary does not load");
    let addresses: BTreeMap<String, u64> = program
        .functions()
        .expect("function list unavailable")
        .into_iter()
        .map(|function| (function.name, function.address))
        .collect();
    let edges = program.call_graph().expect("call graph construction failed");
    let caller = addresses["call_varargs"];
    let callee = addresses["sum_varargs"];
    assert!(
        edges.iter().any(|edge| edge.caller == caller && edge.callee == callee),
        "missing call_varargs -> sum_varargs edge"
    );
    assert!(edges.iter().all(|edge| edge.caller != addresses["my_strlen"]));
}

#[test]
fn failed_decompilation_recovery() {
    let binary = "x86_64-O0";
    let mut program = Program::open(&corpus_binary(binary), None).expect("corpus binary does not load");
    assert!(program.decompile(0).is_err(), "address without code decompiled");
    let main_address = program
        .functions()
        .expect("function list unavailable")
        .into_iter()
        .find(|function| function.name == "main")
        .expect("main missing")
        .address;
    let output = program.decompile(main_address).expect("decompilation after failure");
    assert_eq!(output, expected_c_output(binary)["main"]);
}
