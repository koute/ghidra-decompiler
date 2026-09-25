use std::sync::Arc;

use ghidra_decompiler::address::sign_extend;
use ghidra_decompiler::error::Error;
use ghidra_decompiler::float::FloatFormat;
use ghidra_decompiler::opbehavior::{
    FloatFormatTable, OpBehavior, OpBehaviorFloatAdd, OpBehaviorPtradd, OpBehaviorPtrsub, OpBehaviorRef,
    build_behaviors, register_instructions,
};
use ghidra_decompiler::opcodes::{OpCode, get_opname};

fn default_behaviors() -> Vec<Option<OpBehaviorRef>> {
    build_behaviors(&[FloatFormat::new(4), FloatFormat::new(8)])
}

fn behavior(table: &[Option<OpBehaviorRef>], opcode: OpCode) -> &OpBehaviorRef {
    table[opcode.index()].as_ref().expect("missing behavior")
}

fn describe(result: Result<u64, Error>) -> String {
    match result {
        Ok(value) => format!("R {:x}", value),
        Err(Error::Evaluation(message)) => format!("E Evaluation {}", message),
        Err(Error::Lowlevel(message)) => format!("E Lowlevel {}", message),
        Err(other) => format!("E Other {:?}", other),
    }
}

fn parse_hex(text: &str) -> u64 {
    u64::from_str_radix(text, 16).expect("invalid hex value")
}

#[test]
fn differential_against_reference() {
    let cases = include_str!("core_data/opbehavior_cases.txt");
    let expected = include_str!("core_data/opbehavior_expected.txt");
    let table = default_behaviors();
    let mut compared = 0;
    let mut failures = Vec::new();
    for (line_number, (case, want)) in cases.lines().zip(expected.lines()).enumerate() {
        let fields: Vec<&str> = case.split(' ').collect();
        let opc: usize = fields[0].parse().expect("invalid opcode index");
        let mode = fields[1];
        let sizeout: i32 = fields[2].parse().expect("invalid sizeout");
        let sizein: i32 = fields[3].parse().expect("invalid sizein");
        let slot: i32 = fields[4].parse().expect("invalid slot");
        let in1 = parse_hex(fields[5]);
        let in2 = parse_hex(fields[6]);
        let in3 = parse_hex(fields[7]);
        let Some(entry) = table[opc].as_ref() else {
            if want != "N" {
                failures.push(format!("line {}: missing behavior, want {}", line_number + 1, want));
            }
            continue;
        };
        let got = if mode == "m" {
            format!(
                "M {} {} {}",
                get_opname(entry.get_opcode()),
                entry.is_unary() as i32,
                entry.is_special() as i32
            )
        } else if want == "FPE" {
            let bit = sizein.wrapping_mul(8).wrapping_sub(1);
            let denom = sign_extend(in2 as i64, bit);
            let result = entry.evaluate_binary(sizeout, sizein, in1, in2);
            if denom == 0 {
                assert!(matches!(result, Err(Error::Evaluation(_))), "line {}", line_number + 1);
            } else {
                assert!(result.is_ok(), "line {}", line_number + 1);
            }
            continue;
        } else {
            describe(match mode {
                "u" => entry.evaluate_unary(sizeout, sizein, in1),
                "b" => entry.evaluate_binary(sizeout, sizein, in1, in2),
                "t" => entry.evaluate_ternary(sizeout, sizein, in1, in2, in3),
                "ru" => entry.recover_input_unary(sizeout, in1, sizein),
                _ => entry.recover_input_binary(slot, sizeout, in1, sizein, in2),
            })
        };
        compared += 1;
        if got != want {
            failures.push(format!(
                "line {}: {} -> got {} want {}",
                line_number + 1,
                case,
                got,
                want
            ));
        }
    }
    assert!(compared > 9000);
    assert!(
        failures.is_empty(),
        "{} failures:\n{}",
        failures.len(),
        failures[..failures.len().min(30)].join("\n")
    );
}

#[test]
fn registration_table_shape() {
    let mut table = Vec::new();
    register_instructions(&mut table, &[]);
    assert_eq!(table.len(), OpCode::Max.index());
    assert!(table[OpCode::Blank.index()].is_none());
    assert!(table[OpCode::Unused1.index()].is_none());
    for (index, slot) in table.iter().enumerate().skip(1) {
        if index == OpCode::Unused1.index() {
            continue;
        }
        let entry = slot.as_ref().expect("missing behavior");
        assert_eq!(entry.get_opcode().index(), index);
    }
    let load = behavior(&table, OpCode::Load);
    assert!(load.is_special());
    assert!(!load.is_unary());
    let ptradd = behavior(&table, OpCode::Ptradd);
    assert!(!ptradd.is_special());
    assert_eq!(
        ptradd.evaluate_ternary(4, 4, 1, 2, 3),
        Err(Error::Lowlevel("Ternary emulation unimplemented for LABEL".to_string()))
    );
    assert!(behavior(&table, OpCode::Copy).is_unary());
    assert!(behavior(&table, OpCode::FloatNeg).is_unary());
    assert!(!behavior(&table, OpCode::FloatAdd).is_unary());
}

#[test]
fn float_behaviors_without_formats() {
    let mut table = Vec::new();
    register_instructions(&mut table, &[]);
    assert_eq!(
        behavior(&table, OpCode::FloatAdd).evaluate_binary(4, 4, 0x3f800000, 0x3f800000),
        Err(Error::Lowlevel(
            "Binary emulation unimplemented for FLOAT_ADD".to_string()
        ))
    );
    assert_eq!(
        behavior(&table, OpCode::FloatSqrt).evaluate_unary(8, 8, 0),
        Err(Error::Lowlevel(
            "Unary emulation unimplemented for FLOAT_SQRT".to_string()
        ))
    );
    let adder = OpBehaviorFloatAdd::new(Arc::new(FloatFormatTable::new(&[FloatFormat::new(4)])));
    assert_eq!(adder.evaluate_binary(4, 4, 0x3f800000, 0x3f800000), Ok(0x40000000));
}

#[test]
fn integer_edge_cases() {
    let table = default_behaviors();
    let sdiv = behavior(&table, OpCode::IntSdiv);
    assert_eq!(sdiv.evaluate_binary(1, 1, 0x80, 0xff), Ok(0x80));
    assert_eq!(
        sdiv.evaluate_binary(8, 8, 0x8000000000000000, u64::MAX),
        Ok(0x8000000000000000)
    );
    assert_eq!(
        sdiv.evaluate_binary(1, 1, 5, 0x100),
        Err(Error::Evaluation("Divide by 0".to_string()))
    );
    assert_eq!(
        behavior(&table, OpCode::IntDiv).evaluate_binary(4, 4, 5, 0),
        Err(Error::Evaluation("Divide by 0".to_string()))
    );
    let srem = behavior(&table, OpCode::IntSrem);
    assert_eq!(srem.evaluate_binary(8, 8, 0x8000000000000000, u64::MAX), Ok(0));
    assert_eq!(srem.evaluate_binary(1, 1, 0xf9, 3), Ok(0xff));
    assert_eq!(
        behavior(&table, OpCode::IntRem).evaluate_binary(4, 4, 5, 0),
        Err(Error::Evaluation("Remainder by 0".to_string()))
    );
    let left = behavior(&table, OpCode::IntLeft);
    assert_eq!(left.evaluate_binary(4, 4, 1, 32), Ok(0));
    assert_eq!(left.evaluate_binary(16, 4, 1, 64), Ok(1));
    let sright = behavior(&table, OpCode::IntSright);
    assert_eq!(sright.evaluate_binary(4, 4, 0x80000000, 40), Ok(0xffffffff));
    assert_eq!(sright.evaluate_binary(4, 4, 0x80000000, 4), Ok(0xf8000000));
    let lzcount = behavior(&table, OpCode::Lzcount);
    assert_eq!(lzcount.evaluate_unary(4, 4, 1), Ok(31));
    assert_eq!(lzcount.evaluate_unary(4, 4, 0x100000000), Ok(u64::MAX));
    assert_eq!(
        behavior(&table, OpCode::Popcount).evaluate_unary(1, 8, u64::MAX),
        Ok(64)
    );
    assert_eq!(
        behavior(&table, OpCode::IntSext).evaluate_unary(8, 1, 0x80),
        Ok(0xffffffffffffff80)
    );
    assert_eq!(
        behavior(&table, OpCode::Subpiece).evaluate_binary(1, 8, 0x1122, 8),
        Ok(0)
    );
    assert_eq!(
        behavior(&table, OpCode::Piece).evaluate_binary(4, 2, 0x12, 0x34),
        Ok(0x120034)
    );
    assert_eq!(
        behavior(&table, OpCode::IntZext).recover_input_unary(4, 0x1ff, 1),
        Err(Error::Evaluation(
            "Output is not in range of zext operation".to_string()
        ))
    );
    assert_eq!(
        behavior(&table, OpCode::IntAnd).recover_input_binary(0, 4, 1, 4, 1),
        Err(Error::Lowlevel(
            "Cannot recover input parameter without loss of information".to_string()
        ))
    );
}

#[test]
fn unregistered_pointer_behaviors() {
    assert_eq!(OpBehaviorPtradd::new().evaluate_ternary(4, 4, 0x10, 2, 8), Ok(0x20));
    assert_eq!(OpBehaviorPtrsub::new().evaluate_binary(2, 2, 0xffff, 2), Ok(1));
}
