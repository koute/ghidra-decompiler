use std::path::Path;

use ghidra_decompiler::program::Program;

fn main() -> ghidra_decompiler::error::Result<()> {
    let path = std::env::args().nth(1).expect("usage: inspect <binary>");
    let mut program = Program::open(Path::new(&path), None)?;
    println!("{}", program.language_id());
    for function in program.functions()? {
        println!("{:#x} {}", function.address, function.name);
    }
    let main_address = program
        .functions()?
        .into_iter()
        .find(|function| function.name == "main")
        .map(|function| function.address);
    if let Some(address) = main_address {
        for instruction in program.disassemble(address, 4)? {
            println!(
                "{:#x} {} {}",
                instruction.address, instruction.mnemonic, instruction.operands
            );
        }
        for instruction in program.pcode(address, 1)? {
            for operation in &instruction.operations {
                println!("{operation}");
            }
        }
        println!("{}", program.decompile(address)?);
    }
    for edge in program.call_graph()? {
        println!("{:#x} -> {:#x} at {:#x}", edge.caller, edge.callee, edge.call_site);
    }
    Ok(())
}
