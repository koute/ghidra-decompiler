use ghidra_decompiler::architecture::Architecture;
use ghidra_decompiler::program::Program;

fn require_send<T: Send>() {}

#[test]
fn architecture_and_program_send() {
    require_send::<Architecture>();
    require_send::<Program>();
}
