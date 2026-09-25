#![no_main]

use ghidra_decompiler_fuzz::{
    divergence_report, install_panic_hook, port_sleigh_dump, reference_sleigh_dump, split_input,
};
use libfuzzer_sys::fuzz_target;

const BASE: u64 = 0x10000;
const MAXIMUM_CODE: usize = 4096;

fuzz_target!(|data: &[u8]| {
    install_panic_hook();
    let Some((language, code)) = split_input(data) else {
        return;
    };
    let code = &code[..code.len().min(MAXIMUM_CODE)];
    if std::env::var_os("FUZZ_PORT_ONLY").is_some() {
        eprintln!("{}", port_sleigh_dump(language, code, BASE));
        return;
    }
    let reference_start = std::time::Instant::now();
    let expected = reference_sleigh_dump(language, code, BASE);
    let port_start = std::time::Instant::now();
    let actual = port_sleigh_dump(language, code, BASE);
    if std::env::var_os("FUZZ_TIMING").is_some() {
        eprintln!(
            "timing c++ {:?} rust {:?}",
            port_start - reference_start,
            port_start.elapsed()
        );
    }
    if expected != actual {
        panic!(
            "sleigh divergence for {}: {}",
            language.processor,
            divergence_report(&expected, &actual)
        );
    }
});
