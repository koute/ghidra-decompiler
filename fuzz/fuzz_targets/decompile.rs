#![no_main]

use ghidra_decompiler_fuzz::{divergence_report, install_panic_hook, port_decompile, reference_decompile, split_input};
use libfuzzer_sys::fuzz_target;

const MAXIMUM_CODE: usize = 256;

fuzz_target!(|data: &[u8]| {
    install_panic_hook();
    let Some((language, code)) = split_input(data) else {
        return;
    };
    if code.is_empty() {
        return;
    }
    let code = &code[..code.len().min(MAXIMUM_CODE)];
    if std::env::var_os("FUZZ_PORT_ONLY").is_some() {
        let port_start = std::time::Instant::now();
        let actual = port_decompile(language, code);
        eprintln!(
            "port only {:?}: {}",
            port_start.elapsed(),
            actual.lines().next().unwrap_or_default()
        );
        return;
    }
    let reference_start = std::time::Instant::now();
    let expected = reference_decompile(language, code);
    let reference_time = reference_start.elapsed();
    if expected.starts_with("error: reference crash:") {
        if std::env::var_os("FUZZ_VERBOSE").is_some() {
            eprintln!("skipped: {expected}");
            eprintln!(
                "rust result: {}",
                port_decompile(language, code).lines().next().unwrap_or_default()
            );
        }
        return;
    }
    let port_start = std::time::Instant::now();
    let actual = port_decompile(language, code);
    if std::env::var_os("FUZZ_TIMING").is_some() {
        eprintln!(
            "timing c++ {reference_time:?} rust {:?} {}",
            port_start.elapsed(),
            language.full_id
        );
    }
    if expected != actual {
        panic!(
            "decompile divergence for {}: {}",
            language.full_id,
            divergence_report(&expected, &actual)
        );
    }
});
