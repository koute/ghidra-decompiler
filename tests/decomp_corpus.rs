use std::io::Cursor;
use std::path::{Path, PathBuf};

use ghidra_decompiler::ifacedecomp::{mainloop, register_all_commands, register_console_commands};
use ghidra_decompiler::interface::{IfaceStatus, new_out_stream};

struct CorpusBinary {
    binary: String,
    language: String,
    expected: PathBuf,
}

struct FunctionCase {
    name: String,
    transcript: String,
}

fn corpus_directory() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/data/decomp")
}

fn corpus_binaries() -> Vec<CorpusBinary> {
    let directory = corpus_directory();
    let manifest = std::fs::read_to_string(directory.join("manifest.tsv")).expect("unreadable decomp manifest");
    manifest
        .lines()
        .skip(1)
        .filter(|line| !line.trim().is_empty())
        .map(|line| {
            let columns: Vec<&str> = line.split('\t').collect();
            CorpusBinary {
                binary: columns[0].trim_start_matches("bin/").to_string(),
                language: columns[1].to_string(),
                expected: directory.join(columns[3]),
            }
        })
        .collect()
}

fn function_cases(expected: &Path) -> Vec<FunctionCase> {
    let text = std::fs::read_to_string(expected).expect("unreadable expected decompiler output");
    let mut cases = Vec::new();
    for section in text.split("=== function ").skip(1) {
        let (name, body) = section.split_once('\n').expect("function section without body");
        let transcript = body.split("--- exit").next().unwrap_or_default().to_string();
        cases.push(FunctionCase {
            name: name.to_string(),
            transcript,
        });
    }
    cases
}

fn decompile_transcript(language: &str, binary: &str, function_name: &str) -> String {
    let script = format!(
        "load file default-{language} {binary}\nread symbols\nload function {function_name}\ndecompile\nprint C\nquit\n"
    );
    let output = new_out_stream();
    let mut status = IfaceStatus::new_term("[decomp]> ", Box::new(Cursor::new(script.into_bytes())), output.clone());
    register_all_commands(&mut status);
    register_console_commands(&mut status);
    let run = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| mainloop(&mut status)));
    let transcript = output.lock().expect("poisoned output stream lock").clone();
    match run {
        Ok(()) => transcript,
        Err(payload) => {
            let message = payload
                .downcast_ref::<String>()
                .cloned()
                .or_else(|| payload.downcast_ref::<&str>().map(|text| text.to_string()))
                .unwrap_or_else(|| "unknown panic".to_string());
            format!("{transcript}\nPANIC: {message}\n")
        }
    }
}

fn first_difference(expected: &str, actual: &str) -> String {
    for (index, (expected_line, actual_line)) in expected.lines().zip(actual.lines()).enumerate() {
        if expected_line != actual_line {
            return format!("line {}: expected `{expected_line}` got `{actual_line}`", index + 1);
        }
    }
    format!(
        "line count: expected {} got {}",
        expected.lines().count(),
        actual.lines().count()
    )
}

#[test]
fn decomp_corpus() {
    let filter = std::env::var("DECOMP_FILTER").unwrap_or_default();
    let verbose = std::env::var_os("DECOMP_VERBOSE").is_some();
    std::env::set_current_dir(corpus_directory().join("bin")).expect("missing corpus bin directory");
    let previous_hook = std::panic::take_hook();
    std::panic::set_hook(Box::new(|_| {}));
    let mut total = 0;
    let mut matching = 0;
    let mut report = String::new();
    for corpus in corpus_binaries() {
        let mut binary_matching = 0;
        let mut binary_total = 0;
        for case in function_cases(&corpus.expected) {
            let key = format!("{}:{}", corpus.binary, case.name);
            if !filter.is_empty() && !key.contains(&filter) {
                continue;
            }
            binary_total += 1;
            let actual = decompile_transcript(&corpus.language, &corpus.binary, &case.name);
            if actual == case.transcript {
                binary_matching += 1;
            } else {
                report.push_str(&format!(
                    "MISMATCH {key}: {}\n",
                    first_difference(&case.transcript, &actual)
                ));
                if verbose {
                    report.push_str(&format!("--- actual\n{actual}--- end\n"));
                }
            }
        }
        if binary_total > 0 {
            report.push_str(&format!("{}: {binary_matching}/{binary_total}\n", corpus.binary));
        }
        total += binary_total;
        matching += binary_matching;
    }
    std::panic::set_hook(previous_hook);
    report.push_str(&format!("Total: {matching}/{total} functions identical\n"));
    println!("{report}");
    assert_eq!(matching, total, "decompiler corpus mismatches:\n{report}");
}
