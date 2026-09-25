mod common;
#[path = "common/sleigh_dump.rs"]
mod sleigh_dump;

use std::path::{Path, PathBuf};
use std::sync::Mutex;

use common::gunzip;
use ghidra_decompiler::sleigh_arch::LanguageRegistry;
use sleigh_dump::dump_language;

const PRIMARY_PROCESSORS: &[&str] = &["x86", "ARM", "AARCH64", "MIPS", "PowerPC", "RISCV"];

const KNOWN_FAILURES: &[&str] = &["V850_LE_32_default.random", "V850_LE_32_v850e3v5.random"];

struct Corpus {
    name: String,
    language: String,
    base: u64,
    overrides: Vec<(String, u32)>,
    input: PathBuf,
    expected: PathBuf,
}

fn parse_number(text: &str) -> u64 {
    if let Some(hex) = text.strip_prefix("0x") {
        u64::from_str_radix(hex, 16).expect("invalid hex number")
    } else {
        text.parse().expect("invalid number")
    }
}

fn read_manifest(dir: &Path) -> Vec<Corpus> {
    let text = std::fs::read_to_string(dir.join("manifest.tsv")).expect("missing manifest");
    let mut corpora = Vec::new();
    for line in text.lines().skip(1) {
        if line.is_empty() {
            continue;
        }
        let fields: Vec<&str> = line.split('\t').collect();
        let overrides = if fields[3] == "-" {
            Vec::new()
        } else {
            fields[3]
                .split(',')
                .map(|setting| {
                    let (name, value) = setting.split_once('=').expect("invalid context setting");
                    (name.to_string(), parse_number(value) as u32)
                })
                .collect()
        };
        corpora.push(Corpus {
            name: fields[0].to_string(),
            language: fields[1].to_string(),
            base: parse_number(fields[2]),
            overrides,
            input: dir.join(fields[4]),
            expected: dir.join(fields[5]),
        });
    }
    corpora
}

enum Outcome {
    Skipped,
    Match(usize),
    Mismatch(String),
}

fn run_corpus(registry: &LanguageRegistry, corpus: &Corpus) -> Outcome {
    if registry
        .resolve_architecture(&format!("{}:default", corpus.language))
        .is_err()
    {
        return Outcome::Skipped;
    }
    let bytes = std::fs::read(&corpus.input).expect("missing corpus input");
    let expected_data = gunzip(&std::fs::read(&corpus.expected).expect("missing expected output"));
    let expected_text = String::from_utf8_lossy(&expected_data);
    let expected: Vec<&str> = expected_text.lines().collect();
    let actual = dump_language(registry, &corpus.language, corpus.base, bytes, &corpus.overrides);
    for (index, line) in expected.iter().enumerate() {
        match actual.get(index) {
            Some(actual_line) if actual_line == line => {}
            Some(actual_line) => {
                return Outcome::Mismatch(format!(
                    "line {}:\n  expected: {line}\n  actual:   {actual_line}",
                    index + 1
                ));
            }
            None => {
                return Outcome::Mismatch(format!(
                    "line {}:\n  expected: {line}\n  actual:   <missing>",
                    index + 1
                ));
            }
        }
    }
    if actual.len() > expected.len() {
        return Outcome::Mismatch(format!(
            "line {}:\n  expected: <end of output>\n  actual:   {}",
            expected.len() + 1,
            actual[expected.len()]
        ));
    }
    Outcome::Match(expected.len())
}

fn is_primary(language: &str) -> bool {
    let processor = language.split(':').next().unwrap_or("");
    PRIMARY_PROCESSORS.contains(&processor)
}

#[test]
fn sleigh_corpus() {
    let dir = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests/data/sleigh");
    let registry = LanguageRegistry::embedded();
    let mut corpora = read_manifest(&dir);
    if let Ok(filter) = std::env::var("SLEIGH_CORPUS_FILTER") {
        corpora.retain(|corpus| corpus.name.contains(&filter));
    }
    let next = Mutex::new(0usize);
    let results: Mutex<Vec<(usize, Outcome)>> = Mutex::new(Vec::new());
    let workers = std::thread::available_parallelism()
        .map(|count| count.get())
        .unwrap_or(4)
        .min(corpora.len().max(1));
    std::thread::scope(|scope| {
        for _ in 0..workers {
            scope.spawn(|| {
                loop {
                    let index = {
                        let mut guard = next.lock().expect("work index lock");
                        let index = *guard;
                        *guard += 1;
                        index
                    };
                    if index >= corpora.len() {
                        break;
                    }
                    let outcome = run_corpus(&registry, &corpora[index]);
                    results.lock().expect("result lock").push((index, outcome));
                }
            });
        }
    });
    let mut results = results.into_inner().expect("result lock");
    results.sort_by_key(|(index, _)| *index);
    let mut primary_failures = Vec::new();
    let mut unexpected_failures = Vec::new();
    let mut fixed_known = Vec::new();
    let mut skipped = 0;
    let mut matched = 0;
    let mut instructions = 0;
    let mut known_failing = 0;
    for (index, outcome) in results {
        let corpus = &corpora[index];
        match outcome {
            Outcome::Skipped => skipped += 1,
            Outcome::Match(lines) => {
                matched += 1;
                instructions += lines;
                if KNOWN_FAILURES.contains(&corpus.name.as_str()) {
                    fixed_known.push(corpus.name.clone());
                }
            }
            Outcome::Mismatch(detail) => {
                let report = format!("{}: {detail}", corpus.name);
                if is_primary(&corpus.language) {
                    primary_failures.push(report);
                } else if KNOWN_FAILURES.contains(&corpus.name.as_str()) {
                    known_failing += 1;
                } else {
                    unexpected_failures.push(report);
                }
            }
        }
    }
    eprintln!(
        "sleigh corpus: {matched} identical ({instructions} lines), {known_failing} known failures, {skipped} skipped (processor feature disabled)"
    );
    for report in primary_failures.iter().chain(unexpected_failures.iter()) {
        eprintln!("{report}");
    }
    for name in fixed_known.iter() {
        eprintln!("{name}: listed in KNOWN_FAILURES but now matches");
    }
    assert!(
        primary_failures.is_empty() && unexpected_failures.is_empty() && fixed_known.is_empty(),
        "{} primary mismatches, {} unexpected non-primary mismatches, {} known failures now passing",
        primary_failures.len(),
        unexpected_failures.len(),
        fixed_known.len()
    );
}
