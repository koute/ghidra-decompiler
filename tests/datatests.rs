use std::panic::{AssertUnwindSafe, catch_unwind};
use std::path::{Path, PathBuf};

use ghidra_decompiler::interface::new_out_stream;
use ghidra_decompiler::testfunction::{FunctionTestCollection, new_test_console};
use ghidra_decompiler::xml::xml_tree;

const EXPECTED_TOTAL: i32 = 733;

struct FileOutcome {
    name: String,
    checks: i32,
    applied: i32,
    succeeded: i32,
    problem: Option<String>,
}

fn data_directory() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/data/datatests")
}

fn test_files() -> Vec<PathBuf> {
    let filter = std::env::var("DATATESTS_FILTER").unwrap_or_default();
    let mut files: Vec<PathBuf> = std::fs::read_dir(data_directory())
        .expect("datatests directory is readable")
        .filter_map(|entry| entry.ok().map(|entry| entry.path()))
        .filter(|path| path.extension().is_some_and(|ext| ext == "xml"))
        .filter(|path| {
            filter.is_empty()
                || path
                    .file_name()
                    .and_then(|name| name.to_str())
                    .is_some_and(|name| name.contains(&filter))
        })
        .collect();
    files.sort();
    files
}

fn language_embedded(path: &Path) -> bool {
    let content = std::fs::read_to_string(path).expect("datatest file is readable");
    let Some(start) = content.find("arch=\"") else {
        return true;
    };
    let rest = &content[start + 6..];
    let arch = &rest[..rest.find('"').unwrap_or(0)];
    ghidra_decompiler::sleigh_arch::LanguageRegistry::embedded()
        .resolve_architecture(arch)
        .is_ok()
}

fn count_checks(path: &Path) -> i32 {
    let bytes = std::fs::read(path).expect("datatest file is readable");
    match xml_tree(&bytes) {
        Ok(doc) => doc
            .get_root()
            .get_children()
            .iter()
            .filter(|child| child.get_name() == "stringmatch")
            .count() as i32,
        Err(_) => 0,
    }
}

thread_local! {
    static PANIC_LOCATION: std::cell::RefCell<String> = const { std::cell::RefCell::new(String::new()) };
}

fn panic_message(payload: &(dyn std::any::Any + Send)) -> String {
    let message = if let Some(text) = payload.downcast_ref::<&str>() {
        text.to_string()
    } else if let Some(text) = payload.downcast_ref::<String>() {
        text.clone()
    } else {
        "unknown panic".to_string()
    };
    let location = PANIC_LOCATION.with(|cell| cell.borrow().clone());
    format!("{message} at {location}")
}

fn run_file(path: &Path) -> FileOutcome {
    let name = path
        .file_name()
        .and_then(|name| name.to_str())
        .unwrap_or_default()
        .to_string();
    let checks = count_checks(path);
    let filename = path.to_string_lossy().into_owned();
    let result = catch_unwind(AssertUnwindSafe(|| {
        let output = new_out_stream();
        let mut console = new_test_console(output.clone());
        console.set_error_is_done(true);
        let mut collection = FunctionTestCollection::new();
        let mut failures = Vec::new();
        let counts = collection.run_test_file(&filename, &mut console, &mut failures);
        if std::env::var_os("DATATESTS_CONSOLE").is_some() {
            eprintln!("{}", output.lock().expect("poisoned output stream lock"));
        }
        (counts, failures)
    }));
    match result {
        Ok((Some((applied, succeeded)), failures)) => FileOutcome {
            name,
            checks,
            applied,
            succeeded,
            problem: if failures.is_empty() {
                None
            } else {
                Some(failures.join("; "))
            },
        },
        Ok((None, failures)) => FileOutcome {
            name,
            checks,
            applied: 0,
            succeeded: 0,
            problem: Some(failures.join("; ")),
        },
        Err(payload) => FileOutcome {
            name,
            checks,
            applied: 0,
            succeeded: 0,
            problem: Some(format!("panic: {}", panic_message(payload.as_ref()))),
        },
    }
}

#[test]
fn datatests() {
    let files = test_files();
    let previous_hook = std::panic::take_hook();
    std::panic::set_hook(Box::new(|info| {
        let location = info
            .location()
            .map(|location| format!("{}:{}", location.file(), location.line()))
            .unwrap_or_default();
        PANIC_LOCATION.with(|cell| *cell.borrow_mut() = location);
        if std::env::var("DATATESTS_BACKTRACE").is_ok() {
            let backtrace = std::backtrace::Backtrace::force_capture().to_string();
            let frames: Vec<&str> = backtrace
                .lines()
                .filter(|line| line.contains("ghidra_decompiler::") || line.contains("ghidra-decompiler/src"))
                .collect();
            eprintln!("panic backtrace:\n{}", frames.join("\n"));
        }
    }));
    let (runnable, skipped): (Vec<PathBuf>, Vec<PathBuf>) = files.into_iter().partition(|path| language_embedded(path));
    let outcomes: Vec<FileOutcome> = runnable.iter().map(|path| run_file(path)).collect();
    std::panic::set_hook(previous_hook);
    let mut total_checks = 0;
    let mut total_applied = 0;
    let mut total_succeeded = 0;
    let mut report = String::new();
    for outcome in outcomes.iter() {
        total_checks += outcome.checks;
        total_applied += outcome.applied;
        total_succeeded += outcome.succeeded;
        let status = if outcome.succeeded == outcome.checks && outcome.problem.is_none() {
            "pass"
        } else {
            "FAIL"
        };
        report.push_str(&format!(
            "{status} {}: {}/{} passed ({} applied)",
            outcome.name, outcome.succeeded, outcome.checks, outcome.applied
        ));
        if let Some(problem) = &outcome.problem {
            let first_line = problem.lines().next().unwrap_or_default();
            report.push_str(&format!(" -- {first_line}"));
        }
        report.push('\n');
    }
    report.push_str(&format!(
        "Total: {total_succeeded}/{total_checks} checks passed ({total_applied} applied) in {} files, {} skipped (processor feature disabled)\n",
        outcomes.len(),
        skipped.len()
    ));
    println!("{report}");
    let filtered = std::env::var("DATATESTS_FILTER").is_ok_and(|filter| !filter.is_empty());
    if !filtered && skipped.is_empty() {
        assert_eq!(total_checks, EXPECTED_TOTAL, "unexpected number of datatest checks");
    }
    assert_eq!(total_succeeded, total_checks, "datatest checks failed:\n{report}");
}
