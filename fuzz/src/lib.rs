use std::ffi::{CStr, CString, c_char};
use std::sync::OnceLock;

use ghidra_decompiler::program::Program;
use ghidra_decompiler::sleigh_arch::LanguageRegistry;

#[path = "../../tests/common/sleigh_dump.rs"]
mod sleigh_dump;

unsafe extern "C" {
    fn ghidra_cpp_sleigh_dump(language: *const c_char, data: *const u8, size: usize, base: u64) -> *mut c_char;
    fn ghidra_cpp_decompile(language: *const c_char, data: *const u8, size: usize) -> *mut c_char;
    fn ghidra_cpp_free(text: *mut c_char);
}

pub struct Language {
    pub processor: &'static str,
    pub full_id: &'static str,
}

pub const LANGUAGES: &[Language] = &[
    Language {
        processor: "x86:LE:64:default",
        full_id: "x86:LE:64:default:gcc",
    },
    Language {
        processor: "x86:LE:32:default",
        full_id: "x86:LE:32:default:gcc",
    },
    Language {
        processor: "ARM:LE:32:v8",
        full_id: "ARM:LE:32:v8:default",
    },
    Language {
        processor: "ARM:LE:32:v8T",
        full_id: "ARM:LE:32:v8T:default",
    },
    Language {
        processor: "AARCH64:LE:64:v8A",
        full_id: "AARCH64:LE:64:v8A:default",
    },
    Language {
        processor: "MIPS:BE:32:default",
        full_id: "MIPS:BE:32:default:default",
    },
    Language {
        processor: "MIPS:LE:32:default",
        full_id: "MIPS:LE:32:default:default",
    },
    Language {
        processor: "PowerPC:BE:32:default",
        full_id: "PowerPC:BE:32:default:default",
    },
    Language {
        processor: "RISCV:LE:64:default",
        full_id: "RISCV:LE:64:default:gcc",
    },
    Language {
        processor: "RISCV:LE:32:default",
        full_id: "RISCV:LE:32:default:gcc",
    },
];

pub fn install_panic_hook() {
    static INSTALLED: std::sync::Once = std::sync::Once::new();
    INSTALLED.call_once(|| {
        std::panic::set_hook(Box::new(|info| {
            if std::env::var_os("FUZZ_VERBOSE").is_some() {
                eprintln!("{info}");
            }
        }));
    });
}

pub fn split_input(data: &[u8]) -> Option<(&'static Language, &[u8])> {
    let (selector, code) = data.split_first()?;
    Some((&LANGUAGES[*selector as usize % LANGUAGES.len()], code))
}

fn owned_text(pointer: *mut c_char) -> String {
    let text = unsafe { CStr::from_ptr(pointer) }.to_string_lossy().into_owned();
    unsafe { ghidra_cpp_free(pointer) };
    text
}

pub fn reference_sleigh_dump(language: &Language, code: &[u8], base: u64) -> String {
    let language_id = CString::new(language.processor).expect("language id with NUL");
    owned_text(unsafe { ghidra_cpp_sleigh_dump(language_id.as_ptr(), code.as_ptr(), code.len(), base) })
}

pub fn reference_decompile(language: &Language, code: &[u8]) -> String {
    let language_id = CString::new(language.full_id).expect("language id with NUL");
    owned_text(unsafe { ghidra_cpp_decompile(language_id.as_ptr(), code.as_ptr(), code.len()) })
}

pub fn port_sleigh_dump(language: &Language, code: &[u8], base: u64) -> String {
    static REGISTRY: OnceLock<LanguageRegistry> = OnceLock::new();
    let registry = REGISTRY.get_or_init(LanguageRegistry::embedded);
    let mut lines = sleigh_dump::dump_language(registry, language.processor, base, code.to_vec(), &[]);
    if lines.last().is_some_and(|line| line.starts_with("exit\t")) {
        lines.pop();
    }
    let mut text = lines.join("\n");
    text.push('\n');
    text
}

pub fn port_decompile(language: &Language, code: &[u8]) -> String {
    let result =
        Program::from_raw_bytes(code.to_vec(), language.full_id, 0).and_then(|mut program| program.decompile(0));
    match result {
        Ok(text) => text,
        Err(error) => format!("error: {}", error.explain()),
    }
}

pub fn divergence_report(expected: &str, actual: &str) -> String {
    let mut report = first_difference(expected, actual);
    if std::env::var_os("FUZZ_VERBOSE").is_some() {
        report.push_str(&format!("\n--- c++\n{expected}--- rust\n{actual}--- end"));
    }
    report
}

fn first_difference(expected: &str, actual: &str) -> String {
    for (index, (expected_line, actual_line)) in expected.lines().zip(actual.lines()).enumerate() {
        if expected_line != actual_line {
            return format!("line {}:\n  c++:  {expected_line}\n  rust: {actual_line}", index + 1);
        }
    }
    format!(
        "line count: c++ {} rust {}",
        expected.lines().count(),
        actual.lines().count()
    )
}
