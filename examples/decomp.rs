use std::io::BufReader;
use std::path::Path;
use std::process::ExitCode;

use ghidra_decompiler::ifacedecomp::{mainloop, register_all_commands, register_console_commands};
use ghidra_decompiler::interface::{IfaceError, IfaceStatus, new_out_stream, out_write};
use ghidra_decompiler::sleigh_arch::{add_global_language_directory, scan_global_sleigh_directories};

fn main() -> ExitCode {
    let args: Vec<String> = std::env::args().collect();
    let mut initscript: Option<String> = None;
    let mut extrapaths: Vec<String> = Vec::new();
    let mut index = 1;
    while index < args.len() && args[index].starts_with('-') {
        let option = args[index].as_bytes().get(1).copied();
        if option == Some(b'i') {
            index += 1;
            initscript = args.get(index).cloned();
        } else if option == Some(b's') {
            index += 1;
            if let Some(path) = args.get(index) {
                extrapaths.push(path.clone());
            }
        }
        index += 1;
    }
    if let Ok(sleighhome) = std::env::var("SLEIGHHOME")
        && let Err(err) = scan_global_sleigh_directories(Path::new(&sleighhome))
    {
        eprintln!("{}", err.explain());
    }
    for path in extrapaths.iter() {
        if let Err(err) = add_global_language_directory(Path::new(path)) {
            eprintln!("{}", err.explain());
        }
    }
    let optr = new_out_stream();
    let mut status = IfaceStatus::new_term("[decomp]> ", Box::new(BufReader::new(std::io::stdin())), optr.clone());
    status.attach_sink(&optr, Box::new(std::io::stdout()));
    register_all_commands(&mut status);
    register_console_commands(&mut status);
    if let Some(script) = initscript {
        match status.push_script_file(&script, "init> ") {
            Ok(()) => {}
            Err(IfaceError::Parse(message)) => {
                out_write(&optr, &format!("{message}\n"));
                status.done = true;
            }
            Err(err) => {
                eprintln!("Interface error: {}", err.explain());
                return ExitCode::from(2);
            }
        }
    }
    if !status.done {
        mainloop(&mut status);
    }
    let retval = if status.is_in_error() { 1 } else { 0 };
    status.flush_all();
    ExitCode::from(retval)
}
