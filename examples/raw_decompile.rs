use ghidra_decompiler::program::Program;

fn main() {
    let arguments: Vec<String> = std::env::args().collect();
    if arguments.len() < 3 {
        eprintln!("usage: raw_decompile <language> <file> [skip]");
        std::process::exit(2);
    }
    let skip: usize = arguments.get(3).and_then(|text| text.parse().ok()).unwrap_or(0);
    let bytes = std::fs::read(&arguments[2]).expect("unreadable input file");
    let code = bytes[skip.min(bytes.len())..].to_vec();
    match Program::from_raw_bytes(code, &arguments[1], 0).and_then(|mut program| program.decompile(0)) {
        Ok(text) => print!("{text}"),
        Err(error) => println!("error: {}", error.explain()),
    }
}
