use std::path::{Path, PathBuf};

use ghidra_decompiler::program::{FunctionEntry, FunctionSource, Program};

fn fixture(name: &str) -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("tests/data/program")
        .join(name)
}

fn load(name: &str) -> Program {
    Program::open(&fixture(name), None).unwrap_or_else(|error| panic!("{name} does not load: {error:?}"))
}

fn function_named<'list>(functions: &'list [FunctionEntry], name: &str) -> &'list FunctionEntry {
    functions
        .iter()
        .find(|function| function.name == name)
        .unwrap_or_else(|| panic!("no function {name} in {functions:?}"))
}

#[test]
fn dynsym_function_names() {
    let program = load("libext-x86_64.so");
    let functions = program.functions().expect("function list unavailable");
    let ext = function_named(&functions, "ext");
    assert_eq!(ext.source, FunctionSource::DynamicSymbol);
    assert_eq!(ext.symbol, None);
}

fn check_import_stub_names(name: &str) {
    let mut program = load(name);
    let functions = program.functions().expect("function list unavailable");
    assert!(
        functions.iter().all(|function| function.address != 0),
        "{name}: an undefined symbol is listed as a function at address 0: {functions:?}"
    );
    let ext = function_named(&functions, "ext");
    assert_eq!(ext.source, FunctionSource::ImportStub, "{name}");
    let main = function_named(&functions, "main").address;
    let c_code = program.decompile(main).expect("main does not decompile");
    assert!(c_code.contains("ext("), "{name}: no call to ext in\n{c_code}");
    assert!(!c_code.contains("func_0x"), "{name}: unnamed call in\n{c_code}");
}

#[test]
fn import_stub_names_x86_64_lazy() {
    check_import_stub_names("plt-x86_64-lazy");
}

#[test]
fn import_stub_names_x86_64_ibt() {
    check_import_stub_names("plt-x86_64-ibt");
}

#[test]
fn import_stub_names_i686_pie() {
    check_import_stub_names("plt-i686");
}

#[test]
fn import_stub_names_aarch64() {
    check_import_stub_names("plt-aarch64");
}

#[test]
fn import_stub_names_arm() {
    check_import_stub_names("plt-arm");
}

#[test]
fn import_stub_names_riscv64() {
    check_import_stub_names("plt-riscv64");
}

#[test]
fn demangled_cpp_names() {
    let mut program = load("names-cpp");
    let functions = program.functions().expect("function list unavailable");
    let area = function_named(&functions, "geometry::Circle::area");
    assert_eq!(area.symbol.as_deref(), Some("_ZNK8geometry6Circle4areaEv"));
    let overloads: Vec<&str> = functions
        .iter()
        .filter(|function| function.name == "geometry::scale")
        .filter_map(|function| function.symbol.as_deref())
        .collect();
    assert_eq!(overloads, ["_ZN8geometry5scaleEi", "_ZN8geometry5scaleEii"]);
    let main = function_named(&functions, "main").address;
    let c_code = program.decompile(main).expect("main does not decompile");
    assert!(
        c_code.contains("geometry::Circle::area(") && c_code.contains("geometry::scale("),
        "{c_code}"
    );
}

#[test]
fn demangled_rust_names() {
    let v0 = load("names-rust-v0").functions().expect("function list unavailable");
    let generic = function_named(&v0, "names::item_count::<alloc::vec::Vec<u8>>");
    assert!(generic.symbol.as_deref().is_some_and(|symbol| symbol.starts_with("_R")));

    let legacy = load("names-rust-legacy")
        .functions()
        .expect("function list unavailable");
    let plain = function_named(&legacy, "names::item_count");
    assert!(
        plain
            .symbol
            .as_deref()
            .is_some_and(|symbol| symbol.ends_with('E') && symbol.contains("17h")),
        "the hash is part of the symbol, not of the name: {plain:?}"
    );
}

#[test]
fn data_symbol_names() {
    let mut program = load("data-x86_64");
    let functions = program.functions().expect("function list unavailable");
    let main = function_named(&functions, "main").address;
    let main_code = program.decompile(main).expect("main does not decompile");
    assert!(main_code.contains("counter"), "{main_code}");
    let lookup = function_named(&functions, "lookup").address;
    let lookup_code = program.decompile(lookup).expect("lookup does not decompile");
    assert!(lookup_code.contains("table"), "{lookup_code}");

    let mut library = load("libext-x86_64.so");
    let ext = function_named(&library.functions().expect("function list unavailable"), "ext").address;
    let ext_code = library.decompile(ext).expect("ext does not decompile");
    assert!(ext_code.contains("ext_counter"), "{ext_code}");
}

#[test]
fn string_literals() {
    let mut program = load("data-x86_64");
    let functions = program.functions().expect("function list unavailable");
    let main = function_named(&functions, "main").address;
    let main_code = program.decompile(main).expect("main does not decompile");
    assert!(main_code.contains(r#""hello %d\n""#), "{main_code}");
    let lookup = function_named(&functions, "lookup").address;
    let lookup_code = program.decompile(lookup).expect("lookup does not decompile");
    assert!(
        !lookup_code.contains('"'),
        "the number table in .rodata is printed as a string: {lookup_code}"
    );
}

#[test]
fn discovered_functions_in_stripped_binary() {
    let mut program = load("stripped-static");
    program.discover_functions().expect("discovery failed");
    let functions = program.functions().expect("function list unavailable");
    let expected = std::fs::read_to_string(fixture("stripped-static.functions")).expect("unreadable address list");
    for line in expected.lines() {
        let (name, address) = line.split_once(' ').expect("malformed address list");
        let address = u64::from_str_radix(address.trim_start_matches("0x"), 16).expect("malformed address");
        let function = functions
            .iter()
            .find(|function| function.address == address)
            .unwrap_or_else(|| panic!("{name} at {address:#x} is not discovered"));
        assert_eq!(function.source, FunctionSource::Discovered, "{name}");
    }
}

#[test]
fn discovered_functions_in_raw_code() {
    let call_then_return = vec![0xe8, 0x01, 0x00, 0x00, 0x00, 0xc3, 0x31, 0xc0, 0xc3];
    let mut program =
        Program::from_raw_bytes(call_then_return, "x86:LE:64:default:gcc", 0x1000).expect("raw code does not load");
    program.discover_functions().expect("discovery failed");
    let addresses: Vec<u64> = program
        .functions()
        .expect("function list unavailable")
        .iter()
        .map(|function| function.address)
        .collect();
    assert_eq!(addresses, [0x1000, 0x1006]);
}

#[test]
fn instruction_bytes() {
    let program = load("data-x86_64");
    let main = function_named(&program.functions().expect("function list unavailable"), "main").address;
    let instructions = program.disassemble(main, 3).expect("disassembly failed");
    let bytes: Vec<&[u8]> = instructions
        .iter()
        .map(|instruction| instruction.bytes.as_slice())
        .collect();
    assert_eq!(
        bytes,
        [&[0xf3, 0x0f, 0x1e, 0xfa][..], &[0x53], &[0x89, 0xfb]],
        "objdump -d prints these bytes"
    );
}

#[test]
fn symbol_rename() {
    let mut program = load("data-x86_64");
    let functions = program.functions().expect("function list unavailable");
    let main = function_named(&functions, "main").address;
    let lookup = function_named(&functions, "lookup").address;
    let counter = program
        .data_symbols()
        .expect("data symbol list unavailable")
        .into_iter()
        .find(|data| data.name == "counter")
        .expect("no data symbol counter")
        .address;

    program
        .set_symbol_name(lookup, "table_entry")
        .expect("function rename failed");
    program
        .set_symbol_name(counter, "hit_count")
        .expect("data rename failed");
    let renamed_code = program.decompile(main).expect("main does not decompile");
    assert!(
        renamed_code.contains("table_entry(") && renamed_code.contains("hit_count"),
        "{renamed_code}"
    );
    let functions = program.functions().expect("function list unavailable");
    assert_eq!(function_named(&functions, "table_entry").address, lookup);

    program
        .set_symbol_name(lookup, "")
        .expect("function name restore failed");
    program.set_symbol_name(counter, "").expect("data name restore failed");
    let restored_code = program.decompile(main).expect("main does not decompile");
    assert!(
        restored_code.contains("lookup(") && restored_code.contains("counter"),
        "{restored_code}"
    );

    assert!(
        program.set_symbol_name(lookup, "main").is_err(),
        "two functions named main"
    );
    assert!(
        program.set_symbol_name(main + 1, "inside_main").is_err(),
        "no symbol starts there"
    );
}

#[test]
fn function_name_without_symbol() {
    let mut program = load("stripped-static");
    let expected = std::fs::read_to_string(fixture("stripped-static.functions")).expect("unreadable address list");
    let main_line = expected
        .lines()
        .find(|line| line.starts_with("main "))
        .expect("no main in the address list");
    let main = u64::from_str_radix(main_line.trim_start_matches("main 0x"), 16).expect("malformed address");

    program
        .set_function_name(main, "program_main")
        .expect("a function without a symbol and without discovery is not renamed");
    let functions = program.functions().expect("function list unavailable");
    assert_eq!(function_named(&functions, "program_main").address, main);
    let c_code = program.decompile(main).expect("main does not decompile");
    assert!(c_code.contains("program_main("), "{c_code}");

    program.set_function_name(main, "").expect("name restore failed");
    let functions = program.functions().expect("function list unavailable");
    assert_eq!(function_named(&functions, &format!("func_0x{main:08x}")).address, main);
}

#[test]
fn data_name_rename() {
    let mut program = load("data-x86_64");
    let counter = program
        .data_symbols()
        .expect("data symbol list unavailable")
        .into_iter()
        .find(|data| data.name == "counter")
        .expect("no data symbol counter")
        .address;
    program.set_data_name(counter, "hit_count").expect("data rename failed");
    assert!(
        program
            .data_symbols()
            .expect("data symbol list unavailable")
            .iter()
            .any(|data| data.name == "hit_count" && data.address == counter)
    );
    assert!(
        program.set_data_name(counter + 1, "inside_counter").is_err(),
        "the address is inside the data symbol counter"
    );
}

#[test]
fn data_label_without_symbol() {
    let mut program = load("stripped-static");
    let expected = std::fs::read_to_string(fixture("stripped-static.functions")).expect("unreadable address list");
    let main_line = expected
        .lines()
        .find(|line| line.starts_with("main "))
        .expect("no main in the address list");
    let main = u64::from_str_radix(main_line.trim_start_matches("main 0x"), 16).expect("malformed address");
    let data_line = std::fs::read_to_string(fixture("stripped-static.data")).expect("unreadable data address");
    let data_address = u64::from_str_radix(
        data_line
            .split_whitespace()
            .nth(1)
            .expect("malformed data address")
            .trim_start_matches("0x"),
        16,
    )
    .expect("malformed data address");

    assert!(program.is_code_address(main), "main is not in an executable section");
    assert!(
        !program.is_code_address(data_address),
        "an address past the data symbols is code"
    );

    program
        .set_data_name(data_address, "state_word")
        .expect("no label was created");
    assert!(
        program
            .data_symbols()
            .expect("data symbol list unavailable")
            .iter()
            .any(|data| data.name == "state_word" && data.address == data_address)
    );
    assert!(
        program
            .functions()
            .expect("function list unavailable")
            .iter()
            .all(|function| function.address != data_address),
        "the label is a function"
    );
}
