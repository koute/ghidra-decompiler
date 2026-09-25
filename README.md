DISCLAIMER: This was automatically ported by an agent from Ghidra's C++ source code into Rust.

# ghidra-decompiler

A pure Rust port of the Ghidra decompiler (Ghidra 12.2, `Ghidra/Features/Decompiler/src/decompile/cpp`).
It has no C, C++ or Java dependencies. The output is textually identical to the C++ decompiler on the
test corpora in `tests/data`.

## Library usage

```rust
let mut program = Program::open(Path::new("a.out"), None)?;
let main = program.functions()?.into_iter().find(|function| function.name == "main").expect("no main");
let instructions = program.disassemble(main.address, 4)?;
let pcode = program.pcode(main.address, 1)?;
let c_code = program.decompile(main.address)?;
let edges = program.call_graph()?;
```

## Examples

- `examples/inspect.rs` lists the functions of a binary, prints the disassembly, p-code and C code of
  `main`, and prints the call graph (`cargo run --release --example inspect -- <binary>`).
- `examples/raw_decompile.rs` decompiles a headerless code blob
  (`cargo run --release --example raw_decompile -- x86:LE:64:default:gcc <file>`).
- `examples/decomp.rs` is a port of the C++ `decomp_dbg` console (`consolemain.cc`), mainly useful to
  compare output with the C++ console (`cargo run --release --example decomp`).

- `Program::open(path, language)` and `Program::from_image(name, bytes, language)` load ELF, PE and Mach-O
  images. With `language = None` the language id is derived from the file header; otherwise pass a Ghidra
  language id such as `"x86:LE:64:default:gcc"`.
- `Program::from_raw_bytes(bytes, language, base_address)` loads a headerless code blob.
- `decompile(address)` creates a function at the address if the symbol table has none.
- `call_graph()` follows control flow of every known function and reports direct calls.
- `disassemble(address, count)` returns each instruction with its bytes.
- `discover_functions()` finds the functions of a binary without function symbols (see "Symbols").
- `data_symbols()` lists the data symbols; `set_symbol_name(address, name)` renames the function or data
  symbol that starts at the address, and an empty name restores the loaded name.
- `Program` is `Send`. Internal panics are returned as `Error::Lowlevel`.
- `Program::architecture()` exposes the underlying `Architecture` for everything the C++ decompiler offers
  (options, types, prototypes, actions, the console command set in `ifacedecomp`).

## Symbols

`Program::open` and `Program::from_image` load more symbols than the C++ loader, so the C output has
names where the C++ decompiler prints addresses:

- ELF function symbols from `.symtab` and from `.dynsym` (a stripped binary or a shared library keeps its
  exported names only there). Undefined `.symtab` entries are not functions.
- Import stubs: each PLT entry is named after the symbol of the GOT slot its p-code reads, so a call reads
  `printf(...)`. The stub finder follows constants through the stub's p-code instead of decoding each
  PLT layout; it is tested on x86-64 (`.plt`, `.plt.sec`), i686 PIE, AArch64, ARM and RISC-V 64. A stub
  whose name is also a defined function is `<name>@plt`.
- Data symbols (`STT_OBJECT` with a size, PE and Mach-O data symbols) and one pointer-sized symbol per
  GOT slot with a dynamic relocation (`<name>@got`).
- Demangled names (feature `demangle`, on by default): Rust legacy and v0 names without the hash, C++
  Itanium names without the parameter list. `FunctionEntry.symbol` has the mangled name. Every function
  is in the global scope under its full name, so a call reads `geometry::Circle::area(...)`.
- String literals: before `decompile`, each constant of the function that points into a read-only data
  section at NUL-terminated printable text of at least 4 characters gets a `char[n]` symbol, and the C
  output prints the literal.
- `discover_functions()`, for a binary without function symbols, follows the control flow from the entry
  point (or the base address of raw code) through direct calls and through constants that point into
  executable sections, such as the address of `main` that `_start` passes to `__libc_start_main`. It
  costs one flow analysis per function: about 8 s for a 1.5 MB static glibc binary.

`FunctionEntry.source` says where each function came from. `Program::open_with(path, language,
SymbolLoading::Loader)` loads only the symbols of the C++ loader; the C output of the corpus tests is
equal to the C++ decompiler's in that mode.

Limits: PowerPC32 call stubs in `.text` (lld names them `<n>.plt_pic32.<name>`) and PowerPC64 stubs,
which read the GOT through the TOC register, keep their names; MIPS has no PLT, and its calls go through
the GOT; PE import tables and Mach-O stubs are not named. Rust `&str` constants are not NUL-terminated
and stay addresses. A function reached only through a pointer table in data is not discovered.

## Processor support

The compiled SLEIGH specifications (`.sla`) and the `.ldefs`/`.pspec`/`.cspec` files are embedded with
`include_bytes!`, one Cargo feature per Ghidra processor directory. Default features: `x86`, `arm`, `aarch64`,
`mips`, `powerpc`, `riscv`. The feature `all-processors` enables all 39 processors. Processors outside the
default set decode through the same code but are tested best-effort only.
`sleigh_arch::LanguageRegistry::from_directory` loads language files from disk instead.

The embedded `.sla` files in `languages/` keep the Ghidra `.sla` header, but their payload is xz instead of zlib,
which keeps the crate under the crates.io size limit. Ghidra cannot read these files. The crate reads both
payload formats, so `from_directory` also accepts the `.sla` files of a Ghidra installation.

## Differences from Ghidra

The port fixes upstream decompiler bugs found by differential fuzzing instead of reproducing them:

- Operands that SLEIGH never builds no longer keep handle data from a previous instruction; a p-code
  template that refers to such an operand produces a bad-instruction-data error.
- Instructions with more than 16 bytes read zeros past the instruction buffer instead of adjacent memory.
- Raw p-code that writes to the constant space (for example a RISC-V write to `x0`) is dropped when the
  function is built, instead of leaving an op whose input is later deleted as dead code.
- Repeating action groups stop after 100 repeats and add the warning
  `Exceeded maximum repeat count for action <name>`, instead of looping forever when two rules undo
  each other.
- Common-subexpression elimination no longer matches an op with itself (an op that reads the same varnode in
  two inputs appears twice in the candidate list), which made the rule report a change forever.
- Symbol lookups in address spaces that a scope has no map for return no symbol instead of reading past
  the end of the scope's map table.
- Heritage deletes a free join-space varnode without readers (for example an old call output that a rule
  replaced) instead of dereferencing its missing reader. A free join varnode with several readers produces
  an error.

`tools/fuzz/reference_fixes.patch` applies the same behavior to the C++ reference so that the test data and
the differential fuzzers compare equal behavior.

## Tests

```
cargo test --release --features all-processors
```

- `datatests`: the 89 C++ decompiler data tests (733 checks).
- `decomp_corpus`: 1222 functions from 20 ELF binaries (x86-64, i686, ARM, Thumb, AArch64, MIPS BE/LE,
  PowerPC, RISC-V 32/64, each `-O0` and `-O2`); the transcript must equal the C++ `decomp_dbg` output.
- `sleigh_corpus`: disassembly and raw p-code for every language id, compared with the C++ SLEIGH decoder.
- Ports of the C++ unit tests and differential tests of individual modules.

`ci/jobs/` contains one script per CI job (tests, clippy, rustfmt, docs, MSRV check, package size check,
differential fuzzing); `.github/workflows/rust.yml` runs them. `ci/run-all-tests.sh` runs all jobs locally.

`tools/` contains the scripts that build the C++ reference and regenerate the test data; see
`tools/README.md`. `tools/trace/` compares action and rule traces between the C++ and Rust decompilers.

## License

Apache-2.0, as Ghidra. See `LICENSE` and `NOTICE`.
