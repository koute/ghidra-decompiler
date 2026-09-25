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
- `Program` is `Send`. Internal panics are returned as `Error::Lowlevel`.
- `Program::architecture()` exposes the underlying `Architecture` for everything the C++ decompiler offers
  (options, types, prototypes, actions, the console command set in `ifacedecomp`).

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
