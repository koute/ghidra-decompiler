# Test corpus tools

These scripts regenerate the differential-test data under `tests/data/` from the
C++ reference decompiler. They expect the reference build under `reference/ghidra`: run `build_reference.sh` first. It fetches Ghidra at
commit d6192cb3f9 if the clone is missing, builds `decomp_dbg`, `decomp_test_dbg` and `sleigh_opt`, and
compiles all `.sla` files. Build products go to `reference/build/`.

| Script | Regenerates | Requires |
| --- | --- | --- |
| `corpus/regenerate.sh` | `tests/data/decomp/`: 20 ELF binaries (10 targets x `-O0`/`-O2`: x86-64, i686, ARM, Thumb, AArch64, MIPS BE/LE, PPC32, RISC-V 64/32) built from `corpus/src/*.c`, and the C++ decompiler output for every function | gcc cross compilers (i686, armhf, aarch64, powerpc, riscv64), clang + lld (MIPS), `binutils-multiarch-dev` (the script installs missing packages with apt) |
| `sleigh_dump/regenerate.sh` | `tests/data/sleigh/`: byte corpora (4 KB pseudo-random bytes for each of the 202 language ids of all processors, plus the `.text` sections of the decomp binaries) and the C++ disassembly and raw p-code for each | the decomp binaries (runs `corpus/regenerate.sh` first if they are missing), `readelf`, python3 |

Helper scripts: `corpus/build_decomp.sh` links `reference/build/decomp_multiarch_dbg` (the reference console
linked against the all-targets BFD library), `sleigh_dump/build.sh` builds `reference/build/sleigh_dump` from
`sleigh_dump/sleigh_dump.cc`.

Both regenerations are deterministic: running them twice produces byte-identical files.

Supported processor families for the port: x86, ARM, AARCH64, MIPS, PowerPC, RISCV. The SLEIGH corpus still
covers every language id; the other processors are best-effort (the Rust test classifies rows by processor).

P-code snippet parser (`pcodeparse`): `pcodeparse/gen_tables.py <cpp>/pcodeparse.cc <crate>/src/pcodeparse/tables.rs`
transcribes the bison 3.5.1 LALR tables of the reference parser into Rust. `pcodeparse/gen_cases.py [count] [seed]`
(needs `core_ref/pcodeparse_probe`, built with `make -C core_ref pcodeparse_probe`) collects every `<pcode>` body of the
embedded .pspec/.cspec files plus seeded fuzz snippets and writes `tests/pcodeparse_data/{cases,expected}.txt` from
the C++ `PcodeSnippet` output (deterministic).

Embedded language files: `update_languages.sh` copies the compiled `.sla` files and the `.ldefs`/`.pspec`/`.cspec`
files of every processor (`data/languages` and its direct subdirectories) into `languages/` (it recompresses the
payload of each `.sla` file from zlib to xz, see the main README),
regenerates `src/embedded_languages.rs`, and rewrites the `[features]` table of the crate's `Cargo.toml` (one feature
per processor directory, `all-processors`, default = the six primary families).

## Trace comparison

`trace/compare.sh <datatest>` runs one datatest in the C++ reference and in the Rust port with action and rule
tracing enabled and prints the first differences of the traces and of the printed output. The C++ reference needs
`trace/action_trace.patch` applied (`git apply` in `reference/ghidra`, then `build_reference.sh`). Environment
variables for both implementations: `GHIDRA_ACTION_TRACE` (one line per action or rule that changed the function),
`GHIDRA_ACTION_TRACE_DUMP` (full p-code after each such change), `GHIDRA_OP_TRACE` (one line per created p-code op).
With `TRACE_DUMP=1`, `compare.sh` enables the p-code dumps.
