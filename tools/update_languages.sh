#!/bin/sh
set -e
ROOT=$(cd "$(dirname "$0")/.." && pwd)
PROCESSORS="${GHIDRA_PROCESSORS:-$ROOT/reference/ghidra/Ghidra/Processors}"
CRATE="$ROOT"
test -d "$PROCESSORS" || { echo "missing $PROCESSORS (run tools/build_reference.sh)" >&2; exit 1; }
ls "$PROCESSORS"/*/data/languages/*.sla >/dev/null 2>&1 || { echo "no compiled .sla files (run tools/build_reference.sh)" >&2; exit 1; }
python3 - "$PROCESSORS" "$CRATE" <<'EOF'
import lzma
import os
import shutil
import sys
import zlib

processors_dir, crate = sys.argv[1], sys.argv[2]


def copy_sla_with_xz_payload(source, destination):
    with open(source, "rb") as handle:
        image = handle.read()
    header, payload = image[:4], zlib.decompress(image[4:])
    xz_payload = lzma.compress(payload, format=lzma.FORMAT_XZ, preset=9 | lzma.PRESET_EXTREME)
    if lzma.decompress(xz_payload) != payload:
        sys.exit("xz round trip mismatch: %s" % source)
    with open(destination, "wb") as handle:
        handle.write(header + xz_payload)

primary = ["x86", "arm", "aarch64", "mips", "powerpc", "riscv"]
suffixes = (".sla", ".ldefs", ".pspec", ".cspec")
target_root = os.path.join(crate, "languages")
if os.path.isdir(target_root):
    shutil.rmtree(target_root)
entries = []
for processor in sorted(os.listdir(processors_dir), key=lambda name: (name.lower(), name)):
    languages = os.path.join(processors_dir, processor, "data", "languages")
    if not os.path.isdir(languages):
        continue
    directories = [""] + sorted(
        name for name in os.listdir(languages) if os.path.isdir(os.path.join(languages, name))
    )
    files = []
    for sub in directories:
        folder = os.path.join(languages, sub)
        for name in sorted(os.listdir(folder)):
            path = os.path.join(folder, name)
            if os.path.isfile(path) and name.endswith(suffixes):
                files.append(os.path.join(sub, name) if sub else name)
    if not any(name.endswith(".ldefs") for name in files):
        continue
    for rel in files:
        destination = os.path.join(target_root, processor, rel)
        os.makedirs(os.path.dirname(destination), exist_ok=True)
        source = os.path.join(languages, rel)
        if rel.endswith(".sla"):
            copy_sla_with_xz_payload(source, destination)
        else:
            shutil.copyfile(source, destination)
    entries.append((processor, files))

features = [(processor.lower(), processor) for processor, _ in entries]
lines = [
    "pub struct EmbeddedFile {",
    "    pub processor: &'static str,",
    "    pub path: &'static str,",
    "    pub data: &'static [u8],",
    "}",
    "",
    "pub static EMBEDDED_PROCESSORS: &[(&str, bool)] = &[",
]
for feature, processor in features:
    lines.append('    ("%s", cfg!(feature = "%s")),' % (processor, feature))
lines.append("];")
lines.append("")
lines.append("pub static EMBEDDED_FILES: &[EmbeddedFile] = &[")
for processor, files in entries:
    feature = processor.lower()
    for rel in files:
        lines.append('    #[cfg(feature = "%s")]' % feature)
        lines.append("    EmbeddedFile {")
        lines.append('        processor: "%s",' % processor)
        lines.append('        path: "%s",' % rel)
        lines.append('        data: include_bytes!("../languages/%s/%s"),' % (processor, rel))
        lines.append("    },")
lines.append("];")
with open(os.path.join(crate, "src", "embedded_languages.rs"), "w") as handle:
    handle.write("\n".join(lines) + "\n")

cargo_path = os.path.join(crate, "Cargo.toml")
with open(cargo_path) as handle:
    cargo = handle.read()
marker = "\n[features]\n"
if marker in cargo:
    cargo = cargo[: cargo.index(marker)]
cargo = cargo.rstrip("\n") + "\n"
names = [feature for feature, _ in features]
table = ["", "[features]"]
table.append("default = [%s]" % ", ".join('"%s"' % name for name in ["demangle"] + [name for name in primary if name in names]))
table.append('demangle = ["dep:cpp_demangle", "dep:rustc-demangle"]')
table.append("all-processors = [%s]" % ", ".join('"%s"' % name for name in names))
for name in names:
    table.append('%s = []' % (name if name.replace("_", "").isalnum() and not name[0].isdigit() else '"%s"' % name))
with open(cargo_path, "w") as handle:
    handle.write(cargo + "\n".join(table) + "\n")
print("processors: %d, files: %d" % (len(entries), sum(len(files) for _, files in entries)))
EOF
