import concurrent.futures
import gzip
import hashlib
import os
import pathlib
import re
import shutil
import subprocess
import sys

ROOT = pathlib.Path(__file__).resolve().parents[2]
DUMP_TOOL = ROOT / "reference/build/sleigh_dump"
SLEIGH_HOME = ROOT / "reference/ghidra"
DATA_DIR = ROOT / "tests/data/sleigh"
BINARY_DIR = ROOT / "tests/data/decomp/bin"
RANDOM_SIZE = 4096
RANDOM_BASE = 0x1000
TIMEOUT_SECONDS = 600

CODE_CORPORA = [
    ("x86_64", "x86:LE:64:default", []),
    ("i686", "x86:LE:32:default", []),
    ("arm", "ARM:LE:32:v7", []),
    ("thumb", "ARM:LE:32:v7", ["TMode=1"]),
    ("aarch64", "AARCH64:LE:64:v8A", []),
    ("mips", "MIPS:BE:32:default", []),
    ("mipsel", "MIPS:LE:32:default", []),
    ("ppc", "PowerPC:BE:32:default", []),
    ("riscv64", "RISCV:LE:64:default", []),
    ("riscv32", "RISCV:LE:32:default", []),
]
LEVELS = ["O0", "O2"]


def file_stem(language):
    return re.sub(r"[^A-Za-z0-9.-]", "_", language)


def random_bytes(language):
    content = b""
    counter = 0
    while len(content) < RANDOM_SIZE:
        content += hashlib.sha256(f"sleigh-corpus:{language}:{counter}".encode()).digest()
        counter += 1
    return content[:RANDOM_SIZE]


def text_section(binary):
    listing = subprocess.run(["readelf", "-SW", str(binary)], check=True, capture_output=True, text=True).stdout
    for line in listing.splitlines():
        match = re.search(r"\]\s+\.text\s+\S+\s+([0-9a-f]+)\s+([0-9a-f]+)\s+([0-9a-f]+)", line)
        if match:
            address, offset, size = (int(group, 16) for group in match.groups())
            return address, binary.read_bytes()[offset:offset + size]
    raise RuntimeError(f"no .text section in {binary}")


def languages():
    listing = subprocess.run([str(DUMP_TOOL), str(SLEIGH_HOME), "list"], check=True, capture_output=True,
                             text=True).stdout
    return [line.split("\t")[0] for line in listing.splitlines() if line]


def run_dump(entry):
    name, language, base, context = entry
    command = [str(DUMP_TOOL), str(SLEIGH_HOME), "dump", language, str(DATA_DIR / "input" / f"{name}.bin"),
               hex(base)] + context
    try:
        result = subprocess.run(command, capture_output=True, timeout=TIMEOUT_SECONDS)
        output = result.stdout
        status = str(result.returncode)
        if result.returncode < 0 or result.stderr:
            output += b"stderr\t" + result.stderr.replace(b"\n", b"\\n") + b"\n"
    except subprocess.TimeoutExpired:
        output = b""
        status = "timeout"
    output += f"exit\t{status}\n".encode()
    with open(DATA_DIR / "expected" / f"{name}.txt.gz", "wb") as handle:
        with gzip.GzipFile(filename="", mode="wb", fileobj=handle, mtime=0, compresslevel=9) as compressed:
            compressed.write(output)
    return name, status


def main():
    if DATA_DIR.exists():
        shutil.rmtree(DATA_DIR)
    (DATA_DIR / "input").mkdir(parents=True)
    (DATA_DIR / "expected").mkdir(parents=True)
    entries = []
    for language in languages():
        name = f"{file_stem(language)}.random"
        (DATA_DIR / "input" / f"{name}.bin").write_bytes(random_bytes(language))
        entries.append((name, language, RANDOM_BASE, []))
    for tag, language, context in CODE_CORPORA:
        for level in LEVELS:
            address, content = text_section(BINARY_DIR / f"{tag}-{level}")
            name = f"{file_stem(language)}.code-{tag}-{level}"
            (DATA_DIR / "input" / f"{name}.bin").write_bytes(content)
            entries.append((name, language, address, context))
    with concurrent.futures.ThreadPoolExecutor(max_workers=os.cpu_count()) as pool:
        statuses = dict(pool.map(run_dump, entries))
    manifest = ["name\tlanguage\tbase\tcontext\tinput\texpected\texit"]
    for name, language, base, context in entries:
        manifest.append("\t".join([name, language, hex(base), ",".join(context) or "-", f"input/{name}.bin",
                                   f"expected/{name}.txt.gz", statuses[name]]))
    (DATA_DIR / "manifest.tsv").write_text("\n".join(manifest) + "\n")
    failing = [name for name in statuses if statuses[name] != "0"]
    print(f"{len(entries)} corpora, nonzero exit: {failing}")


if __name__ == "__main__":
    sys.exit(main())
