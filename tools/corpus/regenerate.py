import concurrent.futures
import os
import pathlib
import shutil
import subprocess
import sys

ROOT = pathlib.Path(__file__).resolve().parents[2]
SOURCE_DIR = ROOT / "tools/corpus/src"
DATA_DIR = ROOT / "tests/data/decomp"
DECOMPILER = ROOT / "reference/build/decomp_multiarch_dbg"
SLEIGH_HOME = ROOT / "reference/ghidra"

COMMON_FLAGS = [
    "-ffreestanding", "-fno-stack-protector", "-fno-pic", "-fno-asynchronous-unwind-tables",
    "-fno-unwind-tables", "-fno-ident", "-g0", "-nostdlib", "-static", "-Wl,-e,_start",
    "-Wl,--build-id=none",
]

TARGETS = [
    ("x86_64", "x86:LE:64:default:gcc", ["gcc", "-m64", "-no-pie", "-fcf-protection=none"], ["-lgcc"]),
    ("i686", "x86:LE:32:default:gcc", ["i686-linux-gnu-gcc", "-no-pie", "-fcf-protection=none"], ["-lgcc"]),
    ("arm", "ARM:LE:32:v7:default", ["arm-linux-gnueabihf-gcc", "-no-pie", "-marm"], ["-lgcc"]),
    ("thumb", "ARM:LE:32:v8T:default", ["arm-linux-gnueabihf-gcc", "-no-pie", "-mthumb"], ["-lgcc"]),
    ("aarch64", "AARCH64:LE:64:v8A:default", ["aarch64-linux-gnu-gcc", "-no-pie"], ["-lgcc"]),
    ("mips", "MIPS:BE:32:default:default",
     ["clang", "--target=mips-linux-gnu", "-march=mips32r2", "-mno-abicalls", "-fuse-ld=lld"], []),
    ("mipsel", "MIPS:LE:32:default:default",
     ["clang", "--target=mipsel-linux-gnu", "-march=mips32r2", "-mno-abicalls", "-fuse-ld=lld"], []),
    ("ppc", "PowerPC:BE:32:default:default", ["powerpc-linux-gnu-gcc", "-no-pie"], ["-lgcc"]),
    ("riscv64", "RISCV:LE:64:default:gcc",
     ["riscv64-linux-gnu-gcc", "-no-pie", "-march=rv64gc", "-mabi=lp64d"], ["-lgcc"]),
    ("riscv32", "RISCV:LE:32:default:gcc",
     ["riscv64-linux-gnu-gcc", "-no-pie", "-march=rv32gc", "-mabi=ilp32d"], []),
]

LEVELS = ["O0", "O2"]
TIMEOUT_SECONDS = 300


def compile_binaries(binary_dir):
    sources = sorted(str(path) for path in SOURCE_DIR.glob("*.c"))
    built = []
    for tag, language, compiler, libraries in TARGETS:
        for level in LEVELS:
            name = f"{tag}-{level}"
            output = binary_dir / name
            command = compiler + COMMON_FLAGS + [f"-{level}", "-o", str(output)] + sources + libraries
            subprocess.run(command, check=True)
            built.append((name, language))
    return built


def function_symbols(binary):
    listing = subprocess.run(["readelf", "-Ws", str(binary)], check=True, capture_output=True, text=True).stdout
    found = {}
    for line in listing.splitlines():
        fields = line.split()
        if len(fields) < 8 or fields[3] != "FUNC" or fields[6] == "UND":
            continue
        symbol = fields[7]
        if symbol.startswith("__"):
            continue
        found[symbol] = int(fields[1], 16)
    return sorted(found, key=lambda symbol: (found[symbol], symbol))


def decompile(binary_dir, name, language, function):
    script = (
        f"load file default-{language} {name}\n"
        "read symbols\n"
        f"load function {function}\n"
        "decompile\n"
        "print C\n"
        "quit\n"
    )
    environment = dict(os.environ, SLEIGHHOME=str(SLEIGH_HOME))
    try:
        result = subprocess.run([str(DECOMPILER)], input=script, capture_output=True, text=True,
                                cwd=binary_dir, env=environment, timeout=TIMEOUT_SECONDS)
        stdout, stderr, status = result.stdout, result.stderr, str(result.returncode)
    except subprocess.TimeoutExpired as expired:
        stdout = expired.stdout.decode() if isinstance(expired.stdout, bytes) else (expired.stdout or "")
        stderr = ""
        status = "timeout"
    section = f"=== function {function}\n{stdout}"
    if not section.endswith("\n"):
        section += "\n"
    if stderr:
        section += "--- stderr\n" + stderr
        if not section.endswith("\n"):
            section += "\n"
    section += f"--- exit {status}\n"
    return section


def main():
    if DATA_DIR.exists():
        shutil.rmtree(DATA_DIR)
    binary_dir = DATA_DIR / "bin"
    expected_dir = DATA_DIR / "expected"
    binary_dir.mkdir(parents=True)
    expected_dir.mkdir(parents=True)
    built = compile_binaries(binary_dir)
    jobs = []
    for name, language in built:
        for function in function_symbols(binary_dir / name):
            jobs.append((name, language, function))
    with concurrent.futures.ThreadPoolExecutor(max_workers=os.cpu_count()) as pool:
        sections = list(pool.map(lambda job: decompile(binary_dir, *job), jobs))
    by_binary = {}
    for job, section in zip(jobs, sections):
        by_binary.setdefault(job[0], []).append(section)
    manifest = ["binary\tlanguage\tfunctions\texpected"]
    for name, language in built:
        text = "".join(by_binary.get(name, []))
        (expected_dir / f"{name}.txt").write_text(text)
        count = len(by_binary.get(name, []))
        manifest.append(f"bin/{name}\t{language}\t{count}\texpected/{name}.txt")
    (DATA_DIR / "manifest.tsv").write_text("\n".join(manifest) + "\n")
    print(f"{len(jobs)} functions in {len(built)} binaries")


if __name__ == "__main__":
    sys.exit(main())
