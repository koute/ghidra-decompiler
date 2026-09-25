import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[2]
INPUT = REPO_ROOT / "tests/data/sleigh/input"
SELECTORS = {
    "x86_LE_64_default.code-x86_64": 0,
    "x86_LE_32_default.code-i686": 1,
    "ARM_LE_32_v8.code-arm": 2,
    "ARM_LE_32_v7.code-arm": 2,
    "ARM_LE_32_v8T.code-thumb": 3,
    "ARM_LE_32_v7.code-thumb": 3,
    "AARCH64_LE_64_v8A.code-aarch64": 4,
    "MIPS_BE_32_default.code-mips": 5,
    "MIPS_LE_32_default.code-mipsel": 6,
    "PowerPC_BE_32_default.code-ppc": 7,
    "RISCV_LE_64_default.code-riscv64": 8,
    "RISCV_LE_32_default.code-riscv32": 9,
}
SLICE = int(sys.argv[2]) if len(sys.argv) > 2 else 128
output = Path(sys.argv[1])
output.mkdir(parents=True, exist_ok=True)
count = 0
for path in sorted(INPUT.glob("*.code-*.bin")):
    prefix = path.name.rsplit("-O", 1)[0]
    if prefix not in SELECTORS:
        continue
    data = path.read_bytes()
    for start in range(0, len(data), SLICE):
        piece = data[start:start + SLICE]
        (output / f"{path.stem}-{start:06x}").write_bytes(bytes([SELECTORS[prefix]]) + piece)
        count += 1
print(f"{count} seeds in {output}")
