#!/bin/sh
set -e
ROOT=$(cd "$(dirname "$0")/../.." && pwd)
command -v arm-linux-gnueabihf-gcc >/dev/null && command -v riscv64-linux-gnu-gcc >/dev/null && command -v ld.lld >/dev/null && command -v readelf >/dev/null || \
  sudo DEBIAN_FRONTEND=noninteractive apt-get install -y gcc-i686-linux-gnu gcc-arm-linux-gnueabihf \
    gcc-aarch64-linux-gnu gcc-powerpc-linux-gnu gcc-riscv64-linux-gnu clang lld binutils-multiarch binutils-multiarch-dev
"$ROOT/tools/corpus/build_decomp.sh"
python3 "$ROOT/tools/corpus/regenerate.py"
