#!/bin/sh
set -e
ROOT=$(cd "$(dirname "$0")/../.." && pwd)
CPP=$ROOT/reference/ghidra/Ghidra/Features/Decompiler/src/decompile/cpp
OUT=$ROOT/reference/build
mkdir -p "$OUT"
test -f "$CPP/decomp_dbg" || "$ROOT/tools/build_reference.sh"
test -f /usr/lib/x86_64-linux-gnu/libbfd-multiarch.so || sudo DEBIAN_FRONTEND=noninteractive apt-get install -y binutils-multiarch-dev
g++ -g -o "$OUT/decomp_multiarch_dbg" "$CPP"/com_dbg/*.o -lbfd-multiarch -lz
echo "$OUT/decomp_multiarch_dbg"
