#!/bin/sh
set -e
ROOT=$(cd "$(dirname "$0")/../.." && pwd)
CPP=$ROOT/reference/ghidra/Ghidra/Features/Decompiler/src/decompile/cpp
OUT=$ROOT/reference/build
mkdir -p "$OUT"
test -f "$CPP/decomp_dbg" || "$ROOT/tools/build_reference.sh"
OBJECTS=$(ls "$CPP"/com_dbg/*.o | grep -v '/consolemain\.o$')
g++ -g -Wall -Wno-sign-compare -DCPUI_DEBUG -D__TERMINAL__ -I"$CPP" \
  -o "$OUT/sleigh_dump" "$ROOT/tools/sleigh_dump/sleigh_dump.cc" $OBJECTS -lbfd -lz
echo "$OUT/sleigh_dump"
