#!/bin/sh
set -e
ROOT=$(cd "$(dirname "$0")/../.." && pwd)
SRC="$ROOT/reference/ghidra/Ghidra/Features/Decompiler/src/decompile/datatests"
DEST="$ROOT/tests/data/datatests"
rm -rf "$DEST"
mkdir -p "$DEST"
cp "$SRC"/*.xml "$DEST"/
ls "$DEST" | wc -l
