#!/bin/sh
set -e
REPO_ROOT=$(cd "$(dirname "$0")/.." && pwd)
GHIDRA="$REPO_ROOT/reference/ghidra"
GHIDRA_COMMIT=d6192cb3f900f74152a4eeec1aa6758b6143b093
if [ ! -d "$GHIDRA" ]; then
    git init -q "$GHIDRA"
    git -C "$GHIDRA" fetch -q --depth 1 https://github.com/NationalSecurityAgency/ghidra.git "$GHIDRA_COMMIT"
    git -C "$GHIDRA" checkout -q FETCH_HEAD
fi
CPP="$GHIDRA/Ghidra/Features/Decompiler/src/decompile/cpp"
apply_once() {
    if (cd "$1" && patch -p1 --dry-run -s -f < "$2" > /dev/null 2>&1); then
        (cd "$1" && patch -p1 -s < "$2")
        rm -f "$CPP"/com_dbg/*.o "$CPP"/com_opt/*.o "$CPP"/test_dbg/*.o "$CPP"/sla_dbg/*.o "$CPP"/sla_opt/*.o
    fi
}
apply_once "$GHIDRA" "$REPO_ROOT/tools/trace/action_trace.patch"
apply_once "$CPP" "$REPO_ROOT/tools/fuzz/reference_fixes.patch"
command -v bison >/dev/null || sudo apt-get install -y binutils-dev bison flex zlib1g-dev
cd "$CPP"
mkdir -p com_dbg com_opt test_dbg sla_opt sla_dbg
touch xml.cc grammar.cc pcodeparse.cc slghparse.cc slghparse.hh slghscan.cc
make -j"$(nproc)" decomp_test_dbg decomp_dbg sleigh_opt
./sleigh_opt -a ../../../../../Processors
