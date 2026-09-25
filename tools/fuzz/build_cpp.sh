#!/bin/sh
set -e
REPO_ROOT=$(cd "$(dirname "$0")/../.." && pwd)
ORIGINAL="$REPO_ROOT/reference/ghidra/Ghidra/Features/Decompiler/src/decompile/cpp"
OUT=${FUZZ_CPP_OUT:-$REPO_ROOT/reference/build/fuzz_cpp}
CPP="$OUT/src"
mkdir -p "$OUT/obj" "$CPP"
cp -p "$ORIGINAL"/*.cc "$ORIGINAL"/*.hh "$ORIGINAL"/*.h "$CPP"/
EXCLUDED="consolemain sleighexample test testfunction bfd_arch loadimage_bfd analyzesigs codedata slgh_compile slghparse slghscan rulecompile unify ruleparse ifaceterm"
FLAGS="-O1 -g1 -fPIC -fsanitize=fuzzer-no-link -Wno-everything -I$CPP"
for source in "$CPP"/*.cc "$REPO_ROOT/tools/fuzz/cpp_harness.cc"; do
    name=$(basename "$source" .cc)
    case "$name" in ghidra_*|*_ghidra) continue ;; esac
    skip=0
    for excluded in $EXCLUDED; do [ "$name" = "$excluded" ] && skip=1; done
    [ $skip = 1 ] && continue
    echo "clang++ -std=c++11 -c $source -o $OUT/obj/$name.o $FLAGS"
done | xargs -P "$(nproc)" -I{} sh -c '{}'
rm -f "$OUT/libghidra_cpp.a"
ar rcs "$OUT/libghidra_cpp.a" "$OUT"/obj/*.o
echo "$OUT/libghidra_cpp.a"
