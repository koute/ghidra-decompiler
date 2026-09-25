#!/usr/bin/env bash

set -euo pipefail
cd -- "$(dirname -- "${BASH_SOURCE[0]}")"

SRC="$PWD/src"
OUT="$(cd ../.. && pwd)/tests/data/program"
WORK="$(mktemp -d)"
trap 'rm -rf "$WORK"' EXIT
mkdir -p "$OUT"

COMMON=(-O1 -fno-asynchronous-unwind-tables -Wl,--build-id=none)

gcc "${COMMON[@]}" -fPIC -shared -Wl,-soname,libext.so "$SRC/ext.c" -o "$WORK/libext.so"
strip "$WORK/libext.so" -o "$OUT/libext-x86_64.so"

gcc "${COMMON[@]}" -fcf-protection=none -Wl,-z,lazy "$SRC/plt.c" -L"$WORK" -lext -o "$OUT/plt-x86_64-lazy"
gcc "${COMMON[@]}" -fcf-protection=full -Wl,-z,ibtplt -Wl,-z,now "$SRC/plt.c" -L"$WORK" -lext -o "$OUT/plt-x86_64-ibt"

for target in i686-linux-gnu aarch64-linux-gnu arm-linux-gnueabihf riscv64-linux-gnu; do
    clang --target="$target" -fuse-ld=lld -nostdlib "${COMMON[@]}" -fPIC -shared -Wl,-soname,libext.so "$SRC/ext.c" \
        -o "$WORK/libext-$target.so"
    clang --target="$target" -fuse-ld=lld -nostdlib "${COMMON[@]}" -fPIE -pie -DOWN_START "$SRC/plt.c" \
        -L"$WORK" -l:"libext-$target.so" -o "$OUT/plt-${target%%-*}"
done

gcc "${COMMON[@]}" "$SRC/data.c" -o "$OUT/data-x86_64"
g++ "${COMMON[@]}" -O0 "$SRC/names.cc" -o "$OUT/names-cpp"

for mangling in legacy v0; do
    rustc +nightly -Z unstable-options -C symbol-mangling-version="$mangling" -C opt-level=1 -C panic=abort \
        -C strip=debuginfo -C link-arg=-Wl,--build-id=none "$SRC/names.rs" -o "$OUT/names-rust-$mangling"
done

gcc "${COMMON[@]}" -static "$SRC/stripped.c" -o "$WORK/stripped-static"
nm "$WORK/stripped-static" | awk '$3 == "main" || $3 == "twice" || $3 == "square" { print $3, "0x" $1 }' \
    | sed 's/0x0*/0x/' | sort > "$OUT/stripped-static.functions"
nm "$WORK/stripped-static" | awk '$3 == "_IO_2_1_stdout_" { print $3, "0x" $1 }' \
    | sed 's/0x0*/0x/' > "$OUT/stripped-static.data"
strip "$WORK/stripped-static" -o "$OUT/stripped-static"
