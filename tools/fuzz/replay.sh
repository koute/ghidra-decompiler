#!/bin/sh
TARGET=$1
shift
REPO_ROOT=$(cd "$(dirname "$0")/../.." && pwd)
BINARY=${CARGO_TARGET_DIR:-$REPO_ROOT/fuzz/target}/x86_64-unknown-linux-gnu/release/$TARGET
for input in "$@"; do
    echo "=== $input"
    SLEIGHHOME="$REPO_ROOT/reference/ghidra" FUZZ_VERBOSE=1 "$BINARY" -runs=1 "$input" 2>&1 \
        | sed -n '/divergence\|panicked at\|SUMMARY\|deadly signal/,/--- end/p' | grep -v "^stack backtrace\|^note:" | head -${REPLAY_LINES:-40}
done
