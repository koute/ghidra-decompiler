#!/bin/sh
set -e
TEST_NAME=$1
REPO_ROOT=$(cd "$(dirname "$0")/../.." && pwd)
GHIDRA="$REPO_ROOT/reference/ghidra"
CPP="$GHIDRA/Ghidra/Features/Decompiler/src/decompile/cpp"
DATATESTS="$GHIDRA/Ghidra/Features/Decompiler/src/decompile/datatests"
OUTPUT_DIR=${TRACE_OUTPUT_DIR:-/tmp/trace}
mkdir -p "$OUTPUT_DIR"
env SLEIGHHOME="$GHIDRA" GHIDRA_ACTION_TRACE=1 ${TRACE_DUMP:+GHIDRA_ACTION_TRACE_DUMP=1} "$CPP/decomp_test_dbg" -usesleighenv -path "$DATATESTS" datatests "$TEST_NAME.xml" \
    2> "$OUTPUT_DIR/cpp_raw.txt" > "$OUTPUT_DIR/cpp_stdout.txt" || true
grep -E '^(A|R|  )' "$OUTPUT_DIR/cpp_raw.txt" > "$OUTPUT_DIR/cpp.txt" || true
cd "$REPO_ROOT"
env DATATESTS_FILTER="$TEST_NAME.xml" GHIDRA_ACTION_TRACE=1 ${TRACE_DUMP:+GHIDRA_ACTION_TRACE_DUMP=1} cargo test -q --features all-processors --test datatests -- --nocapture \
    2> "$OUTPUT_DIR/rust_raw.txt" > "$OUTPUT_DIR/rust_stdout.txt" || true
grep -E '^(A|R|  )' "$OUTPUT_DIR/rust_raw.txt" > "$OUTPUT_DIR/rust.txt" || true
echo "cpp events: $(wc -l < "$OUTPUT_DIR/cpp.txt") rust events: $(wc -l < "$OUTPUT_DIR/rust.txt")"
diff "$OUTPUT_DIR/cpp.txt" "$OUTPUT_DIR/rust.txt" | head -${DIFF_LINES:-10} || true
grep -E '^(FAIL|PASS)' "$OUTPUT_DIR/rust_stdout.txt" "$OUTPUT_DIR/rust_raw.txt" | head -3 || true
rm -f "$OUTPUT_DIR/cpp_output.txt" "$OUTPUT_DIR/rust_output.txt"
SLEIGHHOME="$GHIDRA" GHIDRA_TEST_OUTPUT="$OUTPUT_DIR/cpp_output.txt" "$CPP/decomp_test_dbg" -usesleighenv -path "$DATATESTS" datatests "$TEST_NAME.xml" > /dev/null 2>&1 || true
DATATESTS_FILTER="$TEST_NAME.xml" GHIDRA_TEST_OUTPUT="$OUTPUT_DIR/rust_output.txt" cargo test -q --features all-processors --test datatests > /dev/null 2>&1 || true
echo "output diff:"
diff "$OUTPUT_DIR/cpp_output.txt" "$OUTPUT_DIR/rust_output.txt" | head -${DIFF_LINES:-10} || true
