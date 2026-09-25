#!/usr/bin/env bash

set -euo pipefail
cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../.."

echo ">> build C++ reference"
tools/build_reference.sh
tools/fuzz/build_cpp.sh

export SLEIGHHOME="$PWD/reference/ghidra"
SEEDS="$PWD/reference/build/fuzz_seeds"
FUZZ_SECONDS="${FUZZ_SECONDS:-600}"

if [ $# -eq 0 ]; then
    set -- sleigh decompile
fi

for target in "$@"; do
    case "$target" in
        sleigh|decompile) ;;
        *)
            echo "unknown fuzz target: $target" >&2
            exit 1
        ;;
    esac

    if [ ! -d "$SEEDS/$target" ]; then
        python3 tools/fuzz/make_seeds.py "$SEEDS/$target"
    fi

    echo ">> cargo fuzz run ($target)"
    (cd fuzz && cargo fuzz run "$target" "$SEEDS/$target" -- -max_total_time="$FUZZ_SECONDS" -timeout=60 -rss_limit_mb=2048)
done
