#!/usr/bin/env bash

set -euo pipefail
cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../.."

CRATES_IO_SIZE_LIMIT=10485760

echo ">> cargo package"
cargo package --allow-dirty

TARGET_DIRECTORY=$(cargo metadata --format-version 1 --no-deps | python3 -c 'import json, sys; print(json.load(sys.stdin)["target_directory"])')
VERSION=$(cargo metadata --format-version 1 --no-deps | python3 -c 'import json, sys; print(json.load(sys.stdin)["packages"][0]["version"])')
CRATE_SIZE=$(wc -c < "$TARGET_DIRECTORY/package/ghidra-decompiler-$VERSION.crate")
echo "crate size: $CRATE_SIZE bytes (crates.io limit: $CRATES_IO_SIZE_LIMIT bytes)"
if [ "$CRATE_SIZE" -ge "$CRATES_IO_SIZE_LIMIT" ]; then
    echo "crate exceeds the crates.io size limit" >&2
    exit 1
fi
