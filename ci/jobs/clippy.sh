#!/usr/bin/env bash

set -euo pipefail
cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../.."

echo ">> cargo clippy (default features)"
cargo clippy --all-targets -- -D warnings

echo ">> cargo clippy (all processors)"
cargo clippy --all-targets --features all-processors -- -D warnings

echo ">> cargo clippy (fuzz)"
cd fuzz
cargo clippy --all-targets -- -D warnings
