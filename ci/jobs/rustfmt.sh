#!/usr/bin/env bash

set -euo pipefail
cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../.."

echo ">> cargo fmt"
cargo fmt --check --all

echo ">> cargo fmt (fuzz)"
cd fuzz
cargo fmt --check --all
