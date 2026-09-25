#!/usr/bin/env bash

set -euo pipefail
cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../.."

echo ">> cargo doc"
RUSTDOCFLAGS="-D warnings" cargo doc --no-deps
