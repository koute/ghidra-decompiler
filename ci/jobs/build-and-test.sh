#!/usr/bin/env bash

set -euo pipefail
cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../.."

PROFILE="${1:?usage: build-and-test.sh <test|release>}"

echo ">> cargo test (default features, $PROFILE)"
cargo test --profile "$PROFILE" --all-targets

echo ">> cargo test (all processors, $PROFILE)"
cargo test --profile "$PROFILE" --all-targets --features all-processors

echo ">> cargo check (no default features, $PROFILE)"
cargo check --profile "$PROFILE" --all-targets --no-default-features

echo ">> cargo run (inspect example, $PROFILE)"
cargo run --profile "$PROFILE" --example inspect -- tests/data/decomp/bin/x86_64-O2 > /dev/null
