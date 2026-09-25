#!/usr/bin/env bash

set -euo pipefail
cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../.."

MSRV=$(sed -n 's/^rust-version = "\(.*\)"$/\1/p' Cargo.toml)
rustup toolchain install "$MSRV" --profile minimal

echo ">> cargo check (rust $MSRV)"
cargo "+$MSRV" check --all-targets --features all-processors
