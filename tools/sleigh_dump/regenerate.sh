#!/bin/sh
set -e
ROOT=$(cd "$(dirname "$0")/../.." && pwd)
command -v readelf >/dev/null || sudo DEBIAN_FRONTEND=noninteractive apt-get install -y binutils
test -d "$ROOT/tests/data/decomp/bin" || "$ROOT/tools/corpus/regenerate.sh"
"$ROOT/tools/sleigh_dump/build.sh"
python3 "$ROOT/tools/sleigh_dump/regenerate.py"
