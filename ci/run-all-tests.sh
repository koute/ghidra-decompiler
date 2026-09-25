#!/usr/bin/env bash

set -euo pipefail
cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.."

./ci/jobs/rustfmt.sh
./ci/jobs/clippy.sh
./ci/jobs/doc.sh
./ci/jobs/build-and-test.sh test
./ci/jobs/build-and-test.sh release
./ci/jobs/check-msrv.sh
./ci/jobs/package.sh
./ci/jobs/fuzz.sh

echo "----------------------------------------"
echo "All tests finished!"
