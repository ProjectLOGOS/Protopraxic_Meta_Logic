#!/usr/bin/env bash
set -euo pipefail

pushd lean
lake build
popd

pushd coq
[ -f Makefile ] || coq_makefile -f _CoqProject -o Makefile
make -j
popd

echo "OK: Lean+Coq build passed."
