#!/bin/sh
set -eu
cd "$(dirname "$0")"
if [ -x "$PWD/.toolchain/lean-4.34.0-darwin_aarch64/bin/lake" ]; then
  PATH="$PWD/.toolchain/lean-4.34.0-darwin_aarch64/bin:$PATH"
  export PATH
fi
mkdir -p verification
lake build > verification/build.log 2>&1
lake env lean Audit.lean > verification/axioms-and-signatures.log 2>&1
lake env leanchecker -v EtaleCounterexample > verification/kernel-replay.log 2>&1
cat verification/build.log
cat verification/kernel-replay.log
