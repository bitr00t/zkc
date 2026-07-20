#!/usr/bin/env bash
# Build everything, run both test suites, then walk the full pipeline:
# source .zkc -> Core IR -> R1CS -> witness -> Groth16 proof -> verification.
set -euo pipefail
cd "$(dirname "$0")/.."

ZKC=compiler/build/zkc
PROVE=backend/target/debug/zkc-prove

echo "==> building the compiler (GHC, no external packages)"
make -C compiler all

echo; echo "==> compiler tests"
make -C compiler test

echo; echo "==> building the backend (cargo)"
cargo build --manifest-path backend/Cargo.toml

echo; echo "==> backend tests"
cargo test --manifest-path backend/Cargo.toml

mkdir -p build
echo; echo "==> compiling the example circuits"
for name in mul_square iszero iszero_broken; do
  $ZKC build "examples/$name.zkc" -o "build/$name.ir.json"
done

echo; echo "==> a circuit the compiler REJECTS (advice nothing constrains)"
if $ZKC build examples/unconstrained_advice.zkc -o /dev/null 2>&1; then
  echo "UNEXPECTED: that circuit should not have compiled"; exit 1
fi

echo; echo "=============================================================="
echo "1. MulSquare, honest prover"
echo "=============================================================="
$PROVE --ir build/mul_square.ir.json --inputs inputs/mul_square.json

echo; echo "=============================================================="
echo "2. IsZero, x = 0 (honest: out = 1)"
echo "=============================================================="
$PROVE --ir build/iszero.ir.json --inputs inputs/iszero_honest_zero.json

echo; echo "=============================================================="
echo "3. IsZero, x = 5 (honest: out = 0)"
echo "=============================================================="
$PROVE --ir build/iszero.ir.json --inputs inputs/iszero_honest_nonzero.json

echo; echo "=============================================================="
echo "4. IsZero, FORGED: prover claims 5 == 0 and overrides the advice"
echo "   Expected: refused, naming the assertion that catches it."
echo "=============================================================="
if $PROVE --ir build/iszero.ir.json --inputs inputs/iszero_forged.json --verbose; then
  echo "UNEXPECTED: the correct circuit accepted a forgery"; exit 1
fi

echo; echo "=============================================================="
echo "5. IsZeroBroken, FORGED: the same claim, one assertion missing"
echo "   Expected: a valid Groth16 proof that 5 == 0."
echo "=============================================================="
$PROVE --ir build/iszero_broken.ir.json --inputs inputs/iszero_forged.json --verbose

echo
echo "Cases 4 and 5 differ by exactly one line of source. Case 5 is a"
echo "cryptographically valid proof of a false statement — produced by this"
echo "compiler, from a source file that passes every check it currently has."
echo "Closing that gap is phase 2."
