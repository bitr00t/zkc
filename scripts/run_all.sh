#!/usr/bin/env bash
# End-to-end demonstration of the phase-2 pipeline.
#
#   .zkc source -> [Haskell] parse, elaborate, optimize, PROVE DETERMINACY
#               -> Core IR (JSON, schema v2)
#               -> [Rust] lower to R1CS, solve witness, self-check
#               -> Groth16 prove + verify
#
# The headline is the third section: circuits that phase 1 happily compiled
# into forgeable proving keys are now compile errors.
set -uo pipefail
cd "$(dirname "$0")/.."

ZKC=compiler/build/zkc
PROVE=backend/target/release/zkc-prove
mkdir -p build

rule() { printf '\n\033[1m== %s ==\033[0m\n' "$1"; }

if [ ! -x "$ZKC" ]; then echo "building compiler..."; make -C compiler all; fi
if [ ! -x "$PROVE" ]; then echo "building backend..."; (cd backend && cargo build --release); fi

rule "1. Compile the circuits that should compile"
for c in mul_square iszero divide relation; do
  echo "--- $c.zkc"
  $ZKC build "examples/$c.zkc" -o "build/$c.ir.json" --explain
done

rule "2. Prove and verify"
run() {
  echo "--- $1  <-  $2"
  $PROVE --ir "build/$1.ir.json" --inputs "inputs/$2.json" | tail -n 3
}
run mul_square mul_square
run iszero     iszero_honest_zero
run iszero     iszero_honest_nonzero
run divide     divide
run relation   relation

rule "3. The forgery, refused by the constraints"
echo "Claiming 5 == 0 against the CORRECT IsZero circuit:"
$PROVE --ir build/iszero.ir.json --inputs inputs/iszero_forged.json | tail -n 6 || true

rule "4. Circuits the compiler now REJECTS (this is phase 2)"
expect_failure() {
  echo "--- $1"
  if $ZKC build "examples/$1" -o /dev/null 2>&1; then
    echo "!!! expected a compile error, got success"; exit 1
  fi
}
expect_failure iszero_broken.zkc
expect_failure advice_outside_gadget.zkc

rule "5. Division by zero is unsatisfiable by construction"
$PROVE --ir build/divide.ir.json --inputs inputs/divide_by_zero.json 2>&1 | tail -n 2 || true

rule "done"
