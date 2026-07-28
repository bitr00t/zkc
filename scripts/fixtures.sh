#!/usr/bin/env bash
# Regenerate — or verify — the Core IR fixtures the backend tests compile in.
#
#   scripts/fixtures.sh            regenerate backend/zkc-core/tests/fixtures/
#   scripts/fixtures.sh --check    fail if any fixture has drifted (CI mode)
#
# Why this exists. Several backend tests need real frontend output: the IR the
# Haskell compiler actually emits for a committed .zkc source. Two ways to get
# it are both wrong. Pasting the JSON into the test as a literal makes it drift
# silently — the .zkc source moves, the copy does not, and the test goes on
# proving something about a circuit that no longer exists. Reading it from an
# absolute path at build time makes `cargo test` depend on a GHC toolchain and
# on one particular machine's /tmp.
#
# So: the fixtures are committed (cargo test stands alone — no GHC, no network,
# no absolute paths) and this script proves they are byte-for-byte what the
# frontend emits today. The emitter is deterministic, so --check is a plain
# `cmp`. Run it after touching the frontend or any of the sources below.
#
# Hand-written IR is deliberately NOT listed here. lowering_faithfulness_tests
# and the negative fixtures in core_tests carry IR that no source compiles to
# — minimal per-rule specs, and a circuit phase 1 accepted but phase 2 rejects.
# Those are spec artefacts, not compiler output, and belong in their tests.
set -uo pipefail
cd "$(dirname "$0")/.."

ZKC=compiler/build/zkc
DEST=backend/zkc-core/tests/fixtures

# fixture name  <-  source
SOURCES=(
  "iszero:examples/iszero.zkc"
  "index_from_challenge:examples/index_from_challenge.zkc"
  "fri_verify_full:examples/fri_verify_full.zkc"
  "fri_verify_fs:examples/fri_verify_fs.zkc"
)

check=0
[ "${1:-}" = "--check" ] && check=1

if [ ! -x "$ZKC" ]; then
  echo "building compiler..."
  make -C compiler all >/dev/null || { echo "compiler build failed"; exit 1; }
fi

mkdir -p "$DEST"
tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT

drift=0
for entry in "${SOURCES[@]}"; do
  name="${entry%%:*}"
  src="${entry#*:}"
  out="$DEST/$name.ir.json"

  if ! "$ZKC" build "$src" -o "$tmp/$name.ir.json" 2>/dev/null; then
    echo "FAIL  $src did not compile"
    exit 1
  fi

  if [ "$check" = 1 ]; then
    if [ ! -f "$out" ]; then
      echo "MISSING  $out"
      drift=1
    elif ! cmp -s "$tmp/$name.ir.json" "$out"; then
      echo "DRIFT    $out is not what $src compiles to"
      drift=1
    else
      echo "ok       $name"
    fi
  else
    cp "$tmp/$name.ir.json" "$out"
    echo "wrote    $out"
  fi
done

if [ "$check" = 1 ] && [ "$drift" = 1 ]; then
  echo
  echo "Fixtures are stale. Regenerate with: scripts/fixtures.sh"
  exit 1
fi
