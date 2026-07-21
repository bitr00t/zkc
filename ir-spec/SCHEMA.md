# Core IR — schema version 2

The serialized Core IR is the contract between the Haskell frontend and the
Rust backend. It is versioned, validated on load, and round-tripped by tests
on both sides.

The IR is deliberately **not** R1CS-shaped. It is a typed constraint graph, so
the same artifact can be lowered to R1CS today and to a Plonkish or AIR
arithmetization in phase 4 without the frontend changing.

## What changed since version 1

| Addition | Why |
|---|---|
| `visibility: "output"` | Version 1 had only `private`/`public`, which conflated "input the verifier sees" with "value the circuit computes". Determinacy is only a well-posed question once those are separate. |
| `advice_derived` per node | The syntactic taint: does this wire depend on a hint? Distinct from determinacy — a tainted wire may still be uniquely determined. |
| `gadget` and `line` on hint nodes | Advice is only legal inside a `gadget` block, so every hint has a quarantine region to point at in diagnostics. |
| `determinacy` record | The frontend's proof, carried inside the artifact. |
| `line` on inputs | Lets the backend report against source positions. |

## Top level

```json
{
  "schema_version": 2,
  "name": "IsZero",
  "field": "bn254",
  "const_one_wire": 0,
  "inputs": [ ... ],
  "nodes": [ ... ],
  "assertions": [ ... ],
  "determinacy": { ... }
}
```

`field` names the scalar field. The frontend needs its modulus to decide
whether a polynomial coefficient is nonzero; the backend instantiates its
arithmetic over it. Known: `bn254`, `goldilocks`.

## Wires

Wire `0` is the constant one. Inputs occupy `1..=n` in declaration order.
Nodes follow, densely numbered and topologically ordered — every argument
refers to a strictly smaller wire. The backend enforces this rather than
trusting it; a frontend bug that produced a forward reference would otherwise
become a miscompiled circuit.

## Inputs

```json
{"wire": 2, "name": "out", "visibility": "output", "line": 21}
```

| `visibility` | Verifier sees it | Must be determined |
|---|---|---|
| `private` | no | no — it *is* the input |
| `public` | yes | no — still an input the prover supplies |
| `output` | yes | **yes** — proved by the frontend |

`public` and `output` both land in the verifier's public input vector, in
declaration order. The difference is the proof obligation.

## Nodes

```json
{"wire": 4, "advice_derived": true, "op": "mul", "args": [1, 3]}
```

Operations: `const` (with `value`, a decimal **string** — field elements
routinely exceed 64 bits, and JSON numbers are not safe at that width),
`add`, `sub`, `mul`, `neg`, and `hint`.

```json
{"wire": 3, "advice_derived": true, "op": "hint", "hint": "inv_or_zero",
 "name": "inv", "gadget": "is_zero", "line": 24, "args": [1]}
```

A `hint` tells the witness solver how to compute a value that the constraints
do not pin down by themselves. It costs one variable and **zero constraints**.
`name` is the source-level name, which lets a prover override it by name —
that is how the test suite models a dishonest prover.

## Assertions

```json
{"lhs": 4, "rhs": 6, "label": "(x * inv) == (1 - out)", "line": 26}
```

Each asserts two wires are equal. `label` and `line` exist so that a failing
self-check can name the source assertion instead of a constraint index.

## Determinacy

```json
"determinacy": {
  "proved": true,
  "targets": ["out"],
  "branches": [["x == 0"], ["x != 0"]]
}
```

The frontend's proof that every `output` is a function of the inputs, and the
case splits it rested on.

This record is the reason schema v2 exists. Soundness is not a property of
"we used a good compiler" — it is a claim about *this* circuit, so it travels
with the circuit. The backend **refuses to prove** an IR that declares outputs
without a discharged proof, and a missing record deserializes to
`proved: false` rather than defaulting to allow. Deleting the record is
therefore not a way to get a proving key for an under-constrained circuit.

An IR with no outputs (a pure relation, e.g. "I know a factorisation of 12")
needs no proof, and the gate stays quiet.
