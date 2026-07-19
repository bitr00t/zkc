# Core IR — schema version 1

The serialized Core IR is the contract between the Haskell frontend and the
Rust backend. It is versioned, validated on load, and tested from both sides.

JSON was chosen over a binary format deliberately. For the first stretch of a
compiler's life, being able to read the IR in a diff and paste it into a bug
report is worth far more than serialization speed; the format can tighten once
the semantics stop moving.

## Design rule

**The IR is arithmetization-agnostic.** It describes a typed constraint graph
— field operations, hints, assertions — and says nothing about R1CS, Plonkish
gates or AIR traces. Backends decide what a node costs:

| node             | cost in R1CS                       | cost in an AIR backend |
|------------------|------------------------------------|------------------------|
| `add`/`sub`/`neg`| free (folded into linear combos)   | usually a trace column |
| `mul`            | 1 variable + 1 constraint          | a transition constraint|
| `hint`           | 1 variable, **no constraint**      | 1 unconstrained column |

If the IR encoded either cost model, the other backend could not be written.

## Top level

```json
{
  "schema_version": 1,
  "name": "IsZero",
  "field": "bn254",
  "const_one_wire": 0,
  "inputs": [ ... ],
  "nodes": [ ... ],
  "assertions": [ ... ]
}
```

| field            | meaning                                                     |
|------------------|-------------------------------------------------------------|
| `schema_version` | must be `1`; a backend rejects anything else outright        |
| `name`           | circuit name, used in diagnostics                            |
| `field`          | the *named* field, e.g. `bn254`. Never a hardcoded modulus — a FRI backend will read `goldilocks` here |
| `const_one_wire` | always `0`                                                   |

## Wires

Wires are numbered densely and are in SSA form (assigned exactly once):

- wire `0` — the field constant `1`;
- wires `1..=n` — the declared inputs, in declaration order;
- wires `n+1..` — one per node, in topological order.

**Invariant:** every argument of a node refers to a strictly smaller wire.
The backend validates this rather than trusting it — a frontend bug that
reordered nodes would otherwise silently miscompile a circuit, and in this
domain that means a security hole.

## `inputs`

```json
{"wire": 1, "name": "x", "visibility": "private"}
```

`visibility` is `private` or `public`. Public inputs become the verifier's
input vector, **in declaration order**; that ordering is part of the contract.

## `nodes`

Every node has a `wire` and an `op`.

```json
{"wire": 5, "op": "const", "value": "1"}
{"wire": 4, "op": "mul",   "args": [1, 3]}
{"wire": 6, "op": "sub",   "args": [5, 2]}
{"wire": 7, "op": "neg",   "args": [6]}
{"wire": 3, "op": "hint",  "hint": "inv_or_zero", "name": "inv", "args": [1]}
```

| `op`    | arity | notes                                                    |
|---------|-------|----------------------------------------------------------|
| `const` | 0     | `value` is a **decimal string**, possibly negative        |
| `add`   | 2     |                                                          |
| `sub`   | 2     |                                                          |
| `mul`   | 2     |                                                          |
| `neg`   | 1     |                                                          |
| `hint`  | 1     | `hint` is `inv_or_zero` or `inv`; `name` is the source-level advice name |

Constants are strings because field elements routinely exceed 64 bits and
JSON numbers cannot carry them safely. Optimizer-folded constants may be
negative; the backend reduces them modulo whichever prime it instantiates,
which is what keeps the IR field-agnostic.

`hint` nodes carry their source name for two reasons: error messages should
say `inv`, not `wire 3`; and a prover must be able to **override** them
explicitly — advice is by definition prover-chosen, and modelling a dishonest
prover requires being able to say so.

## `assertions`

```json
{"lhs": 4, "rhs": 6, "label": "(x * inv) == (1 - out)", "line": 17}
```

`label` and `line` carry the original source text so a violated constraint can
be reported against the user's code instead of an anonymous row index.

## What is *not* in version 1

Deliberately absent, and slated for the phases that need them:

- **wire kinds** (`Determined` vs `Advice`) — phase 1 checks these in the
  frontend and discards them. Phase 2 puts them in the IR, along with the
  proof obligations discharged by the determinacy pass.
- types beyond `field` (booleans, integers with range bounds, arrays);
- information-flow labels for public/private;
- gadget/module structure — version 1 is a single flat circuit.

Any of these is a schema-version bump, and backends must refuse versions they
do not understand.
