# Gadget reference

Generated from determinacy summaries: each entry states what the compiler proved, not a hand-written description.

## is_zero

    is_zero(x) -> (out)

- inputs: x
- outputs: out
- determined by cases: x == 0; x != 0

## inverse

    inverse(x) -> (inv_x)

- inputs: x
- outputs: inv_x
- determined by cases: x == 0; x != 0
- guarantees: x != 0

## assert_bit

    assert_bit(b) -> (out)

- inputs: b
- outputs: out
- determined: directly, with no case split

## mux

    mux(sel, a, b) -> (out)

- inputs: sel, a, b
- outputs: out
- determined: directly, with no case split

## assert_range4

    assert_range4(x) -> (out)

- inputs: x
- outputs: out
- determined: directly, with no case split

## fri_fold

    fri_fold(p, m, beta, x) -> (folded)

- inputs: p, m, beta, x
- outputs: folded
- determined by cases: x == 0; x != 0
- guarantees: x != 0

## rlc

    rlc(a, b, r) -> (out)

- inputs: a, b, r
- outputs: out
- determined: directly, with no case split

## hash_leaf

    hash_leaf(v) -> (h)

- inputs: v
- outputs: h
- determined: directly, with no case split

## compress

    compress(l, r) -> (h)

- inputs: l, r
- outputs: h
- determined: directly, with no case split

## fs_challenge

    fs_challenge(seed, root) -> (alpha)

- inputs: seed, root
- outputs: alpha
- determined: directly, with no case split

## range8

    range8(x) -> (out)

- inputs: x
- outputs: out
- determined: directly, with no case split

## fs_index_challenge

    fs_index_challenge(seed, root, final0, final1) -> (c)

- inputs: seed, root, final0, final1
- outputs: c
- determined: directly, with no case split

## canonical_low2

    canonical_low2(v) -> (i0, i1)

- inputs: v
- outputs: i0, i1
- determined: directly, with no case split
