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
