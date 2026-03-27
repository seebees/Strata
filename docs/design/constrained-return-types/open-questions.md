# Constrained Return Types: Open Questions

**Date:** 2026-03-27

### Q1: Can a compiler select the WRONG constrained type?

Yes. If JVerify claims `array.length` returns `nat8` (0..255),
the prover would accept programs that overflow at length 256.
This is a compiler bug, not a Strata bug. The fix is to verify
the compiler — which is the long-term goal.

### Q2: Should constrained types have proven subset relationships?

If `nat32 ⊆ int64`, should Strata prove this? This would let the
prover automatically accept assignments from `nat32` to `int64`
without re-proving the constraint. This is a future optimization.

### Q3: What about compound constraints?

Some languages have constraints that aren't simple ranges. For
example, "this value is a valid Unicode code point" (0..0x10FFFF,
excluding surrogates). Should the library support arbitrary
predicates, or only range constraints?

For now, range constraints are sufficient. Arbitrary predicates
can be added later if needed.
