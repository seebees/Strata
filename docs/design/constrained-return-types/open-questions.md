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
without re-proving the constraint. Future optimization.

### Q3: Should `constrainedTypeElim` support constrained return types on functions?

The current implementation uses procedures with postconditions as
a workaround. Supporting constrained return types on functions
directly would be cleaner for pure operations. The `elimProc`
function already has the infrastructure — the `isFunctional` guard
just needs to be removed, and the translator needs to handle
functions with postconditions.

This is not blocking but would be a nice cleanup.
