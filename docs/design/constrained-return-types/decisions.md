# Constrained Return Types: Decisions

**Date:** 2026-03-27

### D1: Constrained types belong in Laurel, not Core or compilers

**Status:** Accepted

Types like `nat32`, `int64`, etc. are mathematical facts about
number ranges. They belong in Laurel. Core doesn't have constrained
types — that's a Laurel concept. If each compiler defined its own
`nat32`, they could define them inconsistently.

### D2: Language compilers select constrained types, not axioms

**Status:** Accepted

- **Core:** Proven universal axioms. Nothing enters Core unproven.
- **Laurel:** Library of constrained types. Strata translates to Core.
- **Compilers:** Select from Laurel's constrained types.

Compilers cannot inject arbitrary axioms. Every constraint traces
back to a proven constrained type or a procedure postcondition that
Strata translates using proven machinery.

### D3: Core already has `Sequence.length(s) >= 0`

**Status:** Confirmed

`seqLengthFunc` in `Factory.lean` has this axiom. Language compilers
only need to add the UPPER bound via their wrapper procedures.

### D4: Functions with axioms — implemented for array length

**Status:** Resolved

`JArray.length` is no longer a procedure. The JVerify compiler now
emits `Sequence.length(arr.$data)` directly in all contexts —
contracts, postconditions, and statements. No procedure wrapper.

Bounds come from two sources:
- `Sequence.length >= 0` — Core Factory axiom (already existed)
- `<= 2147483647` — from the `int32` return type, enforced by
  constrained type elimination

The `pureContext` flag is no longer needed for array length. It
was removed along with the `JArray.length` procedure definitions.

This follows the same pattern as `readInt32` for constrained types
in the heap (see `constrained-types-in-heap/decisions.md` D4):
use Core Factory functions with fixed axioms, let the constrained
type machinery handle the rest.

Commit `055733ad` on `seebees/experimental-work`.

### D5: Different languages have different bounds

**Status:** Documented for future reference

- Java: `nat32` (0..2^31-1) — JLS §10.4, §10.7
- JavaScript: `nat53` (0..2^53-1) — safe integer range
- Go: `nat63` (0..2^63-1) — 64-bit signed, non-negative
- Python: unbounded (`int`) — no constraint needed
