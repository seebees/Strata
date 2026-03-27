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

### D4: Strata changes NOT required for the initial implementation

**Status:** Accepted (revised from original plan)

We originally planned to modify `constrainedTypeElim` to support
constrained return types on functions (D1 in the original design).
This turned out to be unnecessary because:

1. The JVerify compiler emits `JArray.length` as a PROCEDURE (not
   a function) with postconditions
2. Strata's existing procedure postcondition machinery translates
   these to Core postconditions
3. Callers automatically get the constraint knowledge

The `constrainedTypeElim` change (supporting constrained return
types on functions) remains a good future enhancement for Strata,
but it's not blocking any current work.

### D5: Different languages have different bounds

**Status:** Documented for future reference

- Java: `nat32` (0..2^31-1) — JLS §10.4, §10.7
- JavaScript: `nat53` (0..2^53-1) — safe integer range
- Go: `nat63` (0..2^63-1) — 64-bit signed, non-negative
- Python: unbounded (`int`) — no constraint needed
