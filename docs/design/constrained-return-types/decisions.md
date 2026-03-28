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

### D4: Functions with axioms are the right long-term mechanism

**Status:** Revised — deferred pending Core investigation

We originally chose to emit `JArray.length` as a procedure with
ensures because functions couldn't carry postconditions. This was
a workaround, not the right design.

Core functions carry properties via axioms (e.g., Sequence
operations). Functions are pure and callable in all contexts
(contracts, postconditions, statements). `JArray.length` as a
function with axioms would eliminate the `pureContext` flag.

However, the Laurel-to-Core translator does not currently generate
axioms from Laurel functions. Core function axioms are built into
Core's Factory for mathematical operations. Extending the translator
to generate axioms from Laurel is possible but requires
investigation.

For the immediate constrained-type-in-heap problem, we chose a
different mechanism: the constrained type elimination pass generates
assumes for datatype accessor reads. See
`constrained-types-in-heap/decisions.md` D4.

The `JArray.length` refactoring from procedure to function with
axioms remains a future improvement. The `pureContext` flag stays
for now. This is a two-way door — the compiler interface doesn't
change, only Strata internals.

### D5: Different languages have different bounds

**Status:** Documented for future reference

- Java: `nat32` (0..2^31-1) — JLS §10.4, §10.7
- JavaScript: `nat53` (0..2^53-1) — safe integer range
- Go: `nat63` (0..2^63-1) — 64-bit signed, non-negative
- Python: unbounded (`int`) — no constraint needed
