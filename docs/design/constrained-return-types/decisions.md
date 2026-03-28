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

### D4: Functions with axioms are the right mechanism

**Status:** Revised

We originally chose to emit `JArray.length` as a procedure with
ensures because functions couldn't carry postconditions. This was
a workaround, not the right design.

Core functions DO carry properties — via axioms, not postconditions.
Axioms are the established mechanism for function properties in
Core. The Sequence operations use axioms. Functions are pure and
callable in all contexts (contracts, postconditions, statements).

The procedure approach forced a `pureContext` flag in the JVerify
compiler: contracts use `Sequence.length` directly (a function),
while statements use `JArray.length` (a procedure). This
distinction is unnecessary if `JArray.length` is a function with
axioms.

`JArray.length` should be refactored from a procedure with ensures
to a function with axioms:

```
function JArray.length(heap: Heap, s: JArray) : int
  axiom: JArray.length(heap, s) == Sequence.length(...)
  axiom: JArray.length(heap, s) >= 0
  axiom: JArray.length(heap, s) <= 2147483647
```

This eliminates the `pureContext` flag for array length and allows
`JArray.length` to be used in contracts and postconditions.

See also: `constrained-types-in-heap/decisions.md` D4, which uses
the same pattern for constrained-type field reads.

### D5: Different languages have different bounds

**Status:** Documented for future reference

- Java: `nat32` (0..2^31-1) — JLS §10.4, §10.7
- JavaScript: `nat53` (0..2^53-1) — safe integer range
- Go: `nat63` (0..2^63-1) — 64-bit signed, non-negative
- Python: unbounded (`int`) — no constraint needed
