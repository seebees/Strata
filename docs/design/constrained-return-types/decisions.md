# Constrained Return Types: Decisions

**Date:** 2026-03-27

### D1: Support constrained return types on functions

**Status:** Accepted

The `constrainedTypeElim` pass currently rejects functions with
constrained return types (line 249: "constrained return types on
functions are not yet supported"). It should instead:
1. Replace the return type with the base type
2. Add an ensures clause with the constraint

This is a language-agnostic Strata feature. The ensures clause
becomes a Core axiom on the function.

**Rationale:** Constrained return types are the mechanism by which
language compilers express type constraints. Without this, compilers
have no safe way to tell the prover about language-specific bounds.

**Implementation note:** `elimProc` already handles constrained
output types on procedures. The guard `if proc.isFunctional then []`
skips ensures generation for functions. Removing this guard and the
diagnostic error should be the core of the fix.

### D2: Constrained types belong in Laurel (Strata), not in compilers

**Status:** Accepted

Types like `nat32`, `int64`, etc. are mathematical facts about
number ranges. They belong in Laurel — the intermediate language
that all compilers target. This ensures:
- The types are defined once, used by all language compilers
- Compilers can't define inconsistent types
- The set of available axioms is auditable
- Strata translates them to Core with proofs — nothing enters
  Core that isn't proven

Compilers SELECT from this library. They cannot invent new axioms.
The trust surface is: "did the compiler pick the right type?"

**Why not Core:** Core doesn't have constrained types — that's a
Laurel concept. Core only has proven things. Strata's job is to
bridge Laurel to Core, translating constrained types into ensures
clauses and axioms that Core can reason about.

**Why not in compilers:** If each compiler defines its own `nat32`,
they could define them inconsistently. A shared library in Laurel
means one definition, one set of properties, used everywhere.

### D3: Core already has `Sequence.length(s) >= 0`

**Status:** Confirmed

`seqLengthFunc` in `Factory.lean` already has the axiom
`Sequence.length(s) >= 0`. This is a proven, universal fact.
Language compilers only need to add the UPPER bound via constrained
return types (e.g., `nat32` adds `<= 2147483647`).

### D4: Language compilers select constrained types, not axioms

**Status:** Accepted

The architecture is layered:

- **Core:** Proven universal axioms (e.g., `Sequence.length >= 0`).
  Nothing enters Core that isn't proven in Lean.
- **Laurel:** Library of constrained types (`nat32`, `int32`, etc.)
  with mathematical properties. Strata translates these to Core.
- **Compilers:** Select from Laurel's constrained types. Java says
  `array.length` returns `nat32`. JavaScript would say `nat53`.
  Go would say `nat63`. Python says `int` (unbounded).

This means:
- Compilers cannot inject arbitrary axioms
- Every axiom traces back to a proven constrained type in Laurel
- The trust surface is small and auditable: "did the compiler
  pick the right constrained type for this operation?"
- Eventually, we can verify the compiler's type selections by
  verifying the compiler itself with JVerify

### D5: Different languages have different bounds

**Status:** Documented for future reference

Known language-specific array/collection length bounds:
- Java: `nat32` (0..2^31-1) — JLS §10.4, §10.7
- JavaScript: `nat53` (0..2^53-1) — safe integer range
- Go: `nat63` (0..2^63-1) — 64-bit signed, non-negative
- Python: unbounded (`int`) — no constraint needed
- Rust/C: platform-dependent (`usize`)

Each language compiler selects the appropriate constrained type
from the shared Laurel library.
