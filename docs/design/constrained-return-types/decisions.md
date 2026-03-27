# Decision: Constrained Return Types and the Axiom Trust Architecture

**Date:** 2026-03-27

## Context

Language compilers (Java, Python, JavaScript, Go, etc.) target Laurel
as an intermediate language. Each language has its own type constraints
— Java `int` is 32-bit, JavaScript numbers are 64-bit floats, Python
integers are unbounded. When these compilers emit Laurel programs,
they need to express language-specific type constraints on operations
like array length, collection size, and index bounds.

The question: how do language compilers express these constraints
without introducing unsound axioms into the proof system?

## The Trust Boundary Problem

Core proofs are sound — they're checked in Lean. When a language
compiler adds a constraint (e.g., "array length fits in 32 bits"),
that constraint is an axiom. If the axiom is wrong, everything
downstream is unsound.

Currently, external functions in Laurel bridge to Core built-ins
that have proven axioms. The trust is small: "the Laurel name maps
to the correct Core built-in." Adding arbitrary postconditions to
external functions would let compilers inject unproven axioms.

## The Layered Axiom Architecture

### Layer 1: Core — Proven Universal Axioms

Mathematical facts true for all languages:
- `Sequence.length(s) >= 0` (sequences have non-negative length)
- `Sequence.select(Sequence.update(s, i, v), i) == v` (read-after-write)
- `Sequence.length(Sequence.empty) == 0`

These are proven in Lean. No trust required.

### Layer 2: Strata/Laurel — Library of Constrained Types

Mathematical number sets with proven properties:
- `nat32`: `x >= 0 && x <= 2147483647`
- `nat53`: `x >= 0 && x <= 9007199254740991` (JS safe integer)
- `nat63`: `x >= 0 && x <= 9223372036854775807` (64-bit non-negative)
- `int8`, `int16`, `int32`, `int64`: signed ranges
- `uint8`, `uint16`, `uint32`: unsigned ranges

These are mathematical facts — not language-specific. Any language
can use them. Their properties (subset relationships, range bounds)
are provable.

### Layer 3: Language Compiler — Type Selection

Each compiler selects from the library of constrained types:
- Java: `array.length` returns `nat32`
- JavaScript: `array.length` returns `nat53`
- Go: `len(slice)` returns `nat63`
- Python: `len(list)` returns `int` (unbounded, no constraint)

The compiler CANNOT invent new axioms. It can only SELECT from
proven constrained types. The trust surface is: "did the compiler
pick the right type?" This is small, auditable, and eventually
verifiable (by verifying the compiler itself).

## Decisions

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

## Implementation Plan

1. Support constrained return types on functions in `constrainedTypeElim`
2. Define `nat32` and other common constrained types in shared Laurel
3. JVerify compiler: emit `JArray.length` returning `nat32`

## Open Questions

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
