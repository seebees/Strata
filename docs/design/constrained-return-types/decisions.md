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
constrained return types. It should instead:
1. Replace the return type with the base type
2. Add an ensures clause with the constraint

This is a language-agnostic Strata feature. The ensures clause
becomes a Core axiom on the function.

**Rationale:** Constrained return types are the mechanism by which
language compilers express type constraints. Without this, compilers
have no safe way to tell the prover about language-specific bounds.

### D2: Constrained types belong in Strata, not in compilers

**Status:** Accepted

Types like `nat32`, `int64`, etc. are mathematical facts. They
should be defined in Strata's shared library, not in each language
compiler. This ensures:
- The types are proven once, used everywhere
- Compilers can't define inconsistent types
- The set of available axioms is auditable

### D3: Core should have `Sequence.length(s) >= 0` axiom

**Status:** Proposed (needs verification)

This is universally true and should be a Core axiom, not a
language-specific constraint. Need to check if it already exists
in `seqLengthFunc`.

## Implementation Plan

1. Add constrained return type support in `constrainedTypeElim`
2. Verify `Sequence.length >= 0` axiom exists in Core (add if not)
3. Define `nat32` and other common constrained types in Strata
4. JVerify compiler: emit `JArray.length` returning `nat32`

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
