# Constrained Return Types: Design

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

## Implementation Plan

1. Support constrained return types on functions in `constrainedTypeElim`
2. Define `nat32` and other common constrained types in shared Laurel
3. JVerify compiler: emit `JArray.length` returning `nat32`
