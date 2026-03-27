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

### Layer 2: Strata/Laurel — Constrained Types and Procedure Postconditions

Constrained types (`int32`, `nat32`, etc.) are mathematical facts
about number ranges. They live in Laurel. Strata translates them
to Core. The existing procedure postcondition machinery propagates
constraints to callers.

### Layer 3: Language Compiler — Type Selection and Wrapper Procedures

Each compiler selects constrained types and emits wrapper procedures
with postconditions that encode language-specific invariants. The
compiler CANNOT invent new axioms in Core. It can only emit Laurel
procedures with postconditions, which Strata translates to Core
using the existing proven machinery.

## Current Status

The initial design assumed we'd need to modify Strata's
`constrainedTypeElim` to support constrained return types on
functions. This turned out to be unnecessary. The existing procedure
postcondition machinery already handles everything we need.

See `jverify/design/array-support/decisions.md` for the JVerify-side
implementation that uses this architecture.
