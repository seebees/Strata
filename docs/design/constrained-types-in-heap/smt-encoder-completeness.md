# SMT Encoder Completeness for Factory Functions

**Date:** 2026-04-10

## Context

The constrained-types-in-heap feature (D4) introduced Factory
read functions (`readInt32`, `readInt16`, `readInt8`) with bound
axioms, and the translator generates equality axioms connecting
them to the Box system. The heap parameterization emits calls to
these functions for constrained-type field reads.

When verifying `Position.compareTo` with `Long.compare`, the
field reads `self#line` and `o#line` go through `readInt32` in
the heap model. Verification fails.

### Investigation

There are two encoding paths in Strata:

1. **`SMTEncoder.lean`** — the real SMT encoder. Translates Core
   programs to SMT-LIB terms sent to the solver. Handles unknown
   Factory functions correctly through its UF (uninterpreted
   function) default path: creates a proper UF declaration with
   types and registers all axioms.

2. **`ASTtoCST.lean`** — the debug printer. Renders Core programs
   as human-readable text. Uses string-matching handlers
   (`handleUnaryOps`, etc.) that don't cover all Factory functions.
   Missing functions produce error comments in the debug output.

The `ASTtoCST` errors (`Unsupported construct in handleUnaryOps:
unary op: readInt32`) are cosmetic — they affect debug output,
not the actual SMT query.

### The actual bug

The `SMTEncoder` requires type annotations on `.op` nodes
(line 248: `| none => .error "Cannot encode unannotated operation"`).

The translator's `mkReadFuncAxioms` (line 997 of
`LaurelToCoreTranslator.lean`) generates the equality axiom
`readInt32(BoxInt(v)) == v` but creates the `.op` nodes without
type annotations:

```lean
let readOp : Core.Expression.Expr := .op () ⟨readName, ()⟩ none
let constrOp : Core.Expression.Expr := .op () ⟨constrName, ()⟩ none
```

The Factory's own bound axioms work because they use typed
references: `(~readInt32 : %a → int)`.

So the equality axiom is silently dropped by the SMT encoder,
and the solver can't chain through the heap round-trip.

## Decision: Fix the type annotations in mkReadFuncAxioms

The `.op` nodes in `mkReadFuncAxioms` need type annotations
matching the Factory function signatures:

- `readInt32` : `Box → int` (after type parameter instantiation)
- `BoxInt` : `int → Box`

The `SMTEncoder` will then handle these through its existing UF
default path — no changes needed to the encoder itself.

## Open Questions

### Q1: Should ASTtoCST be complete over Factory functions?

The debug printer (`ASTtoCST.lean`) has string-matching handlers
that don't cover 9 Factory functions:

| Missing | Category |
|---|---|
| `readInt32`, `readInt16`, `readInt8` | Heap reads |
| `Sequence.empty` | Sequence constructor |
| `const` | Map constructor |
| `Triggers.empty`, `Triggers.addGroup` | Trigger infrastructure |
| `TriggerGroup.empty`, `TriggerGroup.addTrigger` | Trigger infrastructure |

These produce error comments in debug output. Upstream commit
`83d45ff` (Strata PR #807) improved the fallback from producing
garbage (`.not`, `.bvand`) to producing generic calls
(`readInt32(arg)`), but still logs errors.

Questions:
- Should there be a completeness check that the debug printer
  handles all Factory function names?
- Should the fallback for known-uninterpreted Factory functions
  be error-free (since rendering as `name(args...)` is correct)?
- Is a Lean-level `#eval` check sufficient, or should this be
  a theorem?

This is not blocking — the debug printer doesn't affect
verification correctness. But the error messages are confusing
and make it harder to diagnose real problems.
