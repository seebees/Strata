# Decision: Generated Postconditions and Exception Paths

**Date:** 2026-04-13

## Context

After the merge brought in `ProcBodyVerify`, instance method tests
failed with "assertion could not be proved" at `1:1-1:1`.

Root cause: `constrainedTypeElim` generated unconditional postconditions
like `ensures int32$constraint(result)` for constrained return types.
`ProcBodyVerify` + `callElim` creates exception paths where `result` is
nondeterministic (the call might fail, skipping the result assignment).
The unconditional postcondition is unprovable on that path.

## D1: Guard generated output ensures with `isSuccess($result)`

Generated constraint postconditions for output parameters reference the
return value, which is only meaningful on the success path.

### Decision

`constrainedTypeElim` wraps output ensures in
`$result == Success ==> constraint(result)`.

This is infrastructure, not a user contract. The constraint says "IF the
method returns a value, that value fits in the constrained type." It does
not claim the method can't throw — that's the frontend's responsibility.

## D2: Metadata for generated postconditions

Generated postconditions should carry the procedure's source metadata
when the parameter type metadata lacks a valid file range. This prevents
`1:1-1:1` diagnostics.

The `outputEnsuresOf` helper already implements this fallback.

## D3: Diagnostic responsibility boundary

Strata does not know about frontend-specific contract concepts (e.g.,
JVerify's `postcondition` vs `postconditionOnReturn`). By the time
Strata sees the program, everything is Laurel `ensures` clauses with
metadata.

**Frontend responsibility:**
- Desugar contract forms into Laurel ensures clauses
- Attach source metadata and `propertySummary` tags to each clause

**Strata responsibility:**
- Translate ensures clauses faithfully to Core postconditions
- Report verification failures using the metadata attached to each clause
- Use `getPropertySummary` from metadata for the error description

For JVerify-specific desugaring decisions, see
`design/postcondition-desugaring/decisions.md` in the JVerify repo.
