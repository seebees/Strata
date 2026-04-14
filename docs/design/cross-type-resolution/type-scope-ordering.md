# Cross-Composite Field Resolution: Type Scope Ordering

**Date:** 2026-04-14
**Status:** Implemented

## Problem

When a postcondition on one composite references fields of another composite
via chained field access (e.g., `self#start#line` where `start` is a `Position`
field on `Range` and `line` is a field on `Position`), the resolution pass
failed with "Resolution failed: 'line' is not defined."

Root cause: `preRegisterTopLevel` pre-registered type **names** and field
**names** into the global scope so that declaration order doesn't matter, but
it did not build **type scopes** (the per-composite field lookup tables). Type
scopes were built later in `resolveTypeDefinition`, one composite at a time.
If Range was processed before Position, Range's postconditions needed
Position's type scope, which didn't exist yet.

## Options Considered

### Option 1: Reorder declarations (rejected)

Have the Java compiler emit composites in dependency order. Fragile, doesn't
generalize to other languages, and the existing `preRegisterTopLevel` design
explicitly aims to make declaration order irrelevant.

### Option 2: Two-pass — pre-build all type scopes (chosen)

Extend `preRegisterTopLevel` to build type scopes for all composites after
registering all type and field names. This guarantees all type scopes exist
before any procedure body or postcondition is resolved.

### Option 3: Lazy type scope building (deferred)

Build type scopes on-demand when `resolveFieldInTypeScope` is called and the
scope doesn't exist. Potentially more efficient but harder to reason about
and prove properties on. Could be adopted later if proven equivalent.

## Decision: Option 2

Two-pass pre-building is consistent with the existing design intent of
`preRegisterTopLevel` ("declaration order doesn't matter"). It provides a
clean invariant: **all type scopes are populated before any procedure body
is resolved.** This invariant is easy to state and prove, which matters for
soundness — our north star.

## Implementation

Two changes to `Resolution.lean`:

### 1. Use real field nodes in pre-registration

Changed `preRegisterTopLevel` to register fields with `AstNode.field` (carrying
the field's declared type) instead of `placeholderNode` (which had type `TVoid`).
This is necessary because `targetTypeName` calls `node.getType` on type scope
entries to determine the target type for chained field access.

### 2. Build type scopes after registering all types

Added a second loop in `preRegisterTopLevel` that builds type scopes for all
composites. Each composite's type scope maps field names to their scope entries
(which now carry correct type information from change 1).

### 3. Stable field IDs across pre-registration and resolution

Changed `resolveField` to reuse the pre-registered ID when one exists. Without
this, `resolveField` would generate a new ID, causing the type scope entries
(which reference the pre-registration ID) to become stale. The `model.refToDef`
map (built from the resolved AST) would have the new ID, but postconditions
resolved using the pre-registration type scope would reference the old ID.
`resolveQualifiedFieldName` in heap parameterization would then fail to find
the field, producing Holes.

## Invariant

After `preRegisterTopLevel` completes:
- For every composite `C` with fields `f1, f2, ...`:
  - `state.typeScopes` contains an entry for `C.name.text`
  - That entry maps each `fi.name.text` to a scope entry `(id, .field C fi)`
  - The field's type is the unresolved `fi.type` from the AST
  - The `id` is the same ID that `resolveField` will later use

## Testing

- Range.compareTo postcondition with cross-composite field access: PASS
- Full Strata test suite: zero regressions
- Full JVerify test suite: zero regressions
