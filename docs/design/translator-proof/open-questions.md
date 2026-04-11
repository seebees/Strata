# Translator Proof — Open Questions

## OQ1: Two-layer module architecture for provability

**Status:** Open  
**Date:** 2026-04-11

### Problem

Lean 4's `module` keyword makes definitions opaque across module
boundaries. This is good for large-scale software engineering (hide
implementation details, allow internal refactoring) but bad for
verification (proofs need to unfold definitions to reason about them).

Currently we work around this with:
- `@[expose]` on individual definitions (ad hoc, per-proof)
- Placing proofs inside the module file itself (mixes impl + proof)

Neither approach is principled.

### Proposed Architecture: Two-Layer Onion

**Inner layer (proof workspace):**
- All module-internal definitions are `@[expose]`d
- Module boundaries exist for *organization*, not for hiding
- Proofs can reach into any implementation detail across any module
- This is where all theorem proving happens
- Files: `*.lean` (implementation) + `*Properties.lean` (proofs)

**Outer layer (verified interface):**
- A curated set of modules that re-export only the stable API
- Deliberately chosen properties are exposed as the public contract
- External consumers see proven properties but not the internals
- This layer is the "verified specification" of the pipeline
- Changes to the inner layer that preserve the outer layer's
  properties are safe refactors

### Benefits

1. **Proof freedom:** Inner layer has no visibility barriers.
   Any property that's true is provable.
2. **Stable contract:** Outer layer defines what external consumers
   can rely on. Internal refactoring doesn't break consumers.
3. **Clear separation:** "Can I prove this?" is never blocked by
   module visibility — only by mathematical difficulty.
4. **Incremental adoption:** We can start by `@[expose]`ing
   everything in the inner layer, then gradually build the outer
   layer as we identify the stable API.

### Open Questions

- What's the right granularity for the outer layer? Per-pass?
  Per-feature? Per-property-family (P-Spec, P-Struct, etc.)?
- Should the outer layer be a separate Lean package/library, or
  just a set of "facade" modules in the same package?
- How do we enforce that the inner layer isn't used directly by
  external consumers? Lean doesn't have package-private visibility.
- Does `@[expose]` on everything in the inner layer have
  measurable compile-time impact? Need to benchmark.

### Next Steps

1. Add `@[expose]` to all pass functions that proofs need
   (immediate — unblocks P-Spec-3 and future properties)
2. Document which properties constitute the "outer layer" contract
3. Design the facade module structure
