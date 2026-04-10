# translate_decls_match Proof Status

## What This Is
This document tracks progress on proving `translate_decls_match` in
`Strata/Languages/Laurel/TranslatorEquivalence.lean` — the main correctness
theorem of the jverify translator equivalence project.

## The Theorem
```lean
theorem translate_decls_match (program : Program) (coreProgram : Core.Program)
    (h : (translate {} program).1 = some coreProgram) :
    Core.Program.stripMetaData (Core.Program.eraseTypes coreProgram) = translateProgramModel program
```

When the real Laurel→Core translator succeeds, its output (after stripping metadata
and erasing types) equals the pure model `translateProgramModel`.

## Current Goal State (after existing proof steps)
The proof has been restructured into two theorems:

1. `translate_decls_eq_model` — the core lemma (has the sorry)
2. `translate_decls_match` — the main theorem (calls translate_decls_eq_model)

In `translate_decls_eq_model`, the proof has:
1. Reduced to decl-list equality via `Program_strip_erase_eq_decls`
2. Inlined the full pipeline via `rw [translate_fst]` — so `transformedProg` and `model` are CONCRETE expressions of `program`
3. Split on `coreProgramHasSuperfluousErrors` (false branch)
4. Decomposed the real translator side via `translateLaurelToCore_decls_ext` — existential witnesses `gdt`, `cds`, `pfd`, `procs`, `iprocs` are the actual monadic results on the concrete post-pipeline program
5. Applied `exceptionResultDecl_strip_erase_eq_model` (Category 1)
6. Applied `type_decls_strip_erase_id` on grouped datatype decls
7. Decomposed the model side via `translateProgramModel_decls` — existential witnesses `mInfra`..`mInstProcs` are the actual computed segments
8. Stripped the common `[modelExceptionResultDecl]` prefix

**Key difference from before**: By using `rw [translate_fst]` BEFORE `translateLaurelToCore_decls_ext`, the existential witnesses from the real translator side are tied to the CONCRETE post-pipeline program (not an abstract `transformedProg`). This means `mkReadFuncAxioms` is applied to the concrete pipeline expression, not an abstract variable.

**Remaining goal:**
```
⊢ gdt ++
    (mkReadFuncAxioms <concrete-pipeline-program>).map(s∘e) ++
    cds.map(s∘e) ++
    pfd.map(s∘e) ++
    procs.map(proc).map(s∘e) ++
    iprocs.map(proc).map(s∘e)
  =
  mInfra ++ mDatatypes ++ mReadAxioms ++ mAncestors ++ mConstraints ++ mHeap ++
    mExtFuncs ++ mTransFuncs ++ mProcs ++ mWitness ++ mInstProcs
```

Where `<concrete-pipeline-program>` is the full pipeline expression:
```
(resolve (constrainedTypeElim (resolve (eliminateReturnsInExpressionTransform
  (liftExpressionAssignments (resolve (resolve (modifiesClausesTransform
    (resolve (typeHierarchyTransform (resolve (heapParameterization
      (resolve {program with ...}).model
      (resolve {program with ...}).program)
    (some (resolve {program with ...}).model)).model
    ...) ...) ...) ...) ...) ...) ...) ...) ...) ...).program
```

## Key Hypotheses Available
- `hTranslate`: `(runTranslateM {model} (translateLaurelToCore transformedProg)).1 = some coreProgram`
- `hRealDecls`: decomposition of `coreProgram.decls` into the 6 LHS segments
- `hAllType`: `∀ d ∈ groupedDatatypeDecls, ∃ t, d = Core.Decl.type t`
- `hAllAx`: `∀ d ∈ mkReadFuncAxioms transformedProg, ∃ a, d = Core.Decl.ax a`
- `hModelDecls`: decomposition of `(translateProgramModel program).decls` into the 11 RHS segments
- `transformedProg`: result of ~15 transformation passes on `program`
- `model`: SemanticModel from the resolution pipeline

## Architecture: How the Two Sides Relate

### Real translator pipeline (LaurelToCoreTranslator.lean)
```
program
  → prepend coreDefinitionsForLaurel procs/types
  → resolve → heapParameterization → resolve → typeHierarchyTransform → resolve
  → modifiesClausesTransform → resolve → resolve
  → inferHoleTypes → eliminateHoles → desugarShortCircuit
  → liftExpressionAssignments → eliminateReturnsInExpressionTransform
  → resolve → constrainedTypeElim → resolve
  = transformedProg
  → translateLaurelToCore transformedProg
  = coreProgram
```

### Model (TranslatorModel.lean)
`translateProgramModel program` directly computes the expected output by:
- Building infrastructure datatypes (TypeTag, Field, Box, Heap, etc.)
- Translating user datatypes via `coreMonoType`
- Building read axioms, ancestor decls, constraint funcs, heap funcs
- Translating external/transparent functions via `translateFuncModel`
- Translating procedures via `translateProcModel`
- Translating instance procedures

## Proof Strategy: Work Backwards from Goal

The 6 LHS segments map to the 11 RHS segments as follows:

| LHS Segment | RHS Segment(s) | Bridge Lemma Needed |
|---|---|---|
| `groupedDatatypeDecls` | `mInfra ++ mDatatypes` | `groupedDatatypeDecls_eq_model_full` |
| `(mkReadFuncAxioms transformedProg).map(s∘e)` | `mReadAxioms` | `readAxioms_eq_model` |
| `constantDecls.map(s∘e)` | `mAncestors ++ mConstraints ++ mHeap` | `constantDecls_eq_model` |
| `pureFuncDecls.map(s∘e)` | `mExtFuncs ++ mTransFuncs` | `pureFuncDecls_eq_model` |
| `procedures.map(proc).map(s∘e)` | `mProcs ++ mWitness` | `procedures_eq_model` |
| `instanceProcedures.map(proc).map(s∘e)` | `mInstProcs` | `instanceProcedures_eq_model` |

### What Each Bridge Lemma Requires

**1. `groupedDatatypeDecls_eq_model_full`**
- Need: `groupedDatatypeDecls = mInfra ++ mDatatypes`
- Since `hAllType` says all are `.type` decls, strip/erase is identity (already applied)
- Requires: showing `translateTypes transformedProg model s` produces the same types
  as the model's `infraDatatypes ++ datatypeDecls`
- Key sub-lemma: `translateTypes` on the post-pipeline program = model's type list
- Difficulty: MEDIUM — need to show type translation is invariant under the passes

**2. `readAxioms_eq_model`**
- Need: `(mkReadFuncAxioms transformedProg).map(s∘e) = mReadAxioms`
- `mkReadFuncAxioms` depends on `transformedProg.types` (looks for Box constructors)
- The passes may modify types, so need: `transformedProg.types` preserves Box structure
- Existing: `mkReadFuncAxioms_strip_erase_eq` (conditional on BoxInt)
- Difficulty: MEDIUM — need pass-preservation lemma for Box types

**3. `constantDecls_eq_model`**
- Need: `constantDecls.map(s∘e) = mAncestors ++ mConstraints ++ mHeap`
- `constantDecls` comes from `translateConstants` in the real translator
- The model builds ancestor, constraint, and heap function decls separately
- Difficulty: HARD — need to decompose translateConstants output

**4. `pureFuncDecls_eq_model`**
- Need: `pureFuncDecls.map(s∘e) = mExtFuncs ++ mTransFuncs`
- `pureFuncDecls` comes from `mapM translateFunc` on functional procedures
- The model separates external vs transparent functions
- Difficulty: HARD — need per-function equivalence

**5. `procedures_eq_model`**
- Need: `procedures.map(proc).map(s∘e) = mProcs ++ mWitness`
- `procedures` comes from `mapM translateProcedure` on non-functional procedures
- The model separates regular procs from witness procs
- Existing: `proc_decl_strip_erase_eq_model` (for simple procs with many preconditions)
- Difficulty: VERY HARD — most complex category

**6. `instanceProcedures_eq_model`**
- Need: `instanceProcedures.map(proc).map(s∘e) = mInstProcs`
- Instance procedures come from composite type methods
- Difficulty: HARD — involves composite type resolution

## Completed Work
- [x] Converted `resolveConstrainedInExpr` and `qualifyFieldNamesInExpr` from `partial def` to `def`
- [x] Added `@[expose]` to both for cross-module unfolding
- [x] Proved `resolveConstrainedInExpr_nil` and `qualifyFieldNamesInExpr_nil` (in TranslatorModel.lean)
- [x] Removed 2 of 3 sorrys from TranslatorEquivalence.lean
- [x] Restructured proof: `translate_decls_match` now calls `translate_decls_eq_model`
- [x] `translate_decls_eq_model` decomposes both sides and reduces to 6 bridge equalities
- [ ] Bridge lemma 1: gdt = mInfra ++ mDatatypes (datatypes)
- [ ] Bridge lemma 2: (mkReadFuncAxioms transformedProg).map(s∘e) = mReadAxioms (read axioms)
- [ ] Bridge lemma 3: cds.map(s∘e) = mAncestors ++ mConstraints ++ mHeap (constants)
- [ ] Bridge lemma 4: pfd.map(s∘e) = mExtFuncs ++ mTransFuncs (pure functions)
- [ ] Bridge lemma 5: procs.map(proc).map(s∘e) = mProcs ++ mWitness (procedures)
- [ ] Bridge lemma 6: iprocs.map(proc).map(s∘e) = mInstProcs (instance procedures)
- [ ] Final assembly: use bridge lemmas to close the sorry in translate_decls_eq_model

## Current Sorry Location
File: `Strata/Languages/Laurel/TranslatorEquivalence.lean`
Line: ~2152 (in `translate_decls_eq_model`)
This is the ONLY sorry in the file (others are in comments).

## Approach Tried and Lessons Learned

### What works
- `translate_pipeline_result` + `translateLaurelToCore_decls_ext` decomposes the real translator side
- `translateProgramModel_decls` decomposes the model side
- `exceptionResultDecl_strip_erase_eq_model` handles Category 1
- `type_decls_strip_erase_id` handles strip/erase on .type decls

### What doesn't work
- `native_decide`: can't use on universally quantified theorem
- `rfl` / `simp_all`: not definitionally equal (different functions on different inputs)
- Direct unfolding via `translate_fst` + `unfold translateLaurelToCore`: creates 500+ line hypotheses
- Trying to substitute `coreProgram` with concrete value: expressions too large

### Key challenge
Both decompositions produce abstract existential witnesses. The LHS witnesses come from
`translateLaurelToCore` on `transformedProg` (post-pipeline). The RHS witnesses come from
`translateProgramModel` on `program` (pre-pipeline). These are different functions on
different inputs, so the witnesses can't be directly related.

### Recommended approach for bridge lemmas
Each bridge lemma needs to:
1. Take the existential witnesses from both sides as parameters
2. Take the hypotheses that tie them to the concrete computations
3. Show the witnesses are equal by reasoning about the pipeline passes

For example, Bridge 2 (read axioms) needs:
- `mkReadFuncAxioms transformedProg` depends on `transformedProg.types`
- `heapParameterization` adds Box/BoxInt to types when there are int fields + heap procs
- The model's `readFuncAxioms` uses `hasIntField && hasCompositeProcs`
- Need to show these conditions are equivalent

The bridge lemmas should be proven in TranslatorEquivalence.lean (has access to both
real translator and model definitions) or in TranslatorModel.lean (can unfold model defs).

## Difficulty Assessment
- Bridge 1 (datatypes): HARD — translateTypes uses SemanticModel, model uses coreMonoType
- Bridge 2 (read axioms): MEDIUM — mkReadFuncAxioms is simple, need pass-preservation
- Bridge 3 (constants): HARD — constants become ancestor/constraint/heap funcs via passes
- Bridge 4 (pure functions): HARD — need per-function equivalence
- Bridge 5 (procedures): VERY HARD — most complex, needs full proc equivalence
- Bridge 6 (instance procs): HARD — involves composite type resolution

## Files Modified
- `Strata/Languages/Laurel/TranslatorModel.lean` — converted partial defs, added @[expose], added identity proofs
- `Strata/Languages/Laurel/TranslatorEquivalence.lean` — removed 2 sorrys, proof in progress

## How to Resume
1. Read this file
2. Run `lake build Strata.Languages.Laurel.TranslatorEquivalence` to verify current state (1 sorry)
3. The sorry is at the end of `translate_decls_match` (~line 2123)
4. Work on bridge lemmas in order of difficulty (start with datatypes or read axioms)
5. Each bridge lemma should be proven in TranslatorModel.lean or TranslatorEquivalence.lean
   depending on whether it needs to unfold definitions (TranslatorModel.lean, no `module` barrier)
   or needs access to both real translator and model (TranslatorEquivalence.lean)

## Key Insight About `module` Keyword
TranslatorEquivalence.lean uses `module` which prevents unfolding `@[irreducible]` defs
from other files. Solutions:
- Add `@[expose]` to defs that need unfolding (already done for 2 functions)
- Prove lemmas in the same file as the definition (TranslatorModel.lean)
- Use equation lemmas (`foo.eq_1`) instead of `unfold`

## Build Commands
```bash
cd /home/ryanemer/.workspace/jverify-model/jverify/Strata
export PATH="/home/ryanemer/.elan/bin:$PATH"
lake build Strata.Languages.Laurel.TranslatorEquivalence  # full build
lake env lean --threads=4 Strata/Languages/Laurel/TranslatorEquivalence.lean  # single file
```
