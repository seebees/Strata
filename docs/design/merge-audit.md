# Merge Audit: Design Docs vs Current Code

**Date:** 2026-04-12
**Purpose:** Systematic comparison of design doc requirements against
current code state after merge commit 0562a5c3.

## Methodology

For each design doc, list every concrete requirement, then check
whether the current code satisfies it.

Legend:
- ✅ Implemented correctly
- ❌ Missing or broken (merge regression)
- ⚠️ Partially implemented or pre-existing gap
- 🔧 Fixed during this session

---

## 1. Instance Methods (instance-methods/design.md, decisions.md)

| Requirement | Status | Notes |
|---|---|---|
| `instanceProcCoreName` uses `~>` separator (D9) | ✅ | |
| Parameter order: `[$heap, self, ...params]` (D5) | ✅ | Java frontend adds self, heap pass prepends $heap |
| `self` is regular parameter, not `This` (D6) | ✅ | |
| IM1 consistency proof (D7) | ✅ | In InstanceMethodProperties.lean |
| Heap analysis tracks InstanceCall callees (§2) | ✅ | |
| Heap transform injects $heap into InstanceCall (§3) | ✅ | |
| Modifies clauses process instance procedures (§4) | ✅ | |
| Instance procedure definitions translated (§5) | ✅ | |
| **instanceCallArgs: heap-aware argument ordering (§6)** | ❌ → 🔧 | **MERGE REGRESSION.** `instanceCallArgs` function lost. Current code always treats first arg as heap. Produces `[userArg, self, rest]` instead of `[self, userArg, rest]` when callee doesn't use heap. |

---

## 2. Laurel Exceptions (laurel-exceptions/spec.md, design.md, decisions.md)

| Requirement | Status | Notes |
|---|---|---|
| First-class Throw + TryCatch in Laurel StmtExpr (D1, D4) | ✅ | |
| Result ADT for fallible operations (D2) | ⚠️ | Simplified: `ExceptionResult` with `Success()`/`Failure()` (no args). Pre-merge state too. |
| Throw → `$result := Failure(); exit <target>` (D5) | ✅ | |
| TryCatch → labeled blocks + catch dispatch (D6) | ✅ | |
| Exception target tracking in translator state (D7) | ✅ | `exceptionTarget` field |
| Every procedure gets `$result : ExceptionResult` output | ✅ | |
| Body starts with `$result := Success` | ✅ | |
| `mkCallWithResult` propagation check after calls | ✅ | |
| **$result/Success/Failure in ensures clauses** | ❌ → 🔧 | **MERGE REGRESSION.** Registered in scope but not in refToDef. Translator couldn't look them up → program discarded → soundness failures. Fixed by intercepting in Identifier case. |
| Property 1: Throw Produces Failure | ✅ | ExceptionProperties.lean: `throw_produces_exit` |
| Property 2: Success Path Isolation | ⚠️ | Not directly proven yet |
| Property 7: Result Exhaustiveness | ✅ | ExceptionProperties.lean: `result_exhaustive`, `result_exclusive` |
| Property 8: Ensures Clause Isolation | ✅ | ExceptionProperties.lean: `ensures_isolation_success`, `ensures_isolation_failure` |
| Properties 9-12: Cross-method propagation | ✅ | PropagationProperties.lean: 4 theorems |

---

## 3. Exit Semantics (exit-semantics/spec.md)

| Requirement | Status | Notes |
|---|---|---|
| BlockResult: normal/exited | ✅ | |
| consumeExit: matching block consumes exit | ✅ | |
| E1: Exit preserves store | ✅ | ExitProperties.lean: `exit_preserves_env` |
| E2: Exit skips remaining | ✅ | ExitProperties.lean: `exit_skips_remaining` |
| E3: Matching block consumes | ✅ | ExitProperties.lean: `matching_block_consumes` |
| E4: Non-matching exit propagates | ✅ | ExitProperties.lean: `nonmatching_exit_propagates` |
| E5: Normal block completion | ✅ | ExitProperties.lean: `normal_block_completion` |
| Well-formedness constraints | ✅ | Type checker enforces |

---

## 4. Cross-Type Resolution (cross-type-resolution/decisions.md)

| Requirement | Status | Notes |
|---|---|---|
| Frontend resolves dispatch, not Laurel (D1) | ✅ | |
| Frontend qualifies callee names with `~>` (D2) | ✅ | Java frontend emits qualified names |
| Early qualification pre-pass (D4) | ✅ | `qualifyInstanceProcNames` |
| Heap analysis works with qualified names (D4) | ✅ | |
| Preservation proof obligation (D5) | ⚠️ | Not yet proven |

---

## 5. Constrained Types in Heap (constrained-types-in-heap/design.md)

| Requirement | Status | Notes |
|---|---|---|
| Factory read functions (readInt32, readInt16, readInt8) | ✅ | |
| Equality axioms: `readIntN(BoxInt(v)) == v` | ❌ → 🔧 | **MERGE REGRESSION.** `mkReadFuncAxioms` was lost. Restored with typed `.op` nodes. |
| Heap round-trip: write BoxInt, read with readIntN | ✅ | |
| Constrained type elimination: write-side asserts | ✅ | |

---

## 6. Translator Proof (translator-proof/design.md)

| Requirement | Status | Notes |
|---|---|---|
| TranslatorProperties.lean (46→64 theorems) | ✅ | 64 theorems, 0 sorry |
| TranslatorEqLemmas.lean (30→35 theorems) | ✅ | 35 theorems, 0 sorry |
| HeapParameterizationProperties.lean (17→21 theorems) | ✅ | 21 theorems, 0 sorry |
| InstanceMethodProperties.lean (1→5 theorems) | ✅ | 5 theorems, 0 sorry |
| ExitProperties.lean (10 theorems) | ✅ | 10 theorems, 0 sorry |
| ExceptionProperties.lean (12+2 defs) | ✅ | 12 theorems, 0 sorry |
| PropagationProperties.lean (4 theorems) | ✅ | 4 theorems, 0 sorry |
| P-Call-1: mkCallWithResult includes $result | ✅ | |
| P-Call-2: Instance call argument order | ✅ | But the runtime code it proves about is broken! |
| P-Spec-2f: Function postcondition axiom generation | ✅ | |
| P-Constrained-1: Constraint precondition injection | ✅ | |

---

## 7. Constrained Return Types (constrained-return-types/design.md)

| Requirement | Status | Notes |
|---|---|---|
| Layered axiom architecture | ✅ | No changes needed |
| Procedure postcondition machinery | ✅ | |

---

## Summary of Merge Regressions Found

### Fixed during this session:
1. **mkReadFuncAxioms** — equality axioms for readInt32/readInt16/readInt8 lost in merge. Restored.
2. **$result/Success/Failure scope registration** — registered in scope but not in refToDef. Fixed by intercepting in translator's Identifier case.
3. **Static method ?static suffix stripping** — javac appends ?static to class names. Fixed.
4. **Static method external call filtering** — only qualify for source-file classes. Fixed.

### Still broken:
5. **instanceCallArgs** — heap-aware argument ordering lost. Current code always treats first arg as heap, breaking instance calls when callee doesn't use heap.

### Pre-existing issues (not merge regressions):
6. ExceptionResult simplified (no args) vs spec's Result<T> — was this way before merge
7. "Composite vs int" type checking bug in instance method returns
8. old() expression translation — 5 tests
9. Array types not supported — 8+ tests
10. Cross-type solver unknown — 3 tests (never worked)

---

## Proof Status

| File | Theorems | Sorry | Status |
|------|----------|-------|--------|
| TranslatorProperties.lean | 64 | 0 | ✅ |
| TranslatorEqLemmas.lean | 35 | 0 | ✅ |
| HeapParameterizationProperties.lean | 21 | 0 | ✅ |
| InstanceMethodProperties.lean | 5 | 0 | ✅ |
| ExitProperties.lean | 10 | 0 | ✅ |
| ExceptionProperties.lean | 12 | 0 | ✅ |
| PropagationProperties.lean | 4 | 0 | ✅ |
| **Total** | **151** | **0** | |

All 151 theorems compile with 0 sorry. The proof infrastructure
survived the merge intact. The proofs are about the CODE STRUCTURE
though — they prove things like "mkCallWithResult always includes
$result in the LHS." They don't catch the instanceCallArgs bug
because that bug is in the argument VALUE ordering, not the
structural shape.
