# Translator Functional Model: Decisions

**Date:** 2026-03-31
**Updated:** 2026-04-08
**Status:** Testing Complete, Proof In Progress

## D1–D5: Original Design Decisions

(See git history for original D1–D5 text. Summary: pure functional model
of `translate`, executable, provably correct, models full pipeline end-to-end.)

## D6: Differential Testing Strategy

**Date:** 2026-04-06
**Updated:** 2026-04-07

### Key Lesson

For approximately one week, we attempted to prove `translate ≡ translateProgramModel`
directly. The proof appeared to be making progress — infrastructure was built, lemmas
were proven, the 7-category decomposition was established. But the proof was working
with `sorry`-ed sub-goals, which masked the fact that the model had **35+ bugs**.

Switching to differential testing (running both translators on the same input and
comparing output structurally) found bugs at a rate of roughly 5-10 per session.
The proof attempt found zero bugs because it was operating above the level where
the bugs lived.

**Decision:** Differential testing is the primary bug-finding tool. The proof is
the correctness guarantee. Testing comes FIRST, proof comes AFTER the model is
stable.

### Test Infrastructure

Tests live in `StrataTest/Languages/Laurel/Examples/TranslatorModelTest.lean`.

Each test:
1. Parses a Laurel program string
2. Runs `translateProgramModel` (model) and `translate {}` (real translator)
3. Compares declaration names (catches missing/extra decls)
4. Compares structural output after `stripMetaData ∘ eraseTypes` (catches body differences)

Normalization: assert/assume labels contain source positions that the model can't
know. The `normalizeDecl` function strips numeric offsets from `assert(N)` and
`assume(N)` labels before comparison.

### Test Coverage (118 STRUCT tests)

**109 passing, 9 failing (known model gaps), 4 translation failures (real translator limitations)**

Tested features:
- All integer/boolean/comparison operators, implies, short-circuit
- Literals: int, bool, string
- Control flow: if/else, while, nested, early return, multiple returns
- Functions: static, instance, external, with ensures, multi-arg, nested, chained
- Procedures: static, instance, opaque (with/without impl), with pre/postconditions
- Composites: int/bool/string/constrained fields, 2-3 level inheritance, multiple composites
- Instance calls: function vs procedure, in expressions, in conditions, cross-composite
- Constrained types: int8/int16/int32, field read/write, constraint preconditions
- Datatypes: single/multiple constructors
- Old expressions, forall/exists in postconditions
- Assert/assume statements
- Throw, try-catch, try-catch-finally, labeled blocks, exit
- Exception propagation from procedure calls

Known model gaps (9 failing):
1. Nested try-catch (fixed ID conflicts)
2. String concatenation (`++` operator)
3. Real number literals and arithmetic
4. Forall/exists with triggers
5. Expression-in-statement-position (`$unused` init)
6. Map/Sequence type names

Real translator limitations found (4 failing):
1. `new` in static procedures (typeHierarchyTransform not run with empty model)
2. `abstract` procedures (not yet implemented in translator)
3. Local variables in function bodies (not yet supported)

### Bugs Found and Fixed (35 total)

| # | Bug | Category |
|---|-----|----------|
| 1 | `readFuncAxioms` type annotation: `some int` → `none` | Type erasure |
| 2 | `LocalVariable` types: hardcoded `int` → `coreTypeName ty.val` | Type mapping |
| 3 | Constrained parameter types: `int32` → `int` | Constrained types |
| 4 | Missing constraint preconditions | Constrained types |
| 5 | Constrained field reads: `Box..intVal!` → `readInt32` | Constrained types |
| 6 | Constrained field writes: strip type suffix from field name | Constrained types |
| 7 | `hasFieldAccess`/`hasCompositeProcs`: check bodies AND postconditions | Heap detection |
| 8 | Opaque body wrapping: non-block transparent bodies → `$unused` init | Opaque procs |
| 9 | Precondition label indexing: `requires` vs `requires_N` | Labels |
| 10 | `@[expose]` annotations for cross-module reduction | Module system |
| 11 | Shared `exceptionResultDecl := modelExceptionResultDecl` | Deduplication |
| 12 | Instance function names missing from `isFunc` check | Instance calls |
| 13 | `InstanceCall` in `translateExprModel` missing target and `$heap` args | Instance calls |
| 14 | `InstanceCall` argument order: target before `$heap` | Instance calls |
| 15 | `==>` operator → `ite(a, b, true)` (was catch-all `"op"`) | Operators |
| 16 | `/` → `Int.SafeDiv`, `%` → `Int.SafeMod` (was catch-all) | Operators |
| 17 | Assert/assume label offset normalization | Test infrastructure |
| 18 | Instance proc call in `Return` not handled | Statement translation |
| 19 | Instance proc call in `Assign` not handled | Statement translation |
| 20 | Instance calls in nested expressions unqualified | Name qualification |
| 21 | `InstanceCall` always reads heap | Heap detection |
| 22 | `old()` expression not translated | Expression translation |
| 23 | `old()` inner expressions not qualified by `qualifyMd` | Name qualification |
| 24 | Inherited field names use wrong prefix (child vs parent) | Inheritance |
| 25 | Box type includes unused field types | Datatype generation |
| 26 | Transitive ancestors missing in inheritance chain | Inheritance |
| 27 | Opaque proc heap detection: postconditions/modifies not checked | Heap detection |
| 28 | Opaque postconditions not qualified (field names) | Name qualification |
| 29 | Opaque body missing `$unused` init | Opaque procs |
| 30 | Single postcondition label: `postcondition_0` → `postcondition` | Labels |
| 31 | Instance call in if/while condition not qualified | Name qualification |
| 32 | `containsBareInstanceCallMd` false positive on if conditions | Heap detection |
| 33 | Preconditions use `$heap` instead of `$heap_in` for heap-writing procs | Heap threading |
| 34 | Precondition field names not qualified for instance procs | Name qualification |
| 35 | Function with `ensures` missing body (Opaque with impl) | Function translation |

### Bug Categories

The bugs cluster into clear categories:
- **Name qualification (7):** Instance calls, field names, inherited fields — the model
  didn't qualify names the same way the real translator does after resolution passes.
- **Heap detection (5):** The model's heap read/write analysis didn't match the real
  translator's `analyzeProc`. Instance calls, opaque postconditions, and if-condition
  expressions were missed.
- **Instance calls (4):** The function-vs-procedure distinction, argument ordering,
  and expression-position handling were all wrong initially.
- **Constrained types (4):** Type elimination, field read functions, and constraint
  preconditions needed careful modeling.
- **Opaque procs (3):** Body wrapping, postcondition qualification, and `$unused` init.
- **Labels (2):** Single vs multiple indexing for preconditions and postconditions.
- **Operators (2):** Missing cases in the binary operator translation.
- **Other (8):** Type erasure, module system, inheritance, function bodies.

## D7: Equivalence Proof Structure

### Main Theorem

```lean
theorem translate_eq_model (program : Program) (coreProgram : Core.Program)
    (h : (translate {} program).1 = some coreProgram) :
    stripMetaData (eraseTypes coreProgram) = translateProgramModel program
```

### 7-Category Decomposition

| Cat | Real segment | Model segment | Status |
|-----|-------------|---------------|--------|
| 1 | `[exceptionResultDecl]` | `[modelExceptionResultDecl]` | ✅ Proven |
| 2 | `groupedDatatypeDecls` | `infraDatatypes ++ datatypeDecls` | sorry |
| 3 | `mkReadFuncAxioms(prog)` | `modelReadFuncAxioms` | sorry |
| 4 | `constantDecls` | `ancestorDecls` | sorry |
| 5 | `pureFuncDecls` | `constraintFuncs ++ heapFuncs ++ extFuncs ++ transFuncs` | sorry |
| 6 | `procedures.map (.proc · .empty)` | `procDecls ++ witnessProcDecls` | sorry |
| 7 | `instanceProcedures.map (.proc · .empty)` | `instanceProcDecls` | sorry |

### Sorry Inventory

| File | Count | Notes |
|------|-------|-------|
| `LaurelToCoreTranslator.lean` | 3 | Main theorem + 2 cross-module |
| `TranslatorEquivalence.lean` | 1 | Assembly theorem |
| `TranslatorModel.lean` | 2 | `resolveInstanceCallInStmt_id`, TryCatch termination |

### When to Return to Proof

Criteria:
1. **Zero structural test failures** on hand-crafted tests (currently 9 gaps remain)
2. **Zero structural test failures** on JVerify's existing ~35 test programs
3. **Feature combinations tested** for every proof category's requirements

The 9 remaining gaps are straightforward to fix (missing operator cases, type names,
trigger handling). After fixing those and validating against the JVerify test suite,
the model should be stable enough for proof work.

## D8: Module System Lessons

The DDM `module` keyword makes all definitions private by default.
- `@[expose]` — body available for kernel reduction, name NOT exported
- `public` — name exported, body NOT available for reduction
- `@[expose] public` — both: needed for cross-module proofs

`unfold` works on `@[expose]` defs from other modules. `simp` needs equation lemmas
or `@[expose]` to unfold definitions.


## D9: TypeEnv for Real Arithmetic

**Date:** 2026-04-08

The real translator uses `computeExprType` (which queries a `SemanticModel` HashMap) to determine
whether arithmetic operands are `real` or `int`, selecting `Real.Add` vs `Int.Add` accordingly.

The model doesn't have a `SemanticModel`. Instead, we added a `TypeEnv` — a simple
`List (String × HighType)` built from procedure parameters and extended with local variable
types as the block is processed.

```lean
public abbrev TypeEnv := List (String × HighType)
public def exprIsReal (env : TypeEnv) : StmtExpr → Bool
```

`translateStmtModel` takes `TypeEnv` as a parameter (default `[]`). `translateProcModel`
builds the `TypeEnv` from `proc.inputs` and passes it. The `Block` case in `translateStmtModel`
extends the env with each `LocalVariable` declaration as it processes statements sequentially.

This is clean, pure, and provable. The equivalence proof precondition: "the TypeEnv agrees
with the SemanticModel on all variables in the body."

## D10: Constrained Type Resolution in the Model

**Date:** 2026-04-08

The real translator runs a `constrainedTypeElim` pass that:
1. Resolves constrained types to their base types (e.g., `nat` → `int`)
2. Injects constraint predicates into quantifier bodies (`forall(n: nat) => body` → `forall(n: int) => nat$constraint(n) ==> body`)
3. Adds constraint asserts after constrained local variable assignments
4. Adds constraint assumes for uninitialized constrained variables
5. Adds constraint postconditions for constrained output types
6. Chains parent constraints for nested constrained types (`posnat$constraint` includes `nat$constraint`)

The model replicates these as pure functions:
- `resolveConstrainedInExpr` — pre-processes the AST to inject constraints in quantifiers
- `resolveTypeName` — recursively resolves nested constrained types to base types
- `constrainedBaseTypes` parameter threaded through `translateStmtModel` for local var handling
- `constraintPostconds` in `translateProcModel` for output type constraints
- `resolveConstrainedTy` for function return types

All are pure functions over the AST and the constrained type map.

## D11: eraseTypes Equation Lemmas

**Date:** 2026-04-08

The `Lambda.LExpr.eraseTypes` function is `@[expose]` but had no exported equation lemmas.
This meant `simp` couldn't use it from other modules, blocking proofs.

**Decision:** Add `@[simp] public theorem eraseTypes_X` for every `LExpr` constructor
(const, op, fvar, bvar, abs, quant, all, app, ite, eq) in `Strata/DL/Lambda/LExpr.lean`.
Each is proven by `rfl`. These are pure facts about existing code — no executable changes.

The `eraseTypes_all` lemma is particularly important: `.all` is an abbreviation for
`.quant .all ... (noTrigger ()) ...`, and `simp` can't unfold abbreviations from other
modules. The explicit lemma bridges this gap.

These lemmas will be used by ALL 7 proof categories, not just Category 3.

## D12: Category 3 (ReadFuncAxioms) Proof — Complete

**Date:** 2026-04-08

**Theorem:** `mkReadFuncAxioms_strip_erase_eq` — when BoxInt is in the Box constructors,
`(mkReadFuncAxioms program).map (stripMetaData ∘ eraseTypes)` equals the model's axiom list.

**Proof technique:**
1. `unfold mkReadFuncAxioms; subst hFold; rfl` — eliminates the `let` binding by substituting
   the hypothesis, making both sides definitionally equal
2. `simp [hContains, List.filterMap, ↓reduceIte]` — evaluates the filterMap
3. `unfold Core.Decl.eraseTypes Core.Decl.stripMetaData Core.Axiom.eraseTypes` — strips Core wrappers
4. `simp [eraseTypes_all, eraseTypes_eq, eraseTypes_app, eraseTypes_op, eraseTypes_bvar]` — erases types
5. `rfl` — both sides syntactically identical

**Key insight:** `subst hFold; rfl` solves the `let`/`have` binding problem that blocked
earlier proof attempts. When `mkReadFuncAxioms` unfolds to `have boxConstrs := foldl ...; ...`,
`subst` eliminates the intermediate variable entirely.

**Status:** 0 sorry. Building block proven. Integration into `translate_decls_match` still
needs connecting the precondition (BoxInt exists) to the pipeline output.
