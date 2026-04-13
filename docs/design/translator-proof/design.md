# Translator Pipeline Proofs: Design

**Date:** 2026-04-10
**Status:** Proposed

## Overview

Prove structural properties of each pass in the Laurel→Core translate
pipeline. The properties serve as regression guarantees: when a new
feature (e.g., a new `StmtExpr` constructor) is added, Lean's
exhaustiveness checker forces every pass's proof to handle it. Code
that "looks complete but isn't" fails to compile.

```
                    Per-pass properties (Arrow 2)
                    ┌─────────────────────────────┐
Laurel Program ──→ │ resolve → constrained → heap │
                    │ → typeHier → modifies → LTC  │──→ Core Program
                    └─────────────────────────────┘
                                                          │
                                              Semantic properties (Arrow 3)
                                              ExitProperties.lean
                                              ExceptionProperties.lean
                                              PropagationProperties.lean
                                                          │
                                                          ▼
                                                    Core Semantics
```

Arrow 2 (this design) proves the pipeline produces Core with the right
structure. Arrow 3 (existing) proves Core with that structure has the
right semantics. Composed: Laurel features have correct Core semantics.

## Motivation

The translate pipeline has ~10 passes. When a new language feature is
added (e.g., TryCatch, instance methods, sequence types), each pass
must handle it. In practice, features have been added incompletely:

- Heap parameterization didn't track `InstanceCall` callees
- Name qualification missed instance calls in nested expressions
- Modifies clauses didn't iterate instance procedures
- Opaque procedures had multiple discrepancies
- Function postcondition axioms were never generated (real pipeline bug)

Differential testing between the translator model and the pipeline
surfaced many discrepancies. Most were model bugs (the model didn't
match the pipeline's correct behavior), but the process revealed
real architectural gaps — areas where the pipeline silently dropped
information. Testing is not exhaustive — it covers specific inputs,
not all inputs. Per-pass properties with exhaustive pattern matching
cover all inputs for the properties stated.

The key mechanism: when a property's proof pattern-matches on `StmtExpr`,
adding a new constructor to `StmtExpr` creates a new proof obligation.
The proof doesn't compile until the new case is handled. This is
automatic — no one needs to remember to update the proofs.

## Architecture

### Property files

Each pipeline pass gets a property file in the same directory:

| Pass file | Property file |
|-----------|--------------|
| `LaurelToCoreTranslator.lean` | `TranslatorProperties.lean` |
| `HeapParameterization.lean` | `HeapParameterizationProperties.lean` |
| `ConstrainedTypeElim.lean` | `ConstrainedTypeElimProperties.lean` |
| `Resolution.lean` | `ResolutionProperties.lean` |
| `ModifiesClauses.lean` | `ModifiesClausesProperties.lean` |
| `FunctionPostcondCheck.lean` | `TranslatorProperties.lean` (P-Spec-2f) |

Property files import the pass but do not modify it. They are new
files — zero risk to the existing pipeline.

### Equation lemmas

When a property needs to reason about a pass function's internals,
an equation lemma is added to the pass file. The equation lemma is
the contract between the pass and its properties (see D14 in
translator-model decisions, D4 in this doc's decisions).

```
-- In LaurelToCoreTranslator.lean (pass file):
theorem translateExpr_literalBool (b : Bool) :
    translateExpr ⟨.LiteralBool b, md⟩ = ... := by ...

-- In TranslatorProperties.lean (property file):
theorem bool_literal_always_translates (b : Bool) :
    (translateExpr ⟨.LiteralBool b, md⟩).isSome = true := by
  rw [translateExpr_literalBool]; ...
```

### Precondition chain

Each pass's postconditions are the next pass's preconditions:

```
resolve postcondition:    "all identifiers are resolved in SemanticModel"
    ↓ (= constrainedTypeElim precondition)
constrainedTypeElim post: "all constrained types resolved to base types"
    ↓ (= heapParam precondition)
heapParam postcondition:  "$heap injected for all heap-accessing procs"
    ↓ (= translateLaurelToCore precondition)
translateLTC postcondition: "Core AST has correct structure"
    ↓ (= semantic proof precondition)
ExitProperties / ExceptionProperties: "Core semantics are correct"
```

Initially these are explicit hypotheses on each property. As patterns
emerge, they'll be factored into named predicates (see D5).

## Property Tiers

### Tier 1: Structural Integrity

Cheap to prove, catch the broadest class of regressions.

**P-Struct-1: Declaration completeness.** Every Laurel procedure
produces a Core procedure. Every composite produces Core datatypes.
Nothing is silently dropped.

**P-Struct-2: Signature preservation.** Input count, output count,
and parameter names are preserved through translation (modulo heap
parameters `$heap`, `$heap_in`, `$result`).

**P-Struct-3: Spec preservation.** Every Laurel `requires` appears
as a Core `requires`. Every Laurel `ensures` appears as a Core
`ensures`.

### Tier 2: Feature-Specific Translation

Target the feature areas where bugs cluster.

**P-Heap-1: Heap parameter injection. ✅ PROVEN.** If a procedure has field
access, instance calls, or opaque modifies, it gets `$heap` as
input. If it writes heap, it gets `$heap` as output. Catches the
heap detection discrepancy cluster.

**P-Heap-2: Field read translation.** Field reads for constrained
types use the correct Factory read function (`readInt32` for `int32`
fields, `Box..intVal!` for `int` fields). Validates the
constrained-types-in-heap architecture.

**P-Name-1: Instance call qualification.** Instance calls translate
to Core calls with qualified names (`TypeName..callee`). Catches
the name qualification discrepancy cluster.

**P-Name-2: Field name qualification.** In instance procedures,
field accesses use the declaring type's prefix. Inherited fields
use the parent type's prefix.

**P-Name-3: Instance call expression translation correctness.**
When `translateExpr` handles an `InstanceCall` where the callee
resolves to a non-functional instance procedure (`proc.isFunctional
= false`), the translation must NOT generate `.op` (function
application) — non-functional procedures are not registered in
`C.functions` and the Core type checker will reject them. The
translator must either lift the call to statement position or
handle it as a `Core.Statement.call`. This catches the bug where
`sum() + sum()` in expression position generates an unresolvable
`.op` for a heap-reading procedure.

**P-Constrained-1: Constraint precondition injection. ✅ PROVEN.** Constrained-
type parameters get `requires constraint$check(param)` in the Core
output.

**P-Exception-1: Throw translation.** `Throw(e)` produces
`$result := Failure(e'); exit <target>` where `<target>` is the
current exception target (D7 in exception decisions). Designed to
compose with E1 (exit preserves store) and E2 (exit skips remaining).

**P-Exception-2: TryCatch structure.** `TryCatch(body, catches, finally)`
produces the labeled block pattern with correct labels and catch
dispatch order. Designed to compose with E3 (matching block consumes)
and E4 (non-matching exit propagates).

**P-Opaque-1: Opaque procedure handling.** Opaque procedures get
`$unused` init wrapping. Opaque procedures with implementations get
the body translated. Postconditions are qualified for instance procs.

**P-Exception-3: Exception propagation in procedure calls.** When
`translateStmt` translates a `StaticCall` to a non-function procedure,
the generated `Core.Statement.call` includes `$result` in its LHS
list. This ensures the caller can detect callee exceptions. The model
proves this as `static_proc_call_has_propagation` and
`instance_proc_call_has_propagation`. Designed to compose with P5
(exception propagation) and P9/P10 (cross-method propagation) in
`ExceptionProperties.lean`. See D20.

**P-Call-1: mkCallWithResult always includes $result. ✅ PROVEN.**
`mkCallWithResult lhs callee args md` always produces a call statement
whose LHS is `lhs ++ [⟨"$result", ()⟩]`. This is the formal proof
backing P-Exception-3: since every non-functional call goes through
`mkCallWithResult`, `$result` is always present. Prevents regression
of the missing-$result bug that caused "output length and lhs length
mismatch" in the inliner. Proven by `simp` on the monadic definitions.
File: `InstanceMethodProperties.lean`.

**P-Call-2: Instance call argument order (D14). ✅ PROVEN.**
When an instance call has heap arguments (`coreArgs` is non-empty
after heap parameterization), the argument reordering puts the heap
argument first: `[heapArg, coreTarget, ...rest]`, not
`[coreTarget, heapArg, ...rest]`. This matches the procedure's input
order `[$heap, self, ...params]` established by heap parameterization.
Prevents regression of the D14 argument order bug. Proven by `rfl`.
File: `InstanceMethodProperties.lean`.

**P-Call-3: Call LHS arity. ✅ PROVEN.**
`mkCallWithResult` with a `lhs` of length N produces a call whose
LHS has length N + 1 (the extra element is `$result`). Since
`translateProcedure` produces outputs of length
`proc.outputs.length + 1` (P-output-count), the arity matches when
`lhs.length = proc.outputs.length`. This is the composition that
prevents the "output length and lhs length mismatch" error in the
inliner. File: `InstanceMethodProperties.lean`.

**P-Frame-1: Frame condition generation.** If a procedure has `$heap`
output, `modifiesClausesTransform` generates a frame condition. If
the procedure has explicit `modifies` clauses, the frame is partial
(only modified fields may change). If no `modifies`, the frame is
full (all fields preserved). The model proves this as
`heap_output_implies_frame`, `modifies_implies_partial_frame`, and
`no_heap_no_frame`. See D21.

**P-Identity-1: Pass non-interference.** When a feature isn't used,
the corresponding pass is a no-op. Specifically: if a procedure has
no instance calls, instance call resolution is the identity; if there
are no constrained types, constrained type elimination is the identity;
if there are no fields to qualify, field qualification is the identity.
The model proves these as `resolveInstanceCallInStmt_id`,
`resolveConstrainedInExpr_nil`, and `qualifyFieldNamesInExpr_nil`.
Valuable for Tier 3 composition — lets you skip passes in the proof
chain when the feature isn't relevant. See D21.

### Tier 3: Compositional

Catch interaction bugs between features. May be proven by composing
Tier 2 properties rather than stated independently.

**P-Compose-1: Instance call in expression position.** Instance calls
inside `if`/`while` conditions are qualified AND get heap parameters.
Intersection of P-Name-1 and P-Heap-1.

**P-Compose-2: Opaque + instance + heap.** Opaque instance procedure
postconditions are qualified AND heap analysis checks postconditions
for heap access. Intersection of P-Opaque-1, P-Name-1, P-Heap-1.

**P-Compose-3: Constrained types through full pipeline.** A
constrained-type field write goes through heap parameterization
(BoxInt wrapping), constrained type elimination (constraint assert),
and translation (readInt32 on read-back). Validates the layered
architecture end-to-end.

### Tier 4: Specification Preservation

Target the class of issues that prevent using JVerify to verify
JVerify — specifically, ensures clauses not being available where
they should be. These issues blocked the self-verification work
(Position.compareTo, Range.compareTo) and affect any user who
writes specifications involving instance methods, opaque
procedures, or functions with postconditions. Also motivated by
the "composite with instance methods breaks field reasoning"
Strata bug.

The function postcondition axiom gap (motivating P-Spec-2f) was
found when verifying Position.compareTo with `Long.compare`. The
`feat/function-postconditions` merge added `FunctionPostcondCheck`
(checking direction: does the body satisfy postconditions?) but
not the axiom generation (availability direction: can callers
assume postconditions?). The translator's `translateProcedureToFunction`
silently dropped postconditions because `Core.Function.axioms`
was never populated.

**P-Spec-1: Ensures clause preservation.** When a procedure has
`ensures P`, the Core output contains `P` as a postcondition.
Catches the "postcondition silently dropped" class.

**P-Spec-2: Opaque procedure postcondition availability.** When
a procedure is opaque (has `ensures` but the body is hidden), the
Core output has the postcondition as an axiom that callers can
use. This covers the `translateProcedure` → `Core.Decl.proc` path
where postconditions go into `spec.postconditions`.

**P-Spec-2f: Function postcondition axiom generation. ✅ PROVEN.** When a
function (`isFunctional = true`) has `ensures` clauses, the
translated `Core.Function` has `axioms` whose count equals the
postcondition count, and each axiom is a universally quantified
formula with `result` replaced by `f(params...)`. This covers
the `translateProcedureToFunction` → `Core.Decl.func` path
where postconditions must go into `func.axioms`. The translator
has two separate code paths for postcondition availability:
procedures use `spec.postconditions`, functions use
`func.axioms`. P-Spec-2 and P-Spec-2f together ensure both
paths preserve postconditions. See D18 in decisions.

**P-Spec-3: Instance method postconditions are qualified.** When
an instance method has `ensures self#count == old(self#count) + 1`,
the Core postcondition uses the qualified field name
`TypeName..count`. Catches postconditions and preconditions not
being qualified for instance procs.

**P-Spec-4: Cross-method ensures propagation.** When procedure A
calls procedure B with `ensures P`, the call site in A's Core
output asserts `P` (substituted with actual arguments). This is
the property that would catch the "can't use callee's
postcondition" problem hit with Range.compareTo →
Position.compareTo.

**P-Heap-3: Heap consistency for composites with instance methods. ⚠️ PARTIAL.**
Adding an instance method to a composite does not change the heap
analysis for unrelated static procedures. `analyzeProc` non-
interference proven (4 theorems). Fixpoint monotonicity deferred
(D22).

## Bug Mapping

## Discrepancy Categories

Differential testing between the translator model and the pipeline
surfaced discrepancies in these categories. Most were model bugs
(the model didn't match the pipeline's correct behavior), not
pipeline bugs. The categories are useful for understanding where
the pipeline is complex and where proofs add the most value:

| Category | Proof Coverage |
|----------|---------------|
| Name qualification | P-Name-1 ✅, P-Name-2 ✅ |
| Heap detection | P-Heap-1 ✅, P-Heap-3 ✅ (analyzeProc non-interference) |
| Instance calls | P-Name-1 ✅, IM1 ✅, P-Call-1 ✅, P-Call-2 ✅, P-Call-3 ✅ |
| Constrained types | Infra ✅, P-Constrained-1 ✅ (preconditions + output ensures) |
| Opaque procs | P-Spec-1/2 needed |
| Function postconditions | P-Spec-2f ✅ |
| Labels | Not yet targeted |
| Operators | P-Struct-1 partial |
| Statement translation | P-Exception-1 unblocked (D19), P-Exception-2 unblocked (D19) |
| Exception propagation | P-Exception-3 needed (D20) — model has properties to port |
| Frame conditions | Needed — model has `heap_output_implies_frame` etc. (D21) |
| Fixpoint monotonicity | P-Heap-3 partial, completion deferred (D22) |

The one confirmed real pipeline bug — function postcondition axioms
not being generated — was found during self-verification work, not
by differential testing. The proofs serve a different purpose than
testing: they confirm structural correctness and prevent regressions.
When someone changes the Throw translation, the equation lemma
stops compiling. When someone changes instance call argument order,
P-Name-1 breaks. The differential tests find discrepancies on
specific inputs; the proofs guarantee properties on ALL inputs.

## Relationship to Existing Work

### Translator model (deprecating)

The model (`TranslatorModel.lean`) and equivalence proofs
(`TranslatorEquivalence.lean`) are superseded by this approach.
The differential tests (`TranslatorModelTest.lean`) are kept as
discrepancy-finding tools. See D1, D2 in decisions.

### TranslatorModelProperties.lean (migrating)

The existing properties file proves facts about the model's helper
functions (`expectedDeclNames`, `translateExprTop`, etc.). These
properties guided the design of the tiers above. As pipeline
properties are proven, the model properties become redundant.

Properties to migrate:
- P1 (declaration completeness) → P-Struct-1
- P2 (type consistency) → standalone, already proven
- P3 (partition completeness) → standalone, already proven
- P4 (heap threading) → P-Heap-1
- P5 (instance call qualification) → P-Name-1
- P6 (exception propagation) → P-Exception-1, P-Exception-2

### InstanceMethodProperties.lean (keeping)

The `instance_call_name_consistency` theorem (IM1) is already a
direct pipeline property — it proves a fact about
`resolveInstanceCallName` and `instanceProcCoreName`, which are
real pipeline functions. This is the pattern we're scaling up.

### ExitProperties.lean, ExceptionProperties.lean (composing with)

These are Arrow 3 proofs. The translator properties (Arrow 2) are
designed to compose with them. See D7 in decisions.

## Implementation Plan

### Phase 1: Foundation ✅ COMPLETE

1. Created `TranslatorProperties.lean` with 49 Tier 1/2 properties:
   P-Struct-1 (expression/statement translation succeeds for 21
   constructors), P-Struct-1c (state preservation for 4 literals),
   P-Struct-1d (5 statement properties), P-Struct-2 (5 procedure
   signature properties: name, input count, output count, $result
   output, Success init).
2. Equation lemmas already existed in `LaurelToCoreTranslator.lean`
   (~30 lemmas). Added `@[expose]` to `Body.isExternal` in
   `Laurel.lean`.
3. Validated: `lake build` passes, zero sorry in property files.

### Phase 1b: Heap properties ✅ COMPLETE

4. Created `HeapParameterizationProperties.lean` with 19 P-Heap-1
   properties: heap writer input/output injection (4), heap reader
   input injection + output preservation (2), non-heap identity (3),
   naming consistency (1), plus additional heap threading properties.
5. Infrastructure lemmas in `ConstrainedTypeElim.lean` (6 lemmas,
   zero sorry): isFunctional/isExternal preservation for
   mkConstraintFunc, mkWitnessProc, elimProc.

### Phase 2: Feature-specific properties ✅ COMPLETE

6. P-Constrained-1: constraint precondition injection and output
   ensures preservation in `ConstrainedTypeElim.lean` (14 lemmas).
7. P-Heap-2: FieldSelect → StaticCall elimination components in
   `HeapParameterizationProperties.lean`.
8. P-Heap-3: analyzeProc non-interference (depends only on body
   and preconditions, independent of name/isFunctional) in
   `HeapParameterization.lean` (4 theorems).
9. P-Spec-2f: function postcondition axiom count preservation in
   `TranslatorProperties.lean`.
10. P-Name-2: resolveQualifiedFieldName in
    `InstanceMethodProperties.lean`.

### Phase 2b: Exception restoration ✅ COMPLETE (D19)

11. Restored `.Throw` and `.TryCatch` cases in `translateStmt`
    (lost during merge 07a22e38).
12. Restored `exceptionTarget` in `TranslateState`, `$result`
    output in `translateProcedure`, `ExceptionResult` datatype.
13. Updated equation lemmas and properties for `$result` output.
14. T18_Throw tests all pass.

### Phase 3: Exception properties (NEXT — see D10, D19, D20)

15. Add equation lemma for `translateStmt` on `.Throw`.
16. Add P-Exception-1 (throw translation) to
    `TranslatorProperties.lean`: output is
    `[$result := Failure(), exit <target>]`.
17. Prove composition with E1–E6 from `ExitProperties.lean`.
    This is the first end-to-end Arrow 2 + Arrow 3 proof.
18. Add P-Exception-2 (TryCatch structure): nested labeled blocks
    with correct labels and catch dispatch order.
19. Add P-Exception-3 (D20): procedure calls include `$result`
    in call LHS for exception propagation.

### Phase 4: Frame conditions and specification preservation (see D12, D15, D21)

20. Add P-Spec-1 (ensures clause preservation for opaque procs).
21. Port model frame condition properties to pipeline:
    `heap_output_implies_frame`, `modifies_implies_partial_frame`,
    `no_heap_no_frame` → properties on `ModifiesClauses.lean`.
22. Add P-Struct-2+ (precondition/postcondition count preservation).
23. Prove Tier 3 compositional properties as needed.

### Phase 5: Identity properties and fixpoint (see D21, D22)

24. Port model identity properties: `resolveInstanceCallInStmt_id`,
    `resolveConstrainedInExpr_nil`, `qualifyFieldNamesInExpr_nil`
    → non-interference guarantees on real passes.
25. Establish `BEq.Equiv` for `Identifier`.
26. Prove fixpoint monotonicity for `computeReadsHeap` /
    `computeWritesHeap` (P-Heap-3 completion).
27. Migrate remaining model properties, deprecate model files.

### Current status (2026-04-11)

| File | Theorems | Sorry |
|------|----------|-------|
| `TranslatorProperties.lean` | 46 | 0 |
| `TranslatorEqLemmas.lean` | 30 | 0 |
| `HeapParameterizationProperties.lean` | 17 | 0 |
| `HeapParameterization.lean` (P-Heap-3) | 11 | 0 |
| `ConstrainedTypeElim.lean` (infra) | 14 | 0 |
| `InstanceMethodProperties.lean` (pre-existing) | 1 | 0 |
| `ExitProperties.lean` (Arrow 3) | 10 | 0 |
| `ExceptionProperties.lean` (Arrow 3) | 16 | 0 |
| `PropagationProperties.lean` (Arrow 3) | 5 | 0 |
| **Total** | **150** | **0** |

Note: Arrow 3 proofs (ExitProperties, ExceptionProperties,
PropagationProperties) are semantic proofs about Core constructs.
They compose with Arrow 2 (translator) proofs for end-to-end
guarantees. The first composition target is P-Exception-1 (D19).

### Test coverage analysis (2026-04-11)

| Test area | Tests | Proof coverage |
|-----------|-------|---------------|
| Literals, arithmetic, boolean | T1, T12 | ✅ Full |
| Control flow (if/else, while) | T3, T4, T13 | ✅ Full |
| Procedure calls, signatures | T5, T6, T8 | ⚠️ Partial (no preconditions) |
| Heap parameters | T1_Mutable, T2_Modifies | ✅ P-Heap-1 |
| Field read/write | T1_Mutable, T8_Immutable | ⚠️ P-Heap-2 partial (FieldSelect components) |
| Instance methods | T7, T9, T10 | ✅ IM1 (naming), P-Name-2 (field qualification) |
| Exceptions | T18 | ⚠️ Unblocked (D19), equation lemmas needed |
| Constrained types | T10_Constrained | ✅ P-Constrained-1 (preconditions + output ensures) |
| Inheritance | T5_inheritance | ❌ No properties |
| Quantifiers | T14 | ❌ No properties |
| Function postconditions | Position.compareTo | ✅ P-Spec-2f |

### Success criteria

- Every `StmtExpr` constructor is covered by at least one
  per-pass property (exhaustiveness guarantee).
- Zero `sorry` in property files (CI-enforced).
- At least one composed Arrow 2 + Arrow 3 proof (exceptions).
