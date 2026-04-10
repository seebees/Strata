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

**P-Heap-1: Heap parameter injection.** If a procedure has field
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

**P-Constrained-1: Constraint precondition injection.** Constrained-
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

**P-Spec-2f: Function postcondition axiom generation.** When a
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

**P-Heap-3: Heap consistency for composites with instance methods.**
Adding an instance method to a composite does not change the heap
analysis for unrelated static procedures. Catches the "ANY instance
method on a composite breaks field reasoning" Strata bug.

## Bug Mapping

## Discrepancy Categories

Differential testing between the translator model and the pipeline
surfaced discrepancies in these categories. Most were model bugs
(the model didn't match the pipeline's correct behavior), not
pipeline bugs. The categories are useful for understanding where
the pipeline is complex and where proofs add the most value:

| Category | Proof Coverage |
|----------|---------------|
| Name qualification | P-Name-1 ✅, P-Name-2 needed |
| Heap detection | P-Heap-1 ✅, P-Heap-3 needed |
| Instance calls | P-Name-1 ✅, IM1 ✅ |
| Constrained types | Infra ✅, P-Constrained-1 needed |
| Opaque procs | P-Spec-1/2 needed |
| Function postconditions | P-Spec-2f needed |
| Labels | Not yet targeted |
| Operators | P-Struct-1 partial |
| Statement translation | P-Exception-1 ✅ |

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

### Phase 2: Instance calls and field access (next — see D9, D11)

6. Add equation lemma for `translateExpr` on `InstanceCall` to
   `LaurelToCoreTranslator.lean`.
7. Add P-Name-1 (instance call qualification) to
   `TranslatorProperties.lean`.
8. Add equation lemma for `heapTransformExpr` on `FieldSelect` to
   `HeapParameterization.lean`.
9. Add P-Heap-2 (field read translation) to
   `HeapParameterizationProperties.lean`.

### Phase 3: Exceptions (see D10)

10. Add equation lemma for `translateStmt` on `Throw`.
11. Add P-Exception-1 (throw translation) to
    `TranslatorProperties.lean`.
12. Prove composition with E1–E6 from `ExitProperties.lean`.
    This is the first end-to-end result: Laurel Throw → Core exit
    → correct semantics.
13. Add P-Exception-2 (TryCatch structure) in a later phase.

### Phase 4: Preconditions, constrained types, composition (see D12, D13)

14. Add P-Struct-2+ (precondition/postcondition count preservation).
15. Add P-Constrained-1 (constraint injection on inputs).
16. Prove Tier 3 compositional properties as needed.
17. Migrate remaining model properties, deprecate model files.

### Phase 5: Function postcondition axioms (see D18)

18. Add equation lemma for `translateProcedureToFunction` axiom
    generation in `LaurelToCoreTranslator.lean`.
19. Add P-Spec-2f (function postcondition axiom count preservation)
    to `TranslatorProperties.lean`.
20. Add exhaustive `Body` variant match property (D18 Option C)
    to ensure new body variants get axiom handling.

### Current status (2026-04-10)

| File | Theorems | Sorry |
|------|----------|-------|
| `TranslatorProperties.lean` | 49 | 0 |
| `HeapParameterizationProperties.lean` | 19 | 0 |
| `ConstrainedTypeElim.lean` (infra) | 6 | 0 |
| `InstanceMethodProperties.lean` (pre-existing) | 1 | 0 |
| `FunctionPostcondCheck.lean` | 0 | 0 |
| **Total** | **75** | **0** |

Note: `FunctionPostcondCheck.lean` has the pass implementation
but no properties yet. P-Spec-2f properties will go in a new
`FunctionPostcondProperties.lean` or in `TranslatorProperties.lean`
(see D18 in decisions).

### Test coverage analysis (2026-04-10)

| Test area | Tests | Proof coverage |
|-----------|-------|---------------|
| Literals, arithmetic, boolean | T1, T12 | ✅ Full |
| Control flow (if/else, while) | T3, T4, T13 | ✅ Full |
| Procedure calls, signatures | T5, T6, T8 | ⚠️ Partial (no preconditions) |
| Heap parameters | T1_Mutable, T2_Modifies | ✅ P-Heap-1 |
| Field read/write | T1_Mutable, T8_Immutable | ❌ No P-Heap-2 |
| Instance methods | T7, T9, T10 | ❌ No P-Name-1 |
| Exceptions | T18 | ❌ No P-Exception-1/2 |
| Constrained types | T10_Constrained | ❌ No P-Constrained-1 |
| Inheritance | T5_inheritance | ❌ No properties |
| Quantifiers | T14 | ❌ No properties |
| Function postconditions | Position.compareTo | ❌ No P-Spec-2f |

### Success criteria

- Every `StmtExpr` constructor is covered by at least one
  per-pass property (exhaustiveness guarantee).
- Zero `sorry` in property files (CI-enforced).
- At least one composed Arrow 2 + Arrow 3 proof (exceptions).
