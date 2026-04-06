# Translator Functional Model: Decisions

**Date:** 2026-03-31
**Status:** Design

## D1: Why a functional model?

The `translate` function in `LaurelToCoreTranslator.lean` is the
trust boundary between Laurel and Core. It orchestrates ~10 passes
(resolution, heap parameterization, modifies clauses, constrained
type elimination, etc.) and produces a Core program. If it produces
wrong Core, the prover accepts false things.

The function is ~850 lines of imperative Lean with monadic state,
error accumulation, and HashMap lookups. Bugs we found during
record support and instance call work:

1. `isFunction` didn't handle `.instanceProcedure` — instance
   calls dispatched to the wrong Core construct
2. Instance call grammar (`..`) conflicted with the identifier
   tokenizer — calls parsed as dotted identifiers
3. Heap parameterization didn't propagate heap access through
   instance calls from Laurel source
4. `translateProcedureToFunction` can't handle postconditions
   or return statements — instance functions silently broken
5. Generated `equals` function on records broke static method
   postconditions by its mere presence

These are all bugs in the unproven layer. The proven layer
(Core evaluation, P1-P12) is sound. The translation is not.

**Decision:** Write a pure functional model of `translate` that:
- Is executable (runs on real inputs, produces Core programs)
- Is provably correct (Lean theorems about its properties)
- Serves as the definition of "correct" when it disagrees with
  `translate`

## D2: Scope — model the entire `translate` function

The `translate` function owns the full pipeline:

```
resolve → heapParameterization → resolve → typeHierarchyTransform →
resolve → modifiesClausesTransform → resolve → ... →
constrainedTypeElim → resolve → translateLaurelToCore
```

The model takes the same input (raw Laurel `Program`) and produces
the same output (Core `Program`). The intermediate passes are
internal implementation details — the model doesn't need to mirror
them. It describes the end-to-end transformation directly.

**Decision:** Model the full `translate` function, not individual
passes. The model is a pure function:

```lean
def translateModel (program : Program) : Core.Program
```

When `translate` and `translateModel` disagree on an input, we
ask "who is right?" The model wins — we fix `translate`. If the
model is wrong, we fix the model and update the proofs.

## D3: The model is executable

The model is a regular Lean `def`, not an abstract specification.
It can be `#eval`'d on real inputs. This gives us:

1. **Differential testing:** Run both `translate` and
   `translateModel` on every test input. Assert outputs match.
   Catches bugs without proofs.
2. **No vacuous specs:** If the model produces wrong output,
   differential testing catches it. You can't accidentally
   write a spec that's satisfied by wrong code.
3. **Incremental adoption:** Start with differential testing
   (immediate value), add proofs later (long-term value).

**Decision:** The model must be executable. No `sorry`, no
`axiom`, no `noncomputable` in the model itself. Proofs about
the model may use `sorry` during development.

## D4: Properties to prove about the model

### P1: Name consistency

Every name referenced in a Core procedure body (via `call` or
function application) exists as a declaration in the Core program.

```lean
theorem name_consistency (L : Program) :
  let C := translateModel L
  ∀ name ∈ referencedNames C, name ∈ declaredNames C
```

This catches: missing instance procedure declarations, wrong
qualified names, call/definition name mismatches.

### P2: Type consistency

Every Core declaration's parameter types are well-formed. Every
composite parameter is typed as `Composite` in Core (not the
Laurel type name). Every constrained type parameter is typed as
its base type.

```lean
theorem type_consistency (L : Program) :
  let C := translateModel L
  ∀ decl ∈ C.decls, wellTypedDecl C decl
```

This catches: `Box` vs `Composite` type mismatches, constrained
types not eliminated, wrong return types on functions.

### P3: Completeness

Every Laurel procedure (static and instance) produces exactly
one Core declaration. No procedures silently dropped. No
duplicates.

```lean
theorem completeness (L : Program) :
  let C := translateModel L
  ∀ proc ∈ allProcedures L, ∃! decl ∈ C.decls, correspondsTo decl proc
```

This catches: instance procedures not translated, functional
procedures dropped by partitioning, external procedures
accidentally included.

### P4: Heap threading

Every procedure that transitively accesses the heap has `$heap`
in its Core input parameters. Every procedure that writes the
heap has `$heap` in its Core output parameters.

```lean
theorem heap_threading (L : Program) :
  let C := translateModel L
  ∀ proc ∈ heapAccessingProcedures L,
    "$heap_in" ∈ inputNames (coreDecl C proc) ∧
    "$heap" ∈ outputNames (coreDecl C proc)
```

This catches: heap parameterization not propagating through
instance calls, missing `$heap` on transitively heap-accessing
procedures.

### P5: Instance call qualification

Every instance call to procedure `P` on composite `T` becomes
a Core call to `T..P`. The qualified name at the call site
matches the qualified name on the declaration.

```lean
theorem instance_call_qualification (L : Program) :
  let C := translateModel L
  ∀ (call : InstanceCall) ∈ instanceCalls L,
    coreName C call = instanceProcCoreName call.typeName call.procName
```

This is the generalization of IM1. IM1 proves it for the name
function in isolation. This proves it for the full pipeline.

### P6: Exception propagation

Every procedure call in a Core body is followed by an exception
propagation check. If the callee's `$result` is `Failure`, the
caller's `$result` is set to `Failure` and control exits.

```lean
theorem exception_propagation (L : Program) :
  let C := translateModel L
  ∀ (call : CoreCall) ∈ procedureCalls C,
    followedByPropagationCheck call
```

This catches: missing propagation after instance calls, missing
propagation after static calls in certain code paths.

### P7: Frame conditions

`modifies(x)` produces a frame condition: for every object NOT
in the modifies set, all fields are unchanged between `$heap_in`
and `$heap`. If this is wrong, postconditions can be vacuously
true.

```lean
theorem frame_conditions (L : Program) :
  let C := translateModel L
  ∀ proc ∈ proceduresWithModifies L,
    hasCorrectFrameCondition C proc
```

This is the most important soundness property. A wrong frame
condition means the prover can assume things that aren't true.

## D5: Equivalence proof structure

The ultimate goal is:

```lean
theorem translate_correct (L : Program)
  (h : wellFormed L) :
  translate L = translateModel L
```

This transfers all properties (P1-P7) from the model to the
real code. The `wellFormed` precondition captures what the
passes guarantee about the input.

This proof is the hard part and can come last. The model and
its properties (D4) give value independently.

## Open Questions

### Q1: What defines "valid" input? — Answered

The translator produces three kinds of errors:
- **NotYetImplemented** (13 cases) — unsupported features
- **StrataBug** (8 cases) — upstream pass invariant violations
- **UserError** (3 cases) — malformed user code

"Valid input" = uses only supported Laurel features. This is
defined by which `StmtExpr` variants the model handles. Lean's
exhaustive pattern matching enforces this — the model must have
a case for every variant it supports, and the `valid` predicate
is the union of those cases.

StrataBug errors can't arise in the model because the model
transforms directly (no upstream passes to violate invariants).

### Q2: How to handle the generated datatypes? — Answered

The datatypes are generated declaratively from the program's
structure:
- `TypeTag`: one constructor per composite type
- `Field`: one constructor per field across all composites
- `Box`: one constructor per distinct field base type
  (BoxInt for int fields, BoxBool for bool, BoxSequenceInt
  for Sequence int, etc.)
- `Composite`: always MkComposite(ref: int, typeTag: TypeTag)
- `Heap`: always MkHeap(data: Map Composite (Map Field Box),
  nextReference: int)
- `ExceptionResult`: always Success | Failure

The model describes this as a pure function over the program's
type definitions. No state accumulation needed.

### Q3: Passes vs end-to-end — Deferred

Model the end-to-end transformation. Don't model individual
passes. Differential testing localizes bugs when needed.

### Q4: New features — Not a concern

New Java features (break/continue, switch, etc.) are desugared
by JVerify into existing Laurel constructs (exit + labeled
blocks, if/else chains). The Laurel AST is relatively stable.
New Laurel AST nodes are rare. When they do occur, Lean's
exhaustive pattern matching forces the model to be updated.


## D6: Equivalence Proof Plan (Phase 2)

**Date:** 2026-04-06
**Status:** In Progress

### Current State

The main theorem is:
```lean
theorem translate_eq_model (program : Program) (coreProgram : Core.Program)
    (h : (translate {} program).1 = some coreProgram) :
    stripMetaData (eraseTypes coreProgram) = translateProgramModel program
```

The proof is structured: unfold `translate`, split on error flag, dismiss contradiction.
The remaining goal: show the Core decl lists match.

### Decl List Alignment

Real translator (`translateLaurelToCore` on post-pipeline program):
```
[exceptionResultDecl] ++ groupedDatatypeDecls ++ readFuncAxioms ++
constantDecls ++ pureFuncDecls ++ procDecls ++ instanceProcDecls
```

Model (`translateProgramModel` on original program):
```
[exceptionResultDecl] ++ infraDatatypes ++ datatypeDecls ++ readFuncAxioms ++
ancestorDecls ++ constraintFuncDecls ++ heapFuncDecls ++
externalFuncDecls ++ transparentFuncDecls ++
procDecls ++ witnessProcDecls ++ instanceProcDecls
```

### Key Insight

The pipeline passes ADD procedures/types to the program before `translateLaurelToCore` runs:
- `heapParameterization` adds heap read/write functions → model's `heapFuncDecls`
- `typeHierarchyTransform` adds ancestor functions → model's `ancestorDecls`
- `constrainedTypeElim` adds constraint functions + witness procs → model's `constraintFuncDecls` + `witnessProcDecls`
- `coreDefinitionsForLaurel` adds external function stubs → model's `externalFuncDecls`

So the real translator's `pureFuncDecls` (all isFunctional procs) includes the pass-added
functions. The model generates them directly.

### Sub-lemmas Needed (ordered by dependency)

#### Category 1: ExceptionResult (trivial)
Both hardcode the same ExceptionResult datatype. Should be `rfl` after normalization.

#### Category 2: Datatypes (medium)
Real: `translateTypes program model` produces grouped datatype decls.
Model: `infraDatatypes ++ datatypeDecls` computed directly from program types.
Need: `translateTypes` equivalence lemma.

#### Category 3: Read Function Axioms (easy)
Both conditional on Box constructors existing. Same logic, different code paths.
Need: show both produce the same axiom list.

#### Category 4: Functions — ancestor, constraint, heap, external, transparent (hard)
Real: pipeline passes add these as `isFunctional` procedures, then `translateProcedureToFunction`
translates them to Core functions.
Model: generates Core function decls directly.
Need: for each category, show the pass-added procedure, when translated by
`translateProcedureToFunction`, produces the same Core function as the model.

This is the hardest part. Each pass (heapParameterization, typeHierarchyTransform,
constrainedTypeElim) adds specific procedures with specific bodies. The model
generates the equivalent Core directly. The proof must show these match.

#### Category 5: Procedures (medium, partially done)
Real: `procProcs.mapM translateProcedure` wrapped in `Core.Decl.proc`.
Model: `procProcs.map (translateProcModel isFunc compositeNames)`.
Need: generalize `translateProcedure_matches_model` to handle all procedure types
(heap access, instance calls, preconditions, opaque bodies, non-basic types).
Then lift to list level.

#### Category 6: Instance Procedures (medium)
Same as Category 5 but with qualified names from composite types.
Need: show instance procedure name qualification matches between real and model.

#### Category 7: Constants (easy)
Real: `program.constants.mapM` translates constants to 0-ary functions.
Model: should have equivalent logic (or constants are empty in test programs).

### Proof Strategy

1. Prove Categories 1, 3, 7 first (easy wins)
2. Prove Category 5 by generalizing `translateProcedure_matches_model`
   - Add heap parameter support
   - Add precondition/postcondition support
   - Add non-basic type support
   - Lift to list level
3. Prove Category 6 (extends Category 5 with name qualification)
4. Prove Category 2 (datatype equivalence)
5. Prove Category 4 (function equivalence — hardest, depends on pass analysis)
6. Assemble all categories into the main theorem
