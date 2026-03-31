# Translator Functional Model: Design

**Date:** 2026-03-31
**Status:** Design

## Overview

A pure functional model of the `translate` function that serves
as the definition of correct Laurel→Core translation. The model
is executable (differential testing) and provable (Lean theorems).

## Architecture

```
Laurel Program ──→ translateModel ──→ Core Program
                        │
                   (pure function,
                    no state monad,
                    no error handling)

Laurel Program ──→ translate ──→ Core Program
                        │
                   (imperative,
                    state monad,
                    10+ passes)
```

Both take the same input and should produce the same output.
When they disagree, the model defines what's correct.

## Model Structure

The model is organized by the Core declarations it produces.
For a given Laurel program, the Core program contains:

### 1. Datatype declarations

Generated from the Laurel program's composites and field types:

- `ExceptionResult` — always present (Success | Failure)
- `TypeTag` — one constructor per composite type
- `Field` — one constructor per field across all composites
- `Composite` — always `MkComposite(ref: int, typeTag: TypeTag)`
- `Box` — one constructor per distinct field base type
- `Heap` — always `MkHeap(data: Map Composite (Map Field Box), nextReference: int)`

```lean
def modelDatatypes (program : Program) : List Core.Decl := ...
```

### 2. Function declarations

- `readField`, `updateField`, `increment` — heap operations
- `ancestorsForT` — one per composite type T
- `ancestorsPerType` — maps TypeTag to ancestor map
- `int8$constraint`, ..., `nat32$constraint` — constrained types
- Read function axioms (`readInt32_eq`, etc.)
- Instance functions (isFunctional instance procedures)
- Static functions (isFunctional static procedures)

```lean
def modelFunctions (program : Program) : List Core.Decl := ...
```

### 3. Procedure declarations

- Static procedures (non-functional)
- Instance procedures (non-functional, qualified names)
- Constrained type witness procedures

```lean
def modelProcedures (program : Program) : List Core.Decl := ...
```

### 4. Body translation

Each Laurel procedure body maps to a Core procedure body.
This is the most complex part — it handles:

- Variable declarations → Core `init`
- Assignments → Core `set` or `call`
- If/else → Core `if`
- While loops → Core `while`
- Static calls → Core `call` (procedures) or expression (functions)
- Instance calls → Core `call` with qualified name
- Field access → `readField` / `readInt32` etc.
- Field write → `updateField`
- Return → Core `set` output + `exit`
- Assertions → Core `assert`
- Exception propagation → Core `if isFailure($result) then exit`

```lean
def modelBody (ctx : ModelContext) (body : StmtExpr) : Core.Statement := ...
```

The `ModelContext` carries:
- Which procedures are functions vs procedures
- Which procedures access the heap
- The composite/field/type structure

This replaces the `SemanticModel` + `TranslateState` from the
real code with a pure, computed context.

## Differential Testing

```lean
#eval do
  let laurelProgram := parseLaurelFile "test.laurel"
  let realResult := translate {} laurelProgram
  let modelResult := translateModel laurelProgram
  assert (realResult == modelResult)
```

Run on every test file. Catches bugs without proofs.

## Proof Structure

### Phase 1: Properties of the model (tractable)

Prove P1-P7 from decisions.md about `translateModel`. These
are properties of a pure function — standard Lean theorem
proving.

### Phase 2: Equivalence (hard, deferred)

Prove `translate L = translateModel L` for well-formed `L`.
This requires reasoning about the state monad, HashMap lookups,
and the interaction of 10+ passes. Deferred until Phase 1 is
complete and the model is stable.

### Phase 3: Semantic preservation (research-level)

Prove that if Core verifies a property, the property holds for
the Laurel program. This connects to the existing P1-P12 proofs
in Strata's Core. Deferred until Phase 2 is complete.

## File Organization

```
Strata/Languages/Laurel/
  TranslatorModel.lean          -- the pure functional model
  TranslatorModelProperties.lean -- P1-P7 theorems
  TranslatorEquivalence.lean    -- translate = translateModel (Phase 2)
```

## Implementation Plan

1. Write `modelDatatypes` — generate the correct datatypes
2. Write `modelFunctions` — generate heap ops, constraints, etc.
3. Write `modelProcedures` — translate procedure signatures
4. Write `modelBody` — translate procedure bodies
5. Assemble into `translateModel`
6. Differential testing against `translate`
7. Prove P1 (name consistency)
8. Prove P2-P7
9. Prove equivalence (Phase 2)
