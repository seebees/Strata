# Translator Functional Model: Design

**Date:** 2026-03-31
**Updated:** 2026-04-08
**Status:** Testing Complete, Proof In Progress (Category 3 proven)

## Overview

A pure functional model of the `translate` function that serves as the
definition of correct Laurel→Core translation. The model is executable
(differential testing) and provable (Lean theorems).

```
Laurel Program ──→ translateProgramModel ──→ Core Program
                        │
                   (pure function, no state monad, no error handling)

Laurel Program ──→ translate ──→ Core Program
                        │
                   (imperative, state monad, 10+ passes)
```

Both take the same input and should produce the same output (after
`stripMetaData ∘ eraseTypes` normalization). When they disagree, we
investigate which is correct and fix the other.

## Key Files

| File | Purpose |
|------|---------|
| `TranslatorModel.lean` | Pure model: `translateProgramModel`, `translateProcModel`, `translateStmtModel`, `translateExprModel` |
| `TranslatorEquivalence.lean` | Proof infrastructure: lemmas, decomposition, category proofs |
| `TranslatorModelProof.lean` | Computational proofs |
| `LaurelToCoreTranslator.lean` | Real translator + main theorem statement |
| `TranslatorModelTest.lean` | 118 differential tests |

## Model Architecture

The model translates directly from Laurel AST to Core AST without
intermediate passes. The real translator runs ~10 passes (resolution,
heap parameterization, type hierarchy transform, etc.) then calls
`translateLaurelToCore`. The model captures the end-to-end effect.

### Expression Translation (`translateExprModel`)

Maps Laurel `StmtExpr` to Core `Expression.Expr`. Handles:
- Literals (int, bool, string, decimal)
- Identifiers, field selects (with Box destructor wrapping)
- All primitive operators (arithmetic, comparison, boolean, implies, short-circuit)
- Static and instance function calls
- Conditional expressions, quantifiers (forall/exists), old()
- String concatenation, reference equality

### Statement Translation (`translateStmtModel`)

Maps Laurel `StmtExpr` to Core `Statements`. Handles:
- Return (with/without value, from static/instance call)
- Local variable (with/without init, from static/instance call)
- Assignment (to identifier, to field, from static/instance call)
- Control flow (if/else, while with invariants, labeled blocks)
- Procedure calls (static, instance, with exception propagation)
- Assert, assume
- Throw (→ `$result := Failure; exit <target>`)
- TryCatch (→ labeled blocks + catch dispatch + finally)
- Exit (→ `exit <label>`)

### Procedure Translation (`translateProcModel`)

Assembles a full Core procedure declaration from a Laurel procedure:
- Header: inputs (with heap params), outputs (with heap/result)
- Spec: preconditions (with constraint preconditions), postconditions (with frame conditions)
- Body: `$result := Success; $body: { ... }`

Key concerns:
- Heap detection: reads/writes heap based on field access, instance calls, opaque modifies
- Instance call qualification: `qualifyMd` rewrites field names and call targets
- Opaque bodies: `$unused` init wrapping, postcondition qualification
- Precondition heap variable: `$heap_in` for heap-writing procs

### Program Translation (`translateProgramModel`)

Assembles the full Core program in 7 segments:
1. ExceptionResult datatype
2. Infrastructure + user datatypes (TypeTag, Field, Box, Composite, Heap, user types)
3. Read function axioms (readInt32_eq, etc.)
4. Ancestor declarations (ancestorsForX, ancestorsPerType)
5. Function declarations (constraint, heap, external, transparent)
6. Procedure declarations (static procs + witness procs)
7. Instance procedure declarations

## Testing Strategy

### Differential Testing

The primary bug-finding tool. Each test:
1. Parses a Laurel program
2. Runs both `translateProgramModel` and `translate {}`
3. Compares declaration names
4. Compares structural output after `stripMetaData ∘ eraseTypes`

### Coverage Approach

Three dimensions of coverage:

1. **Branch coverage:** Every match arm in `translateExprModel`, `translateStmtModel`,
   `translateProcModel` has at least one test exercising it.

2. **Feature interaction coverage:** Bugs cluster at feature boundaries (e.g., instance
   call + if condition, opaque + postcondition + field access). Tests combine features
   from different dimensions.

3. **Real-world coverage:** The JVerify test suite (~35 programs in
   `StrataTest/Languages/Laurel/Examples/`) exercises realistic feature combinations.
   These should all pass the differential test.

### When to Return to Proof

Criteria:
1. Zero structural test failures on hand-crafted tests
2. Zero structural test failures on JVerify test suite programs
3. All 9 known model gaps fixed

## Proof Strategy

### Phase 1: Testing (current)
Find and fix model bugs via differential testing. Build confidence that
the model is correct before investing in proofs.

### Phase 2: Proof
Prove `translate ≡ translateProgramModel` using the 7-category decomposition.
Each category is independently provable. The assembly step combines them.

### Key Insight

The proof and tests serve different purposes:
- **Tests** find bugs in the model (fast, concrete, catches interactions)
- **Proof** guarantees correctness for ALL inputs (slow, abstract, complete)

Attempting to prove an incorrect model wastes effort. The first week of proof
work found zero bugs. The first day of differential testing found 11. Testing
must come first.
