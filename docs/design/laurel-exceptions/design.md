# Laurel Exception Support: Design

**Date:** 2026-03-25
**Status:** Proposed

## Overview

Add `Throw` and `TryCatch` as first-class constructs to Laurel's
`StmtExpr` type, with a `Result<T>` datatype in the Core prelude.
The Laurel→Core translator desugars these into labeled blocks,
exits, and Result pattern matching. The desugaring is proven
correct in Lean.

See [decisions.md](decisions.md) for why these choices were made,
[spec.md](spec.md) for the formal correctness properties, and
[examples.md](examples.md) for cross-language patterns.

## Code Changes

### 1. Core Prelude: Result datatype

**File:** `Strata/Languages/Core/Prelude.lean` (or equivalent)

Add:
```
datatype Result<T> {
    Success(value: T),
    Failure(exception: Composite)
}

function isSuccess<T>(r: Result<T>): bool
function isFailure<T>(r: Result<T>): bool
```

The exception is typed as `Composite` — Laurel's existing type
for class-like objects with inheritance. Language translators
define their specific exception hierarchies as composite types.

### 2. Laurel StmtExpr: Throw and TryCatch

**File:** `Strata/Languages/Laurel/Laurel.lean`

Add to the `StmtExpr` inductive type:

```lean
| Throw (exception : WithMetadata StmtExpr)
| TryCatch (body : WithMetadata StmtExpr)
    (catches : List CatchClause)
    (finally : Option (WithMetadata StmtExpr))
```

Add new structure:

```lean
structure CatchClause where
    exceptionType : WithMetadata HighType
    variableName : Option Identifier
    body : WithMetadata StmtExpr
```

### 3. Laurel Grammar

**File:** `Strata/Languages/Laurel/Grammar/LaurelGrammar.st`

Add syntax for `throw` and `try/catch/finally` so Laurel programs
can be written and parsed in text form (for testing).

### 4. Laurel→Core Translator

**File:** `Strata/Languages/Laurel/LaurelToCoreTranslator.lean`

Add translation cases for `Throw` and `TryCatch`.

**Throw translation:**
```
Throw(e) →
    result := Failure(translate(e));
    exit $body;
```

**TryCatch translation:**
```
TryCatch(body, catches, finally) →
    Block "try_end" [
        Block "handlers" [
            translate(body)
            // after each potentially-throwing statement:
            if isFailure(result) { exit "handlers"; }
            ...
            exit "try_end";  // normal completion
        ]
        // catch dispatch:
        for each catch_i:
            if IsType(result.exception, catch_i.type) {
                catch_i.variable := result.exception;
                translate(catch_i.body);
                exit "try_end";
            }
        // uncaught: result stays Failure, propagates
    ]
    // finally:
    translate(finally)
```

### 5. Method Signature Transformation

**File:** `Strata/Languages/Laurel/LaurelToCoreTranslator.lean`

Methods that contain `Throw` or call methods that may throw get
their return type wrapped in `Result<T>`. The translator handles
this during procedure translation.

### 6. Java Type Generator

**File:** `Strata/DDM/Integration/Java/Gen.lean`

Regenerate the Java Laurel types to include `Throw`, `TryCatch`,
and `CatchClause`. These are the Java records in JVerify's
`verifier/src/main/java/com/aws/jverify/laurel/` directory.

### 7. Ion Serialization

**File:** `Strata/Languages/Laurel/Grammar/ConcreteToAbstractTreeTranslator.lean`

Add serialization/deserialization for the new constructs so they
can be transmitted between JVerify (Java) and Strata (Lean) via
Ion binary format.

### 8. Lean Proofs

**File:** `Strata/Languages/Laurel/LaurelToCoreTranslator.lean`
(or a dedicated proof file)

Prove the 8 correctness properties from [spec.md](spec.md):
1. Throw Produces Failure
2. Success Path Isolation
3. Catch Dispatch Correctness
4. Normal Completion Skips Handlers
5. Exception Propagation
6. Finally Execution
7. Result Exhaustiveness
8. Ensures Clause Isolation

### 9. Tests

**Directory:** `StrataTest/Languages/Laurel/`

Add Laurel-level tests for:
- Throw producing Failure
- TryCatch with matching handler
- TryCatch with no matching handler (propagation)
- TryCatch with finally
- Nested TryCatch
- Multiple catch clauses with type dispatch

## Build and Integration

The Strata side builds with `lake build`. After changes:

```bash
cd Strata
lake build        # build everything including proofs
lake test         # run tests
```

The Java type generator produces updated Java records. These
must be copied to JVerify's `verifier/src/main/java/com/aws/jverify/laurel/`
directory (or the generator is run as part of JVerify's build).

## Ordering

1. Result datatype in Core prelude (foundation)
2. Throw + TryCatch in Laurel StmtExpr (IR changes)
3. Grammar + serialization (plumbing)
4. Laurel→Core translation (the semantic work)
5. Tests (validate the translation)
6. Lean proofs (verify the translation)
7. Java type regeneration (enable JVerify integration)
