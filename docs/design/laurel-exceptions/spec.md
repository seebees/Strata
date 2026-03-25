# Laurel Exception Support: Formal Specification

**Version:** 0.1.0
**Date:** 2026-03-25

## 1. Definitions {#definitions}

### 1.1 Result Type {#result-type}

A method that can throw returns a `Result<T>`:

```
datatype Result<T> =
    | Success(value: T)
    | Failure(exception: Exception)
```

### 1.2 Exception Type {#exception-type}

Exceptions are modeled as composite types with inheritance,
matching the source language's exception hierarchy.

### 1.3 Laurel Constructs {#laurel-constructs}

Two new `StmtExpr` constructors:

```
| Throw (exception : WithMetadata StmtExpr)
| TryCatch (body : WithMetadata StmtExpr)
    (catches : List CatchClause)
    (finally : Option (WithMetadata StmtExpr))
```

Where:

```
structure CatchClause where
    exceptionType : WithMetadata HighType
    variableName : Option Identifier
    body : WithMetadata StmtExpr
```

### 1.4 Contract Constructs {#contract-constructs}

Three contract primitives (in the source language, mapped to
Laurel ensures clauses):

- `postcondition(P)` → `ensures isSuccess(result) ==> P(result.value)`
- `guard(C)` → `ensures C_at_entry ==> isFailure(result)`
- `postconditionOnThrow(Q)` → `ensures isFailure(result) ==> Q(result.exception)`

## 2. Translation: Throw {#translation-throw}

### 2.1 Definition {#throw-definition}

```
translate(Throw(e)) =
    result := Failure(translate(e));
    exit $body;
```

### 2.2 Properties {#throw-properties}

After executing `Throw(e)`:
- The method's result is `Failure(e)`
- No subsequent statements in the current block execute
- Control transfers to the nearest enclosing `TryCatch` handler
  or to the method's caller

## 3. Translation: TryCatch {#translation-trycatch}

### 3.1 Definition {#trycatch-definition}

```
translate(TryCatch(body, catches, finally)) =
    Block "try_end" [
        Block "handlers" [
            translate(body)
            -- after each statement that may throw:
            if isFailure(result) { exit "handlers"; }
            ...
            exit "try_end";  -- normal completion
        ]
        -- catch dispatch:
        for each catch_i in catches:
            if isType(result.exception, catch_i.exceptionType) {
                catch_i.variableName := result.exception;
                translate(catch_i.body);
                result := Success(void);  -- or propagate body's result
                exit "try_end";
            }
        -- no catch matched: result remains Failure, propagates
    ]
    -- finally (if present):
    translate(finally)
```

### 3.2 Properties {#trycatch-properties}

- If the body completes normally, catch handlers do not execute
- If the body throws, the first matching catch handler executes
- If no catch handler matches, the exception propagates
- The finally block executes regardless of outcome

## 4. Translation: Method Signatures {#translation-signatures}

### 4.1 Definition {#signature-definition}

A method with return type `T` that may throw is translated to
a procedure returning `Result<T>`:

```
// Source:
int foo(int x) { ... }

// Laurel:
procedure foo(x: int) returns (result: Result<int>)
```

### 4.2 Call Sites {#call-sites}

After calling a method that returns `Result<T>`:

```
var callResult := foo(x);
if isFailure(callResult) {
    result := callResult;  -- propagate
    exit $body;
}
var value := callResult.value;  -- safe: checked isSuccess
```

## 5. Correctness Properties {#correctness-properties}

These properties define the correctness of the Laurel→Core
translation for exception constructs. Each property should be
stated as a Lean theorem and proven.

Note: Properties about `guard` and `postconditionOnThrow` belong
in the JVerify specification, not here. Those are JVerify API
concepts that translate to standard Laurel `ensures` clauses.
Strata's responsibility is proving that `Throw`, `TryCatch`, and
`Result` translate correctly to Core.

### Property 1: Throw Produces Failure {#property-1-throw-produces-failure}

If a `Throw(e)` statement executes, the method's result is
`Failure(e')` where `e'` is the translation of `e`.

Formally: for any program state σ where `Throw(e)` executes,
the translated Core program produces `result = Failure(eval(e, σ))`.

### Property 2: Success Path Isolation {#property-2-success-path-isolation}

If a method returns `Success(v)`, then no `Throw` statement
executed during the method's execution.

Formally: `isSuccess(result) ==> no Throw executed on this path`.

This ensures that `ensures isSuccess(result) ==> P` (which is
how postconditions are expressed) only applies to paths where
no exception occurred.

### Property 3: Catch Dispatch Correctness {#property-3-catch-dispatch}

In a `TryCatch`, if the body throws exception `e` and catch
clause `i` has type `T_i`:

- If `isType(e, T_i)` is true and no earlier clause matched,
  then clause `i`'s body executes with `e` bound to the
  exception variable.
- If no clause matches, the exception propagates (the method's
  result is `Failure(e)`).

### Property 4: Normal Completion Skips Handlers {#property-4-normal-completion}

If a `TryCatch` body completes without throwing, no catch
handler executes. The result is whatever the body produced.

### Property 5: Exception Propagation {#property-5-propagation}

If a callee returns `Failure(e)` and the caller does not have
a `TryCatch` that catches `e`, then the caller's result is
`Failure(e)`.

Formally: for any call `r := callee(args)` where
`isFailure(r)` and no enclosing `TryCatch` catches `r.exception`,
the caller's result is `Failure(r.exception)`.

### Property 6: Finally Execution {#property-6-finally}

If a `TryCatch` has a `finally` block, the finally block
executes regardless of whether the body completed normally,
threw a caught exception, or threw an uncaught exception.

### Property 7: Result Exhaustiveness {#property-7-result-exhaustiveness}

For any method result, exactly one of `isSuccess(result)` or
`isFailure(result)` is true. They are mutually exclusive and
exhaustive.

### Property 8: Ensures Clause Isolation {#property-8-ensures-isolation}

An `ensures` clause guarded by `isSuccess(result)` is never
checked on a failure path. An `ensures` clause guarded by
`isFailure(result)` is never checked on a success path.

This follows from Property 7 (exhaustiveness) and the semantics
of implication, but should be stated explicitly as it is the
foundation for separating success and failure contracts.

## 6. Proof Assumptions {#proof-assumptions}

The Lean proofs in the Laurel→Core translator prove:

> "Given well-formed Laurel with `Throw`/`TryCatch`, the generated
> Core program correctly models exception semantics."

These proofs assume:

1. **The Laurel input is well-formed.** `Throw` contains a valid
   exception expression. `TryCatch` has a body and well-typed
   catch clauses. The language translator is responsible for
   producing well-formed Laurel.

2. **Exception types are correctly modeled.** The exception hierarchy
   in the Core prelude matches the source language's hierarchy.
   `IsType` checks in catch dispatch are correct. The language
   translator (or a shared prelude) is responsible for defining
   the hierarchy.

3. **Every throwing call site has a propagation check.** The
   Laurel→Core translator inserts checks after calls within
   `TryCatch` bodies. But for calls OUTSIDE try/catch, the
   language translator must emit the propagation. (Alternatively,
   the Laurel→Core translator could insert propagation for ALL
   calls, making this assumption unnecessary.)

4. **The source language's scoping rules are respected.** Variables
   declared in try bodies, catch bodies, and finally blocks have
   the correct scope in the generated Laurel. The language
   translator is responsible for scoping.

These assumptions define the **translator contract**. A language
translator that violates these assumptions can produce unsound
verification results, even though the Laurel→Core translation
itself is proven correct.

The translator contract is NOT proven in Lean — it's the
responsibility of each language translator's implementation and
test suite. This is the trust boundary: Lean proves Laurel→Core,
testing validates Language→Laurel.

## 6. Worked Examples

### 6.1 Simple guard clause {#example-guard}

```java
byte[] getContent() {
    guard(isDestroyed());
    postcondition((byte[] r) -> fresh(r));
    if (isDestroyed()) throw new IllegalStateException();
    return content.clone();
}
```

Laurel:
```
procedure getContent() returns (result: Result<ByteArray>)
    ensures old(isDestroyed) ==> isFailure(result)        // guard
    ensures isSuccess(result) ==> fresh(result.value)      // postcondition
{
    if (isDestroyed) {
        Throw(IllegalStateException());
    }
    result := Success(content.clone());
}
```

Core (after translation):
```
procedure getContent() returns (result: Result<ByteArray>)
    ensures old(isDestroyed) ==> isFailure(result)
    ensures isSuccess(result) ==> fresh(result.value)
{
    if (isDestroyed) {
        result := Failure(IllegalStateException());
        exit $body;
    }
    result := Success(content.clone());
}
```

### 6.2 Try/catch converting exception to return value {#example-trycatch}

```java
boolean authorize(String action, Set<String> operators) {
    postcondition((boolean r) -> implies(noRulesFor(action), !r));
    try {
        return doAuthorize(action, operators);
    } catch (ApiLockedException e) {
        return false;
    }
}
```

Core (after translation):
```
procedure authorize(action, operators) returns (result: Result<bool>)
    ensures isSuccess(result) ==> implies(noRulesFor(action), !result.value)
{
    Block "try_end" [
        Block "handlers" [
            var callResult := doAuthorize(action, operators);
            if isFailure(callResult) { exit "handlers"; }
            result := Success(callResult.value);
            exit "try_end";
        ]
        if isType(callResult.exception, ApiLockedException) {
            result := Success(false);
            exit "try_end";
        }
        result := callResult;  // propagate uncaught
    ]
}
```

### 6.3 State preservation on throw {#example-state-preservation}

```java
void destroy() {
    postcondition(isDestroyed == true);
    postcondition(forall(i -> content[i] == 0));
    postconditionOnThrow(isDestroyed == old(isDestroyed));

    isDestroyed = true;
    riskyOperation();  // might throw
    Arrays.fill(content, 0);
}
```

If `riskyOperation()` throws, `isDestroyed` is already `true`
but `content` is not zeroed. The `postconditionOnThrow` requires
`isDestroyed == old(isDestroyed)`, which is `true == false` —
verification FAILS. This correctly identifies the bug: the method
doesn't roll back on failure.
