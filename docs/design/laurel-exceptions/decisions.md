# Laurel Exception Support: Design Decisions

**Date:** 2026-03-25
**Status:** Proposed

This document captures the design decisions for adding exception
handling to the Laurel intermediate language. Each decision follows
the "cake" format: options considered, what was chosen, and why.

## Context

Laurel is an intermediate verification language targeting
garbage-collected languages with imperative features (Java, Python,
JavaScript). Its documentation lists exception handling as "(WIP)."

Python→Laurel translation has partial exception support
([PR #572](https://github.com/strata-org/Strata/pull/572),
[PR #610](https://github.com/strata-org/Strata/pull/610)):
`try/except` is desugared into labeled blocks with a `maybe_except`
variable and `isError` checks. However, `raise` is still translated
to `Hole` (nondeterministic unknown)
([PR #613](https://github.com/strata-org/Strata/pull/613)),
meaning the verifier cannot reason about code that throws exceptions.

Java needs the same capability. Every Java method can throw unchecked
exceptions. `throw`, `try/catch/finally` are fundamental to the
language. Without exception support, JVerify rejects any method
containing these constructs.

---

## Decision 1: Where do exceptions live — in Laurel or in language translators? {#decision-1}

**Context:** The Python translator desugars `try/except` into
existing Laurel constructs (labeled blocks, Exit, variables).
Should Java do the same, or should Laurel have first-class
exception constructs?

### Option A: Per-language desugaring with Exit + Assign

Each language translator desugars exceptions into existing Laurel
primitives: `Assign` (set result to Failure), `Exit` (leave the
block), `Block` (labeled scope), `IfThenElse` + `IsType` (catch
dispatch). Laurel itself has no exception concepts. This is what
Python does today.

- Pro: No Laurel changes needed. Smallest possible change — only
  a `Result` type in the Core prelude. Each language can tailor
  the encoding to its specific exception model.
- Con: The desugaring is in unverified language-specific code.
  Python's implementation had bugs: duplicate labels
  ([PR #572](https://github.com/strata-org/Strata/pull/572)),
  variable scoping
  ([PR #610](https://github.com/strata-org/Strata/pull/610)),
  exception variable typing
  ([PR #613](https://github.com/strata-org/Strata/pull/613)).
  These bugs happened because the translator was encoding a
  high-level concept (try/except) with low-level primitives
  (blocks/exits), and the encoding was wrong.

  Critically, the Lean proofs CANNOT verify this encoding.
  At the Core level, there are no exceptions — just blocks and
  exits. The proofs verify that Core handles blocks and exits
  correctly, but they cannot verify that a specific pattern of
  blocks and exits correctly models exception semantics.

  This is the "goto considered harmful" problem: you CAN express
  everything with goto (or Exit + Assign), but structured
  constructs let verifiers reason about your code. Without
  structure, each language translator must independently get the
  encoding right, and there's no mechanical check that it did.

### Option B: First-class Laurel constructs (Throw + TryCatch)

Add `Throw` and `TryCatch` to Laurel's `StmtExpr` type. The
Laurel→Core translator handles the desugaring to blocks and exits.

- Pro: The desugaring is in Lean and CAN be proven correct.
  Specifically, we can prove:
  - Every `Throw` produces a `Failure` result
  - A `TryCatch` body that completes normally skips all handlers
  - Catch dispatch goes to the first matching handler
  - Uncaught exceptions propagate (result stays Failure)
  - Finally always executes

  These are exactly the properties that Python's per-language
  encoding got wrong. With first-class constructs, the Lean
  type checker verifies the desugaring once, and all languages
  benefit.

  Language translators emit high-level intent (`Throw`,
  `TryCatch`), not low-level encoding (blocks, exits, assigns).
  The translator's job becomes syntactic mapping, not semantic
  transformation.

  Reviewer keyboardDrummer has repeatedly suggested that
  constructs like these belong in Laurel rather than per-language
  ([PR #572](https://github.com/strata-org/Strata/pull/572),
  [PR #573](https://github.com/strata-org/Strata/pull/573)).

- Con: Requires changes to Laurel's `StmtExpr` inductive type,
  the grammar, the Laurel→Core translator, the serializer, and
  the Java type generator. More upfront work.

### Option C: Result type only, no new Laurel constructs

Add `Result<T>` to Core but don't add `Throw`/`TryCatch` to
Laurel. Language translators emit the Exit + Assign pattern
but with a proper `Result` type instead of the ad-hoc
`maybe_except` variable.

- Pro: Smaller change than Option B. Improves the type safety
  of the encoding (Result instead of bare Error variable).
- Con: Same fundamental problem as Option A — the desugaring
  is in unverified language-specific code. The Result type
  improves the data model but doesn't help verify the control
  flow encoding. The bugs Python hit were control flow bugs
  (wrong labels, wrong scoping), not data model bugs.

### Decision: Option B (first-class Laurel constructs)

The exception desugaring is a semantic transformation — converting
structured exception handling into blocks and exits. This is
exactly the kind of transformation that benefits from being in
a verified layer.

The "goto considered harmful" analogy is precise: `Exit + Assign`
is the goto-level encoding of exceptions. `Throw + TryCatch` is
the structured-programming-level encoding. Just as `while` lets
compilers prove loop properties that `goto + label` cannot,
`Throw + TryCatch` lets the Lean verifier prove exception
properties that `Exit + Assign` cannot.

The upfront cost (grammar, serializer, type generator changes)
is mechanical plumbing. The proofs are where the value is.
Python's bugs demonstrate that the unstructured encoding is
error-prone. Structured constructs prevent those bugs by
construction.

Option C (Result only) is a reasonable intermediate step if we
want to ship incrementally. But it should be understood as a
stepping stone, not the end state.

---

## Decision 2: How to model the exception value — Result ADT vs extra output parameter {#decision-2}

**Context:** A method that can throw has two possible outcomes:
a return value or an exception. How should this be represented
in the verification model?

### Option A: Extra output parameter (Python's current approach)

Every method that can throw gets an additional output parameter
of type `Error`. The caller checks `isError(maybe_except)` after
each call.

```
procedure foo(x: int) returns (result: int, maybe_except: Error)
```

- Pro: Simple. Uses existing Laurel constructs (variables,
  assignments). Already working for Python's `try/except`
  structure. No new types needed.
- Con: The `Error` type is a flat enum — `NoError`, `TypeError`,
  `AttributeError`, etc. It doesn't carry the exception object's
  fields or support a type hierarchy. Java's exception hierarchy
  (checked vs unchecked, `IOException` extends `Exception`
  extends `Throwable`) cannot be modeled. The tuple `(result,
  error)` is a convention, not enforced by the type system —
  code could use `result` when `error` is set.

### Option B: Result algebraic datatype

Define a `Result<T>` ADT in the Core prelude:

```
datatype Result<T> {
    Success(value: T),
    Failure(exception: Exception)
}
```

Methods return `Result<T>` instead of `T`. Pattern matching
enforces that you handle both cases.

- Pro: Type-safe — you cannot access the value without matching
  on `Success`. The `Exception` type can be a hierarchy (using
  Strata Core's datatype features). Postconditions naturally
  apply to the `Success` case. The encoding is standard and
  well-understood in functional programming and verification.
- Con: Changes every method's return type in the Laurel model.
  More complex than a simple extra parameter. Requires Core
  to support generic datatypes (which it does — see
  `docs/Datatypes.md`).

### Option C: Result as a convention on the extra parameter

Keep the extra output parameter but define it as `Result<T>`
instead of `Error`. The parameter carries either the value or
the exception, not both.

- Pro: Combines the simplicity of Option A's calling convention
  with Option B's type safety.
- Con: Laurel procedures already support multiple outputs, so
  this is mechanically similar to Option A but with a richer
  type. The distinction is mainly in the type, not the mechanism.

### Decision: Option B (Result ADT)

The Result ADT is the standard encoding for fallible operations
in verification. It enforces at the type level that you cannot
use the return value without handling the error case. This
prevents an entire class of bugs where the caller ignores an
exception and uses a garbage return value.

The extra-parameter approach (Option A) works for Python's
dynamically typed world where everything is `Any`, but Java's
static type system and exception hierarchy need a richer model.
The Result ADT naturally supports:

- Postconditions on success: `ensures Result.isSuccess(r) ==> P(r.value)`
- Postconditions on failure: `ensures Result.isFailure(r) ==> Q(r.exception)`
- Guard conditions: `ensures C_at_entry ==> Result.isFailure(r)`
- Exception type dispatch: `match r.exception { ISE => ..., IAE => ... }`

---

## Decision 3: How does catch dispatch work in Laurel? {#decision-3}

**Context:** A `TryCatch` catch clause matches exceptions by type.
Laurel needs a mechanism to check whether a thrown exception matches
a catch clause's declared type.
A try-catch clause matches exceptions by type.

### Option A: New exception-specific type check

Add a new `IsExceptionType` construct to Laurel specifically for
catch dispatch.

- Pro: Explicit about its purpose.
- Con: Redundant. Laurel already has `IsType` in `StmtExpr` for
  runtime type checks. Exception types are just types — they don't
  need special handling.

### Option B: Use existing `IsType`

Catch dispatch uses Laurel's existing `IsType` expression. The
catch clause checks `IsType(exception, catchClauseType)`. If the
exception's type is the declared type or a subtype, the clause
matches.

- Pro: No new constructs. Reuses existing infrastructure. Works
  for any language's exception types — Java's class hierarchy,
  Python's exception classes, JavaScript's prototype chain — as
  long as the language translator models them as Laurel composite
  types with inheritance.
- Con: Relies on the language translator correctly modeling the
  exception type hierarchy as Laurel composite types. But this is
  the translator's job, not Laurel's.

### Decision: Option B (use existing IsType)

Laurel already has the machinery for type-based dispatch. Exception
types are just types. The language translator is responsible for
defining the exception type hierarchy (e.g., Java's
`IOException extends Exception extends Throwable`) as Laurel
composite types. Laurel's `IsType` handles the rest.

This keeps Laurel language-agnostic. It doesn't know or care that
`IOException` is a Java exception — it just knows it's a composite
type that extends another composite type.

**Generality across languages:** The typed `CatchClause` with
`exceptionType` is designed for the most specific case (Java,
Python) where catch clauses dispatch by exception type. Languages
with less specific exception handling fall back naturally:

- **Java**: Multiple typed catch clauses → multiple `CatchClause`
  entries, each with a specific `exceptionType`. Direct mapping.
- **Python**: Multiple typed `except` clauses → same as Java.
  `except ValueError as e` maps to `CatchClause(ValueError, "e", body)`.
- **JavaScript**: Single untyped `catch (e)` → one `CatchClause`
  with `exceptionType` set to the root type (catches everything).
  Any `instanceof` checks inside the handler body are just
  `IfThenElse` + `IsType` in the handler's Laurel code.
- **Go**: No exceptions at all → no `TryCatch` needed. Go's
  `(value, error)` return pattern maps directly to `Result`.

The construct supports the most specific case (typed multi-catch)
but gracefully degrades for less specific cases (untyped single
catch, no exceptions). This is one of the advantages of putting
typed dispatch in Laurel: languages that need it get it for free,
and languages that don't need it simply don't use the full
specificity. A less specific construct (e.g., untyped catch only)
would force Java and Python to encode their type dispatch manually
in handler bodies — duplicating work that Laurel can handle once.

---

## Decision 4: What new constructs to add to Laurel's StmtExpr {#decision-4}

**Context:** Laurel's `StmtExpr` inductive type defines all
statement and expression forms. What constructs are needed for
exceptions?

### Option A: Throw only

Add `Throw` to `StmtExpr`. Model `try/catch` as desugared
labeled blocks (the existing Python pattern).

- Pro: Minimal change to Laurel. `try/catch` desugaring is
  already working via labeled blocks and Exit.
- Con: The `try/catch` desugaring remains implicit. Each
  language translator must know the labeled-block pattern.
  The Laurel→Core translator cannot verify the `try/catch`
  semantics because it doesn't see `try/catch` — it sees
  blocks and exits.

### Option B: Throw and TryCatch

Add both `Throw` and `TryCatch` to `StmtExpr`:

```lean
| Throw (exception : WithMetadata StmtExpr)
| TryCatch (body : WithMetadata StmtExpr)
    (catches : List CatchClause)
    (finally : Option (WithMetadata StmtExpr))
```

- Pro: Both constructs are first-class. The Laurel→Core
  translator handles the full desugaring. Language translators
  emit high-level constructs. The desugaring can be proven
  correct in Lean.
- Con: More changes to Laurel. Requires defining `CatchClause`
  as a new type.

### Option C: Throw, TryCatch, and Rethrow

Add `Throw`, `TryCatch`, and `Rethrow` (throw with no argument,
re-raising the current exception in a catch block).

- Pro: Covers all exception patterns including re-raise.
- Con: `Rethrow` can be modeled as `Throw(currentException)` —
  it may not need its own construct.

### Decision: Option B (Throw and TryCatch)

Both constructs are needed for the Laurel→Core translator to
produce correct verification conditions. `Throw` without
`TryCatch` would leave the catch desugaring implicit. `Rethrow`
can be expressed as `Throw` with the caught exception variable,
so it doesn't need a separate construct.

The `CatchClause` type would be:

```lean
structure CatchClause where
    exceptionType : WithMetadata HighType
    variableName : Option Identifier
    body : WithMetadata StmtExpr
```

---

## Decision 5: How to translate Throw to Core {#decision-5}

**Context:** Strata Core has no exception constructs. `Throw`
must be translated to Core primitives.

### Option A: Assume false

Translate `throw` to `assume false`, making the throw path
vacuously true.

- Pro: Simple. One line of code.
- Con: Unsound. `assume false` tells the prover "this path
  cannot happen" without proof. If the path CAN happen at
  runtime, postconditions are satisfied vacuously — the prover
  says "verified" on buggy code. This is the worst possible
  failure mode for a verification tool.

### Option B: Assert false

Translate `throw` to `assert false`, requiring the prover to
prove the path is unreachable.

- Pro: Sound — the prover must prove unreachability.
- Con: Too restrictive. Methods that legitimately throw cannot
  be verified. The prover would always fail on the throw path
  unless preconditions guarantee it's unreachable. This forces
  all exceptions to be modeled as precondition violations.

### Option C: Result.Failure assignment + return

Translate `throw e` to:

```
result := Result.Failure(e);
return;
```

The method's return type is `Result<T>`. Postconditions are
guarded by `Result.isSuccess(result)`. Guard conditions produce
`ensures C ==> Result.isFailure(result)`.
`postconditionOnThrow` produces
`ensures Result.isFailure(result) ==> P`.

- Pro: Sound. Both success and failure paths are modeled
  explicitly. The prover checks postconditions on the success
  path and postconditionOnThrow on the failure path. Guard
  conditions are verified bidirectionally. No path is assumed
  away or required to be unreachable.
- Con: Every method's return type changes to `Result<T>`.
  Every call site must check the result. More complex generated
  Core code.

### Decision: Option C (Result.Failure + return)

Options A and B are both wrong — A is unsound, B is too
restrictive. Option C is the only approach that correctly models
both outcomes of a method that can throw.

The complexity of Result-wrapping every method is real but
manageable. Methods that provably never throw (no throw
statements, no calls to throwing methods) can be optimized to
return `T` directly. But the base model must handle the general
case.

---

## Decision 6: How to translate TryCatch to Core {#decision-6}

**Context:** `TryCatch` must be translated to Core primitives.
The Python translator already has a working pattern using labeled
blocks and Exit.

### Option A: Labeled blocks with Exit (Python's pattern)

```
Block "try_end" [
    Block "exception_handlers" [
        body_stmt;
        if isError(maybe_except) { exit "exception_handlers"; }
        ...
        exit "try_end";  // normal completion
    ]
    // catch handlers here
    if isType(exception, IOException) { handler1 }
    if isType(exception, Exception) { handler2 }
]
```

- Pro: Already working for Python. Uses existing Core constructs.
  No new Core features needed.
- Con: The pattern is complex and error-prone — Python's
  implementation had bugs with duplicate labels
  ([PR #572](https://github.com/strata-org/Strata/pull/572)),
  variable scoping
  ([PR #610](https://github.com/strata-org/Strata/pull/610)),
  and exception variable typing
  ([PR #613](https://github.com/strata-org/Strata/pull/613)).

### Option B: Same pattern, but generated from Laurel TryCatch

Use the same labeled-block pattern as Option A, but generate it
from the first-class `TryCatch` construct in the Laurel→Core
translator rather than in each language translator.

- Pro: Single implementation in Lean. Can be proven correct.
  The bugs from Python's per-language implementation are avoided
  because the translation is centralized and verified.
  Language translators emit clean `TryCatch` nodes.
- Con: Same generated Core code complexity as Option A.

### Decision: Option B (centralized translation from TryCatch)

The labeled-block pattern works — Python proved that. The problem
was implementing it per-language, which led to bugs. Centralizing
it in the Laurel→Core translator (in Lean) and generating it from
a first-class `TryCatch` construct gives us the working pattern
with the correctness guarantee.

## Decision 7: How to route cross-method propagation in try/catch {#decision-7}

**Context:** After every procedure call, the translator inserts a
propagation check: `if isFailure($result) { exit <label> }`. The
question is what `<label>` should be.

### Option A: Always exit $body (current, broken)

The propagation check always exits `$body` (the procedure-level
label). This is correct when the call is NOT inside a try/catch,
but wrong when it IS — the exception skips the catch handler.

- Pro: Simple. No context tracking needed.
- Con: **Broken.** try/catch around method calls doesn't work.

### Option B: Track exception target label in translator state

The translator maintains a "current exception target" label:
- At procedure level: `$body`
- Inside a try body: the try body's `$handlers_N` label
- Nested try: innermost handler label

The propagation check uses this label instead of hardcoding `$body`.

- Pro: Correct. Matches Java semantics. Composable with nesting.
- Con: Adds state to the translator. Must be threaded through
  all `translateStmt` calls.

### Option C: Don't insert propagation checks; let TryCatch handle it

Instead of inserting propagation checks after calls, rely on the
TryCatch translation's existing `isFailure` check at the end of
the body block. The call sets `$result = Failure` (via the output
parameter), and the TryCatch body block's normal exit check
detects it.

- Pro: No propagation check needed inside try bodies.
- Con: Doesn't work — the call's `$result` output is separate
  from the procedure's `$result`. The TryCatch body block doesn't
  see the callee's result unless we explicitly propagate it.

### Decision: Option B (track exception target label)

Option B is the only correct approach. The translator already
tracks state (fresh IDs, diagnostics, model). Adding an exception
target label is a small addition. The label is set when entering
a TryCatch body and restored when leaving.

This satisfies Properties 9-12 in the spec.
