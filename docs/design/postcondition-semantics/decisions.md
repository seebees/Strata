# Decision: Postcondition Semantics and Exception Paths

**Date:** 2026-04-13

## Context

After the merge brought in `ProcBodyVerify`, two instance method tests
(`StrataInstanceCallsInstance`, `StrataInstancePreconditionFail`) fail
with a spurious "assertion could not be proved" at `1:1-1:1`.

Root cause: `ProcBodyVerify` converts procedures to a flat verification
statement: `assume preconditions → body → assert postconditions`. The
`callElim` transform replaces procedure calls with `havoc outputs →
assume postconditions`, which creates a nondeterministic `$result` that
can be `Failure`. This creates an exception path where `result` (the
return value) is never assigned. Unconditional postconditions about
`result` (e.g., `int32$constraint(result)` from `constrainedTypeElim`)
fail on this phantom path because `result` is nondeterministic.

Pre-merge, the verifier evaluated bodies directly and could see that
`$result` was always `Success` for non-throwing methods. `ProcBodyVerify`
loses this information.

## JVerify Postcondition API

JVerify provides three postcondition forms:

- `postcondition(P)` — unconditional, must hold on ALL exit paths
- `postconditionOnReturn(P)` — must hold only when the method returns normally
- `postconditionOnThrow(P)` — must hold only when the method throws

The Javadoc for `postcondition` explicitly states: "applies to all exit
paths." This is distinct from `postconditionOnReturn`.

## D1: How should `postcondition(r -> P(r))` (lambda form) be translated?

The lambda form binds the return value. On the failure path, there is
no return value — `result` is meaningless. An unconditional postcondition
about a value that doesn't exist is semantically incoherent.

### Option A: Translate as unconditional `ensures P(result)`

The literal translation. `result` is nondeterministic on the failure
path, so the postcondition is unprovable for any method that might throw
(which is effectively all methods, since `callElim` creates exception
paths for all calls).

- Pro: Simple, literal.
- Con: Unprovable in practice. Forces users to add `postconditionOnThrow(false)`
  to every non-throwing method, which is terrible ergonomics.

### Option B: Silently desugar to `postconditionOnReturn`

Treat `postcondition(r -> P(r))` as `ensures isSuccess($result) ==> P(result)`.

- Pro: "Just works" for the common case.
- Con: Silently weakens the user's contract. The user wrote an unconditional
  postcondition but gets a conditional one. This is a semantic lie — the tool
  does something different from what the user said. Breaks the principle that
  `postcondition` and `postconditionOnReturn` are distinct.

### Option C: Desugar to `postconditionOnReturn` AND `postconditionOnThrow(false)`

`postcondition(r -> P(r))` desugars to both:
- `ensures isSuccess($result) ==> P(result)`
- `ensures isFailure($result) ==> false`

The user is making a strong claim: "P holds on my return value, AND I
never throw." If the method can throw, the `postconditionOnThrow(false)`
fails — which is correct, because the user's contract is wrong.

- Pro: Preserves the unconditional semantics. The conjunction of both
  ensures clauses is equivalent to "I always succeed and P holds on the
  result." No silent weakening. Backwards compatible — strictly stronger
  than the ambiguous previous behavior.
- Con: Methods that call other methods will need to prove they can't throw,
  which may require `postconditionOnThrow(false)` on callees or try/catch.

### Option D: Reject the lambda form on `postcondition` — require explicit choice

Make `postcondition(r -> P(r))` a compilation error. Force the user to
write either `postconditionOnReturn(r -> P(r))` or both
`postconditionOnReturn(r -> P(r))` + `postconditionOnThrow(false)`.

- Pro: No ambiguity. The user must be explicit about exception behavior.
- Con: Breaking change. Existing code uses `postcondition(r -> ...)`.

### Decision: Option C

Option C preserves the unconditional semantics without silently weakening
the contract. The user who writes `postcondition(r -> P(r))` is saying
"this always succeeds with a result satisfying P." If that's not true,
the verification correctly fails.

This creates a clear migration path: if a method CAN throw, the user
should use `postconditionOnReturn` instead of `postcondition` for
result-dependent properties.

## D2: How should `constrainedTypeElim` generate output ensures?

`constrainedTypeElim` generates `ensures int32$constraint(result)` for
procedures with constrained return types. This is about the return value
and is only meaningful on the success path.

### Decision: Guard with `isSuccess($result)`

Generated constraint postconditions for output parameters should be
guarded: `ensures isSuccess($result) ==> int32$constraint(result)`.

This is infrastructure, not a user contract. The constraint says "IF the
method returns a value, that value fits in int32." It does not claim the
method can't throw — that's the user's responsibility via their contract.

## D3: Metadata for generated postconditions

Generated postconditions from `constrainedTypeElim` should carry the
procedure's source metadata (fallback from parameter type metadata),
not empty metadata. This prevents `1:1-1:1` diagnostics.

The `outputEnsures` code already has this fallback. The `inputRequires`
code should have the same fallback (see D5 in constrained-types-in-heap).

## D4: Diagnostic responsibility boundary

Strata does not know about `postcondition`, `postconditionOnReturn`, or
`postconditionOnThrow`. By the time Strata sees the program, everything
is Laurel `ensures` clauses with metadata.

**JVerify's responsibility:**
- Desugar `postcondition(r -> P(r))` into two ensures clauses
- Attach source metadata (the `postcondition(...)` line) to both clauses
- Optionally attach `propertySummary` metadata to customize the error
  message (e.g., "postcondition no-throw guarantee" on the
  `isFailure ==> false` clause)

**Strata's responsibility:**
- Translate ensures clauses faithfully to Core postconditions
- Report verification failures using the metadata attached to each clause
- Use `getPropertySummary` from metadata for the error description

This design works naturally when the user writes both lines explicitly:
`postconditionOnReturn(r -> P(r))` + `postconditionOnThrow(false)`.
JVerify emits the same two ensures clauses, each with metadata pointing
to its own source line. The diagnostics point to the right place because
the user wrote both lines.

The desugaring of `postcondition(r -> P(r))` just means both ensures
clauses share the same source location. The error message distinguishes
them via `propertySummary`.

## Open Questions

### OQ1: Asynchronous exceptions in Java

Java allows asynchronous exceptions (`ThreadDeath`, `OutOfMemoryError`,
`StackOverflowError`) that can occur at any point during execution. This
means that in the strictest interpretation of Java semantics, ANY method
can throw — even `int addTwo(int x) { return x + 2; }`.

The current model adds `$result : ExceptionResult` to every procedure
and generates exception propagation for every call. This is conservative
and correct for the general case.

Questions:
1. Should the model distinguish between methods that can throw checked/
   unchecked exceptions (via `throws` clause or `throw` statements) and
   methods that can only fail via asynchronous exceptions?
2. Should asynchronous exceptions be modeled at all? Dafny and most
   verification tools ignore them. The JLS treats them specially
   (§11.1.3). Modeling them makes ALL unconditional postconditions about
   `result` unprovable without explicit no-throw claims.
3. If we don't model asynchronous exceptions, can we optimize away the
   `$result` parameter for methods that provably can't throw (no `throw`
   statements, no calls to throwing methods)? This would eliminate the
   phantom exception path entirely for simple methods.

### OQ2: `postcondition(boolean)` (non-lambda form) and exception paths

The boolean form `postcondition(someState)` doesn't reference `result`.
It's about state and is meaningful on all paths. No desugaring needed —
it stays as `ensures someState`.

However: if the postcondition references heap state that was partially
modified before a throw, the unconditional postcondition correctly fails.
This is the intended behavior (see spec example 6.3, `destroy()`).
