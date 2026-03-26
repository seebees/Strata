# Instance Method Support: Open Questions

**Date:** 2026-03-26

## ~~Q1: InstanceCall heap parameter placement~~ → Decision 4

Resolved. Heap parameterization injects `$heap` into InstanceCall args,
same as it does for StaticCall. See Decision 4.

## ~~Q2: Instance procedure parameter order in Core~~ → Decision 5

Resolved. Same pattern as static calls. `$heap` is prepended to args
by heap parameterization. The translator flattens InstanceCall by
prepending `target` (which maps to `self`) after `$heap`. No new
information — follows the existing static call convention. See Decision 5.

## ~~Q3: SelfRef / This handling~~ → Decision 6

Resolved. `This`/`SelfRef` is dead code in the Laurel AST — nothing
parses it, no test uses it, the translator rejects it. Instance methods
use `self` as a regular parameter (`Identifier("self")`). Field access
`self#count` is `FieldSelect(Identifier("self"), "count")` — identical
to how static procedures access composite fields (`c#intValue`).
No special handling needed. See Decision 6.

## ~~Q4: Heap analysis for InstanceCall callees~~ → Not a decision, mechanical fix

Confirmed this is a real bug. The analysis does NOT add `InstanceCall`
callees to the `callees` list. A procedure that only interacts with
the heap through instance calls (no direct field access, no `new`)
won't be identified as a heap reader/writer.

The analysis already runs over all procedures including instance ones
(line 478: `allProcs := staticProcedures ++ instanceProcs`), so
instance procedures themselves are correctly analyzed. The gap is
at CALL SITES — `InstanceCall` in a caller's body doesn't propagate
the callee's heap status to the caller.

Fix: add callee to `callees` list in `collectExpr`, same as `StaticCall`.
Also: inject `$heap` into `InstanceCall` in the transform phase, same
pattern as `StaticCall`. Both are mechanical — follow the existing code.

## ~~Q5: Modifies clauses for instance procedures~~ → Not a decision, mechanical fix

`modifiesClausesTransform` only iterates `staticProcedures`. The
per-procedure function `transformModifiesClauses` works on any
`Procedure` — it doesn't care if it's static or instance.

Fix: also iterate instance procedures from composites and put them
back. Trivial change to `modifiesClausesTransform`.

## ~~Q6: What does the consistency proof look like concretely?~~ → Decision 7

Resolved. Write a formal Lean theorem, even though it's trivially `rfl`.
See Decision 7.

## ~~Q7: Instance methods calling other instance methods~~ → Covered by Q4

Not a separate question. Once InstanceCall callees are added to the
`callees` list (Q4 fix), the fixpoint computation in `computeReadsHeap`
and `computeWritesHeap` handles transitive heap access automatically.
If `increment` calls `reset` and `reset` writes the heap, the fixpoint
propagates this to `increment`. The fixpoint doesn't care about call
type — just callee names.

## ~~Q8: Inherited instance methods~~ → Pre-existing limitation, not blocking

Instance procedures are defined in the GLOBAL scope (via `defineName`),
not in a per-type scope. So `Base.foo` is visible everywhere — a call
to `extender.foo()` resolves `foo` in the global scope and finds it.

Inheritance works for the simple case. The issue is if two different
types define a method with the same name — the second shadows the first
in the global scope. This is a pre-existing limitation of the resolution
pass, not something we introduce.

For our immediate goal (verifying Java code), this isn't blocking:
Java method calls are resolved by the Java compiler, and JVerify
emits the resolved method. We don't need Laurel's resolution to
handle method overriding — JVerify already knows which method is
being called.

If Laurel needs proper method dispatch later, the resolution pass
would need per-type method scopes (like it has for fields). That's
future work.
