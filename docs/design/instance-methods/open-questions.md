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

## Q7: What about instance methods calling other instance methods?

If `Counter.increment` calls `Counter.reset` internally, the body
of `increment` contains an `InstanceCall` to `reset`. After heap
parameterization, does this work? The callee `reset` needs to be
recognized as a heap writer, and the call needs heap parameter
injection. This is the same as Q4 but for intra-composite calls.

## Q8: What about inherited instance methods?

If `Extender extends Base` and `Base` has instance method `foo`,
can `Extender` objects call `foo`? The resolution pass builds
type scopes with inherited fields. Does it also inherit instance
procedures? If not, calls to inherited methods won't resolve.
