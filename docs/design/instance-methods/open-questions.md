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

## Q4: Heap analysis for InstanceCall callees

The heap analysis phase does NOT add `InstanceCall` callees to the
`callees` list (line 62 of HeapParameterization.lean). This means
if procedure A calls instance method B that writes the heap, A won't
know it needs `$heap` as a parameter.

Fix seems straightforward: add callee to `callees` list. But the
callee name must match the instance procedure's name as it appears
in the analysis. Need to verify the names align.

## Q5: Modifies clauses for instance procedures

The modifies clauses transform only processes `staticProcedures`.
Instance procedures with `modifies self` won't get frame conditions.

Options:
- a. Also iterate instance procedures from composites
- b. Handle modifies in the translator for instance procedures
- c. Promote instance procedures to staticProcedures just for
     this pass (but this contradicts Decision 1)

## Q6: What does the consistency proof look like concretely?

We decided to prove name consistency (Decision 2, Option C). The
sketch is:

```lean
def instanceProcCoreName (typeName : String) (procName : String) : String :=
  typeName ++ ".." ++ procName
```

Both the definition translator and call translator use this function.
The proof is trivially `rfl`. But:
- Where does this function live? (Shared module?)
- How do we enforce that both sites actually call it?
  (The proof checks this, but do we need a lint/test too?)
- Should the proof be a `#check` or a full `theorem`?

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
