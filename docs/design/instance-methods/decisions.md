# Instance Method Support: Decisions

**Date:** 2026-03-26

---

## Decision 1: What happens to InstanceCall as it moves through the pipeline?

When Laurel parses `target.method(args)`, it creates an `InstanceCall` node.
This node passes through 5 transforms before reaching the translator.
The question: does it stay as `InstanceCall`, or get converted to something else?

**Options:**

- **A. Convert InstanceCall → StaticCall early (in heap parameterization).**
  The heap parameterization pass already transforms `FieldSelect` into
  `StaticCall("readField", ...)`. We could similarly convert
  `InstanceCall target callee args` into
  `StaticCall("Counter..increment", target :: args)`. All downstream
  passes (type hierarchy, modifies, translator) already handle StaticCall,
  so no further changes needed. This is the fewest lines of code.

- **B. Keep InstanceCall through all passes, flatten in translator only.**
  Each pass that encounters InstanceCall handles it natively (recursing
  into target and args, injecting heap params as needed). The translator
  is the single place where InstanceCall becomes a Core `call`.

**Choice:** B

**Rationale:** Option A is tempting because it's less code — downstream
passes already handle StaticCall. But it scatters the instance method
translation across two places: the heap parameterization constructs the
qualified name, and the translator emits the Core call. If we later want
to prove the translation is correct, we'd need to reason across both passes.

With Option B, the name mapping lives in exactly one place (the translator).
This makes it easier to prove consistency (see Decision 2) and easier to
audit. Each pass does need an InstanceCall case, but those cases are
mechanical (recurse into children, same as the existing patterns).

We also considered that keeping the semantic distinction visible is
valuable — if a future pass needs to treat instance calls differently
from static calls (e.g., for virtual dispatch), Option A would have
erased that information.

---

## Decision 2: How do we know the translation is correct?

The translator maps instance procedure definitions to Core procedures,
and instance calls to Core calls. How do we verify these match?

**Options:**

- **A. Rely on Core type-checking.**
  The Core type checker already validates that every `call` references
  an existing procedure with matching arity and types. This catches
  many bugs for free. But it can't distinguish "calls the right procedure"
  from "calls a different procedure that happens to have a compatible
  signature." If `Counter..increment` and `Timer..increment` both take
  `(Composite) → ()`, a mixup wouldn't be caught.

- **B. Prove translator correctness in Lean.**
  Write a theorem: "If the Laurel program has InstanceCall resolving to
  procedure P, the translator produces a Core call to the procedure that
  P was translated to, with correct arguments in correct order." This is
  the strongest guarantee. But we haven't proven any part of the translator
  correct — not even static calls. The translator is imperative Lean code
  with monadic state, and reasoning about it formally is research-level work.

- **C. Prove a name consistency property.**
  Define a single pure function `instanceProcCoreName(typeName, procName)`
  that both the definition translator and the call translator use. Prove
  they call the same function. This doesn't prove argument order or
  semantic preservation, but it proves the call hits the right procedure.
  Combined with Core type-checking (A), arity and type mismatches are
  also caught.

**Choice:** C (with A as baseline, B as future goal)

**Rationale:** We debated whether C is "enough." It doesn't prove
everything — argument order could still be wrong. But Core type-checking
(A) catches arity/type mismatches, and our test suite exercises the full
pipeline. The combination of C + A + tests gives reasonable confidence.

Option B is the right long-term answer, but attempting it now would be a
significant detour. We agreed: if empirical testing reveals bugs that C
wouldn't have caught, that's the signal to invest in B.

---

## Decision 3: How are instance procedures named in Core?

Core doesn't have instance methods — just procedures with names. We need
a naming convention that avoids collisions and is consistent.

**Options:**

- **A. Unqualified name (e.g., `increment`).**
  Simple, but collides immediately. The heap constants already define a
  function called `increment` (for heap allocation). We hit this exact
  bug during investigation — the Counter's `increment` collided with
  the heap's `increment`.

- **B. Qualified with `..` separator (e.g., `Counter..increment`).**
  Follows the existing convention for datatype destructors (`Color..isRed`,
  `Heap..data!`, `Box..intVal!`). Unlikely to collide since composite
  type names are unique.

- **C. Use resolution unique IDs instead of names.**
  Every resolved identifier has a unique numeric ID. We could use that
  as the Core procedure name. No collision possible. But Core procedure
  names become opaque numbers, making debugging and error messages
  unreadable.

**Choice:** B

**Rationale:** Option A is broken (we proved it by hitting the collision).
Option C works but sacrifices readability. Option B follows established
convention, is human-readable, and the `..` separator is already used
throughout the codebase. A single pure function constructs the name,
which is what Decision 2 relies on for the consistency proof.

The key insight: an instance procedure is defined on the composite TYPE,
not on any particular instance. There is one `Counter..increment` for all
Counters. When you call `myCounter.increment()` vs `yourCounter.increment()`,
you're calling the same procedure — the difference is the value of `self`
passed as a parameter. After heap parameterization, `self` is a `Composite`
reference and field access goes through `readField($heap, self, field)`.
Different instances have different references, so they read different heap
locations, but the procedure body is identical.

The prover proves properties about `Counter..increment` that hold for ALL
counters: "for any self and any heap, if the precondition holds, then after
executing the body, the postcondition holds." We don't need per-instance
names because we're proving universal properties. The `Counter..` prefix
distinguishes between different TYPES (Counter vs Timer), not different
instances of the same type.
