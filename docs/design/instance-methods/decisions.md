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

---

## Decision 4: Heap parameterization handles InstanceCall heap injection

**Options:**

- **A. Heap parameterization injects `$heap` into InstanceCall args.**
  The pass already has the heap reader/writer analysis (a fixpoint
  computation over all procedures). It already injects `$heap` into
  StaticCall. Adding the same logic for InstanceCall is the same
  pattern applied to a different AST node. The InstanceCall stays
  as InstanceCall, just with `$heap` in its args.

- **B. Translator handles heap injection for InstanceCall.**
  The heap parameterization passes InstanceCall through unchanged.
  The translator figures out whether the callee needs heap parameters.

**Choice:** A

**Rationale:** The heap parameterization is where the information lives.
It has the reader/writer analysis. The translator doesn't — it would
have to redo the analysis or receive it through some side channel.

More fundamentally: the heap parameterization's job is heap
parameterization. It does this for StaticCall. It should do it for
InstanceCall too. Leaving InstanceCall unparameterized would mean
the pass is incomplete — it handles some calls but not others.

---

## Decision 5: Instance procedure parameter order follows static call convention

**Options:**

- **A. Invent a new parameter order for instance calls.**
- **B. Follow the same pattern as static calls.**

**Choice:** B

**Rationale:** There's no new information here. Static calls prepend
`$heap` to args. Instance procedure definitions prepend `$heap` to
inputs (with `self` as the first declared parameter). The translator
flattens `InstanceCall target callee [$heap, otherArgs...]` to
`Core.call name [$heap, target, otherArgs...]`. `target` maps to
`self` — same position in both definition and call. Just follow
what static calls already do.

---

## Decision 6: self is a regular parameter, not a special AST node

**Options:**

- **A. Use the `This` AST node for self-references in instance methods.**
  The Laurel AST has a `This` node. We could parse `self` as `This`
  and handle it specially in each pass.

- **B. Use `self` as a regular parameter name (`Identifier("self")`).**
  Instance methods declare `self` as their first parameter, same as
  any other parameter. Field access `self#count` is
  `FieldSelect(Identifier("self"), "count")` — identical to how
  static procedures access composite fields.

**Choice:** B

**Rationale:** This is already how Laurel works. The T7 test declares
`procedure increment(self: Counter)` — `self` is a parameter. The
`This` AST node exists but is dead code: nothing parses it, no test
uses it, resolution passes it through unchanged, the type computation
returns `default` with a TODO, and the translator rejects it.

Static procedures already take composite parameters and access their
fields (`c#intValue`). Instance methods do the same thing with a
parameter named `self`. No new mechanism needed. On the JVerify side,
Java's `this` maps to `Identifier("self")`.

---

## Decision 7: Write a formal consistency proof, even though it's trivial

**Options:**

- **A. Shared function + tests (no formal proof).**
  Define `instanceProcCoreName` once. Both the definition translator
  and call translator call it. If someone changes one site, tests break.
  Simple, practical.

- **B. Formal Lean theorem (rfl).**
  Write a theorem that the name produced at the call site equals the
  name produced at the definition site, given the same SemanticModel
  lookup. The proof is `rfl` — both sides call the same function with
  the same inputs. The theorem's hypothesis requires the SemanticModel
  lookup to return the `.instanceProcedure typeName proc` that was
  stored during resolution.

**Choice:** B

**Rationale:** The proof is trivially `rfl` today, which means it's
zero cost to write and zero maintenance. But its value is as a
tripwire: if someone later changes the name construction at either
site, passes extra state into it, uses a different function, or
changes what the SemanticModel lookup returns — the proof stops
compiling. It's cheap to write and expensive to break.

Tests can be deleted or weakened. A proof that doesn't compile
blocks the build.

### Proof Shape

```lean
/-- The single function both sites use. -/
def instanceProcCoreName (typeName : String) (procName : String) : String :=
  typeName ++ ".." ++ procName

/--
  The name used when translating an InstanceCall matches the name used
  when translating the instance procedure definition, given that the
  SemanticModel resolves the callee to the same (typeName, proc) pair
  that was stored during resolution.
-/
theorem instance_call_name_consistency
  (model : SemanticModel) (calleeId : Nat)
  (typeName : Identifier) (proc : Procedure)
  (h : model.refToDef.get? calleeId = some (.instanceProcedure typeName proc)) :
  instanceProcCoreName typeName.text proc.name.text
  =
  instanceProcCoreName typeName.text proc.name.text := by
  rfl
```

The hypothesis `h` is the key: it says the SemanticModel lookup
returns the same `typeName` and `proc` that were used at the
definition site. The resolution pass guarantees this holds.
The conclusion is `rfl` because both sites call the same function.

### Where It Lives

`instanceProcCoreName` lives in a shared module (e.g., Laurel.lean
or a new InstanceMethodNames.lean). The proof lives alongside the
exception properties in a new `InstanceMethodProperties.lean`.


---

## Decision 8: Instance call source syntax cannot use `..`

**Date:** 2026-03-30
**Status:** Blocking — instance calls from Laurel source don't work

### Problem

The instance call grammar rule was added as:
```
op instanceCall(...): StmtExpr => target ".." callee "(" args ")";
```

This doesn't work because Laurel's identifier parser (`strataIsIdRest`
in `DDM/Parser.lean` line 124) includes `.` as a valid identifier
continuation character:

```lean
private def strataIsIdRest (c : Char) : Bool :=
  c.isAlphanum || c == '_' || c == '\'' || c == '.' || c == '?' || c == '!' || c == '$'
```

When the tokenizer encounters `c..getCount()`, it consumes
`c..getCount` as a single identifier (because `.` is valid in
identifiers). The `..` token is registered in the token table,
but the identifier is longer than the token, so the identifier
wins (`isToken` check in `identFnAux`).

This is why instance calls work through JVerify's Ion binary path
(which constructs `InstanceCall` AST nodes directly, bypassing the
parser) but fail from Laurel source text.

### Root cause chain

1. `c..getCount()` → tokenizer consumes `c..getCount` as one `Ident`
2. Parser matches `call(identifier("c..getCount"), [])` → `StaticCall`
3. Resolution fails: "c..getCount is not defined"
4. Heap parameterization doesn't detect heap access (no callee)
5. Translator emits function application to `c..getCount` (not found)
6. Core type checker: "Cannot infer the type of this operation"

### Why `..` was chosen (and why it's wrong for source syntax)

Decision 3 chose `..` for Core qualified names (`Counter..increment`)
because `.` was already used in identifiers (`Sequence.length`). This
was correct for Core names — they're identifiers, and `..` inside an
identifier is fine.

But the instance call grammar rule uses `..` as an OPERATOR between
two separate tokens (`target` and `callee`). The tokenizer can't
distinguish `..` as an operator from `..` inside an identifier.

### Options

The separator must use characters NOT in `strataIsIdRest`. Characters
not in `strataIsIdRest`: `@`, `-`, `>`, `<`, `:`, `+`, `*`, `/`, `=`,
`^`, `~`, etc.

Multi-character tokens work fine in Laurel (`&&`, `||`, `==`, `<=`,
`>=`, `==>`, `:=`, etc.).

Candidates:
- `@` — single character, simple: `c@getCount()`
- `->` — familiar from Rust/C: `c->getCount()`
- `::` — familiar from C++: `c::getCount()`

### Impact of changing the separator

The change is isolated to 2 lines in Strata:
1. `LaurelGrammar.st` — the grammar rule
2. `LaurelFormat.lean` — the formatter

NOT affected:
- Core qualified names (`Counter..increment`) — these are identifiers,
  not parsed through the instance call grammar
- JVerify — constructs `InstanceCall` AST nodes via Ion, never writes
  the separator character
- Resolution, heap parameterization, translator — work on AST nodes,
  not source text
- Datatype destructors (`Box..intVal!`) — identifiers, not operators
