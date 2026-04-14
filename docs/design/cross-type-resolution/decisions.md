# Cross-Type Instance Call Resolution: Design Decisions

**Date:** 2026-04-11
**Status:** Proposed

## Context

Range.compareTo calls Position.compareTo. Both are instance
procedures named `compareTo` on different composite types. The
Laurel resolution pass uses a global name-based scope, so the
second `compareTo` registered shadows the first. When Range's
body calls `start().compareTo(o.start())`, resolution resolves
`compareTo` to Range's own (the last one registered), not
Position's.

This causes two failures:
1. The translator generates `Range..compareTo` instead of
   `Position..compareTo` at the call site
2. The heap parameterization crashes ("output length and lhs
   length mismatch") because the wrong procedure's signature
   is used for output arity

The Java frontend knows the correct target — javac resolves
every method call. But the frontend emits only the unqualified
name `"compareTo"` as the callee. The type information is lost
at the Java frontend → Laurel AST boundary. The resolution pass
then re-resolves in the global scope and gets the wrong answer.

The existing instance methods design (Q8) identified this
shadowing limitation and said "not blocking" because "JVerify
already knows which method is being called." That was true for
single-composite programs. It's false for Range calling Position.

---

## Decision 1: Should Laurel model method dispatch?

### Context

The resolution pass is currently doing method dispatch — deciding
which procedure an `InstanceCall` targets by looking up the
callee name in a global scope. The question is whether this is
the right layer for dispatch to happen.

Dispatch rules are language-specific. Java uses static dispatch
based on the compile-time type of the receiver. Python uses
dynamic dispatch via the Method Resolution Order (MRO), a C3
linearization of the class hierarchy. JavaScript uses prototype
chain delegation, where the chain itself is mutable at runtime.
Even within Java, interface calls introduce limited dynamic
dispatch — `Comparable.compareTo()` could target Position, Range,
or any other implementor.

These are fundamentally different algorithms. If Laurel's
resolution pass does dispatch, it has to pick one algorithm or
be parameterized by a dispatch strategy.

### Option A: Laurel models dispatch

The resolution pass (or a new dispatch pass) determines which
procedure each `InstanceCall` targets. The pass would need to
be parameterized by the source language's dispatch rules, or
Laurel would need a dispatch model general enough to cover
Java, Python, JavaScript, etc.

- Pro: The frontend is simpler — it emits unqualified calls and
  Laurel figures out the target. All dispatch logic is in one
  place (Strata), provable in Lean.
- Con: Laurel becomes language-aware. The dispatch model must
  handle Java's static dispatch, Python's MRO, JavaScript's
  prototype chains, and whatever comes next. This is a large
  design surface that grows with every new language. It bakes
  language-specific semantics into a language-agnostic IR.

### Option B: The frontend resolves dispatch, Laurel preserves it

The frontend knows the language's dispatch rules. For static
dispatch (most calls in Java and Python), the frontend resolves
the call to a specific target and tells Laurel which procedure
to call. For dynamic dispatch (interfaces, prototypes), the
frontend generates explicit dispatch logic as verifiable Laurel
code using Laurel's existing primitives (conditionals, type
checks, procedure calls). Laurel doesn't do dispatch — it
carries the frontend's answer through faithfully.

- Pro: Laurel stays language-agnostic. Each frontend handles
  its own language's dispatch rules. Adding a new language
  doesn't change Laurel. Dynamic dispatch becomes verifiable
  code — the prover can reason about dispatch tables, prototype
  chains, or MRO logic because it's ordinary Laurel code, not
  hidden infrastructure.
- Con: Every frontend must resolve dispatch independently.
  The trust boundary includes the frontend's dispatch
  resolution — if the frontend resolves incorrectly, Laurel
  won't catch it. For dynamic dispatch, the frontend must
  generate dispatch code, which is more work.

### Decision: Option B

Dispatch is a language concern, not an IR concern. Laurel should
not model dispatch. The frontend resolves static dispatch and
provides the answer. For dynamic dispatch, the frontend generates
explicit dispatch logic as Laurel code that the prover can verify.

This matches the existing trust architecture: Java→Laurel is a
structural mapping (validated by testing), Laurel→Core is a
semantic transformation (proven in Lean). Dispatch resolution is
part of the structural mapping — the frontend knows the language,
the IR preserves the answer.

---

## Decision 2: How does the frontend communicate the resolved target?

### Context

Given Decision 1 (the frontend resolves dispatch), the frontend
needs a way to tell Laurel which procedure an `InstanceCall`
targets. Currently the frontend emits only the unqualified callee
name. We need to carry the owner type through.

Dispatch is a pattern that the frontend composes from Laurel's
existing primitives. For static dispatch (the common case), the
pattern collapses to a direct call — the frontend just needs to
say which procedure. For dynamic dispatch, the pattern is
explicit Laurel code (conditionals, type checks, calls) that
eventually bottoms out at direct calls. In both cases, the
minimal thing Laurel needs is the ability to say "this call goes
to this specific procedure on this specific type."

Note: `InstanceCall` must remain as a distinct AST node (not
collapsed into `StaticCall`) because it marks the receiver
object — the heap parameterization pass needs to know which
argument is `self` for heap threading.

### Option A: Qualify the callee name in the frontend

The frontend emits `InstanceCall(target, "Position..compareTo", args)`
instead of `InstanceCall(target, "compareTo", args)`. The callee
string is already qualified with the owner type using the `..`
separator (a Strata convention from instance methods Decision 3).

- Pro: No Strata AST changes. No Ion format changes. Resolution
  just needs to handle qualified names in `resolveRef`. The
  qualified name matches the Core procedure name, so the
  translator can use it directly.
- Con: Couples the frontend to the `..` naming convention. If
  the convention changes, every frontend must change. The Laurel
  AST carries a Strata-internal encoding.

### Option B: Add owner type field to InstanceCall AST node

Extend `InstanceCall` to carry the owner type:
`InstanceCall target callee ownerType args`. The frontend emits
`InstanceCall(target, "compareTo", "Position", args)`. Resolution
uses `ownerType` to look up the correct instance procedure in
that type's scope.

- Pro: Clean separation. The AST carries semantic information
  without encoding it in a naming convention. The `ownerType`
  field is the frontend's statement of "I resolved dispatch to
  this type." Other frontends populate it from their own type
  systems. The naming convention stays in the translator.
- Con: Requires a Strata grammar change (new field on
  `InstanceCall`). Every pass that handles `InstanceCall` needs
  to carry the new field. The Ion serialization format changes.
  The Laurel text parser needs to handle it.

### Option C: Type-directed resolution in the resolution pass

Don't change the AST or the frontend. Teach the resolution pass
to infer the target's type from the expression and use it to
look up the correct instance procedure.

- Pro: No AST changes. No frontend changes. Fix is entirely
  within Strata.
- Con: This puts dispatch back in Laurel, which contradicts
  Decision 1. The resolution pass would need expression type
  inference, which it doesn't have today. It works for Java's
  static dispatch but not for dynamic dispatch languages.

### Decision: Option A

Option A is the simplest mechanism that solves the problem. It
works for static dispatch (Java, Python) and extends to dynamic
dispatch (interfaces, abstract methods) through the same pattern:
the frontend generates explicit dispatch code (conditionals, type
checks) where each branch bottoms out at a direct call with a
qualified name.

Options A and B are equivalent in expressiveness. Both require
the frontend to know the target type at code-generation time.
For truly dynamic dispatch (runtime-determined types), both
require the frontend to enumerate possible types and generate a
branch per type. The dispatch table pattern is the same
regardless of whether the type is carried as a qualified name
(A) or a structured field (B).

The difference is ergonomics: A is a string convention, B is a
structured AST field. B would be better if a Laurel pass needed
to inspect the owner type programmatically — with A, the pass
would have to parse the qualified name; with B, it's a field.
But no pass currently needs this. The translator uses the
qualified name directly as the Core procedure name.

We choose A because:
1. It solves the immediate problem (Range calling Position)
2. It requires no Strata AST, grammar, or Ion format changes
3. It extends to interface dispatch and abstract methods
4. If we later need programmatic access to the owner type
   (e.g., for a truly dynamic dispatch primitive), we can
   move to B at that point — the proof structure we build
   around A will make the migration path clear

Per Decision 9 in `instance-methods/decisions.md`, the
separator is `~>` (not `..`). The frontend emits:
`InstanceCall(target, "Position~>compareTo", args)`.

---

## Decision 3: How do we verify that the frontend correctly expresses language semantics?

### Context

Decisions 1 and 2 establish that the frontend is responsible for
dispatch — and more broadly, for expressing the source language's
semantics in Laurel. Dispatch is the instance we hit today, but
the same question applies to everything the frontend translates:
field access, exception handling, loop semantics, integer
overflow, null handling. Every piece of Java semantics that gets
expressed in Laurel raises the same question: **how do we know
the Laurel code means what the Java code means?**

This is a fundamental problem of this IR and this modality. Any
language that targets Laurel — Java, Python, JavaScript, whatever
comes next — must express its semantics in Laurel. And we need
to be able to verify that expression is correct.

There are two sub-problems:

**A. "Did I write down the right specification?"** You formalize
Java's dispatch rules as a Lean predicate. You prove JVerify
implements it. But what if the predicate is wrong — what if it
doesn't match what Java actually does? This is fundamentally
empirical. You can't prove a formal spec matches a natural-
language standard (the JLS). You can only test it against real
Java programs and look for discrepancies.

**B. "Does my translation implement my specification?"** Given a
formal spec (however you arrived at it), does the Laurel code
that JVerify generates satisfy it? This is provable. The spec is
a predicate on Laurel ASTs. The translation is a function from
Java ASTs to Laurel ASTs. You prove the function's output
satisfies the predicate.

The feedback loop: when a real Java program behaves differently
than what the verified pipeline predicts, the bug is in the
formal spec (because the translation and pipeline are proven
correct relative to the spec). You update the spec, which breaks
the translation proof, which tells you exactly what in the
translation needs to change.

### Option A: Testing only (current approach)

Validate the frontend's translation with end-to-end tests and
differential tests. No formal specification of language
semantics. Trust that the test suite covers enough cases.

- Pro: No new infrastructure. Already working. Fast to iterate.
- Con: Tests can miss edge cases. A subtle translation bug
  could produce unsound proofs that no test catches. No formal
  artifact that says "this is what we believe Java dispatch
  means." When a bug is found, there's no systematic way to
  determine whether it's a translation bug or a spec bug.

### Option B: Formal spec as Lean predicates, proven translation

Define formal specifications of language semantics as Lean
predicates on Laurel ASTs. For each language feature (dispatch,
exceptions, field access, etc.), write a predicate that says
"this Laurel code correctly implements this Java feature." Prove
that JVerify's translation satisfies the predicate.

The spec for Java static dispatch might look like:

```
-- "An InstanceCall on a target of type T to method M
--  resolves to the procedure T..M"
def correctStaticDispatch (call : StmtExpr) (targetType : String)
    (methodName : String) : Prop :=
  call.ownerType = targetType ∧
  call.callee = methodName
```

The spec for Java interface dispatch (future) might look like:

```
-- "A dispatch block for interface method M covers all
--  implementors and each branch calls the correct procedure"
def correctInterfaceDispatch (block : StmtExpr)
    (interfaceName : String) (methodName : String)
    (implementors : List String) : Prop :=
  ∀ impl ∈ implementors,
    ∃ branch ∈ block.branches,
      branch.typeCheck = impl ∧
      branch.call = impl ++ ".." ++ methodName
```

Empirical testing validates that the spec matches the JLS.
Lean proofs validate that the translation satisfies the spec.

- Pro: Formal artifact for each language feature. When a bug is
  found, you can determine whether the spec or the translation
  is wrong. The proof breaks when the translation changes,
  forcing the spec to be updated. This is the CompCert/CakeML
  architecture.
- Con: Significant upfront investment. Requires formalizing
  language semantics, which is research-level work for a full
  language. Must be done incrementally, feature by feature.

### Option C: Incremental specs, starting with dispatch

Don't try to formalize all of Java semantics at once. Start with
the feature that's broken (dispatch). Write a formal spec for
Java static dispatch. Prove JVerify's translation satisfies it.
Test the spec against real Java programs. Then move to the next
feature (exceptions, field access, etc.) as each one becomes a
verification target.

Each feature gets:
1. A formal spec (Lean predicate on Laurel AST)
2. A proof that the translation satisfies the spec
3. Empirical tests that the spec matches the language standard

Over time, the collection of specs becomes a formal model of
the source language's semantics — built incrementally, driven
by what we actually need to verify.

- Pro: Incremental. Each spec is independently valuable. Driven
  by real verification needs, not abstract completeness. The
  dispatch spec is small and immediately useful.
- Con: Incomplete coverage until all features are specified.
  Features without specs rely on testing only.

### Decision: Option C

Build formal specs incrementally, driven by what we need to
verify. Dispatch is the first spec because it's the feature
that's broken. Each spec is a Lean predicate on the Laurel AST,
proven to be satisfied by the translation, and empirically
tested against real programs. Features without specs rely on
testing until they become verification targets.

---

## Decision 4: How does the heap analysis work with qualified callee names?

### Context

Decision 2 chose qualified callee names: the frontend emits
`InstanceCall(target, "Position~>compareTo", args)`. But
instance procedure *definitions* use unqualified names — the
procedure is defined as `compareTo` on the `Position` composite.

The heap analysis (`computeReadsHeap`/`computeWritesHeap`) builds
its reader/writer lists from procedure definitions using `p.name`
— the unqualified name. The heap transform then checks
`heapReaders.contains callee` at call sites. After D2, the
callee is `"Position~>compareTo"` but the list contains
`"compareTo"`. The `contains` check fails — the qualified name
doesn't match the unqualified name.

This means the heap transform would stop injecting `$heap` into
instance calls, breaking heap threading entirely.

### Option A: Qualify procedure definition names too

Before the heap analysis runs, qualify all instance procedure
names in their definitions: `compareTo` → `Position~>compareTo`.
The analysis builds lists with qualified names. The call site
lookup matches.

- Pro: Names match everywhere. No special-case logic. The
  qualification is a simple pre-pass over composites.
- Con: Changes the program structure. Every downstream pass
  sees qualified names on definitions. The translator already
  qualifies names via `instanceProcCoreName` — this would be
  a second, earlier qualification. Need to ensure they agree.

### Option B: Extract the method name from the qualified callee

When the heap transform checks `readsHeap callee`, extract the
method name from the qualified callee: `"Position~>compareTo"`
→ `"compareTo"`. Look up the unqualified name in the
reader/writer lists.

- Pro: Minimal change. The analysis stays the same. Only the
  lookup at call sites changes. One helper function that strips
  the qualifier.
- Con: The lookup is imprecise — it matches ANY `compareTo`,
  not specifically Position's. But this is the same
  conservatism the analysis already has (it treats all
  same-named procedures as one). No loss of precision.

### Option C: Build the heap analysis from qualified names

Change `computeReadsHeap`/`computeWritesHeap` to use qualified
names. When iterating instance procedures, construct the
qualified name (`typeName~>procName`) and use that as the key.
Call sites use the same qualified name. Exact match.

- Pro: Precise. Each procedure has a unique key. No
  conservatism from name collisions.
- Con: More changes to the analysis. The `collectExpr` function
  that gathers callees from procedure bodies would also need to
  produce qualified names for `InstanceCall` callees. This
  requires knowing the owner type during body analysis, which
  the analysis doesn't currently track. Qualification happens
  in two places (heap analysis and translator) — same
  duplication that instance methods Decision 2 warned about.

### Decision: Option A

Qualify instance procedure definition names early, before the
heap analysis runs. One qualification, used everywhere. The
translator no longer needs to qualify names itself — they're
already qualified.

This makes the proof surface larger (more things change) but
simpler (each change is mechanical). The existing translator
proofs will break because the names changed — but updating
string comparisons is a mechanical task. Option B would
introduce a new stripping function into the proof chain,
requiring new reasoning at every call site about the
correctness of the stripping. Option A avoids that entirely.

For a project building toward full pipeline proofs, making
proofs mechanically updatable is more valuable than minimizing
the number of lines changed.

---

## Decision 5: What proof obligations does this create?

### Context

The existing IM1 proof has the hypothesis:

```
model.refToDef.get? calleeId =
    some (.instanceProcedure typeName proc)
```

This says "the SemanticModel maps the callee ID to the correct
(typeName, proc) pair." Nobody proved this hypothesis holds for
cross-type calls. Whatever solution we choose needs to make this
hypothesis provable.

### Option A: Prove resolution correctness

Prove: "when the resolution pass resolves an `InstanceCall`
callee, the returned ID maps to the correct `(typeName, proc)`
pair — the one belonging to the owner type, not a shadowing
type."

- Pro: Closes the gap. IM1 becomes end-to-end.
- Con: Requires formalizing "correct owner type" as a Lean
  predicate. The definition of "correct" depends on the
  mechanism chosen in Decision 2.

### Option B: Prove preservation (frontend provides, Laurel preserves)

If the frontend provides the resolved target (Decision 2),
prove: "Laurel faithfully carries the frontend's resolved target
through all passes to Core." The correctness of the dispatch
resolution itself is validated per Decision 3.

The Lean proof becomes: "if the callee is
`Position~>compareTo` at the Laurel AST level, the pipeline
preserves this and the translator generates
`Position~>compareTo` in Core."

- Pro: Simpler Lean proof — preservation, not dispatch
  correctness. Matches the existing trust architecture.
- Con: Trust boundary includes the frontend. Mitigated by
  Decision 3 (formal spec + empirical testing).

### Option C: Prove non-interference (document the limitation)

Prove: "if all instance procedure names are globally unique,
the current resolution is correct." This documents the
limitation without fixing it.

- Pro: No changes needed. Proof documents the precondition.
- Con: Doesn't fix the problem. Range and Position both have
  `compareTo`. The precondition doesn't hold.

### Decision: Option B

Laurel's proof obligation is preservation, not dispatch
correctness. The frontend provides the resolved target (D2).
Laurel proves it delivers that target faithfully to Core.
Whether the frontend chose the right target is the frontend's
concern, verified by the incremental formal specs (D3).

This matches the architecture established by D1: dispatch is a
language concern. Laurel doesn't decide what's correct — it does
what it's told and proves it did so faithfully. Option A would
have Laurel proving dispatch correctness, which contradicts D1.
Option B is the proof obligation that matches our trust
architecture.

The composition:
- D3: JVerify satisfies the Java dispatch spec (proven + tested)
- D5 B: Laurel preserves what JVerify provides (proven in Lean)
- Together: end-to-end from Java dispatch rules to Core

---

## Decision 6: What is the implementation order?

### Option A: Implement first, prove after

1. Implement the fix (from Decisions 2 and 4)
2. Verify Range.compareTo passes
3. Write the dispatch spec (Decision 3)
4. Prove the property (Decision 5)

- Pro: Unblocks Range quickly.
- Con: Fix might be wrong without proof guidance.

### Option B: Prove first, implement after

1. Write the dispatch spec (Decision 3)
2. Formalize the property (Decision 5)
3. Implement to satisfy the property
4. Prove it

- Pro: Proof guides implementation.
- Con: Slower. May be blocked by missing infrastructure.

### Option C: Implement and prove in parallel

1. Implement the simplest fix that unblocks Range
2. In parallel, write the dispatch spec and formalize the
   preservation property
3. Iterate if the proof reveals issues

### Decision: Option C

Implement and prove in parallel. The implementation unblocks
Range testing. The proof work builds on the existing translator
proof infrastructure. If the proof reveals issues with the
implementation, iterate.

---

## Resolved Questions

### RQ1: Multiple resolution passes (was OQ2)

The pipeline runs `resolve` four times. The qualification
pre-pass (D4) must run BEFORE the first `resolve` call. It
renames instance procedure definitions to qualified names.
Then `preRegisterTopLevel` registers `"Position~>compareTo"`
and `"Range~>compareTo"` as separate scope entries. No
shadowing. Re-resolution preserves the qualified names because
they're already in the scope.

### RQ2: Self-calls within the same type (was OQ3)

Works naturally. Range calling itself: the frontend emits
`InstanceCall(self, "Range~>compareTo", args)` — resolves to
Range's procedure. Range calling Position: the frontend emits
`InstanceCall(target, "Position~>compareTo", args)` — resolves
to Position's procedure. Different qualified names, no ambiguity.

### RQ3: Pre-registration phase (was OQ4)

With D4 (qualify definitions early), `preRegisterTopLevel`
registers `"Position~>compareTo"` and `"Range~>compareTo"` as
separate scope entries. No overwriting. Problem solved.

### RQ4: `methodSym.owner` for inherited methods (was OQ1)

`methodSym.owner` returns the declaring class — the class where
the method is actually written. For inherited methods, this is
the superclass. For overridden methods, this is the overriding
class. Both are correct for our purposes: the declaring class
is the composite that has the instance procedure in Laurel.

Closed. Validated by the dispatch test suite (see Testing below).

---

## Open Questions

### OQ1: Dynamic dispatch code generation

Future work. The frontend generates dispatch tables as Laurel
code for interface/abstract dispatch. Each branch is a direct
call with a qualified name. The prover verifies the dispatch
logic as ordinary code. What does this look like concretely?

---

## Testing

The frontend qualification (`methodSym.owner + "~>" + name`)
must be validated with a series of dispatch tests covering
increasingly complex scenarios:

1. **Direct call, same type:** `this.method()` inside an
   instance method — owner is the current class
2. **Direct call, different type:** `pos.compareTo(other)`
   where `pos` is a different composite — owner is the
   target's type (the current bug fix)
3. **Inherited method, no override:** `child.parentMethod()`
   where the method is declared on the parent — owner should
   be the parent class
4. **Inherited method, with override:** `child.method()` where
   the child overrides — owner should be the child class
5. **Chained calls:** `a.getB().method()` — owner of `method`
   is B's type, not A's
6. **Self-call to own method:** `this.compareTo()` inside
   Range — owner is Range, not Position
7. **Cross-type in same hierarchy:** Range calls
   Position.compareTo where both have compareTo — owner
   must be Position for the cross-type call

Each test verifies the qualified callee name in the emitted
Laurel AST. Tests 1-2 and 6-7 are needed immediately. Tests
3-5 are needed when inheritance support (F13) lands.

---

## Implementation Summary

Given all decisions, here's what needs to change:

### Strata changes (this belongs in Strata)

1. **Separator change (Decision 9, instance-methods):**
   `instanceProcCoreName` uses `~>` instead of `..`.

2. **Early qualification pre-pass (D4):**
   Before `heapParameterization` runs, a new pass qualifies
   instance procedure names on their definitions:
   `proc.name` → `"TypeName~>procName"` for each instance
   procedure on each composite. This runs once, before the
   first `resolve` call.

3. **Resolution handles qualified names (OQ2):**
   `preRegisterTopLevel` registers instance procedures under
   their qualified names. `resolveInstanceProcedure` uses the
   qualified name. `resolveRef` finds them by qualified name.

4. **Translator simplification:**
   `translateProcedure` for instance procedures no longer needs
   to call `instanceProcCoreName` to construct the name — it's
   already qualified on the definition. The translator just uses
   `proc.name.text` directly.

5. **Heap parameterization:**
   `computeReadsHeap`/`computeWritesHeap` now see qualified
   names on definitions. Call sites also use qualified names.
   The `contains` check matches. No stripping needed.

### Frontend changes

6. **Frontend qualification (D2):**
   The frontend qualifies instance call callee names with the
   owner type using the `~>` separator. See the frontend's own
   design doc for implementation details.
   (`jverify/design/cross-type-resolution/README.md`)


## D7: Type scope ordering for cross-composite field access

**Date:** 2026-04-14
**Status:** Implemented

### Problem

D1-D6 solved cross-type *procedure call* resolution (Range calling
Position.compareTo). But cross-type *field access* in postconditions
still failed. `start().line()` in Range's postcondition compiles to
`FieldSelect(FieldSelect(self, "start"), "line")`. Resolution needs
Position's type scope to resolve `line`, but type scopes were built
incrementally in `resolveTypeDefinition` — if Range was processed
before Position, Position's type scope didn't exist yet.

### Decision

Pre-build all type scopes in `preRegisterTopLevel`, extending the
existing two-phase design. This is consistent with the design intent
("declaration order doesn't matter") and provides a clean invariant
for soundness proofs: all type scopes are populated before any
procedure body is resolved.

Alternatives considered:
- **Lazy scope building:** build on demand in `resolveFieldInTypeScope`.
  Harder to prove properties about. Deferred as a potential optimization.
- **Declaration reordering:** fragile, doesn't generalize.

### Details

See `type-scope-ordering.md` in this directory for the full design
document including implementation details and the invariant statement.
