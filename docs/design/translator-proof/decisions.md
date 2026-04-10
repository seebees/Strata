# Translator Pipeline Proofs: Decisions

**Date:** 2026-04-10
**Status:** Proposed

## D1: Proof approach — model equivalence vs direct pipeline properties

**Context:** We want mechanical assurance that the translate pipeline
is correct and that new features are completely implemented across
all passes. The first attempt was to build a pure functional model
of `translate` and prove `translate ≡ translateProgramModel`. This
required building and maintaining a parallel implementation of the
entire pipeline, then proving the two agree.

### Option A: Model equivalence (the current approach)

Build a pure functional model that captures the end-to-end effect
of the ~10-pass pipeline in a single function. Prove the real
pipeline produces the same output as the model. Properties proven
about the model then transfer to the pipeline via the equivalence
proof.

- Pro: Once proven, you get ALL properties of the model for free.
  The model serves as both spec and reference implementation.
- Con: The model itself had many discrepancies (D6 in translator-model
  decisions). The equivalence proof is enormous — 7 categories,
  most still `sorry`. The model must track every pipeline change,
  creating a maintenance burden that scales with feature velocity.
  Adding a feature means changing both the pipeline AND the model,
  then re-proving equivalence. The first week of proof work found
  zero discrepancies; the first day of differential testing found 11
  discrepancies.

### Option B: Direct properties on the pipeline

Prove properties directly against the real pipeline passes. Each
pass gets a property file that states what the pass guarantees.
No model needed — the properties ARE the spec.

- Pro: No parallel implementation to maintain. Properties are
  incremental — add one at a time, each independently valuable.
  Lean's exhaustiveness checker enforces that every `StmtExpr`
  constructor is handled when a property pattern-matches on it.
  This is the core value: adding a new constructor breaks every
  incomplete proof. Properties compose — pass A's postcondition
  is pass B's precondition.
- Con: You only get the properties you state. If you don't write
  a property, you don't get the guarantee. Requires equation
  lemmas or `@[expose]` to reason about pass internals from
  external proof files.

### Option C: Hybrid — model as spec, properties on pipeline

Keep the model as a specification document but don't prove
equivalence. Prove properties directly on the pipeline. Use the
model's structure to guide which properties to state. Differential
tests validate that the pipeline matches the model on concrete
inputs.

- Pro: Gets the best of both — the model documents intent, the
  properties provide guarantees, the tests catch bugs.
- Con: The model drifts from the pipeline over time if not
  maintained. Two sources of truth.

### Decision: Option B (direct properties on the pipeline)

The model served its purpose — differential testing between the
model and the pipeline surfaced many discrepancies and established
the 7-category decomposition that clarified the pipeline's
structure. But the equivalence proof is not the right investment.
The model is a liability: every pipeline change requires a
corresponding model change, and the model itself is a source of
discrepancies (most were model bugs, not pipeline bugs).

Direct properties give us the specific guarantee we need: when a
feature is added to the pipeline, the proofs enforce that it's
handled completely. This is the "looks complete but isn't" problem
that motivated this work. Lean's exhaustiveness checker is the
mechanism — a new `StmtExpr` constructor creates a new proof
obligation in every property that matches on statements.

The differential tests remain as the primary discrepancy-finding tool.
The properties are the regression guarantee.

---

## D2: Model deprecation

**Context:** Given D1 (direct properties instead of model
equivalence), what happens to the existing model infrastructure?

### Option A: Keep everything

Keep `TranslatorModel.lean`, `TranslatorEquivalence.lean`,
`TranslatorModelProof.lean`, and all 118 differential tests.

- Pro: No work to remove anything. The model remains as
  documentation.
- Con: Maintenance burden. Every pipeline change that touches
  translation output risks breaking differential tests. Two
  parallel implementations to understand.

### Option B: Keep tests, deprecate model and equivalence proofs

Keep `TranslatorModelTest.lean` (the 118 differential tests).
Deprecate `TranslatorModel.lean`, `TranslatorEquivalence.lean`,
`TranslatorModelProof.lean`. Mark them as deprecated with a
comment pointing to the new property files.

- Pro: Tests continue finding discrepancies. No model maintenance.
  Clear signal that the property approach is the path forward.
- Con: Differential tests depend on the model (they compare
  pipeline output to model output). Deprecating the model
  eventually means rewriting or removing the tests.

### Option C: Keep interesting test programs, deprecate everything else

Extract the test programs (the Laurel source strings) from
`TranslatorModelTest.lean` into standalone test files. These
become pipeline-only tests (run `translate`, check for errors,
verify against expected output). Deprecate the model, equivalence
proofs, and differential test infrastructure.

- Pro: Cleanest end state. Test programs preserved. No model
  dependency.
- Con: More work upfront to extract and restructure tests.
  Loses the structural comparison (model vs pipeline) — but
  the pipeline properties replace that guarantee.

### Decision: Option B now, Option C eventually

Keep the differential tests — they're the best discrepancy-finding tool
we have. Deprecate the model and equivalence proofs. As the
pipeline property coverage grows and the model falls behind,
transition to Option C: extract the interesting test programs
into standalone pipeline tests and remove the model entirely.

The trigger for the transition: when maintaining the model for
differential tests costs more than the discrepancies it finds.

---

## D3: Proof granularity — per-pass vs end-to-end

**Context:** The translate pipeline is a sequential composition
of passes:

```
Laurel → resolve → constrainedTypeElim → heapParam →
  typeHierarchy → modifies → translateLaurelToCore → Core
```

Properties can be stated at different granularities.

### Option A: End-to-end (black box)

Prove properties about `translate` as a whole: "Laurel program
with feature X → Core program with property Y." Don't reference
individual passes.

- Pro: Survives pipeline refactoring (reordering passes, merging
  passes, splitting passes). The property statement doesn't
  mention internal structure.
- Con: Hard to prove — you're reasoning about the composition of
  ~6 passes at once. When a proof breaks, it's hard to tell which
  pass caused the failure. Doesn't give you the exhaustiveness
  benefit (a new constructor only needs to be handled in the
  passes it affects, not in a monolithic proof).

### Option B: Per-pass properties

Prove properties about each pass individually. Each pass's
postconditions become the next pass's preconditions. End-to-end
properties follow by composition.

- Pro: Each proof is small and focused. When a proof breaks, you
  know exactly which pass changed. Lean's exhaustiveness checker
  works at the pass level — a new `StmtExpr` constructor breaks
  the specific passes that match on it. Composition gives you
  end-to-end properties when needed.
- Con: Proofs are coupled to the pipeline structure. Reordering
  or merging passes breaks the proof chain. Requires stating
  inter-pass contracts explicitly.

### Option C: Grouped passes

Treat related passes as a unit. For example, "preprocessing"
(resolve + constrainedTypeElim) and "core translation"
(translateLaurelToCore). Prove properties at group boundaries.

- Pro: Fewer proof files. Less coupling than per-pass. Groups
  can be refactored internally without breaking proofs.
- Con: Loses some of the exhaustiveness benefit within groups.
  Group boundaries are somewhat arbitrary.

### Decision: Option B (per-pass properties)

The primary goal is catching incomplete features. A new `StmtExpr`
constructor needs to be handled in heap parameterization, constrained
type elimination, the translator, and possibly other passes. Per-pass
properties with exhaustive pattern matching catch exactly this: if
the constructor isn't handled, the proof for that pass doesn't close.

The coupling to pipeline structure is acceptable. The pipeline
structure is stable — the passes exist for clear architectural
reasons and are unlikely to be reordered. If a pass is refactored,
the proof for that pass is refactored too — that's the point. The
proof breaking IS the signal that the refactoring needs attention.

End-to-end properties (Option A) are a future goal for specific
high-value properties (e.g., "exceptions are sound"). These would
be proven by composing per-pass properties, not by reasoning about
the pipeline monolithically.

---

## D4: Equation lemma strategy

**Context:** The DDM module system makes definitions private by
default. Cross-module proofs can't `unfold` non-`@[expose]`
definitions. To prove properties about a pass from an external
property file, we need either `@[expose]` annotations or equation
lemmas in the defining module.

### Option A: Add `@[expose]` liberally

Mark pass functions as `@[expose]` so property files can `unfold`
them directly.

- Pro: Simple. No extra theorems to write. Property files can
  reason about the full implementation.
- Con: `@[expose]` changes how the Lean kernel treats definitions
  (makes them reducible). This can change `simp` and `decide`
  behavior in existing proofs. Risk of breaking downstream proofs
  that relied on a definition NOT reducing. Leaks implementation
  details — property files become coupled to internal structure.

### Option B: Equation lemmas (the D14 pattern)

Prove theorems in the defining module that expose exactly what
downstream proofs need. The defining module can `unfold` freely;
the equation lemma is the contract.

- Pro: States exactly what downstream proofs need. Doesn't leak
  implementation details. Stable under internal refactoring —
  the lemma statement is the contract, the proof adapts. No risk
  of changing `simp`/`decide` behavior.
- Con: More upfront work — each property may need a corresponding
  equation lemma. The equation lemma must be proven in the
  defining module, which means touching existing files.

### Option C: Mix — `@[expose]` for simple definitions, equation lemmas for complex ones

Use `@[expose]` for type abbreviations, simple helpers, and
definitions that are unlikely to change. Use equation lemmas for
complex pass functions where the internal structure might evolve.

- Pro: Pragmatic. Minimizes boilerplate for simple cases.
  Protects complex cases.
- Con: Judgment call on which is "simple" vs "complex."

### Decision: Option C (mix), added conservatively as needed

Don't do an upfront audit. When a property needs to reason about
a pass function, determine whether `@[expose]` or an equation
lemma is appropriate:

- `@[expose]` for: type abbreviations (`TranslateM`), pure
  helpers (`instanceProcCoreName`, `coreTypeName`), constructors.
- Equation lemmas for: pass functions (`translateExpr`,
  `translateStmt`, `heapParameterize`), anything with monadic
  state, anything likely to be refactored.

After adding either, rebuild everything and run the full test
suite. If anything breaks, prefer the equation lemma approach.

The principle: we're making proofs possible, not exposing
internals. The equation lemma is a contract between the pass
and its properties.

---

## D5: Well-formedness preconditions

**Context:** Pipeline properties only hold for well-formed
programs. Each pass has implicit preconditions — `translateStmt`
assumes resolution already ran, heap parameterization assumes
types are resolved. How do we state these?

### Option A: Single `wellFormed` predicate

Define one predicate that means "the program is valid Laurel
that has passed parsing and type checking." Use it as the
precondition for all properties.

- Pro: Simple. One precondition everywhere.
- Con: Too coarse. A property about `translateExpr` doesn't need
  to know about modifies clauses. The predicate becomes a grab-bag
  that's hard to prove and hard to understand.

### Option B: Per-pass preconditions as explicit hypotheses

Each pass's properties state exactly what they need. For example,
heap parameterization properties require "all field accesses are
resolved" but don't mention constrained types.

- Pro: Precise. Each property states its minimal requirements.
  Easy to understand what each property actually guarantees.
- Con: More hypotheses to manage. Composition requires proving
  that pass A's postconditions satisfy pass B's preconditions.

### Option C: Chain — each pass's postconditions ARE the next pass's preconditions

Define the inter-pass contract as a type. Pass A proves it
produces output satisfying the contract. Pass B's properties
take the contract as a hypothesis.

- Pro: The chain is explicit and mechanically checked. Adding a
  new pass means defining its contract and proving it satisfies
  the next pass's preconditions.
- Con: Requires defining the contracts upfront, which is design
  work.

### Decision: Option B now, evolving toward Option C

Start with explicit per-pass hypotheses. This is the simplest
thing that works — each property states what it needs, no
infrastructure required. As patterns emerge (the same hypotheses
appearing in multiple properties), factor them into named
predicates. These predicates naturally become the inter-pass
contracts of Option C.

The key insight: the postconditions of one pass are the
preconditions of the next. We don't need to define this
abstractly — it falls out of the per-pass properties. If
`heapParam_injects_heap` proves "$heap is in the output," and
`translateStmt_preserves_inputs` requires "$heap is in the
input," the composition is just applying one theorem's
conclusion as the other's hypothesis.

---

## D6: Partial function handling

**Context:** Some pipeline functions are `partial` in Lean,
meaning Lean can't prove they terminate. Lean generates equation
axioms for `partial` functions that are sound but not
kernel-checked. Properties about `partial` functions rely on
these axioms.

### Current state

The pipeline has only 2 partial functions:

1. `resolveBaseType` (ConstrainedTypeElim) — recurses through
   constrained type chains via HashMap lookup. Partial because
   Lean can't prove the chain terminates (it would need an
   acyclicity proof on the constrained type map).

2. `substituteIdentifier` (HeapParameterization) — walks the
   AST replacing identifier names. Partial because of nested
   inductive recursion (`StmtExprMd` contains `List StmtExprMd`).

The core translation functions (`translateExpr`, `translateStmt`,
`translateProcedure`) are total. They use `TranslateM` (a state
monad with `Option`) but are not `partial`.

### Option A: Accept partial functions, use equation axioms

Prove properties using the equation axioms Lean generates for
`partial` functions. These axioms are sound (they reflect the
actual computation) but not kernel-checked.

- Pro: No refactoring needed. Properties can be proven now.
- Con: Proofs depend on axioms outside the kernel. If a `partial`
  function has a bug (e.g., infinite loop on some input), the
  axiom still holds vacuously for that input (the function
  doesn't return, so the equation doesn't apply).

### Option B: Refactor to total as needed

When a property needs to reason about a `partial` function,
refactor it to be total first. For `resolveBaseType`, add a fuel
parameter or prove acyclicity. For `substituteIdentifier`, use
well-founded recursion on AST depth.

- Pro: Kernel-checked proofs. No axiom dependency.
- Con: Refactoring work. Risk of introducing bugs during
  refactoring (mitigated by test suite).

### Option C: Defer — the partial functions aren't blocking

The 2 partial functions are not in the core translation path.
`resolveBaseType` runs during constrained type elimination
(before translation). `substituteIdentifier` runs during heap
parameterization (before translation). The core translation
functions are already total. Focus properties on the total
functions first.

- Pro: No work needed now. Properties on the core translation
  are unblocked.
- Con: Eventually need to address partial functions to get
  full-pipeline properties.

### Decision: Option C now, Option B when needed

The core translation functions are total — this is the good news.
Start proving properties there. When properties need to reach
into constrained type elimination or heap parameterization,
refactor those specific functions to total. The test suite (516
tests) validates that refactoring doesn't introduce bugs.

The priority order:
1. Properties on `translateExpr`, `translateStmt`,
   `translateProcedure` (total, provable now)
2. Properties on `heapParameterize` (may need
   `substituteIdentifier` totality)
3. Properties on `constrainedTypeElim` (may need
   `resolveBaseType` totality)

---

## D7: Composition with existing semantic proofs

**Context:** Strata already has formal semantic proofs:

- Exit semantics (E1–E9 in `ExitProperties.lean`): properties
  of `EvalStmt`/`EvalBlock` for exit and labeled blocks
- Exception properties (`ExceptionProperties.lean`): properties
  of exception propagation
- Propagation properties (`PropagationProperties.lean`)

These are "Arrow 3" proofs — they prove that Core programs with
certain structures have certain semantic properties. The
translator pipeline properties are "Arrow 2" — they prove the
pipeline produces Core with those structures.

### Option A: Design for composition from the start

State translator properties so their conclusions match the
preconditions of the semantic proofs. For example, if E3
(matching block consumes exit) requires a block with label L
containing `exit (some L)`, the translator property for Throw
should conclude that the output contains exactly that structure.

- Pro: Composition is mechanical — apply the translator property,
  then apply the semantic property. End-to-end guarantees from
  Laurel to Core semantics.
- Con: Constrains the translator property statements. May need
  to state properties in a less natural form to match the
  semantic proof's preconditions.

### Option B: Independent properties, compose later

State translator properties in whatever form is most natural.
Write composition lemmas later that bridge between the translator
property conclusions and the semantic proof preconditions.

- Pro: Each property is stated in its most natural form.
  Flexibility to evolve both sides independently.
- Con: Composition lemmas are extra work. Risk that the
  properties don't actually compose (the forms are incompatible).

### Decision: Option A (design for composition)

The whole point is the end-to-end chain: Laurel → Core structure
→ Core semantics. If the translator properties don't compose with
the semantic proofs, we've proven isolated facts that don't
connect. Designing for composition from the start avoids
discovering incompatibilities later.

Concretely: when stating a translator property about exception
translation, look at what `ExceptionProperties.lean` needs as
input. State the translator property to produce exactly that.
The property statement is driven by the downstream consumer.

This doesn't mean every translator property needs a semantic
counterpart. Structural properties (declaration completeness,
signature preservation) stand alone. But for feature-specific
properties (exceptions, exit, heap), the semantic proofs define
the target.

---

## D8: Property priority — which features to prove first

**Context:** We have 35 test files exercising Laurel features. Our
initial 45 proven properties (TranslatorProperties.lean,
HeapParameterizationProperties.lean) cover literals, arithmetic,
control flow, loops, basic statements, procedure signatures, and
heap parameter injection. A gap analysis against the test suite
reveals which features have test coverage but zero proof coverage.

The discrepancy history from differential testing clusters
around: instance methods, heap detection, opaque procedures,
name qualification, and function postconditions.

### Option A: Cover breadth first — one property per StmtExpr constructor

Add a shallow property (e.g., "translateExpr succeeds") for every
`StmtExpr` constructor. This maximizes the exhaustiveness tripwire:
adding a new constructor breaks the most proofs.

- Pro: Maximum coverage breadth. Every constructor has at least
  one proof obligation.
- Con: Shallow properties don't catch semantic issues. "Succeeds"
  doesn't mean "produces the right output." The discrepancy clusters are
  in specific features, not in missing constructors.

### Option B: Cover depth first — full properties for high-risk features

Prove deep properties (correct output structure, correct naming,
correct heap threading) for the features where discrepancies cluster:
instance methods, exceptions, field access, constrained types.

- Pro: Targets the actual risk areas. Each property catches a
  class of issues, not just one. Composes with semantic proofs for
  end-to-end guarantees.
- Con: Leaves some constructors with zero coverage. A new
  constructor in an uncovered area won't trigger a proof failure.

### Option C: Prioritized hybrid — depth for high-risk areas, breadth for the rest

Prove deep properties for the 6 highest-risk features (instance
calls, exceptions, field access, preconditions, constrained types,
function postconditions). Add shallow "succeeds" properties for
remaining constructors as time permits.

### Decision: Option C (prioritized hybrid)

The discrepancy data tells us where to invest. The 6 priority features
below are the highest-risk areas based on discrepancy history and
self-verification experience. Deep properties for these features
give us the most regression protection per proof.
Shallow breadth properties are added opportunistically.

Priority order (see D9–D13, D18 for each):

1. **Instance calls** (P-Name-1) — 3 test files, zero proofs
2. **Exceptions** (P-Exception-1, P-Exception-2) — 1 test file, zero proofs
3. **Field access** (P-Heap-2) — 2 test files, zero proofs
4. **Preconditions/postconditions** (P-Struct-2 generalization) — 3 test files, partial proofs
5. **Constrained types** (P-Constrained-1) — 1 test file, infrastructure only
6. **Function postconditions** (P-Spec-2f) — Position.compareTo, zero proofs

---

## D9: Instance call translation (P-Name-1)

**Context:** Instance calls (`target~>callee(args)`) are the most
complex feature in the pipeline. The test suite has 3 dedicated
files (T7_InstanceProcedures, T9_InstanceCall, T10_InstanceCallCases).
Differential testing surfaced many name qualification discrepancies. The
existing `IM1` theorem proves naming consistency between call sites
and definition sites, but no property proves the translation output
is correct.

The pipeline handles instance calls in multiple passes:
- Resolution maps `callee` to `(typeName, proc)` via SemanticModel
- HeapParameterization detects instance calls for heap threading
- LaurelToCoreTranslator translates `InstanceCall` to a qualified
  static call with `self` prepended to args

### Option A: Single end-to-end property

Prove one theorem: "InstanceCall translates to
`TypeName..callee(self, args)` with correct heap parameters."

- Pro: One theorem, maximum value.
- Con: Requires reasoning across 3 passes simultaneously. Hard
  to prove, hard to maintain.

### Option B: Per-pass properties that compose

Prove separate properties for each pass:
1. Resolution: `InstanceCall` callee resolves to `(typeName, proc)`
2. HeapParameterization: `containsInstanceCallMd` detects instance
   calls, triggering heap parameter injection
3. Translator: `translateExpr` on `InstanceCall` produces
   `app(op(TypeName..callee), [self, args...])`

Compose them for the end-to-end guarantee.

- Pro: Each property is focused and maintainable. Composition
  gives the end-to-end result. Each property independently
  catches bugs in its pass.
- Con: More theorems to write. Composition requires stating
  inter-pass contracts.

### Option C: Translator property only, with preconditions

Prove the translator property (step 3 above) with explicit
preconditions about what resolution and heap parameterization
have already done. Don't prove the preconditions hold — that's
future work.

- Pro: Gets the highest-value property (correct Core output)
  without needing to reason about upstream passes. The
  preconditions document what the translator assumes.
- Con: The preconditions are unverified. If resolution has a
  bug, the property's precondition doesn't hold and the
  guarantee is vacuous.

### Decision: Option C now, evolving toward Option B

Start with the translator property: when `translateExpr` sees
`InstanceCall target callee args` and the SemanticModel maps
`callee` to `instanceProcedure typeName proc`, the output is
`app(op(TypeName..callee), [self, args...])`.

This requires an equation lemma for `translateExpr` on
`InstanceCall` in `LaurelToCoreTranslator.lean`.

The preconditions (resolution correctness, heap detection) are
stated as hypotheses. As we prove properties on those passes,
the hypotheses become dischargeable.

This matches the existing `IM1` pattern: `IM1` proves naming
consistency with a hypothesis about the SemanticModel. The new
property proves translation correctness with the same kind of
hypothesis.

---

## D10: Exception translation (P-Exception-1, P-Exception-2)

**Context:** Exception handling (`throw`, `try/catch/finally`) is
tested in T18_Throw with 5 test cases. The pipeline translates
`Throw(e)` to `$result := Failure(e); exit <target>` and
`TryCatch` to a labeled block pattern with catch dispatch.

The existing semantic proofs (E1–E6 in ExitProperties.lean) prove
properties of the Core `exit` and labeled block constructs. The
translator properties need to show the pipeline produces exactly
the structures these semantic proofs expect.

### Option A: Prove Throw first, TryCatch later

`Throw` is simpler — it produces 2 statements. `TryCatch` is
complex — it produces a labeled block with dispatch logic. Start
with Throw, which composes with E1 (exit preserves store) and
E2 (exit skips remaining).

- Pro: Quick win. Throw is the most common exception pattern.
  Composes immediately with existing semantic proofs.
- Con: TryCatch is where the structural complexity lives. The
  5 test cases in T18 test both Throw and TryCatch.

### Option B: Prove both together

Prove Throw and TryCatch properties in the same phase. The
TryCatch property composes with E3 (matching block consumes)
and E4 (non-matching exit propagates).

- Pro: Complete exception coverage. All T18 test cases covered.
- Con: TryCatch is significantly harder. May block progress on
  other priorities.

### Decision: Option A (Throw first)

Throw is the higher-value property per unit of proof effort.
It's also the first end-to-end composition opportunity: Laurel
`throw` → Core `exit` → E1/E2 semantics. This validates the
Arrow 2 + Arrow 3 composition pattern from the design doc.

TryCatch follows in a later phase. The equation lemma for
`translateStmt` on `TryCatch` is more complex (labeled blocks,
catch dispatch, finally) but follows the same pattern.

---

## D11: Field access translation (P-Heap-2)

**Context:** Field reads (`c#field`) and writes (`c#field := v`)
are tested in T1_MutableFields (12 test procedures) and
T8_ImmutableFields. The pipeline translates field access through
heap parameterization (field → `readField`/`updateField`) and
then through the Core translator.

The heap parameterization pass already has 6 proven properties
(P-Heap-1) about parameter injection. The gap is in the field
access translation itself: no property proves that `FieldSelect`
produces `readField($heap, obj, Field.TypeName.fieldName)`.

### Option A: Property on heapTransformExpr (the pass function)

Prove that `heapTransformExpr` on `FieldSelect` produces the
correct `readField` call with the right field constructor.

- Pro: Directly targets the pass where field bugs occur.
  Pattern-matches on `FieldSelect`, so adding a new field
  access pattern creates a proof obligation.
- Con: `heapTransformExpr` is in a `module` file. Needs
  equation lemmas or `@[expose]`.

### Option B: Property on translateExpr (after all passes)

Prove that `translateExpr` on the post-pipeline expression
(which is already a `StaticCall` to `readField`) produces the
correct Core expression.

- Pro: Uses existing equation lemmas for `StaticCall`.
- Con: Doesn't catch bugs in the heap parameterization pass
  itself. The field access has already been transformed to a
  static call by the time `translateExpr` sees it.

### Decision: Option A (property on heapTransformExpr)

The bugs are in the heap parameterization pass, not in the
Core translator. A property on `heapTransformExpr` catches
the actual bug class: incorrect field name qualification,
wrong Box constructor selection, missing heap threading.

This requires equation lemmas for `heapTransformExpr` on
`FieldSelect` in `HeapParameterization.lean`.

---

## D12: Precondition/postcondition generalization (P-Struct-2+)

**Context:** The current P-Struct-2 properties (name, input count,
output count, $result, Success init) only apply to transparent
procedures with no preconditions (`hNoPre`). Tests T6_Preconditions,
T8_Postconditions, and T8b_EarlyReturnPostconditions exercise
procedures with `requires` and `ensures` clauses.

### Option A: New equation lemma for procedures with preconditions

Add `translateProcedure_eq_transparent_withPre` that handles
non-empty preconditions. The preconditions translate via
`translateChecks`, which maps each precondition expression
through `translateExpr` and wraps it in a `Check`.

- Pro: Directly extends the existing P-Struct-2 pattern.
  Covers T6_Preconditions.
- Con: `translateChecks` is monadic and uses `mapIdxM`. The
  equation lemma is more complex than the no-precondition case.

### Option B: Separate property for precondition count

Instead of a full equation lemma, prove a focused property:
"the number of Core preconditions equals the number of Laurel
preconditions." This is a P-Struct-3 (spec preservation)
property.

- Pro: Simpler to prove. Catches the "precondition silently
  dropped" bug class.
- Con: Doesn't prove the precondition content is correct.

### Decision: Option B first, Option A when needed

The "precondition dropped" bug is the most likely regression.
A count-preservation property catches it with minimal proof
effort. Content correctness (the precondition expression
translates correctly) follows from the expression-level
properties we already have.

For postconditions, the same pattern applies: count
preservation first, content correctness later.

---

## D13: Constrained type properties (P-Constrained-1)

**Context:** Constrained types (`constrained nat = x: int where
x >= 0 witness 0`) are tested in T10_ConstrainedTypes with 10+
test procedures. The pipeline handles them in `constrainedTypeElim`,
which injects constraint preconditions on inputs and postconditions
on outputs.

We already have infrastructure lemmas in `ConstrainedTypeElim.lean`:
`mkConstraintFunc_isFunctional`, `mkWitnessProc_not_isFunctional`,
`elimProc_preserves_isFunctional`, etc. The gap is a property that
proves constraint injection: "a procedure with a constrained-type
input gets a `requires constraint$check(param)` in the Core output."

### Option A: Property on constrainedTypeElim output

Prove that `elimProc` on a procedure with constrained-type inputs
adds the constraint preconditions.

- Pro: Directly targets the pass. Catches the "constraint not
  injected" bug class.
- Con: `elimProc` is complex (handles Transparent, Opaque,
  Abstract, External bodies differently). The property needs
  case analysis.

### Option B: Property on the constraint function itself

Prove that `mkConstraintFunc` produces a function whose body
is the constraint expression. This is simpler and validates
the constraint definition, not the injection.

- Pro: Simpler. `mkConstraintFunc` is a pure function with
  no case analysis.
- Con: Doesn't prove injection. The constraint function could
  exist but never be called.

### Decision: Option A, starting with the input constraint case

The value is in proving injection, not existence. Start with
the input case: "if `proc.inputs` contains a parameter of
constrained type `T`, then `elimProc` adds
`T$constraint(param)` to the preconditions."

This requires reading the `elimProc` definition to understand
how `constraintCallFor` generates the precondition expression.
The infrastructure lemmas we already have (`elimProc_preserves_
isFunctional`) show the pattern for reasoning about `elimProc`.

---

## D14: Opaque procedure equation lemma

**Context:** Opaque procedures (procedures with `ensures` but hidden
bodies) are where postconditions live. Multiple discrepancies were
found in opaque procedure handling. The current P-Struct-2
properties only cover transparent procedures with no preconditions
(`translateProcedure_eq_transparent`). To prove P-Spec-1 and P-Spec-2,
we need an equation lemma for opaque procedures.

`translateProcedure` handles opaque procedures differently:
- Postconditions are translated via `translateExpr` in pure context
- The body (if present) is wrapped with `$unused` init
- Modifies clauses generate frame conditions
- `translateChecks` handles preconditions with indexed labels

### Option A: Single equation lemma for all opaque cases

One lemma covering opaque with implementation, opaque without
implementation, and abstract procedures.

- Pro: One lemma to maintain.
- Con: Complex statement with many case splits. Hard to read.

### Option B: Separate equation lemmas per body variant

Separate lemmas for `.Opaque postconds (some impl) modif`,
`.Opaque postconds none modif`, and `.Abstract postconds`.

- Pro: Each lemma is focused and readable. Matches the pattern
  match in `translateProcedure`.
- Con: More lemmas to write.

### Decision: Option B (separate lemmas)

The body variants have genuinely different behavior (with-impl
wraps the body in `$unused` init; without-impl doesn't; abstract
has no body at all). Separate lemmas make the differences explicit
and are easier to apply in downstream proofs.

Start with `.Opaque postconds (some impl) modif` — this is the
most common case in real Java code (methods with postconditions
and implementations).

---

## D15: Postcondition preservation (P-Spec-1, procedure path)

**Context:** The self-verification work was blocked by postconditions
being silently dropped or incorrectly translated. We want to prove
that postconditions survive the translation pipeline.

**Important:** This decision covers the **procedure path** only
(`translateProcedure` → `Core.Decl.proc` → `spec.postconditions`).
The **function path** (`translateProcedureToFunction` →
`Core.Decl.func` → `func.axioms`) is covered by D18. The function
postcondition axiom gap showed that these are genuinely separate
code paths with independent failure modes — the procedure path
can be correct while the function path silently drops postconditions.

### Option A: Count preservation

Prove: "a procedure with N postconditions produces a Core procedure
with at least N postconditions." This catches the "dropped" class
but not the "corrupted" class.

- Pro: Simple to state and prove. Only needs to count, not
  inspect content.
- Con: Doesn't catch content bugs (wrong field name, wrong
  expression structure).

### Option B: Content preservation

Prove: "each Laurel postcondition expression, after translation
through `translateExpr`, appears in the Core postcondition list."
This catches both dropped and corrupted postconditions.

- Pro: Stronger guarantee. Catches content bugs.
- Con: Harder to prove — needs to relate Laurel expressions to
  Core expressions through `translateExpr`.

### Option C: Structural preservation

Prove: "the Core postcondition list is exactly
`postconds.map(translateExpr)` — same order, same content."
This is the strongest form.

- Pro: Exact correspondence. No ambiguity.
- Con: May be too strong — the pipeline might reorder or wrap
  postconditions legitimately.

### Decision: Option A first, then Option B for high-value cases

Count preservation is the 80/20 — it catches the most common
failure mode (postcondition dropped) with the least proof effort.
Content preservation for specific cases (instance method
postconditions with field access) follows as P-Spec-3.

---

## D16: Field name qualification in specifications (P-Spec-3, P-Name-2)

**Context:** Multiple discrepancies were found around field names not
being qualified correctly in postconditions and preconditions. When
an instance method has `ensures self#count == old(self#count) + 1`,
the Core output must use `TypeName..count`, not just `count`. The
qualification happens in the resolution pass (`qualifyFieldName`)
and must survive through all subsequent passes.

### Option A: Property on resolution pass

Prove that `resolveProcedure` qualifies field names in
postconditions for instance procedures.

- Pro: Targets the pass where qualification happens.
- Con: Resolution is complex (global scope, per-type fields,
  inheritance). The equation lemma would be large.

### Option B: Property on translator output

Prove that `translateExpr` on a `FieldSelect` in postcondition
context produces a Core expression with the qualified field name.
Assume resolution already ran (precondition).

- Pro: Simpler — only reasons about the translator, not
  resolution. The precondition documents the assumption.
- Con: Doesn't prove resolution is correct.

### Decision: Option B (translator property with precondition)

Same pattern as D9 (instance calls): prove the translator
property with a precondition about what resolution did. The
precondition is: "the field name in the Laurel AST is already
qualified (contains `..`)." This is true after resolution runs.

The property then proves: `translateExpr` on
`FieldSelect(target, qualifiedFieldName)` produces a Core
expression that uses `qualifiedFieldName` in the heap read.

---

## D17: Heap analysis stability (P-Heap-3)

**Context:** The self-verification work found that "the presence
of ANY instance method/function on a composite breaks the prover's
ability to reason about field reads in static method postconditions."
This is a Strata bug in the heap analysis — adding instance methods
to a composite changes the heap reader/writer sets, which changes
the modifies frame for ALL procedures, including unrelated static
ones.

### Option A: Prove heap analysis is monotone

Prove: "adding a procedure to the program can only ADD entries to
`heapReaders`/`heapWriters`, never remove them." This means
existing procedures keep their heap status.

- Pro: Strong structural property. Catches any bug where adding
  code changes existing analysis results.
- Con: The fixpoint computation in `computeReadsHeap` /
  `computeWritesHeap` is complex. Monotonicity of a fixpoint
  requires showing the step function is monotone.

### Option B: Prove static procedures are independent of instance procedures

Prove: "the heap analysis result for a static procedure depends
only on the static procedures it (transitively) calls, not on
instance procedures it doesn't call."

- Pro: Directly addresses the bug. More focused than full
  monotonicity.
- Con: Still requires reasoning about the fixpoint, but only
  for the independence property.

### Option C: Prove the specific bug is fixed

Write a test-like property: "for a program with one composite
(one field, one instance method) and one static procedure that
reads the field, the static procedure is in `heapReaders` and
its modifies frame is correct."

- Pro: Directly validates the fix. Concrete, easy to understand.
- Con: Only covers one specific case. Doesn't prevent similar
  bugs in other configurations.

### Decision: Option C now, Option A as a stretch goal

The specific bug needs a specific fix, and a specific test
validates the fix. Option C is achievable now. Option A
(monotonicity) is the right long-term property but requires
significant fixpoint reasoning infrastructure that doesn't
exist yet.

---

## D18: Function postcondition axiom generation (P-Spec-2f)

**Context:** The function postcondition axiom gap revealed that the
translator has two separate code paths for postcondition availability:

1. **Procedure path:** `translateProcedure` → `Core.Decl.proc` →
   postconditions go into `spec.postconditions`. Covered by D15.
2. **Function path:** `translateProcedureToFunction` →
   `Core.Decl.func` → postconditions must go into `func.axioms`.
   NOT covered by D15.

The `feat/function-postconditions` merge added `FunctionPostcondCheck`
(generates `$check` procedures to verify function bodies satisfy
postconditions) but did not add axiom generation in the translator.
`translateProcedureToFunction` created `Core.Function` with
`axioms := []` (default), silently dropping all postconditions.
The fix populates `func.axioms` by translating each postcondition
to a universally quantified Core expression with `result` replaced
by `f(params...)`.

The precondition chain for function postconditions:

```
FunctionPostcondCheck postcondition:
    "postconditions preserved on function (not stripped)"
    ↓
translateProcedureToFunction precondition:
    "function has postconditions in its Body"
    ↓
P-Spec-2f postcondition:
    "Core.Function.axioms.length = postconditions.length"
    ↓
SMTEncoder precondition:
    "func.axioms added to SMT context when function encountered"
```

### Option A: Count preservation on `translateProcedureToFunction`

Prove: "a function with N postconditions produces a `Core.Function`
with N axioms." Matches the D15 Option A pattern for procedures.

- Pro: Simple. Catches the "axioms silently dropped" class (the
  function postcondition axiom gap). Requires only an equation lemma for
  `translateProcedureToFunction` that exposes the axiom count.
- Con: Doesn't prove axiom content is correct. The axioms could
  have wrong structure (e.g., missing `result` substitution,
  wrong quantifier nesting).

### Option B: Structural preservation

Prove: "each axiom is `∀ params :: {f(params)} postcond[result :=
f(params)]`." This catches both dropped and malformed axioms.

- Pro: Stronger guarantee. Validates the substitution and
  quantifier wrapping.
- Con: Harder to prove. Requires reasoning about `substFvar`,
  `buildQuants`, and the function application construction.
  The axiom structure involves de Bruijn indices, which are
  notoriously tricky to reason about.

### Option C: Exhaustive pattern match on Body variants

Prove a property that pattern-matches on all `Body` variants
in `translateProcedureToFunction`. For each variant with
postconditions (`.Transparent _ posts`, `.Opaque posts _ _`,
`.Abstract posts`), prove axioms are generated. For variants
without (`.External`, empty postconds), prove axioms are empty.

- Pro: Lean's exhaustiveness checker enforces that new `Body`
  variants get handled. This is the core mechanism from the
  design doc — adding a new body variant breaks the proof.
- Con: More cases to prove. But each case is simple.

### Decision: Option A first, then Option C

Count preservation (Option A) catches the exact bug class that
motivated this decision. It's the 80/20 — one theorem, maximum
value. The equation lemma for `translateProcedureToFunction`
needs to expose:

```lean
theorem translateProcedureToFunction_axiom_count
    (proc : Procedure) (hFunc : proc.isFunctional)
    (hPosts : getPostconds proc.body = posts)
    (hNonEmpty : posts ≠ []) :
    (translateProcedureToFunction {} false proc).axioms.length =
    posts.length
```

Option C (exhaustive Body match) follows as the regression
guarantee: when a new `Body` variant is added, the proof
breaks until the new case is handled.

Option B (structural preservation) is a stretch goal. The de
Bruijn index reasoning is complex and the count property already
catches the practical failure mode.

**Implementation notes:**

- The equation lemma goes in `LaurelToCoreTranslator.lean`
  (following D4: equation lemma strategy).
- The property goes in `TranslatorProperties.lean` alongside
  the existing P-Spec properties.
- Precondition: `FunctionPostcondCheck` has run (postconditions
  are on the function, not stripped). This is an explicit
  hypothesis, following D5.
- The property file for `FunctionPostcondCheck.lean` itself
  (proving postconditions are preserved, not stripped) is
  future work. For now, the hypothesis documents the assumption.