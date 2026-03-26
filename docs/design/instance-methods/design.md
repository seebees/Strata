# Instance Method Support: Design

**Date:** 2026-03-26
**Status:** In progress

## Decisions

### Decision 1: Keep InstanceCall through the Laurel pipeline

**Options:**
- A. Convert InstanceCall → StaticCall early (in heap parameterization)
- B. Keep InstanceCall through all passes, flatten in translator only

**Choice:** B

**Rationale:** Keeps the semantic distinction visible through the pipeline.
The translator is the single place where InstanceCall becomes a Core `call`.
This makes the translation more provable — the name mapping is localized
to one function in one place.

### Decision 2: Prove a consistency property

**Options:**
- A. Prove at Core level (type-checking catches mismatches)
- B. Prove at Laurel level (theorem about translator correctness)
- C. Prove via SemanticModel (name consistency between call and definition)

**Choice:** C (with A as baseline, B as future goal)

**Rationale:** Option A is free but insufficient — it can't distinguish
"correct translation" from "accidentally correct." Option B is the right
long-term answer but is research-level work we haven't attempted for any
translation. Option C is achievable now: prove that the name construction
function used at the call site is the same function used at the definition
site. Combined with Core type-checking (A), this gives reasonable confidence.

If empirical testing reveals bugs, that's the signal to invest in B.

### Decision 3: Instance procedure naming

The Core procedure name for an instance procedure must be qualified:
`typeName ++ ".." ++ procName`. This follows the existing convention
used for datatype destructors (`Color..isRed`, `Heap..data!`).

A single pure function `instanceProcCoreName` constructs this name.
Both the definition translator and the call translator use it.
The consistency proof is that they call the same function.

---

## What Each Pass Needs

### 1. Resolution (no changes needed)

Already works correctly:
- `resolveInstanceProcedure` defines the procedure name in scope
- `InstanceCall` resolution looks up callee via `resolveRef`
- The callee gets a unique ID pointing to `.instanceProcedure typeName proc`
- `instanceTypeName` is set for field resolution inside instance methods

### 2. Heap Parameterization — Analysis (needs fix)

**Current:** `InstanceCall` recurses into target and args but does NOT
add callee to the `callees` list. Instance method callees are invisible
to the heap reader/writer fixpoint computation.

**Fix:** Add callee to `callees` list, same as `StaticCall` does.
The callee name must match the instance procedure's name as it appears
in the analysis. Since analysis runs over `allProcs` (which includes
instance procedures), and instance procedures have their unqualified
names at this point, the callee name from `InstanceCall` (also
unqualified) should match.

### 3. Heap Parameterization — Transform (needs fix)

**Current:** `InstanceCall` recurses and returns `InstanceCall` unchanged.
No heap parameter injection.

**Fix:** Handle `InstanceCall` like `StaticCall` but keep it as
`InstanceCall`:
- Check if callee reads/writes heap
- If writes: inject `$heap` as input and output, wrap in assignment
- If reads: inject `$heap` as input
- Keep the node as `InstanceCall` (don't convert to `StaticCall`)

This requires extending `InstanceCall` or wrapping it to carry the
heap parameter. Options:
- a. Add heap args to the existing `args` list (target is separate)
- b. The heap param is always first in args if present (convention)
- c. Add a separate field to `InstanceCall` for heap params

Option (a) with convention (b) is simplest and matches how `StaticCall`
works — heap param is prepended to args.

### 4. Heap Parameterization — Procedure Transform (needs fix)

**Current:** Instance procedures are transformed by `heapTransformProcedure`
(which adds `$heap` input/output) but stay on the composite.

**No change needed here.** Instance procedures stay on the composite.
The translator will find them there.

### 5. Type Hierarchy (no changes needed)

Already recurses into `InstanceCall` target and args. No `New` or
`IsType` nodes to rewrite inside instance calls specifically.

### 6. Modifies Clauses (needs review)

**Current:** Only processes `staticProcedures`. Instance procedures
with `modifies self` won't get frame conditions.

**Fix:** Also process instance procedures from composites.

### 7. Translator — Instance Procedure Definitions (needs implementation)

**Current:** Emits "not yet supported" diagnostic.

**Fix:** Translate instance procedures from composites to Core procedures.
- Core procedure name: `instanceProcCoreName typeName procName`
- Inputs: same as Laurel (self is already a regular parameter after heap transform)
- Outputs: same as Laurel (plus `$result` for exceptions)
- Body: translate normally

### 8. Translator — InstanceCall at Call Sites (needs implementation)

**Current:** Havocs result or emits "not yet implemented."

**Fix:** Translate `InstanceCall target callee args` to:
1. Look up callee in SemanticModel → `.instanceProcedure typeName proc`
2. Construct Core name: `instanceProcCoreName typeName procName`
3. Emit `Core.call coreName (target :: args)`
4. Add exception propagation check (same as static calls)

Handle all positions:
- Expression position (function-like instance methods)
- Variable initializer (`var x := target.method(args)`)
- Assignment (`x := target.method(args)`)
- Statement position (`target.method(args)`)
- Multi-assignment (`(x, y) := target.method(args)`)

---

## The Consistency Property

### Definition

```lean
def instanceProcCoreName (typeName : String) (procName : String) : String :=
  typeName ++ ".." ++ procName
```

### Property to Prove

```
theorem instance_call_name_consistency :
  ∀ (typeName procName : String),
    -- The name used when translating the definition
    definitionCoreName typeName procName
    =
    -- The name used when translating the call
    callSiteCoreName typeName procName
```

This is trivially true if both `definitionCoreName` and `callSiteCoreName`
are defined as `instanceProcCoreName`. The proof's value is as a design
constraint — it FORCES both sites to use the same function.

### What This Proves and Doesn't Prove

**Proves:**
- The call hits the right procedure (name matches)
- Name construction is consistent across the translator

**Doesn't prove:**
- Argument order is correct
- Arity matches
- Semantic preservation (the Core call does what the Laurel call means)

**Mitigated by:**
- Core type checker catches arity/type mismatches
- Strata tests exercise the full pipeline
- JVerify tests exercise Java → Laurel → Core → prover

---

## Work Items (ordered)

### Strata Changes
1. Define `instanceProcCoreName` as a shared pure function
2. Fix heap analysis: add `InstanceCall` callee to `callees` list
3. Fix heap transform: inject heap params into `InstanceCall`
4. Fix modifies clauses: process instance procedures from composites
5. Implement translator: instance procedure definitions
6. Implement translator: `InstanceCall` at all call positions
7. Remove "not yet supported" diagnostic for instance procedures
8. Write consistency proof
9. Update T7 test to expect success
10. Write new tests: instance method with ensures, instance method
    calling another instance method, instance method with modifies

### JVerify Changes (after Strata)
11. Emit composites from Java classes (fields, instance methods)
12. Emit `InstanceCall` from `obj.method(args)`
13. Emit `FieldSelect` from `obj.field`
14. Emit `SelfRef` from `this`
15. Handle constructors
16. Write JVerify tests with Java instance methods

---

## Open Questions

### Q1: InstanceCall heap parameter placement
When heap parameterization injects `$heap` into an `InstanceCall`,
where does it go? The target is separate from args. Options:
- Prepend to args (like StaticCall): `InstanceCall target callee ($heap :: args)`
- This means the instance procedure's `self` parameter is the target,
  and `$heap` is the first arg. The translator flattens to
  `Core.call name ($heap :: target :: args)` or
  `Core.call name (target :: $heap :: args)`.
- Need to match the parameter order in the definition.

### Q2: Instance procedure parameter order in Core
After heap transform, an instance procedure has:
- `$heap_in` (if heap writer) or `$heap` (if heap reader)
- `self: Composite`
- Other params

The `self` parameter is explicit in Laurel. After heap transform,
`$heap` is prepended. So the Core parameter order is:
`($heap, self, other_params...)`.

At the call site, `InstanceCall target callee args` should produce:
`Core.call name ($heap, target, args...)`.

This matches if `target` maps to `self` and `args` maps to `other_params`.

### Q3: What about `SelfRef` / `This`?
Inside an instance method body, `self` is just a parameter name.
`SelfRef` / `This` in the Laurel AST might not be needed if the
user writes `self` explicitly. But Java uses `this` implicitly.
The JVerify compiler would need to emit `SelfRef` or just
`Identifier("self")`.
