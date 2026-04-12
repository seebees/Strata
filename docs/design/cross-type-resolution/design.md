# Cross-Type Instance Call Resolution: Implementation Design

**Date:** 2026-04-12
**Status:** Ready for implementation
**Decisions:** See [decisions.md](decisions.md)

## Overview

Qualify instance procedure names with their owner type using the
`~>` separator, so that `compareTo` on Position becomes
`Position~>compareTo` and `compareTo` on Range becomes
`Range~>compareTo`. The frontend sends qualified callee names.
The resolution pass registers definitions under qualified names.
No ambiguity, no shadowing.

## Changes by File

### 1. `Laurel.lean` — separator change

**Line 525:** Change `instanceProcCoreName` separator from `..`
to `~>`:

```lean
def instanceProcCoreName (typeName : String) (procName : String) : String :=
  typeName ++ "~>" ++ procName
```

Note: after all other changes land, `instanceProcCoreName` may
become dead code — the translator won't need it if names are
already qualified. Keep it for now as the single source of truth
for the separator convention. Remove later if unused.

### 2. `LaurelToCoreTranslator.lean` — qualify definitions before pipeline

**In `translateWithLaurel` (line 1049):** Add a qualification
step before the first `resolve` call. This renames instance
procedure definitions on the Program:

```lean
-- Qualify instance procedure names before resolution
let program := qualifyInstanceProcNames program
let result := resolve program
```

The function:

```lean
def qualifyInstanceProcNames (program : Program) : Program :=
  { program with types := program.types.map fun td =>
    match td with
    | .Composite ct =>
      .Composite { ct with instanceProcedures :=
        ct.instanceProcedures.map fun proc =>
          { proc with name := { proc.name with
            text := instanceProcCoreName ct.name.text proc.name.text } } }
    | other => other }
```

After this, `proc.name.text` is `"Position~>compareTo"` on the
definition. The frontend already sends `"Position~>compareTo"`
as the callee. Both match.

### 3. `Resolution.lean` — register under qualified names

**`preRegisterTopLevel` (line 744):** Instance procedures are
now pre-registered under their qualified name (because
`proc.name.text` is already qualified from step 2):

```lean
for proc in ct.instanceProcedures do
  let _ ← defineName proc.name placeholderNode
```

No change needed — `defineName` uses `proc.name.text` as the
scope key by default, and `proc.name.text` is now
`"Position~>compareTo"`.

**`resolveInstanceProcedure` (line 469):** Same — `proc.name`
is already qualified, so `defineName proc.name (.instanceProcedure
typeName proc)` registers under the qualified name.

No change needed.

**`resolveRef` for InstanceCall (line 350):** The callee's
`name.text` is `"Position~>compareTo"`. `resolveRef` does
`scope.get? name.text`. The scope has
`"Position~>compareTo"` → (id, instanceProcedure ...).
Match found. Correct ID assigned.

No change needed.

### 4. `LaurelToCoreTranslator.lean` — simplify translator

**Definition site (line 1163):** Currently does:
```lean
name := { proc.name with text := instanceProcCoreName ct.name.text proc.name.text }
```

After our change, `proc.name.text` is already
`"Position~>compareTo"`. Simplify to:
```lean
let qualifiedProc := proc  -- name is already qualified
let procDecl ← translateProcedure qualifiedProc
```

**Call sites (lines 317, 407, 461, 491, 540):** Currently do:
```lean
let coreName := instanceProcCoreName typeName.text callee.text
```

After our change, `callee.text` is already
`"Position~>compareTo"`. Simplify to:
```lean
let coreName := callee.text
```

The `model.get callee` still works — it looks up by `uniqueId`,
which was correctly assigned during resolution.

### 5. `HeapParameterization.lean` — no changes

The heap analysis uses `proc.name` from definitions and `callee`
from call sites. Both are now qualified. The `contains` check
matches. `computeReadsHeap`, `computeWritesHeap`,
`heapTransformProcedure`, and `heapTransformExpr` all work
without modification.

### 6. `InstanceMethodProperties.lean` — update proofs

**`instanceProcCoreName_shape`:** Change expected string:
```lean
theorem instanceProcCoreName_shape (typeName procName : String) :
    instanceProcCoreName typeName procName = typeName ++ "~>" ++ procName := by
  rfl
```

**`instance_call_name_consistency`:** The theorem becomes
simpler. Since both the callee and the definition use the
qualified name directly, the consistency property is:
`callee.text = proc.name.text` (both are the qualified name).
The `instanceProcCoreName` call is no longer in the proof —
it was already applied before resolution.

```lean
theorem instance_call_name_consistency
    (callee : Identifier) (proc : Procedure)
    (hName : callee.text = proc.name.text) :
    callee.text = proc.name.text := by
  exact hName
```

This is trivially true but serves as a tripwire: if someone
changes how names flow through the pipeline, the hypothesis
`hName` won't be satisfiable.

### 7. `HeapParameterizationProperties.lean` — mechanical updates

Theorems that have hypotheses like
`s.heapWriters.contains proc.name = true` will still work —
`proc.name` is now the qualified name, and the heap analysis
built its lists from the same qualified names. The hypotheses
are about the relationship between the procedure and the
analysis result, which is unchanged.

If any theorem hardcodes an unqualified name in a test case,
update it to the qualified form.

### 8. `TranslatorProperties.lean` — no changes expected

The 30+ theorems test static calls, literals, and control flow.
None reference `instanceProcCoreName` or instance calls. These
should be unaffected.

## What Does NOT Change

- **Laurel AST** — `InstanceCall` node structure is unchanged
- **Ion serialization** — format is unchanged, just the callee
  string value changes
- **Laurel grammar** — `~>` source syntax is unchanged
- **Core grammar** — destructor `..` syntax is unchanged
- **Heap analysis algorithm** — `computeReadsHeap`,
  `computeWritesHeap` are unchanged
- **Other passes** — `filterNonCompositeModifies`,
  `typeHierarchyTransform`, `modifiesClausesTransform`,
  `constrainedTypeElim`, `functionPostcondCheck` all handle
  `InstanceCall` by recursing into children. The qualified
  name flows through unchanged.

## Ordering

1. Change separator in `instanceProcCoreName` (`..` → `~>`)
2. Add `qualifyInstanceProcNames` and call it in
   `translateWithLaurel` before the first `resolve`
3. Simplify translator definition site (remove redundant
   `instanceProcCoreName` call)
4. Simplify translator call sites (use `callee.text` directly)
5. Update IM1 proofs
6. Update HeapParameterizationProperties if needed
7. Run full test suite

Steps 1-4 are the functional changes. Steps 5-6 are mechanical
proof updates. Step 7 validates everything.

## Placement

`qualifyInstanceProcNames` lives in `LaurelToCoreTranslator.lean`
next to `translateWithLaurel` where it's called.
