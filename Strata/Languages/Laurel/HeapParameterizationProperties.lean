/-
  Copyright Strata Contributors
  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
import Strata.Languages.Laurel.HeapParameterization

/-!
# Heap Parameterization Properties

Properties of the heap parameterization pass. This pass injects `$heap`
parameters into procedures that access the heap (field reads/writes,
instance calls, opaque modifies).

See `docs/design/translator-proof/design.md` for the full design.

## P-Heap-1: Heap parameter injection

The core equation lemmas are in `HeapParameterization.lean`:
- `heapTransformProcedure_writesHeap_inputs`: writes → `$heap_in` prepended to inputs
- `heapTransformProcedure_writesHeap_outputs`: writes → `$heap` prepended to outputs
- `heapTransformProcedure_readsHeap_inputs`: reads only → `$heap` prepended to inputs
- `heapTransformProcedure_readsHeap_outputs`: reads only → outputs unchanged
- `heapTransformProcedure_noHeap`: no heap → procedure unchanged
- `heapTransformProcs_noHeap`: no heap for any proc → list unchanged

This file adds derived properties that compose with downstream proofs.
-/

namespace Strata.Laurel

/-! ### P-Heap-1a: Heap writers get both $heap_in and $heap

When a procedure writes to the heap, it gets `$heap_in` as the first
input and `$heap` as the first output. This is the key structural
property that downstream semantic proofs rely on. -/

/-- A heap-writing procedure's first input is $heap_in with type Heap. -/
theorem heapWriter_first_input_is_heap_in (model : SemanticModel) (proc : Procedure)
    (s : TransformState) (hWrite : s.heapWriters.contains proc.name = true) :
    ((heapTransformProcedure model proc) s).1.inputs.head? =
      some { name := "$heap_in", type := ⟨.THeap, #[]⟩ } := by
  rw [heapTransformProcedure_writesHeap_inputs model proc s hWrite]; rfl

/-- A heap-writing procedure's first output is $heap with type Heap. -/
theorem heapWriter_first_output_is_heap (model : SemanticModel) (proc : Procedure)
    (s : TransformState) (hWrite : s.heapWriters.contains proc.name = true) :
    ((heapTransformProcedure model proc) s).1.outputs.head? =
      some { name := "$heap", type := ⟨.THeap, #[]⟩ } := by
  rw [heapTransformProcedure_writesHeap_outputs model proc s hWrite]; rfl

/-- A heap-writing procedure has one more input than the original. -/
theorem heapWriter_input_count (model : SemanticModel) (proc : Procedure)
    (s : TransformState) (hWrite : s.heapWriters.contains proc.name = true) :
    ((heapTransformProcedure model proc) s).1.inputs.length = proc.inputs.length + 1 := by
  rw [heapTransformProcedure_writesHeap_inputs model proc s hWrite]; simp

/-- A heap-writing procedure has one more output than the original. -/
theorem heapWriter_output_count (model : SemanticModel) (proc : Procedure)
    (s : TransformState) (hWrite : s.heapWriters.contains proc.name = true) :
    ((heapTransformProcedure model proc) s).1.outputs.length = proc.outputs.length + 1 := by
  rw [heapTransformProcedure_writesHeap_outputs model proc s hWrite]; simp

/-! ### P-Heap-1b: Heap readers get $heap input only

When a procedure reads but doesn't write the heap, it gets `$heap` as
the first input but outputs are unchanged. -/

/-- A read-only heap procedure's first input is $heap with type Heap. -/
theorem heapReader_first_input_is_heap (model : SemanticModel) (proc : Procedure)
    (s : TransformState)
    (hRead : s.heapReaders.contains proc.name = true)
    (hNoWrite : s.heapWriters.contains proc.name = false) :
    ((heapTransformProcedure model proc) s).1.inputs.head? =
      some { name := "$heap", type := ⟨.THeap, #[]⟩ } := by
  rw [heapTransformProcedure_readsHeap_inputs model proc s hRead hNoWrite]; rfl

/-- A read-only heap procedure's outputs are unchanged. -/
theorem heapReader_outputs_unchanged (model : SemanticModel) (proc : Procedure)
    (s : TransformState)
    (hRead : s.heapReaders.contains proc.name = true)
    (hNoWrite : s.heapWriters.contains proc.name = false) :
    ((heapTransformProcedure model proc) s).1.outputs = proc.outputs := by
  exact heapTransformProcedure_readsHeap_outputs model proc s hRead hNoWrite

/-! ### P-Heap-1c: Non-heap procedures are unchanged

When a procedure doesn't access the heap at all, the pass is identity. -/

/-- A non-heap procedure is completely unchanged by the pass. -/
theorem noHeap_procedure_unchanged (model : SemanticModel) (proc : Procedure)
    (s : TransformState)
    (hNoRead : s.heapReaders.contains proc.name = false)
    (hNoWrite : s.heapWriters.contains proc.name = false) :
    ((heapTransformProcedure model proc) s).1 = proc := by
  have := heapTransformProcedure_noHeap model proc s hNoRead hNoWrite
  simp [this]

/-- A non-heap procedure preserves its inputs exactly. -/
theorem noHeap_inputs_unchanged (model : SemanticModel) (proc : Procedure)
    (s : TransformState)
    (hNoRead : s.heapReaders.contains proc.name = false)
    (hNoWrite : s.heapWriters.contains proc.name = false) :
    ((heapTransformProcedure model proc) s).1.inputs = proc.inputs := by
  rw [noHeap_procedure_unchanged model proc s hNoRead hNoWrite]

/-- A non-heap procedure preserves its outputs exactly. -/
theorem noHeap_outputs_unchanged (model : SemanticModel) (proc : Procedure)
    (s : TransformState)
    (hNoRead : s.heapReaders.contains proc.name = false)
    (hNoWrite : s.heapWriters.contains proc.name = false) :
    ((heapTransformProcedure model proc) s).1.outputs = proc.outputs := by
  rw [noHeap_procedure_unchanged model proc s hNoRead hNoWrite]

/-! ### P-Heap-1d: Heap parameter naming consistency

The heap parameter names are consistent: writers use `$heap_in`/`$heap`,
readers use `$heap`. This is important for the translator which looks
up these names. -/

/-- Writers use different names for input ($heap_in) and output ($heap). -/
theorem heapWriter_input_output_names_differ (model : SemanticModel) (proc : Procedure)
    (s : TransformState) (hWrite : s.heapWriters.contains proc.name = true) :
    ((heapTransformProcedure model proc) s).1.inputs.head?.map (·.name) ≠
    ((heapTransformProcedure model proc) s).1.outputs.head?.map (·.name) := by
  rw [heapTransformProcedure_writesHeap_inputs model proc s hWrite,
      heapTransformProcedure_writesHeap_outputs model proc s hWrite]
  simp

/-! ### P-Name-2: Field name qualification

`resolveQualifiedFieldName` produces the qualified name
`OwnerType.fieldName` when the SemanticModel maps the field to
its owning type. This is the function where bugs #23, #24
(inherited field names use wrong prefix) would manifest.

These properties are tripwires: if anyone changes the name
construction, these proofs break. -/

/-- When the model resolves a field to its owner, the qualified name
    is `owner.text ++ "." ++ fieldName.text`. -/
theorem resolveQualifiedFieldName_field
    (model : SemanticModel) (fieldName : Identifier)
    (owner : Identifier) (fld : Field)
    (hField : model.get fieldName = .field owner fld) :
    resolveQualifiedFieldName model fieldName = some (owner.text ++ "." ++ fieldName.text) := by
  unfold resolveQualifiedFieldName; rw [hField]

/-- When the model can't resolve a field, qualification fails. -/
theorem resolveQualifiedFieldName_unresolved
    (model : SemanticModel) (fieldName : Identifier)
    (hUnresolved : model.get fieldName = .unresolved) :
    resolveQualifiedFieldName model fieldName = none := by
  unfold resolveQualifiedFieldName; rw [hUnresolved]

/-- Two fields with different owners get different qualified names. -/
theorem resolveQualifiedFieldName_owner_distinguishes
    (model : SemanticModel) (fieldName : Identifier)
    (owner1 owner2 : Identifier) (fld1 : Field)
    (hField1 : model.get fieldName = .field owner1 fld1)
    (hOwnerNe : owner1.text ≠ owner2.text) :
    resolveQualifiedFieldName model fieldName ≠
      some (owner2.text ++ "." ++ fieldName.text) := by
  rw [resolveQualifiedFieldName_field model fieldName owner1 fld1 hField1]
  intro h
  have := Option.some.inj h
  have : owner1.text ++ "." ++ fieldName.text = owner2.text ++ "." ++ fieldName.text := this
  have : owner1.text = owner2.text := by
    simp [String.append] at this
    exact this
  exact hOwnerNe this

/-! ### P-Heap-2: FieldSelect is eliminated before Core translation

The translator rejects FieldSelect — it must be eliminated by
heap parameterization first. This is a design invariant: field
access in Core is always through `readField`/`updateField` calls,
never through direct field selection.

`heapTransformExpr_fieldSelect_is_staticCall` (in HeapParameterization.lean)
proves that heapTransformExpr on FieldSelect always produces a StaticCall
when the field name resolves. The properties below prove correctness of
the components used in that StaticCall:

1. resolveQualifiedFieldName produces the correct qualified name (above)
2. boxDestructorName produces the correct destructor name (below) -/

/-- boxDestructorName for int fields produces the int Box destructor. -/
theorem boxDestructorName_int (model : SemanticModel) :
    (boxDestructorName model .TInt).text = "Box..intVal!" := by
  unfold boxDestructorName; rfl

/-- boxDestructorName for bool fields produces the bool Box destructor. -/
theorem boxDestructorName_bool (model : SemanticModel) :
    (boxDestructorName model .TBool).text = "Box..boolVal!" := by
  unfold boxDestructorName; rfl

/-- boxDestructorName for string fields produces the string Box destructor. -/
theorem boxDestructorName_string (model : SemanticModel) :
    (boxDestructorName model .TString).text = "Box..stringVal!" := by
  unfold boxDestructorName; rfl

/-- boxDestructorName for real fields produces the real Box destructor. -/
theorem boxDestructorName_real (model : SemanticModel) :
    (boxDestructorName model .TReal).text = "Box..realVal!" := by
  unfold boxDestructorName; rfl

/-! ## P-Spec-3: Postcondition count preservation through heap parameterization -/

set_option linter.unusedSimpArgs false in
/-- mapM.loop through StateM preserves length: result.length = acc.length + l.length. -/
private theorem List.length_mapM_loop_stateM {α β σ : Type}
    (f : α → StateM σ β) (l : List α) (acc : List β) (s : σ) :
    ((List.mapM.loop f l acc s).1).length = acc.length + l.length := by
  induction l generalizing acc s with
  | nil => simp [List.mapM.loop, pure, StateT.pure, List.length_reverse]
  | cons x xs ih =>
    simp only [List.mapM.loop, bind, StateT.bind]
    generalize f x s = p; obtain ⟨b, s1⟩ := p
    simp only; rw [ih]; simp [List.length_cons]; omega

/-- mapM through StateM preserves list length. -/
theorem List.length_mapM_stateM {α β σ : Type}
    (f : α → StateM σ β) (l : List α) (s : σ) :
    ((l.mapM f s).1).length = l.length := by
  simp [List.mapM]
  have := List.length_mapM_loop_stateM f l [] s
  simp at this; exact this

/-- P-Spec-3: heapTransformExpr mapped over postconditions preserves count. -/
theorem heapTransform_postconditions_count
    (heapVar : Identifier) (model : SemanticModel)
    (postconds : List StmtExprMd) (st : TransformState) :
    ((postconds.mapM (heapTransformExpr heapVar model ·) st).1).length = postconds.length :=
  List.length_mapM_stateM _ postconds st

/-- P-Spec-3: heapTransformExpr mapped over preconditions preserves count. -/
theorem heapTransform_preconditions_count
    (heapVar : Identifier) (model : SemanticModel)
    (preconditions : List StmtExprMd) (st : TransformState) :
    ((preconditions.mapM (heapTransformExpr heapVar model) st).1).length = preconditions.length :=
  List.length_mapM_stateM _ preconditions st

end Strata.Laurel
