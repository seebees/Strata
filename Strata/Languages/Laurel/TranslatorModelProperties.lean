/-
  Copyright Strata Contributors
  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

import Strata.Languages.Laurel.TranslatorModel

/-!
# Translator Model Properties

Theorems about the translator functional model.
See `docs/design/translator-model/decisions.md` D4.

## Status
- ✅ = proven (no sorry)
- 🔧 = stated with sorry (proof in progress)
-/

namespace Strata.Laurel

/-! ## P5: Instance call qualification ✅ -/

@[simp] theorem qualified_name_eq (typeName procName : String) :
  qualifiedName typeName procName = typeName ++ ".." ++ procName := by
  simp [qualifiedName]

theorem instance_proc_name_is_qualified
  (typeName : String) (proc : Procedure) :
  qualifiedName typeName proc.name.text =
  typeName ++ ".." ++ proc.name.text := by
  simp [qualifiedName]

/-! ## P1 (partial): Fixed datatypes always declared ✅ -/

theorem exceptionResult_always_declared (program : Program) :
  "ExceptionResult" ∈ expectedDatatypeNames program := by
  simp [expectedDatatypeNames]

theorem composite_always_declared (program : Program) :
  "Composite" ∈ expectedDatatypeNames program := by
  simp [expectedDatatypeNames]

theorem heap_always_declared (program : Program) :
  "Heap" ∈ expectedDatatypeNames program := by
  simp [expectedDatatypeNames]

theorem typeTag_always_declared (program : Program) :
  "TypeTag" ∈ expectedDatatypeNames program := by
  simp [expectedDatatypeNames]

theorem field_always_declared (program : Program) :
  "Field" ∈ expectedDatatypeNames program := by
  simp [expectedDatatypeNames]

theorem box_always_declared (program : Program) :
  "Box" ∈ expectedDatatypeNames program := by
  simp [expectedDatatypeNames]

/-! ## P1 (partial): Heap operations always in decl names ✅ -/

theorem readField_in_declNames (program : Program) :
  "readField" ∈ expectedDeclNames program := by
  simp [expectedDeclNames, expectedFunctionNames]

theorem updateField_in_declNames (program : Program) :
  "updateField" ∈ expectedDeclNames program := by
  simp [expectedDeclNames, expectedFunctionNames]

theorem increment_in_declNames (program : Program) :
  "increment" ∈ expectedDeclNames program := by
  simp [expectedDeclNames, expectedFunctionNames]

theorem exceptionResult_in_declNames (program : Program) :
  "ExceptionResult" ∈ expectedDeclNames program := by
  simp [expectedDeclNames, expectedDatatypeNames]

/-! ## Helper lemmas for List.filter/map membership -/

private theorem List.mem_map_of_mem' {f : α → β} {a : α} {l : List α}
  (h : a ∈ l) : f a ∈ l.map f := by
  exact List.mem_map.mpr ⟨a, h, rfl⟩

private theorem List.mem_filter_intro {p : α → Bool} {a : α} {l : List α}
  (hm : a ∈ l) (hp : p a = true) : a ∈ l.filter p := by
  exact List.mem_filter.mpr ⟨hm, hp⟩

/-! ## P3: Partition completeness ✅ -/

theorem static_proc_in_procs_or_funcs
  (program : Program) (proc : Procedure)
  (h : proc ∈ nonExternalStaticProcs program) :
  proc.name.text ∈ expectedProcedureNames program ∨
  proc.name.text ∈ expectedFunctionNames program := by
  by_cases hf : proc.isFunctional
  · right; simp only [expectedFunctionNames]
    have : proc ∈ (nonExternalStaticProcs program).filter (·.isFunctional) :=
      List.mem_filter.mpr ⟨h, hf⟩
    have : proc.name.text ∈ ((nonExternalStaticProcs program).filter (·.isFunctional)).map (·.name.text) :=
      List.mem_map.mpr ⟨proc, ‹_›, rfl⟩
    simp_all [List.mem_append]
  · left; simp only [expectedProcedureNames]
    have hff : proc.isFunctional = false := by cases hb : proc.isFunctional <;> simp_all
    have hneg : (!proc.isFunctional) = true := by rw [hff]; rfl
    have : proc ∈ (nonExternalStaticProcs program).filter (!·.isFunctional) :=
      List.mem_filter.mpr ⟨h, hneg⟩
    have : proc.name.text ∈ ((nonExternalStaticProcs program).filter (!·.isFunctional)).map (·.name.text) :=
      List.mem_map.mpr ⟨proc, ‹_›, rfl⟩
    simp_all [List.mem_append]

theorem instance_proc_in_procs_or_funcs
  (program : Program) (typeName : String) (proc : Procedure)
  (h : (typeName, proc) ∈ nonExternalInstanceProcs program) :
  qualifiedName typeName proc.name.text ∈ expectedProcedureNames program ∨
  qualifiedName typeName proc.name.text ∈ expectedFunctionNames program := by
  by_cases hf : proc.isFunctional
  · right; simp only [expectedFunctionNames]
    have : (typeName, proc) ∈ (nonExternalInstanceProcs program).filter (·.2.isFunctional) :=
      List.mem_filter.mpr ⟨h, hf⟩
    have : qualifiedName typeName proc.name.text ∈
        ((nonExternalInstanceProcs program).filter (·.2.isFunctional)).map
          (fun (t, p) => qualifiedName t p.name.text) :=
      List.mem_map.mpr ⟨(typeName, proc), ‹_›, rfl⟩
    simp_all [List.mem_append]
  · left; simp only [expectedProcedureNames]
    have hff : proc.isFunctional = false := by cases hb : proc.isFunctional <;> simp_all
    have hneg : (!proc.isFunctional) = true := by rw [hff]; rfl
    have : (typeName, proc) ∈ (nonExternalInstanceProcs program).filter (!·.2.isFunctional) :=
      List.mem_filter.mpr ⟨h, by simp [hneg]⟩
    have : qualifiedName typeName proc.name.text ∈
        ((nonExternalInstanceProcs program).filter (!·.2.isFunctional)).map
          (fun (t, p) => qualifiedName t p.name.text) :=
      List.mem_map.mpr ⟨(typeName, proc), ‹_›, rfl⟩
    simp_all [List.mem_append]

/-! ## P1: Subsumption — component names are in declNames ✅ -/

theorem proc_names_subset_declNames (program : Program) :
  ∀ n, n ∈ expectedProcedureNames program → n ∈ expectedDeclNames program := by
  intro n h
  simp [expectedDeclNames, List.mem_append]
  left; exact h

theorem func_names_subset_declNames (program : Program) :
  ∀ n, n ∈ expectedFunctionNames program → n ∈ expectedDeclNames program := by
  intro n h
  simp [expectedDeclNames, List.mem_append]
  right; left; exact h

theorem dtype_names_subset_declNames (program : Program) :
  ∀ n, n ∈ expectedDatatypeNames program → n ∈ expectedDeclNames program := by
  intro n h
  simp [expectedDeclNames, List.mem_append]
  right; right; left; exact h

theorem axiom_names_subset_declNames (program : Program) :
  ∀ n, n ∈ expectedAxiomNames program → n ∈ expectedDeclNames program := by
  intro n h
  simp [expectedDeclNames, List.mem_append]
  right; right; right; exact h

/-! ## P1: Name consistency — referenced names are declared

Infrastructure names (readField, updateField, increment) are
always declared regardless of program content. This means any
FieldSelect, field Assign, or New in a body references a name
that exists.

For StaticCall and InstanceCall, the callee must be a procedure
in the program — this is the well-formedness condition that the
resolution pass guarantees.
-/

/-- FieldSelect always references readField ✅ (depends on axiom referencedNamesInExprVal_fieldSelect) -/
theorem fieldSelect_refs_readField (target : WithMetadata StmtExpr) (fieldId : Identifier) :
  "readField" ∈ referencedNamesInExprVal (.FieldSelect target fieldId) := by
  rw [referencedNamesInExprVal_fieldSelect]; simp

/-- New always references increment ✅ (depends on axiom referencedNamesInExprVal_new) -/
theorem new_refs_increment (className : Identifier) :
  "increment" ∈ referencedNamesInExprVal (.New className) := by
  rw [referencedNamesInExprVal_new]; simp

/-- A program is well-formed if every referenced name in every
    procedure body is a declared name -/
@[expose] def wellFormedCalls (program : Program) : Prop :=
  ∀ name ∈ allReferencedNames program,
    name ∈ expectedDeclNames program

/-- P1: name consistency for well-formed programs -/
theorem name_consistency
  (program : Program)
  (hwf : wellFormedCalls program) :
  ∀ name ∈ allReferencedNames program,
    name ∈ expectedDeclNames program :=
  hwf

/-! ## P4: Heap threading — signature properties ✅ -/

/-- Instance procedures that access heap always have $heap_in as first input -/
theorem heap_accessing_instance_has_heap_in
  (proc : Procedure) (accessesHeap : Bool) (h : accessesHeap = true) :
  ("$heap_in", "Heap") ∈ expectedInputs proc true accessesHeap := by
  simp [expectedInputs, h]

private theorem mem_append_left' {a : α} {l₁ l₂ : List α} (h : a ∈ l₁) : a ∈ l₁ ++ l₂ := by
  induction l₁ with
  | nil => contradiction
  | cons x xs ih =>
    cases h with
    | head => exact List.Mem.head _
    | tail _ h => exact List.Mem.tail _ (ih h)

private theorem mem_append_right' {a : α} (l₁ : List α) {l₂ : List α} (h : a ∈ l₂) : a ∈ l₁ ++ l₂ := by
  induction l₁ with
  | nil => exact h
  | cons x xs ih => exact List.Mem.tail _ (ih)

/-- Instance procedures always have self in inputs -/
theorem instance_proc_has_self (proc : Procedure) (accessesHeap : Bool) :
  ("self", "Composite") ∈ expectedInputs proc true accessesHeap := by
  show ("self", "Composite") ∈
    (if accessesHeap then [("$heap_in", "Heap")] else []) ++
    [("self", "Composite")] ++
    ((proc.inputs.map fun p => (p.name.text, coreTypeName p.type.val)).filter (fun (n, _) => n != "self"))
  cases accessesHeap
  · exact mem_append_left' (List.Mem.head _)
  · exact mem_append_left' (mem_append_right' _ (List.Mem.head _))

/-- All procedures have $result in outputs -/
theorem proc_has_result (proc : Procedure) (accessesHeap : Bool) :
  ("$result", "ExceptionResult") ∈ expectedOutputs proc accessesHeap := by
  unfold expectedOutputs
  cases accessesHeap <;> simp [List.mem_append]

/-- Heap-accessing procedures have $heap in outputs -/
theorem heap_accessing_has_heap_out (proc : Procedure) :
  ("$heap", "Heap") ∈ expectedOutputs proc true := by
  unfold expectedOutputs
  simp

/-! ## P4 completeness: heap flag ↔ heap parameters -/

/-- accessesHeap = true → $heap_in in inputs -/
theorem heap_true_implies_heap_in (proc : Procedure) (isInstance : Bool) :
  ("$heap_in", "Heap") ∈ expectedInputs proc isInstance true := by
  show ("$heap_in", "Heap") ∈
    [("$heap_in", "Heap")] ++
    (if isInstance then [("self", "Composite")] else []) ++
    _
  exact mem_append_left' (List.Mem.head _)

/-- accessesHeap = true → $heap in outputs -/
theorem heap_true_implies_heap_out (proc : Procedure) :
  ("$heap", "Heap") ∈ expectedOutputs proc true := by
  unfold expectedOutputs; simp

/-- accessesHeap = false → $heap NOT in outputs -/
theorem heap_false_implies_no_heap_out (proc : Procedure)
  (hNoClash : ∀ p ∈ proc.outputs, ¬(p.name.text = "$heap" ∧ coreTypeName p.type.val = "Heap")) :
  ("$heap", "Heap") ∉ expectedOutputs proc false := by
  unfold expectedOutputs; dsimp
  -- Goal: ("$heap", "Heap") ∉ proc.outputs.map (fun p => ...) ++ [("$result", "ExceptionResult")]
  intro h
  rw [List.mem_append] at h
  rcases h with h | h
  · -- h : ("$heap", "Heap") ∈ proc.outputs.map ...
    rw [List.mem_map] at h
    obtain ⟨p, hp, heq⟩ := h
    exact hNoClash p hp ⟨congrArg Prod.fst heq, congrArg Prod.snd heq⟩
  · -- h : ("$heap", "Heap") ∈ [("$result", "ExceptionResult")]
    simp at h

/-! ## Modifies clause properties -/

/-- A non-empty modifies clause implies the procedure reads heap directly -/
theorem modifies_implies_reads_heap (proc : Procedure)
  (postconds : List (WithMetadata StmtExpr))
  (impl : Option (WithMetadata StmtExpr))
  (modif : List (WithMetadata StmtExpr))
  (hBody : proc.body = .Opaque postconds impl modif)
  (hModif : !modif.isEmpty = true) :
  procReadsHeapDirectly proc = true :=
  procReadsHeapDirectly_opaque_modifies proc postconds impl modif hBody hModif

/-- A non-empty modifies clause implies the procedure writes heap directly -/
theorem modifies_implies_writes_heap (proc : Procedure)
  (postconds : List (WithMetadata StmtExpr))
  (impl : Option (WithMetadata StmtExpr))
  (modif : List (WithMetadata StmtExpr))
  (hBody : proc.body = .Opaque postconds impl modif)
  (hModif : !modif.isEmpty = true) :
  procWritesHeapDirectly proc = true :=
  procWritesHeapDirectly_opaque_modifies proc postconds impl modif hBody hModif

/-- External procedures never read heap directly -/
theorem external_no_reads_heap (proc : Procedure)
  (hBody : proc.body = .External)
  (hNoPrecond : proc.preconditions = []) :
  procReadsHeapDirectly proc = false :=
  procReadsHeapDirectly_external proc hBody hNoPrecond

/-- External procedures never write heap directly -/
theorem external_no_writes_heap (proc : Procedure)
  (hBody : proc.body = .External)
  (hNoPrecond : proc.preconditions = []) :
  procWritesHeapDirectly proc = false :=
  procWritesHeapDirectly_external proc hBody hNoPrecond

/-! ## P6: Exception propagation soundness -/

/-- Every static procedure call in a pattern includes exception propagation.
    This means the translator never silently drops exceptions. -/
theorem static_proc_call_propagates_exceptions
  (isFunction : String → Bool) (callee : Identifier) (args : List (WithMetadata StmtExpr))
  (hNotFunc : isFunction callee.text = false) :
  "$result" ∈ (predictPattern isFunction (.StaticCall callee args)).referencedNames := by
  rw [static_proc_call_has_propagation isFunction callee args hNotFunc,
      referencedNames_callWithPropagation]
  simp

/-- Every instance procedure call in a pattern includes exception propagation. -/
theorem instance_proc_call_propagates_exceptions
  (isFunction : String → Bool) (target : WithMetadata StmtExpr) (callee : Identifier)
  (args : List (WithMetadata StmtExpr))
  (hNotFunc : isFunction callee.text = false) :
  "$result" ∈ (predictPattern isFunction (.InstanceCall target callee args)).referencedNames := by
  rw [instance_proc_call_has_propagation isFunction target callee args hNotFunc,
      referencedNames_callWithPropagation]
  simp

/-- Return-via-procedure-call includes exception propagation. -/
theorem return_proc_call_propagates_exceptions
  (isFunction : String → Bool) (callee : Identifier) (args : List (WithMetadata StmtExpr))
  (md : MetaData)
  (hNotFunc : isFunction callee.text = false) :
  "$result" ∈ (predictPattern isFunction (.Return (some ⟨.StaticCall callee args, md⟩))).referencedNames := by
  rw [return_static_proc_call_pattern isFunction callee args md hNotFunc,
      referencedNames_returnCall]
  simp

/-- Local variable initializer is preserved in translation pattern. -/
theorem local_var_preserves_init
  (isFunction : String → Bool) (name : Identifier) (ty : WithMetadata HighType)
  (init : WithMetadata StmtExpr) :
  ∃ p, predictPattern isFunction (.LocalVariable name ty (some init)) = .initVar name.text (some p) := by
  exact ⟨predictPattern isFunction init.val,
    local_var_init_has_value isFunction name ty init⟩

end Strata.Laurel
