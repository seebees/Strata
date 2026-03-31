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

/-- Equation lemma: FieldSelect case (WF reduction — needs Lean 4 equation compiler support) -/
@[simp] theorem referencedNamesInExprMd_fieldSelect (target : WithMetadata StmtExpr) (fieldId : Identifier) (md : MetaData) :
  referencedNamesInExprMd ⟨.FieldSelect target fieldId, md⟩ = ["readField"] ++ referencedNamesInExprMd target := by
  sorry

/-- Equation lemma: New case -/
@[simp] theorem referencedNamesInExprMd_new (className : Identifier) (md : MetaData) :
  referencedNamesInExprMd ⟨.New className, md⟩ = ["increment"] := by
  sorry

/-- FieldSelect always references readField -/
theorem fieldSelect_refs_readField (target : WithMetadata StmtExpr) (fieldId : Identifier) (md : MetaData) :
  "readField" ∈ referencedNamesInExprMd ⟨.FieldSelect target fieldId, md⟩ := by
  rw [referencedNamesInExprMd_fieldSelect]; simp

/-- New always references increment -/
theorem new_refs_increment (className : Identifier) (md : MetaData) :
  "increment" ∈ referencedNamesInExprMd ⟨.New className, md⟩ := by
  rw [referencedNamesInExprMd_new]; simp

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

end Strata.Laurel
