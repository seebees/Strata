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

/-! ## P3: Partition completeness

Every non-external procedure appears in either the procedure
names or the function names list. -/

theorem static_proc_in_procs_or_funcs
  (program : Program) (proc : Procedure)
  (h : proc ∈ nonExternalStaticProcs program) :
  proc.name.text ∈ expectedProcedureNames program ∨
  proc.name.text ∈ expectedFunctionNames program := by
  sorry -- needs helper lemmas for List.filter/map membership

theorem instance_proc_in_procs_or_funcs
  (program : Program) (typeName : String) (proc : Procedure)
  (h : (typeName, proc) ∈ nonExternalInstanceProcs program) :
  qualifiedName typeName proc.name.text ∈ expectedProcedureNames program ∨
  qualifiedName typeName proc.name.text ∈ expectedFunctionNames program := by
  sorry -- needs helper lemmas for List.filter/map membership

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

end Strata.Laurel
