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
-/

namespace Strata.Laurel

/-! ## P5: Instance call qualification

The qualified name function is deterministic: same inputs,
same output.
-/

@[simp] theorem qualified_name_eq (typeName procName : String) :
  qualifiedName typeName procName = typeName ++ ".." ++ procName := by
  simp [qualifiedName]

/-! ## P3 (partial): Every instance procedure name is qualified -/

theorem instance_proc_name_is_qualified
  (typeName : String) (proc : Procedure) :
  qualifiedName typeName proc.name.text =
  typeName ++ ".." ++ proc.name.text := by
  simp [qualifiedName]

/-! ## P1 (partial): ExceptionResult always declared -/

theorem exceptionResult_always_declared (program : Program) :
  "ExceptionResult" ∈ expectedDatatypeNames program := by
  simp [expectedDatatypeNames]

end Strata.Laurel
