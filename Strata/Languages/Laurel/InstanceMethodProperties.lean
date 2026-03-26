/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
import Strata.Languages.Laurel.Laurel
import Strata.Languages.Laurel.Resolution
import Strata.Languages.Laurel.LaurelToCoreTranslator

/-!
# Instance Method Properties

## IM1: Name Consistency

The Core procedure name used when translating an InstanceCall at a call site
equals the Core procedure name used when translating the instance procedure
definition, given that the SemanticModel resolves the callee to the same
(typeName, proc) pair that was stored during resolution.

This is a design constraint enforced as a compile-time tripwire: if anyone
changes the name construction at either site, this proof stops compiling.
-/

namespace Strata.Laurel

/--
  IM1: The name produced by `resolveInstanceCallName` (used at call sites)
  equals the name produced by `instanceProcCoreName` (used at definition sites),
  given the SemanticModel maps the callee to `.instanceProcedure typeName proc`.
-/
theorem instance_call_name_consistency
    (model : SemanticModel) (callee : Identifier)
    (typeName : Identifier) (proc : Procedure)
    (h : model.get callee = .instanceProcedure typeName proc) :
    resolveInstanceCallName model callee = some (instanceProcCoreName typeName.text callee.text) := by
  unfold resolveInstanceCallName
  rw [h]

end Strata.Laurel
