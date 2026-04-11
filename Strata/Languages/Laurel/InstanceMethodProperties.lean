/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
import Strata.Languages.Laurel.Laurel
import Strata.Languages.Laurel.LaurelToCoreTranslator

/-!
# Instance Method Properties

## IM1: Name Consistency

The Core procedure name used when translating an `InstanceCall` at a call site
must equal the Core procedure name used when translating the instance procedure
definition, given that the SemanticModel resolves the callee to the same
`(typeName, proc)` pair stored during resolution.

Both sites use `instanceProcCoreName` (see Decision 7).

### Call site (translateExpr / translateStmt)

When `model.get callee = .instanceProcedure typeName proc`, the translator
computes `instanceProcCoreName typeName.text callee.text`.

### Definition site (translateLaurelToCore)

For each composite type `ct` and instance procedure `proc`, the translator
creates `{ proc with name.text := instanceProcCoreName ct.name.text proc.name.text }`.

### Why the names match

Resolution stores `(.instanceProcedure ct.name proc)` in the SemanticModel,
so `typeName = ct.name`. Resolution also preserves the procedure name:
`callee.text = proc.name.text`. Therefore both sites compute
`instanceProcCoreName typeName.text procName.text` with the same arguments.
-/

namespace Strata.Laurel

/-- `instanceProcCoreName` produces the expected qualified name shape. -/
theorem instanceProcCoreName_shape (typeName procName : String) :
    instanceProcCoreName typeName procName = typeName ++ ".." ++ procName := by
  rfl

/-- P-Name-1: Instance call name consistency.

    The Core procedure name produced at the call site equals the Core procedure
    name produced at the definition site, given that resolution preserves the
    procedure name (`callee.text = proc.name.text`). Both sites use
    `instanceProcCoreName typeName.text procName.text`. -/
theorem instance_call_name_consistency
    (typeName : Identifier) (callee : Identifier) (proc : Procedure)
    (hName : callee.text = proc.name.text) :
    instanceProcCoreName typeName.text callee.text =
    instanceProcCoreName typeName.text proc.name.text := by
  rw [hName]

end Strata.Laurel
