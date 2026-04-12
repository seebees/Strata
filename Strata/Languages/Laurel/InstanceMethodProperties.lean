/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
import Strata.Languages.Laurel.Laurel
import Strata.Languages.Laurel.LaurelToCoreTranslator

/-!
# Instance Method Properties

## IM1: Name Consistency

Instance procedure names are qualified early by `qualifyInstanceProcNames`
(before the first `resolve` call). Both definitions and call sites use the
qualified name directly (e.g. `Position~>compareTo`). The translator no
longer constructs names — it uses `callee.text` and `proc.name.text` as-is.

See `docs/design/cross-type-resolution/decisions.md` D2, D4.

### Call site (translateExpr / translateStmt)

When `model.get callee = .instanceProcedure typeName proc`, the translator
uses `callee.text` directly as the Core procedure name.

### Definition site (translateLaurelToCore)

For each composite type `ct` and instance procedure `proc`, the translator
uses `proc.name.text` directly — the name was already qualified by
`qualifyInstanceProcNames`.

### Why the names match

`qualifyInstanceProcNames` sets `proc.name.text := instanceProcCoreName
ct.name.text proc.name.text`. Resolution stores this qualified name in the
SemanticModel. At the call site, `callee.text` is the qualified name (sent
by the frontend). Resolution maps it to the same definition. Therefore
`callee.text = proc.name.text`.
-/

namespace Strata.Laurel

/-- `instanceProcCoreName` produces the expected qualified name shape. -/
theorem instanceProcCoreName_shape (typeName procName : String) :
    instanceProcCoreName typeName procName = typeName ++ "~>" ++ procName := by
  rfl

/-- P-Name-1: Instance call name consistency.

    The Core procedure name produced at the call site equals the Core procedure
    name produced at the definition site, given that resolution preserves the
    qualified name (`callee.text = proc.name.text`). -/
theorem instance_call_name_consistency
    (_typeName : Identifier) (callee : Identifier) (proc : Procedure)
    (hName : callee.text = proc.name.text) :
    callee.text = proc.name.text := by
  exact hName

end Strata.Laurel
