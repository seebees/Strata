/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
import Strata.Languages.Laurel.Laurel
import Strata.Languages.Laurel.LaurelToCoreTranslator

/-!
# Instance Method Properties

## IM1: Name Consistency (design tripwire)

The Core procedure name used when translating an `InstanceCall` at a call site
must equal the Core procedure name used when translating the instance procedure
definition, given that the SemanticModel resolves the callee to the same
`(typeName, proc)` pair stored during resolution.

Both sites must use `instanceProcCoreName` (see Decision 7).

### Current status

Instance methods are not yet supported in the translator pipeline.
`translateWithLaurel` → `translateTypes` emits a `NotYetImplemented` diagnostic
for every instance procedure on a composite type, and `translateStmt` returns
an empty list for `InstanceCall` statements.

When instance method support is added, the `InstanceCall` cases will change,
and this file should be updated with the real IM1 name-consistency proof.

The definition below witnesses that `instanceProcCoreName` exists and has the
expected shape. When instance methods are implemented, this file should be
updated with the real IM1 name-consistency proof.
-/

namespace Strata.Laurel

/-- Witness that `instanceProcCoreName` produces the expected qualified name.
    When instance methods are implemented, add the real IM1 proof here. -/
theorem instanceProcCoreName_shape (typeName procName : String) :
    instanceProcCoreName typeName procName = typeName ++ ".." ++ procName := by
  rfl

end Strata.Laurel
