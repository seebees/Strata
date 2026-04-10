/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
import Strata.Languages.Laurel.Laurel
import Strata.Languages.Laurel.ToOrderedProgram
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

Instance methods are not yet supported in the `OrderedProgram` pipeline.
`toLaurelOrdered` emits a `NotYetImplemented` diagnostic for every instance
procedure and does not include them in the ordered declarations.

The theorem below witnesses this: every composite's instance procedures produce
a diagnostic. When instance method support is added, this theorem will fail to
compile, signalling that the name-consistency property (IM1) must be stated and
proved against the new translation.
-/

namespace Strata.Laurel

/-- Every instance procedure on a composite type produces a `NotYetImplemented`
    diagnostic from `toLaurelOrdered`. When instance methods are implemented,
    this will stop compiling — add the real IM1 name-consistency proof then. -/
theorem instance_methods_not_yet_supported
    (program : Program)
    (ct : CompositeType) (proc : Procedure)
    (hType : TypeDefinition.Composite ct ∈ program.types)
    (hProc : proc ∈ ct.instanceProcedures) :
    ∃ d ∈ (toLaurelOrdered program).2,
      d.type = DiagnosticType.NotYetImplemented := by
  unfold toLaurelOrdered
  simp only [List.flatMap]
  refine ⟨_, List.mem_flatMap.mpr ⟨_, hType, List.mem_map.mpr ⟨proc, hProc, rfl⟩⟩, ?_⟩
  unfold Imperative.MetaData.toDiagnostic
  cases Imperative.getFileRange proc.md <;> rfl

end Strata.Laurel
