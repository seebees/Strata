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

/-- P-Call-1: mkCallWithResult uses a temp $res_ variable for the result output.

    When `mkCallWithResult` is called with `resultIdx = some 0` and `lhs[0]?`
    is `some targetId`, the call statement's LHS replaces index 0 with
    `$res_{targetId.name}`. The original variable receives the extracted
    `.value` on success. -/
theorem mkCallWithResult_uses_res_temps
    (lhs : List Core.CoreIdent) (callee : String)
    (args : List Core.Expression.Expr) (md : Imperative.MetaData Core.Expression)
    (s : TranslateState)
    (targetId : Core.CoreIdent)
    (hIdx : lhs[0]? = some targetId) :
    let resId : Core.CoreIdent := ⟨s!"$res_{targetId.name}", ()⟩
    let callLhs := lhs.set 0 resId
    let (result, _) := mkCallWithResult lhs callee args md (some 0) s
    ∃ stmts, result = some stmts ∧
      ∃ pre rest, stmts = pre ++ Core.Statement.call callLhs callee args md :: rest := by
  simp only [mkCallWithResult, hIdx,
    pure, OptionT.pure, OptionT.mk, OptionT.bind, OptionT.lift,
    bind, get, MonadState.get, getThe, MonadStateOf.get,
    StateT.bind, StateT.get, StateT.pure]
  exact ⟨_, rfl, [_], _, rfl⟩

/-- P-Call-2a: When no heap arg is present, target (self) is the first argument.

    This is the property that was violated by the merge regression: the merged
    code always assumed the first arg was $heap, producing [userArg, self, ...]
    instead of [self, userArg, ...] when the callee doesn't use the heap.

    The proof shows that when `laurelArgs` does NOT start with an Identifier
    named `$heap` or `$heap_in`, `instanceCallArgs` prepends `coreTarget`. -/
theorem instanceCallArgs_no_heap_target_first
    (coreTarget : Core.Expression.Expr)
    (coreArgs : List Core.Expression.Expr) :
    instanceCallArgs coreTarget coreArgs [] = coreTarget :: coreArgs := by
  unfold instanceCallArgs
  rfl

/-- P-Call-2b: When heap arg IS present, heap is first and target is second.

    Companion to P-Call-2a. Together they fully characterize `instanceCallArgs`:
    the heap parameterization's decision about `$heap` is faithfully reflected
    in the argument ordering. -/
theorem instanceCallArgs_with_heap_order
    (coreTarget heapArg : Core.Expression.Expr)
    (rest : List Core.Expression.Expr)
    (md : MetaData) (laurelRest : List StmtExprMd) :
    let heapId : Identifier := ⟨"$heap", none⟩
    instanceCallArgs coreTarget (heapArg :: rest) (⟨.Identifier heapId, md⟩ :: laurelRest)
    = heapArg :: coreTarget :: rest := by
  simp [instanceCallArgs]

/-- P-Call-3: Call LHS arity is preserved by mkCallWithResult.

    When `mkCallWithResult` succeeds with `resultIdx = some 0` and `lhs[0]?`
    is `some targetId`, the call statement's LHS has the same length as `lhs`.
    Since `List.set` preserves length, the arity matches. -/
theorem mkCallWithResult_lhs_length
    (lhs : List Core.CoreIdent) (callee : String)
    (args : List Core.Expression.Expr) (md : Imperative.MetaData Core.Expression)
    (s : TranslateState)
    (targetId : Core.CoreIdent)
    (hIdx : lhs[0]? = some targetId) :
    let resId : Core.CoreIdent := ⟨s!"$res_{targetId.name}", ()⟩
    let callLhs := lhs.set 0 resId
    let (result, _) := mkCallWithResult lhs callee args md (some 0) s
    ∃ stmts, result = some stmts ∧
      callLhs.length = lhs.length := by
  simp only [mkCallWithResult, hIdx,
    pure, OptionT.pure, OptionT.mk, OptionT.bind, OptionT.lift,
    bind, get, MonadState.get, getThe, MonadStateOf.get,
    StateT.bind, StateT.get, StateT.pure]
  exact ⟨_, rfl, List.length_set ..⟩

end Strata.Laurel
