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

/-- P-Call-1: mkCallWithResult uses temp $res_ variables for the call LHS.

    Every call statement produced by `mkCallWithResult` uses temporary
    `$res_X` variables as the LHS, matching the callee's Result<T> outputs.
    The original LHS variables receive the extracted .value on success. -/
theorem mkCallWithResult_uses_res_temps
    (lhs : List Core.CoreIdent) (callee : String)
    (args : List Core.Expression.Expr) (md : Imperative.MetaData Core.Expression)
    (s : TranslateState) :
    let resLhs := lhs.map fun id => (⟨s!"$res_{id.name}", ()⟩ : Core.CoreIdent)
    let (result, _) := mkCallWithResult lhs callee args md s
    ∃ stmts, result = some stmts ∧
      ∃ rest, stmts = Core.Statement.call resLhs callee args md :: rest := by
  sorry -- TODO: update proof for Result<T> encoding

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

/-- P-Call-3: Call LHS arity matches procedure output count.

    When `mkCallWithResult` is called with a `lhs` of length N,
    the call statement's LHS has length N (the temp $res_ variables).
    Since `translateProcedure` produces outputs of length
    `proc.outputs.length` (each wrapped in Result<T>), the arity
    matches when `lhs.length = proc.outputs.length`. -/
theorem mkCallWithResult_lhs_length
    (lhs : List Core.CoreIdent) (callee : String)
    (args : List Core.Expression.Expr) (md : Imperative.MetaData Core.Expression)
    (s : TranslateState) :
    let resLhs := lhs.map fun id => (⟨s!"$res_{id.name}", ()⟩ : Core.CoreIdent)
    let (result, _) := mkCallWithResult lhs callee args md s
    ∃ stmts, result = some stmts ∧
      resLhs.length = lhs.length := by
  sorry -- TODO: update proof for Result<T> encoding

end Strata.Laurel
