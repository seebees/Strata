/-
  Copyright Strata Contributors
  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
import Strata.Languages.Laurel.LaurelToCoreTranslator
import Strata.Languages.Laurel.TranslatorEqLemmas

/-!
# Translator Pipeline Properties

Direct structural properties of the Laurel→Core translation pipeline.
Each property pattern-matches on `StmtExpr` constructors, so adding a
new constructor creates a compile-time proof obligation.

See `docs/design/translator-proof/design.md` for the full design.

## Tier 1: Structural Integrity

P-Struct-1: translateExpr/translateStmt succeeds for each constructor
(given appropriate preconditions on sub-expressions).
-/

namespace Strata.Laurel

open Strata.Core Lambda

/-! ### P-Struct-1a: Expression translation succeeds — literals

Literals translate unconditionally. No preconditions needed. -/

/-- Literal bool always translates. -/
theorem translateExpr_succeeds_literalBool (b : Bool) (md : MetaData) (bv : List Identifier) (pc : Bool) (s : TranslateState) :
    (translateExpr ⟨.LiteralBool b, md⟩ bv pc s).1.isSome = true := by
  simp [translateExpr_eq_literalBool]

/-- Literal int always translates. -/
theorem translateExpr_succeeds_literalInt (i : Int) (md : MetaData) (bv : List Identifier) (pc : Bool) (s : TranslateState) :
    (translateExpr ⟨.LiteralInt i, md⟩ bv pc s).1.isSome = true := by
  simp [translateExpr_eq_literalInt]

/-- Literal string always translates. -/
theorem translateExpr_succeeds_literalString (str : String) (md : MetaData) (bv : List Identifier) (pc : Bool) (s : TranslateState) :
    (translateExpr ⟨.LiteralString str, md⟩ bv pc s).1.isSome = true := by
  simp [translateExpr_eq_literalString]

/-- Static call with no args always translates. -/
theorem translateExpr_succeeds_staticCall_noArgs (callee : Identifier) (md : MetaData) (bv : List Identifier) (s : TranslateState)
    (hNotPure : s.model.isFunction callee = false) :
    (translateExpr ⟨.StaticCall callee [], md⟩ bv false s).1.isSome = true := by
  simp [translateExpr_eq_staticCall_noArgs callee md bv s hNotPure]

/-! ### P-Struct-1b: Expression translation succeeds — compound expressions

Compound expressions succeed when their sub-expressions succeed. -/

/-- Static call with one arg succeeds when the arg succeeds. -/
theorem translateExpr_succeeds_staticCall_oneArg
    (callee : Identifier) (a1 : StmtExprMd) (md : MetaData) (bv : List Identifier)
    (s s1 : TranslateState) (r1 : Core.Expression.Expr)
    (hNotPure : s.model.isFunction callee = false)
    (h1 : translateExpr a1 bv false s = (some r1, s1)) :
    (translateExpr ⟨.StaticCall callee [a1], md⟩ bv false s).1.isSome = true := by
  simp [translateExpr_eq_staticCall_oneArg callee a1 md bv s s1 r1 hNotPure h1]

/-- Static call with two args succeeds when both args succeed. -/
theorem translateExpr_succeeds_staticCall_twoArgs
    (callee : Identifier) (a1 a2 : StmtExprMd) (md : MetaData) (bv : List Identifier)
    (s s1 s2 : TranslateState) (r1 r2 : Core.Expression.Expr)
    (hNotPure : s.model.isFunction callee = false)
    (h1 : translateExpr a1 bv false s = (some r1, s1))
    (h2 : translateExpr a2 bv false s1 = (some r2, s2)) :
    (translateExpr ⟨.StaticCall callee [a1, a2], md⟩ bv false s).1.isSome = true := by
  simp [translateExpr_eq_staticCall_twoArgs callee a1 a2 md bv s s1 s2 r1 r2 hNotPure h1 h2]

/-- PrimitiveOp Eq succeeds when both args succeed. -/
theorem translateExpr_succeeds_primEq
    (e1 e2 : StmtExprMd) (md : MetaData) (bv : List Identifier) (pc : Bool)
    (s s1 s2 : TranslateState) (r1 r2 : Core.Expression.Expr)
    (h1 : translateExpr e1 bv pc s = (some r1, s1))
    (h2 : translateExpr e2 bv pc s1 = (some r2, s2)) :
    (translateExpr ⟨.PrimitiveOp .Eq [e1, e2], md⟩ bv pc s).1.isSome = true := by
  simp [translateExpr_eq_primEq e1 e2 md bv pc s s1 s2 r1 r2 h1 h2]

/-- PrimitiveOp Neq succeeds when both args succeed. -/
theorem translateExpr_succeeds_primNeq
    (e1 e2 : StmtExprMd) (md : MetaData) (bv : List Identifier) (pc : Bool)
    (s s1 s2 : TranslateState) (r1 r2 : Core.Expression.Expr)
    (h1 : translateExpr e1 bv pc s = (some r1, s1))
    (h2 : translateExpr e2 bv pc s1 = (some r2, s2)) :
    (translateExpr ⟨.PrimitiveOp .Neq [e1, e2], md⟩ bv pc s).1.isSome = true := by
  simp [translateExpr_eq_primNeq e1 e2 md bv pc s s1 s2 r1 r2 h1 h2]

/-- PrimitiveOp Not succeeds when the arg succeeds. -/
theorem translateExpr_succeeds_primNot
    (e : StmtExprMd) (md : MetaData) (bv : List Identifier) (pc : Bool)
    (s s1 : TranslateState) (r : Core.Expression.Expr)
    (h : translateExpr e bv pc s = (some r, s1)) :
    (translateExpr ⟨.PrimitiveOp .Not [e], md⟩ bv pc s).1.isSome = true := by
  simp [translateExpr_eq_primNot e md bv pc s s1 r h]

/-- PrimitiveOp And succeeds when both args succeed. -/
theorem translateExpr_succeeds_primAnd
    (e1 e2 : StmtExprMd) (md : MetaData) (bv : List Identifier) (pc : Bool)
    (s s1 s2 : TranslateState) (r1 r2 : Core.Expression.Expr)
    (h1 : translateExpr e1 bv pc s = (some r1, s1))
    (h2 : translateExpr e2 bv pc s1 = (some r2, s2)) :
    (translateExpr ⟨.PrimitiveOp .And [e1, e2], md⟩ bv pc s).1.isSome = true := by
  simp [translateExpr_eq_primAnd e1 e2 md bv pc s s1 s2 r1 r2 h1 h2]

/-- PrimitiveOp Or succeeds when both args succeed. -/
theorem translateExpr_succeeds_primOr
    (e1 e2 : StmtExprMd) (md : MetaData) (bv : List Identifier) (pc : Bool)
    (s s1 s2 : TranslateState) (r1 r2 : Core.Expression.Expr)
    (h1 : translateExpr e1 bv pc s = (some r1, s1))
    (h2 : translateExpr e2 bv pc s1 = (some r2, s2)) :
    (translateExpr ⟨.PrimitiveOp .Or [e1, e2], md⟩ bv pc s).1.isSome = true := by
  simp [translateExpr_eq_primOr e1 e2 md bv pc s s1 s2 r1 r2 h1 h2]

/-- PrimitiveOp Add (int) succeeds when both args succeed and types are not real. -/
theorem translateExpr_succeeds_primAdd_int
    (e1 e2 : StmtExprMd) (md : MetaData) (bv : List Identifier) (pc : Bool)
    (s s1 s2 : TranslateState) (r1 r2 : Core.Expression.Expr)
    (h1 : translateExpr e1 bv pc s = (some r1, s1))
    (h2 : translateExpr e2 bv pc s1 = (some r2, s2))
    (hNotReal : ∀ x, computeExprType s.model e1 ≠ ⟨.TReal, x⟩) :
    (translateExpr ⟨.PrimitiveOp .Add [e1, e2], md⟩ bv pc s).1.isSome = true := by
  simp [translateExpr_eq_primAdd_int e1 e2 md bv pc s s1 s2 r1 r2 h1 h2 hNotReal]

/-- PrimitiveOp Sub (int) succeeds when both args succeed and types are not real. -/
theorem translateExpr_succeeds_primSub_int
    (e1 e2 : StmtExprMd) (md : MetaData) (bv : List Identifier) (pc : Bool)
    (s s1 s2 : TranslateState) (r1 r2 : Core.Expression.Expr)
    (h1 : translateExpr e1 bv pc s = (some r1, s1))
    (h2 : translateExpr e2 bv pc s1 = (some r2, s2))
    (hNotReal : ∀ x, computeExprType s.model e1 ≠ ⟨.TReal, x⟩) :
    (translateExpr ⟨.PrimitiveOp .Sub [e1, e2], md⟩ bv pc s).1.isSome = true := by
  simp [translateExpr_eq_primSub_int e1 e2 md bv pc s s1 s2 r1 r2 h1 h2 hNotReal]

/-- PrimitiveOp Mul (int) succeeds when both args succeed and types are not real. -/
theorem translateExpr_succeeds_primMul_int
    (e1 e2 : StmtExprMd) (md : MetaData) (bv : List Identifier) (pc : Bool)
    (s s1 s2 : TranslateState) (r1 r2 : Core.Expression.Expr)
    (h1 : translateExpr e1 bv pc s = (some r1, s1))
    (h2 : translateExpr e2 bv pc s1 = (some r2, s2))
    (hNotReal : ∀ x, computeExprType s.model e1 ≠ ⟨.TReal, x⟩) :
    (translateExpr ⟨.PrimitiveOp .Mul [e1, e2], md⟩ bv pc s).1.isSome = true := by
  simp [translateExpr_eq_primMul_int e1 e2 md bv pc s s1 s2 r1 r2 h1 h2 hNotReal]

/-- PrimitiveOp Lt (int) succeeds when both args succeed and types are not real. -/
theorem translateExpr_succeeds_primLt_int
    (e1 e2 : StmtExprMd) (md : MetaData) (bv : List Identifier) (pc : Bool)
    (s s1 s2 : TranslateState) (r1 r2 : Core.Expression.Expr)
    (h1 : translateExpr e1 bv pc s = (some r1, s1))
    (h2 : translateExpr e2 bv pc s1 = (some r2, s2))
    (hNotReal : ∀ x, computeExprType s.model e1 ≠ ⟨.TReal, x⟩) :
    (translateExpr ⟨.PrimitiveOp .Lt [e1, e2], md⟩ bv pc s).1.isSome = true := by
  simp [translateExpr_eq_primLt_int e1 e2 md bv pc s s1 s2 r1 r2 h1 h2 hNotReal]

/-- PrimitiveOp Gt (int) succeeds when both args succeed and types are not real. -/
theorem translateExpr_succeeds_primGt_int
    (e1 e2 : StmtExprMd) (md : MetaData) (bv : List Identifier) (pc : Bool)
    (s s1 s2 : TranslateState) (r1 r2 : Core.Expression.Expr)
    (h1 : translateExpr e1 bv pc s = (some r1, s1))
    (h2 : translateExpr e2 bv pc s1 = (some r2, s2))
    (hNotReal : ∀ x, computeExprType s.model e1 ≠ ⟨.TReal, x⟩) :
    (translateExpr ⟨.PrimitiveOp .Gt [e1, e2], md⟩ bv pc s).1.isSome = true := by
  simp [translateExpr_eq_primGt_int e1 e2 md bv pc s s1 s2 r1 r2 h1 h2 hNotReal]

/-- PrimitiveOp Leq (int) succeeds when both args succeed and types are not real. -/
theorem translateExpr_succeeds_primLeq_int
    (e1 e2 : StmtExprMd) (md : MetaData) (bv : List Identifier) (pc : Bool)
    (s s1 s2 : TranslateState) (r1 r2 : Core.Expression.Expr)
    (h1 : translateExpr e1 bv pc s = (some r1, s1))
    (h2 : translateExpr e2 bv pc s1 = (some r2, s2))
    (hNotReal : ∀ x, computeExprType s.model e1 ≠ ⟨.TReal, x⟩) :
    (translateExpr ⟨.PrimitiveOp .Leq [e1, e2], md⟩ bv pc s).1.isSome = true := by
  simp [translateExpr_eq_primLeq_int e1 e2 md bv pc s s1 s2 r1 r2 h1 h2 hNotReal]

/-- PrimitiveOp Geq (int) succeeds when both args succeed and types are not real. -/
theorem translateExpr_succeeds_primGeq_int
    (e1 e2 : StmtExprMd) (md : MetaData) (bv : List Identifier) (pc : Bool)
    (s s1 s2 : TranslateState) (r1 r2 : Core.Expression.Expr)
    (h1 : translateExpr e1 bv pc s = (some r1, s1))
    (h2 : translateExpr e2 bv pc s1 = (some r2, s2))
    (hNotReal : ∀ x, computeExprType s.model e1 ≠ ⟨.TReal, x⟩) :
    (translateExpr ⟨.PrimitiveOp .Geq [e1, e2], md⟩ bv pc s).1.isSome = true := by
  simp [translateExpr_eq_primGeq_int e1 e2 md bv pc s s1 s2 r1 r2 h1 h2 hNotReal]

/-- IfThenElse (with else) succeeds when all three sub-expressions succeed. -/
theorem translateExpr_succeeds_ite
    (c t e : StmtExprMd) (md : MetaData) (bv : List Identifier) (pc : Bool)
    (s s1 s2 s3 : TranslateState) (rc rt re : Core.Expression.Expr)
    (hc : translateExpr c bv pc s = (some rc, s1))
    (ht : translateExpr t bv pc s1 = (some rt, s2))
    (he : translateExpr e bv pc s2 = (some re, s3)) :
    (translateExpr ⟨.IfThenElse c t (some e), md⟩ bv pc s).1.isSome = true := by
  simp [translateExpr_eq_ite c t e md bv pc s s1 s2 s3 rc rt re hc ht he]

/-! ### P-Struct-1c: Expression translation preserves state for literals -/

theorem translateExpr_state_literalBool (b : Bool) (md : MetaData) (bv : List Identifier) (pc : Bool) (s : TranslateState) :
    (translateExpr ⟨.LiteralBool b, md⟩ bv pc s).2 = s := by
  simp [translateExpr_eq_literalBool]

theorem translateExpr_state_literalInt (i : Int) (md : MetaData) (bv : List Identifier) (pc : Bool) (s : TranslateState) :
    (translateExpr ⟨.LiteralInt i, md⟩ bv pc s).2 = s := by
  simp [translateExpr_eq_literalInt]

theorem translateExpr_state_literalString (str : String) (md : MetaData) (bv : List Identifier) (pc : Bool) (s : TranslateState) :
    (translateExpr ⟨.LiteralString str, md⟩ bv pc s).2 = s := by
  simp [translateExpr_eq_literalString]

theorem translateExpr_state_staticCall_noArgs (callee : Identifier) (md : MetaData) (bv : List Identifier) (s : TranslateState)
    (hNotPure : s.model.isFunction callee = false) :
    (translateExpr ⟨.StaticCall callee [], md⟩ bv false s).2 = s := by
  simp [translateExpr_eq_staticCall_noArgs callee md bv s hNotPure]

/-! ### P-Struct-1d: Statement translation succeeds -/

/-- Return none always translates. -/
theorem translateStmt_succeeds_return_none (outParams : List Parameter) (md : MetaData) (s : TranslateState) :
    (translateStmt outParams ⟨.Return none, md⟩ s).1.isSome = true := by
  simp [translateStmt_eq_return_none]

/-- LocalVariable with no initializer always translates. -/
theorem translateStmt_succeeds_localVar_noInit
    (outParams : List Parameter) (name : Identifier) (ty : WithMetadata HighType) (md : MetaData)
    (s s1 : TranslateState) (coreTy : LMonoTy)
    (hTy : translateType ty s = (some coreTy, s1)) :
    (translateStmt outParams ⟨.LocalVariable name ty none, md⟩ s).1.isSome = true := by
  simp [translateStmt_eq_localVar_noInit outParams name ty md s s1 coreTy hTy]

/-- IfThenElse (no else) succeeds when condition and then-branch succeed. -/
theorem translateStmt_succeeds_ite_noElse
    (cond thenB : StmtExprMd) (md : MetaData) (outParams : List Parameter)
    (s s1 s2 : TranslateState) (rc : Core.Expression.Expr) (rt : List Core.Statement)
    (hc : translateExpr cond [] false s = (some rc, s1))
    (ht : translateStmt outParams thenB s1 = (some rt, s2)) :
    (translateStmt outParams ⟨.IfThenElse cond thenB none, md⟩ s).1.isSome = true := by
  simp [translateStmt_eq_ite_noElse outParams cond thenB md s s1 s2 rc rt hc ht]

/-- IfThenElse (with else) succeeds when all branches succeed. -/
theorem translateStmt_succeeds_ite_withElse
    (cond thenB elseB : StmtExprMd) (md : MetaData) (outParams : List Parameter)
    (s s1 s2 s3 : TranslateState) (rc : Core.Expression.Expr) (rt re : List Core.Statement)
    (hc : translateExpr cond [] false s = (some rc, s1))
    (ht : translateStmt outParams thenB s1 = (some rt, s2))
    (he : translateStmt outParams elseB s2 = (some re, s3)) :
    (translateStmt outParams ⟨.IfThenElse cond thenB (some elseB), md⟩ s).1.isSome = true := by
  simp [translateStmt_eq_ite_withElse outParams cond thenB elseB md s s1 s2 s3 rc rt re hc ht he]

/-- Assign to a single identifier succeeds when the value expression succeeds
    (and the value is not a StaticCall or InstanceCall). -/
theorem translateStmt_succeeds_assign_expr
    (targetId : Identifier) (targetMd : MetaData) (value : StmtExprMd)
    (md : MetaData) (outParams : List Parameter)
    (s s1 : TranslateState) (coreExpr : Core.Expression.Expr)
    (hNotStaticCall : ∀ c a, value.val ≠ .StaticCall c a)
    (hNotInstanceCall : ∀ t c a, value.val ≠ .InstanceCall t c a)
    (hExpr : translateExpr value [] false s = (some coreExpr, s1)) :
    (translateStmt outParams ⟨.Assign [⟨.Identifier targetId, targetMd⟩] value, md⟩ s).1.isSome = true := by
  simp [translateStmt_eq_assign_expr targetId targetMd value md outParams s s1 coreExpr
    hNotStaticCall hNotInstanceCall hExpr]

/-- Block (unlabeled) succeeds when all inner statements succeed. -/
theorem translateStmt_succeeds_block_unlabeled
    (stmts : List StmtExprMd) (md : MetaData) (outParams : List Parameter)
    (s s1 : TranslateState) (result : List Core.Statement)
    (hInner : stmts.flatMapM (fun stmt => translateStmt outParams stmt) s = (some result, s1)) :
    (translateStmt outParams ⟨.Block stmts none, md⟩ s).1.isSome = true := by
  simp [translateStmt_eq_block_unlabeled outParams stmts md s s1 result hInner]

/-- While loop succeeds when condition, invariants, decreases, and body all succeed. -/
theorem translateStmt_succeeds_while
    (cond : StmtExprMd) (invariants : List StmtExprMd) (decreasesExpr : Option StmtExprMd)
    (body : StmtExprMd) (md : MetaData) (outParams : List Parameter)
    (s s1 s2 s3 s4 : TranslateState)
    (condExpr : Core.Expression.Expr) (invExprs : List Core.Expression.Expr)
    (decExprCore : Option Core.Expression.Expr) (bodyStmts : List Core.Statement)
    (hCond : translateExpr cond [] false s = (some condExpr, s1))
    (hInvs : (invariants.mapM (fun i => translateExpr i) s1) = (some invExprs, s2))
    (hDec : (decreasesExpr.mapM (fun d => translateExpr d) s2) = (some decExprCore, s3))
    (hBody : translateStmt outParams body s3 = (some bodyStmts, s4)) :
    (translateStmt outParams ⟨.While cond invariants decreasesExpr body, md⟩ s).1.isSome = true := by
  simp [translateStmt_eq_while outParams cond invariants decreasesExpr body md
    s s1 s2 s3 s4 condExpr invExprs decExprCore bodyStmts hCond hInvs hDec hBody]

/-! ### P-Struct-2: Signature preservation for translateProcedure

When translateProcedure succeeds, the output Core.Procedure preserves
the input/output parameter structure. -/

-- Common hypotheses for transparent procedure theorems
private abbrev TransparentHyps (proc : Procedure) (bodyExpr : StmtExprMd)
    (s sI sO sBody : TranslateState)
    (coreInputs : List (Core.CoreIdent × LMonoTy))
    (coreOutputs : List (Core.CoreIdent × LMonoTy))
    (bodyStmts : List Core.Statement) :=
  proc.body = Body.Transparent bodyExpr [] ∧
  proc.preconditions = [] ∧
  (proc.inputs.mapM translateParameterToCore s) = (some coreInputs, sI) ∧
  (proc.outputs.mapM translateParameterToCore sI) = (some coreOutputs, sO) ∧
  (translateStmt proc.outputs bodyExpr sO).1 = some bodyStmts ∧
  (translateStmt proc.outputs bodyExpr sO).2 = sBody

/-- The output procedure's name matches the input procedure's name. -/
theorem translateProcedure_preserves_name
    (proc : Procedure) (bodyExpr : StmtExprMd)
    (s sI sO sBody : TranslateState)
    (coreInputs : List (Core.CoreIdent × LMonoTy))
    (coreOutputs : List (Core.CoreIdent × LMonoTy))
    (bodyStmts : List Core.Statement) (coreProc : Core.Procedure)
    (hTransparent : proc.body = Body.Transparent bodyExpr [])
    (hNoPre : proc.preconditions = [])
    (hInputs : (proc.inputs.mapM translateParameterToCore s) = (some coreInputs, sI))
    (hOutputs : (proc.outputs.mapM translateParameterToCore sI) = (some coreOutputs, sO))
    (hBody : (translateStmt proc.outputs bodyExpr sO).1 = some bodyStmts)
    (hState : (translateStmt proc.outputs bodyExpr sO).2 = sBody)
    (hSucc : (translateProcedure proc s).1 = some coreProc) :
    coreProc.header.name = ⟨proc.name.text, ()⟩ :=
  (translateProcedure_transparent_get proc bodyExpr s sI sO sBody
    coreInputs coreOutputs bodyStmts hTransparent hNoPre hInputs hOutputs
    hBody hState coreProc hSucc).1

/-- The output procedure has the same number of inputs as the source. -/
theorem translateProcedure_preserves_input_count
    (proc : Procedure) (bodyExpr : StmtExprMd)
    (s sI sO sBody : TranslateState)
    (coreInputs : List (Core.CoreIdent × LMonoTy))
    (coreOutputs : List (Core.CoreIdent × LMonoTy))
    (bodyStmts : List Core.Statement) (coreProc : Core.Procedure)
    (hTransparent : proc.body = Body.Transparent bodyExpr [])
    (hNoPre : proc.preconditions = [])
    (hInputs : (proc.inputs.mapM translateParameterToCore s) = (some coreInputs, sI))
    (hOutputs : (proc.outputs.mapM translateParameterToCore sI) = (some coreOutputs, sO))
    (hBody : (translateStmt proc.outputs bodyExpr sO).1 = some bodyStmts)
    (hState : (translateStmt proc.outputs bodyExpr sO).2 = sBody)
    (hSucc : (translateProcedure proc s).1 = some coreProc) :
    coreProc.header.inputs = coreInputs :=
  (translateProcedure_transparent_get proc bodyExpr s sI sO sBody
    coreInputs coreOutputs bodyStmts hTransparent hNoPre hInputs hOutputs
    hBody hState coreProc hSucc).2.1

/-! ### P-Spec-1: Postcondition preservation for opaque procedures -/

/-- An opaque procedure with implementation preserves its postconditions. -/
theorem translateProcedure_opaque_withImpl_preserves_postconditions
    (proc : Procedure) (postconds : List StmtExprMd) (impl : StmtExprMd)
    (modif : List StmtExprMd)
    (s sI sO sPre sPost sBody : TranslateState)
    (coreInputs : List (Core.CoreIdent × LMonoTy))
    (coreOutputs : List (Core.CoreIdent × LMonoTy))
    (corePre : ListMap Core.CoreLabel Core.Procedure.Check)
    (corePost : ListMap Core.CoreLabel Core.Procedure.Check)
    (bodyStmts : List Core.Statement) (coreProc : Core.Procedure)
    (hOpaque : proc.body = Body.Opaque postconds (some impl) modif)
    (hInputs : (proc.inputs.mapM translateParameterToCore s) = (some coreInputs, sI))
    (hOutputs : (proc.outputs.mapM translateParameterToCore sI) = (some coreOutputs, sO))
    (hPre : translateChecks proc.preconditions "requires" sO = (some corePre, sPre))
    (hPost : translateChecks postconds "postcondition" sPre = (some corePost, sPost))
    (hBody : translateStmt proc.outputs impl sPost = (some bodyStmts, sBody))
    (hSucc : (translateProcedure proc s).1 = some coreProc) :
    coreProc.spec.postconditions = corePost :=
  (translateProcedure_opaque_withImpl_get proc postconds impl modif
    s sI sO sPre sPost sBody coreInputs coreOutputs corePre corePost bodyStmts
    hOpaque hInputs hOutputs hPre hPost hBody coreProc hSucc).2.2.2.2

/-- An opaque procedure with implementation preserves its preconditions. -/
theorem translateProcedure_opaque_withImpl_preserves_preconditions
    (proc : Procedure) (postconds : List StmtExprMd) (impl : StmtExprMd)
    (modif : List StmtExprMd)
    (s sI sO sPre sPost sBody : TranslateState)
    (coreInputs : List (Core.CoreIdent × LMonoTy))
    (coreOutputs : List (Core.CoreIdent × LMonoTy))
    (corePre : ListMap Core.CoreLabel Core.Procedure.Check)
    (corePost : ListMap Core.CoreLabel Core.Procedure.Check)
    (bodyStmts : List Core.Statement) (coreProc : Core.Procedure)
    (hOpaque : proc.body = Body.Opaque postconds (some impl) modif)
    (hInputs : (proc.inputs.mapM translateParameterToCore s) = (some coreInputs, sI))
    (hOutputs : (proc.outputs.mapM translateParameterToCore sI) = (some coreOutputs, sO))
    (hPre : translateChecks proc.preconditions "requires" sO = (some corePre, sPre))
    (hPost : translateChecks postconds "postcondition" sPre = (some corePost, sPost))
    (hBody : translateStmt proc.outputs impl sPost = (some bodyStmts, sBody))
    (hSucc : (translateProcedure proc s).1 = some coreProc) :
    coreProc.spec.preconditions = corePre :=
  (translateProcedure_opaque_withImpl_get proc postconds impl modif
    s sI sO sPre sPost sBody coreInputs coreOutputs corePre corePost bodyStmts
    hOpaque hInputs hOutputs hPre hPost hBody coreProc hSucc).2.2.2.1

/-- An opaque procedure without implementation preserves its postconditions. -/
theorem translateProcedure_opaque_noImpl_preserves_postconditions
    (proc : Procedure) (postconds : List StmtExprMd) (modif : List StmtExprMd)
    (s sI sO sPre sPost : TranslateState)
    (coreInputs : List (Core.CoreIdent × LMonoTy))
    (coreOutputs : List (Core.CoreIdent × LMonoTy))
    (corePre : ListMap Core.CoreLabel Core.Procedure.Check)
    (corePost : ListMap Core.CoreLabel Core.Procedure.Check)
    (coreProc : Core.Procedure)
    (hOpaque : proc.body = Body.Opaque postconds none modif)
    (hInputs : (proc.inputs.mapM translateParameterToCore s) = (some coreInputs, sI))
    (hOutputs : (proc.outputs.mapM translateParameterToCore sI) = (some coreOutputs, sO))
    (hPre : translateChecks proc.preconditions "requires" sO = (some corePre, sPre))
    (hPost : translateChecks postconds "postcondition" sPre = (some corePost, sPost))
    (hSucc : (translateProcedure proc s).1 = some coreProc) :
    coreProc.spec.postconditions = corePost :=
  (translateProcedure_opaque_noImpl_get proc postconds modif
    s sI sO sPre sPost coreInputs coreOutputs corePre corePost
    hOpaque hInputs hOutputs hPre hPost coreProc hSucc).2.2.2.2

/-- An opaque procedure without implementation preserves its preconditions. -/
theorem translateProcedure_opaque_noImpl_preserves_preconditions
    (proc : Procedure) (postconds : List StmtExprMd) (modif : List StmtExprMd)
    (s sI sO sPre sPost : TranslateState)
    (coreInputs : List (Core.CoreIdent × LMonoTy))
    (coreOutputs : List (Core.CoreIdent × LMonoTy))
    (corePre : ListMap Core.CoreLabel Core.Procedure.Check)
    (corePost : ListMap Core.CoreLabel Core.Procedure.Check)
    (coreProc : Core.Procedure)
    (hOpaque : proc.body = Body.Opaque postconds none modif)
    (hInputs : (proc.inputs.mapM translateParameterToCore s) = (some coreInputs, sI))
    (hOutputs : (proc.outputs.mapM translateParameterToCore sI) = (some coreOutputs, sO))
    (hPre : translateChecks proc.preconditions "requires" sO = (some corePre, sPre))
    (hPost : translateChecks postconds "postcondition" sPre = (some corePost, sPost))
    (hSucc : (translateProcedure proc s).1 = some coreProc) :
    coreProc.spec.preconditions = corePre :=
  (translateProcedure_opaque_noImpl_get proc postconds modif
    s sI sO sPre sPost coreInputs coreOutputs corePre corePost
    hOpaque hInputs hOutputs hPre hPost coreProc hSucc).2.2.2.1

/-- An opaque procedure (with impl) preserves its name. -/
theorem translateProcedure_opaque_withImpl_preserves_name
    (proc : Procedure) (postconds : List StmtExprMd) (impl : StmtExprMd)
    (modif : List StmtExprMd)
    (s sI sO sPre sPost sBody : TranslateState)
    (coreInputs : List (Core.CoreIdent × LMonoTy))
    (coreOutputs : List (Core.CoreIdent × LMonoTy))
    (corePre : ListMap Core.CoreLabel Core.Procedure.Check)
    (corePost : ListMap Core.CoreLabel Core.Procedure.Check)
    (bodyStmts : List Core.Statement) (coreProc : Core.Procedure)
    (hOpaque : proc.body = Body.Opaque postconds (some impl) modif)
    (hInputs : (proc.inputs.mapM translateParameterToCore s) = (some coreInputs, sI))
    (hOutputs : (proc.outputs.mapM translateParameterToCore sI) = (some coreOutputs, sO))
    (hPre : translateChecks proc.preconditions "requires" sO = (some corePre, sPre))
    (hPost : translateChecks postconds "postcondition" sPre = (some corePost, sPost))
    (hBody : translateStmt proc.outputs impl sPost = (some bodyStmts, sBody))
    (hSucc : (translateProcedure proc s).1 = some coreProc) :
    coreProc.header.name = ⟨proc.name.text, ()⟩ :=
  (translateProcedure_opaque_withImpl_get proc postconds impl modif
    s sI sO sPre sPost sBody coreInputs coreOutputs corePre corePost bodyStmts
    hOpaque hInputs hOutputs hPre hPost hBody coreProc hSucc).1

/-! ### P-Spec-2f: Function postcondition axiom count preservation

When translateProcedureToFunction succeeds, the number of axioms in the
Core.Function equals the number of postconditions in the source procedure's
Body. This catches the "axioms silently dropped" bug class — the function
postcondition axiom gap where translateProcedureToFunction created
Core.Function with axioms := [] (default), silently dropping all
postconditions. See D18 in decisions.md. -/

/-- P-Spec-2f: Function axiom count equals postcondition count.
    When translateProcedureToFunction produces a Core.Decl.func,
    the function's axiom count equals the postcondition count from
    the procedure's body. -/
theorem translateProcedureToFunction_axiom_count
    (options : LaurelTranslateOptions) (isRecursive : Bool)
    (proc : Procedure) (s s' : TranslateState) (f : Core.Function) (fmd : MetaData)
    (hSucc : translateProcedureToFunction options isRecursive proc s = (some (.func f fmd), s')) :
    f.axioms.length = (getPostconds proc.body).length :=
  translateProcedureToFunction_axioms_length options isRecursive proc s s' f fmd hSucc

end Strata.Laurel
