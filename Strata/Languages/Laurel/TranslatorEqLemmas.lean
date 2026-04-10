/-
  Copyright Strata Contributors
  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
import Strata.Languages.Laurel.LaurelToCoreTranslator

/-!
# Translator Equation Lemmas

Per-constructor equation lemmas for `translateExpr`, `translateStmt`, and
`translateProcedure`. Contract between the translator and
`TranslatorProperties.lean` (see D4 in translator-proof decisions).
-/

namespace Strata.Laurel

open Strata.Core Lambda

-- Unfold the OptionT/StateM monad stack.
local macro "mu" : tactic =>
  `(tactic| simp only [
    pure, OptionT.pure, OptionT.mk, OptionT.bind, OptionT.lift,
    bind, get, MonadState.get, getThe, MonadStateOf.get,
    StateT.bind, StateT.get, StateT.pure,
    liftM, monadLift, MonadLift.monadLift])

/-! ## translateExpr: Literals -/

@[simp] theorem translateExpr_eq_literalBool (b : Bool) (md : MetaData)
    (bv : List Identifier) (pc : Bool) (s : TranslateState) :
    (translateExpr ⟨.LiteralBool b, md⟩ bv pc s) =
    (some (.const () (.boolConst b)), s) := by
  simp only [translateExpr.eq_def]; mu

@[simp] theorem translateExpr_eq_literalInt (i : Int) (md : MetaData)
    (bv : List Identifier) (pc : Bool) (s : TranslateState) :
    (translateExpr ⟨.LiteralInt i, md⟩ bv pc s) =
    (some (.const () (.intConst i)), s) := by
  simp only [translateExpr.eq_def]; mu

@[simp] theorem translateExpr_eq_literalString (str : String) (md : MetaData)
    (bv : List Identifier) (pc : Bool) (s : TranslateState) :
    (translateExpr ⟨.LiteralString str, md⟩ bv pc s) =
    (some (.const () (.strConst str)), s) := by
  simp only [translateExpr.eq_def]; mu

/-! ## translateExpr: PrimitiveOp (unary) -/

theorem translateExpr_eq_primNot (e : StmtExprMd) (md : MetaData)
    (bv : List Identifier) (pc : Bool)
    (s s1 : TranslateState) (r : Core.Expression.Expr)
    (h : translateExpr e bv pc s = (some r, s1)) :
    (translateExpr ⟨.PrimitiveOp .Not [e], md⟩ bv pc s) =
    (some (.app () Core.boolNotOp r), s1) := by
  rw [translateExpr.eq_def]; mu; rw [h]; mu

/-! ## translateExpr: PrimitiveOp (binary, no isReal) -/

theorem translateExpr_eq_primEq (e1 e2 : StmtExprMd) (md : MetaData)
    (bv : List Identifier) (pc : Bool)
    (s s1 s2 : TranslateState) (r1 r2 : Core.Expression.Expr)
    (h1 : translateExpr e1 bv pc s = (some r1, s1))
    (h2 : translateExpr e2 bv pc s1 = (some r2, s2)) :
    (translateExpr ⟨.PrimitiveOp .Eq [e1, e2], md⟩ bv pc s) =
    (some (.eq () r1 r2), s2) := by
  rw [translateExpr.eq_def]; mu; rw [h1]; mu; rw [h2]; mu

theorem translateExpr_eq_primNeq (e1 e2 : StmtExprMd) (md : MetaData)
    (bv : List Identifier) (pc : Bool)
    (s s1 s2 : TranslateState) (r1 r2 : Core.Expression.Expr)
    (h1 : translateExpr e1 bv pc s = (some r1, s1))
    (h2 : translateExpr e2 bv pc s1 = (some r2, s2)) :
    (translateExpr ⟨.PrimitiveOp .Neq [e1, e2], md⟩ bv pc s) =
    (some (.app () Core.boolNotOp (.eq () r1 r2)), s2) := by
  rw [translateExpr.eq_def]; mu; rw [h1]; mu; rw [h2]; mu

theorem translateExpr_eq_primAnd (e1 e2 : StmtExprMd) (md : MetaData)
    (bv : List Identifier) (pc : Bool)
    (s s1 s2 : TranslateState) (r1 r2 : Core.Expression.Expr)
    (h1 : translateExpr e1 bv pc s = (some r1, s1))
    (h2 : translateExpr e2 bv pc s1 = (some r2, s2)) :
    (translateExpr ⟨.PrimitiveOp .And [e1, e2], md⟩ bv pc s) =
    (some (.app () (.app () Core.boolAndOp r1) r2), s2) := by
  rw [translateExpr.eq_def]; mu; rw [h1]; mu; rw [h2]; mu; simp [LExpr.mkApp]

theorem translateExpr_eq_primOr (e1 e2 : StmtExprMd) (md : MetaData)
    (bv : List Identifier) (pc : Bool)
    (s s1 s2 : TranslateState) (r1 r2 : Core.Expression.Expr)
    (h1 : translateExpr e1 bv pc s = (some r1, s1))
    (h2 : translateExpr e2 bv pc s1 = (some r2, s2)) :
    (translateExpr ⟨.PrimitiveOp .Or [e1, e2], md⟩ bv pc s) =
    (some (.app () (.app () Core.boolOrOp r1) r2), s2) := by
  rw [translateExpr.eq_def]; mu; rw [h1]; mu; rw [h2]; mu; simp [LExpr.mkApp]

/-! ## translateExpr: PrimitiveOp (binary, with isReal — sorry for now) -/

theorem translateExpr_eq_primAdd_int (e1 e2 : StmtExprMd) (md : MetaData)
    (bv : List Identifier) (pc : Bool)
    (s s1 s2 : TranslateState) (r1 r2 : Core.Expression.Expr)
    (h1 : translateExpr e1 bv pc s = (some r1, s1))
    (h2 : translateExpr e2 bv pc s1 = (some r2, s2))
    (hNotReal : ∀ x, computeExprType s.model e1 ≠ ⟨.TReal, x⟩) :
    (translateExpr ⟨.PrimitiveOp .Add [e1, e2], md⟩ bv pc s).1.isSome = true := by
  rw [translateExpr.eq_def]; mu; rw [h1]; mu; rw [h2]; mu; rfl

theorem translateExpr_eq_primSub_int (e1 e2 : StmtExprMd) (md : MetaData)
    (bv : List Identifier) (pc : Bool)
    (s s1 s2 : TranslateState) (r1 r2 : Core.Expression.Expr)
    (h1 : translateExpr e1 bv pc s = (some r1, s1))
    (h2 : translateExpr e2 bv pc s1 = (some r2, s2))
    (hNotReal : ∀ x, computeExprType s.model e1 ≠ ⟨.TReal, x⟩) :
    (translateExpr ⟨.PrimitiveOp .Sub [e1, e2], md⟩ bv pc s).1.isSome = true := by
  rw [translateExpr.eq_def]; mu; rw [h1]; mu; rw [h2]; mu; rfl

theorem translateExpr_eq_primMul_int (e1 e2 : StmtExprMd) (md : MetaData)
    (bv : List Identifier) (pc : Bool)
    (s s1 s2 : TranslateState) (r1 r2 : Core.Expression.Expr)
    (h1 : translateExpr e1 bv pc s = (some r1, s1))
    (h2 : translateExpr e2 bv pc s1 = (some r2, s2))
    (hNotReal : ∀ x, computeExprType s.model e1 ≠ ⟨.TReal, x⟩) :
    (translateExpr ⟨.PrimitiveOp .Mul [e1, e2], md⟩ bv pc s).1.isSome = true := by
  rw [translateExpr.eq_def]; mu; rw [h1]; mu; rw [h2]; mu; rfl

theorem translateExpr_eq_primLt_int (e1 e2 : StmtExprMd) (md : MetaData)
    (bv : List Identifier) (pc : Bool)
    (s s1 s2 : TranslateState) (r1 r2 : Core.Expression.Expr)
    (h1 : translateExpr e1 bv pc s = (some r1, s1))
    (h2 : translateExpr e2 bv pc s1 = (some r2, s2))
    (hNotReal : ∀ x, computeExprType s.model e1 ≠ ⟨.TReal, x⟩) :
    (translateExpr ⟨.PrimitiveOp .Lt [e1, e2], md⟩ bv pc s).1.isSome = true := by
  rw [translateExpr.eq_def]; mu; rw [h1]; mu; rw [h2]; mu; rfl

theorem translateExpr_eq_primGt_int (e1 e2 : StmtExprMd) (md : MetaData)
    (bv : List Identifier) (pc : Bool)
    (s s1 s2 : TranslateState) (r1 r2 : Core.Expression.Expr)
    (h1 : translateExpr e1 bv pc s = (some r1, s1))
    (h2 : translateExpr e2 bv pc s1 = (some r2, s2))
    (hNotReal : ∀ x, computeExprType s.model e1 ≠ ⟨.TReal, x⟩) :
    (translateExpr ⟨.PrimitiveOp .Gt [e1, e2], md⟩ bv pc s).1.isSome = true := by
  rw [translateExpr.eq_def]; mu; rw [h1]; mu; rw [h2]; mu; rfl

theorem translateExpr_eq_primLeq_int (e1 e2 : StmtExprMd) (md : MetaData)
    (bv : List Identifier) (pc : Bool)
    (s s1 s2 : TranslateState) (r1 r2 : Core.Expression.Expr)
    (h1 : translateExpr e1 bv pc s = (some r1, s1))
    (h2 : translateExpr e2 bv pc s1 = (some r2, s2))
    (hNotReal : ∀ x, computeExprType s.model e1 ≠ ⟨.TReal, x⟩) :
    (translateExpr ⟨.PrimitiveOp .Leq [e1, e2], md⟩ bv pc s).1.isSome = true := by
  rw [translateExpr.eq_def]; mu; rw [h1]; mu; rw [h2]; mu; rfl

theorem translateExpr_eq_primGeq_int (e1 e2 : StmtExprMd) (md : MetaData)
    (bv : List Identifier) (pc : Bool)
    (s s1 s2 : TranslateState) (r1 r2 : Core.Expression.Expr)
    (h1 : translateExpr e1 bv pc s = (some r1, s1))
    (h2 : translateExpr e2 bv pc s1 = (some r2, s2))
    (hNotReal : ∀ x, computeExprType s.model e1 ≠ ⟨.TReal, x⟩) :
    (translateExpr ⟨.PrimitiveOp .Geq [e1, e2], md⟩ bv pc s).1.isSome = true := by
  rw [translateExpr.eq_def]; mu; rw [h1]; mu; rw [h2]; mu; rfl

/-! ## translateExpr: IfThenElse -/

theorem translateExpr_eq_ite (cond thenBr elseBr : StmtExprMd) (md : MetaData)
    (bv : List Identifier) (pc : Bool)
    (s s1 s2 s3 : TranslateState)
    (rc rt re : Core.Expression.Expr)
    (hc : translateExpr cond bv pc s = (some rc, s1))
    (ht : translateExpr thenBr bv pc s1 = (some rt, s2))
    (he : translateExpr elseBr bv pc s2 = (some re, s3)) :
    (translateExpr ⟨.IfThenElse cond thenBr (some elseBr), md⟩ bv pc s) =
    (some (.ite () rc rt re), s3) := by
  rw [translateExpr.eq_def]; mu; rw [hc]; mu; rw [ht]; mu; rw [he]; mu

/-! ## translateExpr: StaticCall -/

theorem translateExpr_eq_staticCall_noArgs (callee : Identifier) (md : MetaData)
    (bv : List Identifier) (s : TranslateState)
    (hNotPure : s.model.isFunction callee = false) :
    (translateExpr ⟨.StaticCall callee [], md⟩ bv false s) =
    (some (Lambda.LExpr.op () ⟨callee.text, ()⟩ none), s) := by
  rw [translateExpr.eq_def]; mu; simp only [hNotPure]; rfl

theorem translateExpr_eq_staticCall_oneArg (callee : Identifier) (arg : StmtExprMd)
    (md : MetaData) (bv : List Identifier)
    (s s1 : TranslateState) (r : Core.Expression.Expr)
    (hNotPure : s.model.isFunction callee = false)
    (hArg : translateExpr arg bv false s = (some r, s1)) :
    (translateExpr ⟨.StaticCall callee [arg], md⟩ bv false s).1.isSome = true := by
  rw [translateExpr.eq_def]; mu; simp only [hNotPure]
  simp (config := { decide := true }); mu; rw [hArg]; mu; rfl

theorem translateExpr_eq_staticCall_twoArgs (callee : Identifier)
    (a1 a2 : StmtExprMd) (md : MetaData) (bv : List Identifier)
    (s s1 s2 : TranslateState) (r1 r2 : Core.Expression.Expr)
    (hNotPure : s.model.isFunction callee = false)
    (h1 : translateExpr a1 bv false s = (some r1, s1))
    (h2 : translateExpr a2 bv false s1 = (some r2, s2)) :
    (translateExpr ⟨.StaticCall callee [a1, a2], md⟩ bv false s).1.isSome = true := by
  rw [translateExpr.eq_def]; mu; simp only [hNotPure]
  simp (config := { decide := true }); mu; rw [h1]; mu; rw [h2]; mu; rfl

/-! ## translateExpr: InstanceCall — NOT YET IMPLEMENTED in translator

InstanceCall in translateExpr calls throwExprDiagnostic (returns none).
The old properties claiming success were stale. These are removed.
When InstanceCall support is added to translateExpr, add equation lemmas here. -/

/-! ## translateStmt: Throw — NOT HANDLED as direct case

Throw falls through to the catch-all in translateStmt which calls
exprAsUnusedInit → translateExpr → disallowed → throwExprDiagnostic → none.
The old properties claiming success were stale. -/

/-! ## translateStmt -/

theorem translateStmt_eq_return_none (outParams : List Parameter) (md : MetaData)
    (s : TranslateState) :
    (translateStmt outParams ⟨.Return none, md⟩ s).1.isSome = true := by
  rw [translateStmt.eq_def]; mu; rfl

theorem translateStmt_eq_localVar_noInit (outParams : List Parameter)
    (name : Identifier) (ty : WithMetadata HighType) (md : MetaData)
    (s s1 : TranslateState) (coreTy : LMonoTy)
    (hTy : translateType ty s = (some coreTy, s1)) :
    (translateStmt outParams ⟨.LocalVariable name ty none, md⟩ s).1.isSome = true := by
  rw [translateStmt.eq_def]; mu; rw [hTy]; mu; rfl

theorem translateStmt_eq_ite_noElse (outParams : List Parameter)
    (cond thenBr : StmtExprMd) (md : MetaData)
    (s s1 s2 : TranslateState)
    (rc : Core.Expression.Expr) (rt : List Core.Statement)
    (hc : translateExpr cond [] false s = (some rc, s1))
    (ht : translateStmt outParams thenBr s1 = (some rt, s2)) :
    (translateStmt outParams ⟨.IfThenElse cond thenBr none, md⟩ s).1.isSome = true := by
  rw [translateStmt.eq_def]; mu; rw [hc]; mu; rw [ht]; mu; rfl

theorem translateStmt_eq_ite_withElse (outParams : List Parameter)
    (cond thenBr elseBr : StmtExprMd) (md : MetaData)
    (s s1 s2 s3 : TranslateState)
    (rc : Core.Expression.Expr) (rt re : List Core.Statement)
    (hc : translateExpr cond [] false s = (some rc, s1))
    (ht : translateStmt outParams thenBr s1 = (some rt, s2))
    (he : translateStmt outParams elseBr s2 = (some re, s3)) :
    (translateStmt outParams ⟨.IfThenElse cond thenBr (some elseBr), md⟩ s).1.isSome = true := by
  rw [translateStmt.eq_def]; mu; rw [hc]; mu; rw [ht]; mu; rw [he]; mu; rfl

theorem translateStmt_eq_assign_expr (targetId : Identifier) (targetMd : MetaData)
    (value : StmtExprMd) (md : MetaData) (outParams : List Parameter)
    (s s1 : TranslateState) (coreExpr : Core.Expression.Expr)
    (hNotStaticCall : ∀ c a, value.val ≠ .StaticCall c a)
    (hNotInstanceCall : ∀ t c a, value.val ≠ .InstanceCall t c a)
    (hExpr : translateExpr value [] false s = (some coreExpr, s1)) :
    (translateStmt outParams ⟨.Assign [⟨.Identifier targetId, targetMd⟩] value, md⟩ s).1.isSome = true := by
  sorry

theorem translateStmt_eq_block_unlabeled (outParams : List Parameter)
    (stmts : List StmtExprMd) (md : MetaData)
    (s s1 : TranslateState) (rs : List Core.Statement)
    (h : (stmts.flatMapM (fun stmt => translateStmt outParams stmt) s) = (some rs, s1)) :
    (translateStmt outParams ⟨.Block stmts none, md⟩ s) = (some rs, s1) := by
  rw [translateStmt.eq_def]; mu; rw [h]; mu

theorem translateStmt_eq_while (outParams : List Parameter)
    (cond : StmtExprMd) (invs : List StmtExprMd)
    (decr : Option StmtExprMd) (body : StmtExprMd) (md : MetaData)
    (s s1 s2 s3 s4 : TranslateState)
    (rc : Core.Expression.Expr) (ri : List Core.Expression.Expr)
    (rd : Option Core.Expression.Expr) (rb : List Core.Statement)
    (hc : translateExpr cond [] false s = (some rc, s1))
    (hi : (invs.mapM (fun i => translateExpr i) s1) = (some ri, s2))
    (hd : (decr.mapM (fun d => translateExpr d) s2) = (some rd, s3))
    (hb : translateStmt outParams body s3 = (some rb, s4)) :
    (translateStmt outParams ⟨.While cond invs decr body, md⟩ s).1.isSome = true := by
  rw [translateStmt.eq_def]; mu; rw [hc]; mu; rw [hi]; mu; rw [hd]; mu; rw [hb]; mu; rfl

/-! ## translateProcedure — proved directly, no equation lemma needed -/

-- translateProcedure properties are proved directly in TranslatorProperties.lean
-- by unfolding translateProcedure.eq_def. No intermediate equation lemma is needed
-- because the procedure construction is complex (mapM on inputs/outputs, translateChecks,
-- translateStmt) and the properties only need to extract individual fields.

theorem translateProcedure_eq_transparent (proc : Procedure)
    (bodyExpr : StmtExprMd) (s s1 : TranslateState)
    (bodyStmts : List Core.Statement)
    (hTransparent : proc.body = Body.Transparent bodyExpr [])
    (hNoPre : proc.preconditions = [])
    (hBody : (translateStmt proc.outputs bodyExpr s).1 = some bodyStmts)
    (hState : (translateStmt proc.outputs bodyExpr s).2 = s1) :
    (translateProcedure proc s).1.isSome = true := by
  sorry

theorem translateProcedure_eq_opaque_withImpl (proc : Procedure)
    (postconds : List StmtExprMd) (impl : StmtExprMd) (modif : List StmtExprMd)
    (s : TranslateState)
    (hOpaque : proc.body = Body.Opaque postconds (some impl) modif) :
    (translateProcedure proc s).1.isSome = true := by
  sorry

theorem translateProcedure_eq_opaque_noImpl (proc : Procedure)
    (postconds : List StmtExprMd) (modif : List StmtExprMd)
    (s : TranslateState)
    (hOpaque : proc.body = Body.Opaque postconds none modif) :
    (translateProcedure proc s).1.isSome = true := by
  sorry

end Strata.Laurel
