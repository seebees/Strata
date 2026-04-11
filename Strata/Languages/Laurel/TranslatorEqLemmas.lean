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
  rw [translateStmt.eq_def]; mu
  revert hExpr hNotStaticCall hNotInstanceCall
  cases value with
  | mk val valMd =>
    intro hNotStaticCall hNotInstanceCall hExpr
    cases val with
    | StaticCall c a => exact absurd rfl (hNotStaticCall c a)
    | InstanceCall t c a => exact absurd rfl (hNotInstanceCall t c a)
    | _ => rw [hExpr]; rfl

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

/-! ## translateStmt: Throw -/

/-- Equation lemma for translateStmt on .Throw: produces exactly
    [$result := Failure(), exit <exceptionTarget>]. -/
theorem translateStmt_throw (outParams : List Parameter)
    (exception : WithMetadata StmtExpr) (md : MetaData)
    (s : TranslateState) :
    (translateStmt outParams ⟨.Throw exception, md⟩ s) =
      (some [Core.Statement.set ⟨"$result", ()⟩ (.op () ⟨"Failure", ()⟩ none) md,
             Imperative.Stmt.exit (some s.exceptionTarget) md], s) := by
  rw [translateStmt.eq_def]; mu

/-! ## translateProcedure -/

-- The `module` system creates a local copy of `mdWithUnknownLoc` when
-- `translateProcedure.eq_def` is unfolded. This prevents proving exact
-- equations with `rfl`. Instead, we prove `.isSome` and provide a
-- `get` lemma that extracts the Core.Procedure value for field access.

/-- When translateProcedure succeeds on a transparent procedure with no
    preconditions, we can extract the resulting Core.Procedure. -/
theorem translateProcedure_transparent_get (proc : Procedure)
    (bodyExpr : StmtExprMd)
    (s sI sO sBody : TranslateState)
    (coreInputs : List (Core.CoreIdent × LMonoTy))
    (coreOutputs : List (Core.CoreIdent × LMonoTy))
    (bodyStmts : List Core.Statement)
    (hTransparent : proc.body = Body.Transparent bodyExpr [])
    (hNoPre : proc.preconditions = [])
    (hInputs : (proc.inputs.mapM translateParameterToCore s) = (some coreInputs, sI))
    (hOutputs : (proc.outputs.mapM translateParameterToCore sI) = (some coreOutputs, sO))
    (hBody : (translateStmt proc.outputs bodyExpr sO).1 = some bodyStmts)
    (hState : (translateStmt proc.outputs bodyExpr sO).2 = sBody)
    (coreProc : Core.Procedure)
    (hSucc : (translateProcedure proc s).1 = some coreProc) :
    coreProc.header.name = ⟨proc.name.text, ()⟩ ∧
    coreProc.header.inputs = coreInputs ∧
    coreProc.header.outputs = coreOutputs ++ [(⟨"$result", ()⟩, .tcons "ExceptionResult" [])] ∧
    coreProc.spec.preconditions = [] ∧
    coreProc.spec.postconditions = [] := by
  rw [translateProcedure.eq_def] at hSucc; simp only [
    pure, OptionT.pure, OptionT.mk, OptionT.bind, OptionT.lift,
    bind, get, MonadState.get, getThe, MonadStateOf.get,
    StateT.bind, StateT.get, StateT.pure,
    liftM, monadLift, MonadLift.monadLift] at hSucc
  rw [hInputs] at hSucc; simp only [
    pure, OptionT.pure, OptionT.mk, OptionT.bind, OptionT.lift,
    bind, get, MonadState.get, getThe, MonadStateOf.get,
    StateT.bind, StateT.get, StateT.pure,
    liftM, monadLift, MonadLift.monadLift] at hSucc
  rw [hOutputs] at hSucc; simp only [
    pure, OptionT.pure, OptionT.mk, OptionT.bind, OptionT.lift,
    bind, get, MonadState.get, getThe, MonadStateOf.get,
    StateT.bind, StateT.get, StateT.pure,
    liftM, monadLift, MonadLift.monadLift] at hSucc
  rw [hNoPre] at hSucc; simp only [translateChecks, List.mapIdxM, List.mapIdxM.go,
    pure, OptionT.pure, OptionT.mk, OptionT.bind, OptionT.lift,
    bind, get, MonadState.get, getThe, MonadStateOf.get,
    StateT.bind, StateT.get, StateT.pure,
    liftM, monadLift, MonadLift.monadLift] at hSucc
  rw [hTransparent] at hSucc; simp only [
    pure, OptionT.pure, OptionT.mk, OptionT.bind, OptionT.lift,
    bind, get, MonadState.get, getThe, MonadStateOf.get,
    StateT.bind, StateT.get, StateT.pure,
    liftM, monadLift, MonadLift.monadLift] at hSucc
  have hPair : (translateStmt proc.outputs bodyExpr sO) = (some bodyStmts, sBody) :=
    Prod.ext hBody hState
  rw [hPair] at hSucc; simp only [
    pure, OptionT.pure, OptionT.mk, OptionT.bind, OptionT.lift,
    bind, get, MonadState.get, getThe, MonadStateOf.get,
    StateT.bind, StateT.get, StateT.pure,
    liftM, monadLift, MonadLift.monadLift] at hSucc
  have := Option.some.inj hSucc
  subst this
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem translateProcedure_eq_transparent (proc : Procedure)
    (bodyExpr : StmtExprMd)
    (s sI sO sBody : TranslateState)
    (coreInputs : List (Core.CoreIdent × LMonoTy))
    (coreOutputs : List (Core.CoreIdent × LMonoTy))
    (bodyStmts : List Core.Statement)
    (hTransparent : proc.body = Body.Transparent bodyExpr [])
    (hNoPre : proc.preconditions = [])
    (hInputs : (proc.inputs.mapM translateParameterToCore s) = (some coreInputs, sI))
    (hOutputs : (proc.outputs.mapM translateParameterToCore sI) = (some coreOutputs, sO))
    (hBody : (translateStmt proc.outputs bodyExpr sO).1 = some bodyStmts)
    (hState : (translateStmt proc.outputs bodyExpr sO).2 = sBody) :
    (translateProcedure proc s).1.isSome = true := by
  rw [translateProcedure.eq_def]; mu
  rw [hInputs]; mu; rw [hOutputs]; mu
  rw [hNoPre]; simp only [translateChecks, List.mapIdxM, List.mapIdxM.go]; mu
  rw [hTransparent]; mu
  have hPair : (translateStmt proc.outputs bodyExpr sO) = (some bodyStmts, sBody) :=
    Prod.ext hBody hState
  rw [hPair]; mu; rfl

theorem translateProcedure_eq_opaque_withImpl (proc : Procedure)
    (postconds : List StmtExprMd) (impl : StmtExprMd) (modif : List StmtExprMd)
    (s sI sO sPre sPost sBody : TranslateState)
    (coreInputs : List (Core.CoreIdent × LMonoTy))
    (coreOutputs : List (Core.CoreIdent × LMonoTy))
    (corePre : ListMap Core.CoreLabel Core.Procedure.Check)
    (corePost : ListMap Core.CoreLabel Core.Procedure.Check)
    (bodyStmts : List Core.Statement)
    (hOpaque : proc.body = Body.Opaque postconds (some impl) modif)
    (hInputs : (proc.inputs.mapM translateParameterToCore s) = (some coreInputs, sI))
    (hOutputs : (proc.outputs.mapM translateParameterToCore sI) = (some coreOutputs, sO))
    (hPre : translateChecks proc.preconditions "requires" sO = (some corePre, sPre))
    (hPost : translateChecks postconds "postcondition" sPre = (some corePost, sPost))
    (hBody : translateStmt proc.outputs impl sPost = (some bodyStmts, sBody)) :
    (translateProcedure proc s).1.isSome = true := by
  rw [translateProcedure.eq_def]; mu
  rw [hInputs]; mu; rw [hOutputs]; mu; rw [hPre]; mu
  rw [hOpaque]; mu; rw [hPost]; mu; rw [hBody]; mu; rfl

theorem translateProcedure_eq_opaque_noImpl (proc : Procedure)
    (postconds : List StmtExprMd) (modif : List StmtExprMd)
    (s sI sO sPre sPost : TranslateState)
    (coreInputs : List (Core.CoreIdent × LMonoTy))
    (coreOutputs : List (Core.CoreIdent × LMonoTy))
    (corePre : ListMap Core.CoreLabel Core.Procedure.Check)
    (corePost : ListMap Core.CoreLabel Core.Procedure.Check)
    (hOpaque : proc.body = Body.Opaque postconds none modif)
    (hInputs : (proc.inputs.mapM translateParameterToCore s) = (some coreInputs, sI))
    (hOutputs : (proc.outputs.mapM translateParameterToCore sI) = (some coreOutputs, sO))
    (hPre : translateChecks proc.preconditions "requires" sO = (some corePre, sPre))
    (hPost : translateChecks postconds "postcondition" sPre = (some corePost, sPost)) :
    (translateProcedure proc s).1.isSome = true := by
  rw [translateProcedure.eq_def]; mu
  rw [hInputs]; mu; rw [hOutputs]; mu; rw [hPre]; mu
  rw [hOpaque]; mu; rw [hPost]; mu; rfl

/-- When translateProcedure succeeds on an opaque procedure with implementation,
    we can extract the resulting Core.Procedure fields. -/
theorem translateProcedure_opaque_withImpl_get (proc : Procedure)
    (postconds : List StmtExprMd) (impl : StmtExprMd) (modif : List StmtExprMd)
    (s sI sO sPre sPost sBody : TranslateState)
    (coreInputs : List (Core.CoreIdent × LMonoTy))
    (coreOutputs : List (Core.CoreIdent × LMonoTy))
    (corePre : ListMap Core.CoreLabel Core.Procedure.Check)
    (corePost : ListMap Core.CoreLabel Core.Procedure.Check)
    (bodyStmts : List Core.Statement)
    (hOpaque : proc.body = Body.Opaque postconds (some impl) modif)
    (hInputs : (proc.inputs.mapM translateParameterToCore s) = (some coreInputs, sI))
    (hOutputs : (proc.outputs.mapM translateParameterToCore sI) = (some coreOutputs, sO))
    (hPre : translateChecks proc.preconditions "requires" sO = (some corePre, sPre))
    (hPost : translateChecks postconds "postcondition" sPre = (some corePost, sPost))
    (hBody : translateStmt proc.outputs impl sPost = (some bodyStmts, sBody))
    (coreProc : Core.Procedure)
    (hSucc : (translateProcedure proc s).1 = some coreProc) :
    coreProc.header.name = ⟨proc.name.text, ()⟩ ∧
    coreProc.header.inputs = coreInputs ∧
    coreProc.header.outputs = coreOutputs ++ [(⟨"$result", ()⟩, .tcons "ExceptionResult" [])] ∧
    coreProc.spec.preconditions = corePre ∧
    coreProc.spec.postconditions = corePost := by
  -- Rewrite hSucc by unfolding translateProcedure step by step
  have hIsSome := translateProcedure_eq_opaque_withImpl proc postconds impl modif
    s sI sO sPre sPost sBody coreInputs coreOutputs corePre corePost bodyStmts
    hOpaque hInputs hOutputs hPre hPost hBody
  rw [Option.isSome_iff_exists] at hIsSome
  obtain ⟨val, hVal⟩ := hIsSome
  rw [hVal] at hSucc
  have := Option.some.inj hSucc; subst this
  -- Now coreProc = val. We need to show the fields match.
  -- Use the same rewriting strategy on hVal.
  rw [translateProcedure.eq_def] at hVal
  simp only [pure, OptionT.pure, OptionT.mk, OptionT.bind, OptionT.lift,
    bind, get, MonadState.get, getThe, MonadStateOf.get,
    StateT.bind, StateT.get, StateT.pure,
    liftM, monadLift, MonadLift.monadLift] at hVal
  rw [hInputs] at hVal
  simp only [pure, OptionT.pure, OptionT.mk, OptionT.bind, OptionT.lift,
    bind, get, MonadState.get, getThe, MonadStateOf.get,
    StateT.bind, StateT.get, StateT.pure,
    liftM, monadLift, MonadLift.monadLift] at hVal
  rw [hOutputs] at hVal
  simp only [pure, OptionT.pure, OptionT.mk, OptionT.bind, OptionT.lift,
    bind, get, MonadState.get, getThe, MonadStateOf.get,
    StateT.bind, StateT.get, StateT.pure,
    liftM, monadLift, MonadLift.monadLift] at hVal
  rw [hPre] at hVal
  simp only [pure, OptionT.pure, OptionT.mk, OptionT.bind, OptionT.lift,
    bind, get, MonadState.get, getThe, MonadStateOf.get,
    StateT.bind, StateT.get, StateT.pure,
    liftM, monadLift, MonadLift.monadLift] at hVal
  rw [hOpaque] at hVal
  simp only [pure, OptionT.pure, OptionT.mk, OptionT.bind, OptionT.lift,
    bind, get, MonadState.get, getThe, MonadStateOf.get,
    StateT.bind, StateT.get, StateT.pure,
    liftM, monadLift, MonadLift.monadLift] at hVal
  rw [hPost] at hVal
  simp only [pure, OptionT.pure, OptionT.mk, OptionT.bind, OptionT.lift,
    bind, get, MonadState.get, getThe, MonadStateOf.get,
    StateT.bind, StateT.get, StateT.pure,
    liftM, monadLift, MonadLift.monadLift] at hVal
  rw [hBody] at hVal
  simp only [pure, OptionT.pure, OptionT.mk, OptionT.bind, OptionT.lift,
    bind, get, MonadState.get, getThe, MonadStateOf.get,
    StateT.bind, StateT.get, StateT.pure,
    liftM, monadLift, MonadLift.monadLift] at hVal
  have := Option.some.inj hVal; subst this
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- When translateProcedure succeeds on an opaque procedure without implementation,
    we can extract the resulting Core.Procedure fields. -/
theorem translateProcedure_opaque_noImpl_get (proc : Procedure)
    (postconds : List StmtExprMd) (modif : List StmtExprMd)
    (s sI sO sPre sPost : TranslateState)
    (coreInputs : List (Core.CoreIdent × LMonoTy))
    (coreOutputs : List (Core.CoreIdent × LMonoTy))
    (corePre : ListMap Core.CoreLabel Core.Procedure.Check)
    (corePost : ListMap Core.CoreLabel Core.Procedure.Check)
    (hOpaque : proc.body = Body.Opaque postconds none modif)
    (hInputs : (proc.inputs.mapM translateParameterToCore s) = (some coreInputs, sI))
    (hOutputs : (proc.outputs.mapM translateParameterToCore sI) = (some coreOutputs, sO))
    (hPre : translateChecks proc.preconditions "requires" sO = (some corePre, sPre))
    (hPost : translateChecks postconds "postcondition" sPre = (some corePost, sPost))
    (coreProc : Core.Procedure)
    (hSucc : (translateProcedure proc s).1 = some coreProc) :
    coreProc.header.name = ⟨proc.name.text, ()⟩ ∧
    coreProc.header.inputs = coreInputs ∧
    coreProc.header.outputs = coreOutputs ++ [(⟨"$result", ()⟩, .tcons "ExceptionResult" [])] ∧
    coreProc.spec.preconditions = corePre ∧
    coreProc.spec.postconditions = corePost := by
  have hIsSome := translateProcedure_eq_opaque_noImpl proc postconds modif
    s sI sO sPre sPost coreInputs coreOutputs corePre corePost
    hOpaque hInputs hOutputs hPre hPost
  rw [Option.isSome_iff_exists] at hIsSome
  obtain ⟨val, hVal⟩ := hIsSome
  rw [hVal] at hSucc
  have := Option.some.inj hSucc; subst this
  rw [translateProcedure.eq_def] at hVal
  simp only [pure, OptionT.pure, OptionT.mk, OptionT.bind, OptionT.lift,
    bind, get, MonadState.get, getThe, MonadStateOf.get,
    StateT.bind, StateT.get, StateT.pure,
    liftM, monadLift, MonadLift.monadLift] at hVal
  rw [hInputs] at hVal
  simp only [pure, OptionT.pure, OptionT.mk, OptionT.bind, OptionT.lift,
    bind, get, MonadState.get, getThe, MonadStateOf.get,
    StateT.bind, StateT.get, StateT.pure,
    liftM, monadLift, MonadLift.monadLift] at hVal
  rw [hOutputs] at hVal
  simp only [pure, OptionT.pure, OptionT.mk, OptionT.bind, OptionT.lift,
    bind, get, MonadState.get, getThe, MonadStateOf.get,
    StateT.bind, StateT.get, StateT.pure,
    liftM, monadLift, MonadLift.monadLift] at hVal
  rw [hPre] at hVal
  simp only [pure, OptionT.pure, OptionT.mk, OptionT.bind, OptionT.lift,
    bind, get, MonadState.get, getThe, MonadStateOf.get,
    StateT.bind, StateT.get, StateT.pure,
    liftM, monadLift, MonadLift.monadLift] at hVal
  rw [hOpaque] at hVal
  simp only [pure, OptionT.pure, OptionT.mk, OptionT.bind, OptionT.lift,
    bind, get, MonadState.get, getThe, MonadStateOf.get,
    StateT.bind, StateT.get, StateT.pure,
    liftM, monadLift, MonadLift.monadLift] at hVal
  rw [hPost] at hVal
  simp only [pure, OptionT.pure, OptionT.mk, OptionT.bind, OptionT.lift,
    bind, get, MonadState.get, getThe, MonadStateOf.get,
    StateT.bind, StateT.get, StateT.pure,
    liftM, monadLift, MonadLift.monadLift] at hVal
  have := Option.some.inj hVal; subst this
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-! ## Abstract body equation lemmas -/

/-- When translateProcedure is called on an abstract procedure, it succeeds. -/
theorem translateProcedure_eq_abstract (proc : Procedure)
    (postconds : List StmtExprMd)
    (s sI sO sPre sPost : TranslateState)
    (coreInputs : List (Core.CoreIdent × LMonoTy))
    (coreOutputs : List (Core.CoreIdent × LMonoTy))
    (corePre : ListMap Core.CoreLabel Core.Procedure.Check)
    (corePost : ListMap Core.CoreLabel Core.Procedure.Check)
    (hAbstract : proc.body = Body.Abstract postconds)
    (hInputs : (proc.inputs.mapM translateParameterToCore s) = (some coreInputs, sI))
    (hOutputs : (proc.outputs.mapM translateParameterToCore sI) = (some coreOutputs, sO))
    (hPre : translateChecks proc.preconditions "requires" sO = (some corePre, sPre))
    (hPost : translateChecks postconds "postcondition" sPre = (some corePost, sPost)) :
    (translateProcedure proc s).1.isSome = true := by
  rw [translateProcedure.eq_def]; mu
  rw [hInputs]; mu; rw [hOutputs]; mu; rw [hPre]; mu
  rw [hAbstract]; mu; rw [hPost]; mu; rfl

/-- When translateProcedure succeeds on an abstract procedure,
    we can extract the resulting Core.Procedure fields. -/
theorem translateProcedure_abstract_get (proc : Procedure)
    (postconds : List StmtExprMd)
    (s sI sO sPre sPost : TranslateState)
    (coreInputs : List (Core.CoreIdent × LMonoTy))
    (coreOutputs : List (Core.CoreIdent × LMonoTy))
    (corePre : ListMap Core.CoreLabel Core.Procedure.Check)
    (corePost : ListMap Core.CoreLabel Core.Procedure.Check)
    (hAbstract : proc.body = Body.Abstract postconds)
    (hInputs : (proc.inputs.mapM translateParameterToCore s) = (some coreInputs, sI))
    (hOutputs : (proc.outputs.mapM translateParameterToCore sI) = (some coreOutputs, sO))
    (hPre : translateChecks proc.preconditions "requires" sO = (some corePre, sPre))
    (hPost : translateChecks postconds "postcondition" sPre = (some corePost, sPost))
    (coreProc : Core.Procedure)
    (hSucc : (translateProcedure proc s).1 = some coreProc) :
    coreProc.header.name = ⟨proc.name.text, ()⟩ ∧
    coreProc.header.inputs = coreInputs ∧
    coreProc.header.outputs = coreOutputs ++ [(⟨"$result", ()⟩, .tcons "ExceptionResult" [])] ∧
    coreProc.spec.preconditions = corePre ∧
    coreProc.spec.postconditions = corePost := by
  have hIsSome := translateProcedure_eq_abstract proc postconds
    s sI sO sPre sPost coreInputs coreOutputs corePre corePost
    hAbstract hInputs hOutputs hPre hPost
  rw [Option.isSome_iff_exists] at hIsSome
  obtain ⟨val, hVal⟩ := hIsSome
  rw [hVal] at hSucc
  have := Option.some.inj hSucc; subst this
  rw [translateProcedure.eq_def] at hVal
  simp only [pure, OptionT.pure, OptionT.mk, OptionT.bind, OptionT.lift,
    bind, get, MonadState.get, getThe, MonadStateOf.get,
    StateT.bind, StateT.get, StateT.pure,
    liftM, monadLift, MonadLift.monadLift] at hVal
  rw [hInputs] at hVal
  simp only [pure, OptionT.pure, OptionT.mk, OptionT.bind, OptionT.lift,
    bind, get, MonadState.get, getThe, MonadStateOf.get,
    StateT.bind, StateT.get, StateT.pure,
    liftM, monadLift, MonadLift.monadLift] at hVal
  rw [hOutputs] at hVal
  simp only [pure, OptionT.pure, OptionT.mk, OptionT.bind, OptionT.lift,
    bind, get, MonadState.get, getThe, MonadStateOf.get,
    StateT.bind, StateT.get, StateT.pure,
    liftM, monadLift, MonadLift.monadLift] at hVal
  rw [hPre] at hVal
  simp only [pure, OptionT.pure, OptionT.mk, OptionT.bind, OptionT.lift,
    bind, get, MonadState.get, getThe, MonadStateOf.get,
    StateT.bind, StateT.get, StateT.pure,
    liftM, monadLift, MonadLift.monadLift] at hVal
  rw [hAbstract] at hVal
  simp only [pure, OptionT.pure, OptionT.mk, OptionT.bind, OptionT.lift,
    bind, get, MonadState.get, getThe, MonadStateOf.get,
    StateT.bind, StateT.get, StateT.pure,
    liftM, monadLift, MonadLift.monadLift] at hVal
  rw [hPost] at hVal
  simp only [pure, OptionT.pure, OptionT.mk, OptionT.bind, OptionT.lift,
    bind, get, MonadState.get, getThe, MonadStateOf.get,
    StateT.bind, StateT.get, StateT.pure,
    liftM, monadLift, MonadLift.monadLift] at hVal
  have := Option.some.inj hVal; subst this
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-! ## mapM length preservation for OptionT/StateM -/

/-- mapM through OptionT (StateM σ) preserves list length when it succeeds. -/
theorem List.length_mapM_optionT_stateM {α β σ : Type}
    (f : α → OptionT (StateM σ) β) (l : List α) (s : σ) (result : List β) (s' : σ)
    (h : l.mapM f s = (some result, s')) :
    result.length = l.length := by
  induction l generalizing s result s' with
  | nil =>
    simp only [List.mapM, pure, OptionT.pure, OptionT.mk, StateT.pure] at h
    have := Option.some.inj (Prod.mk.inj h).1; subst this; rfl
  | cons x xs ih =>
    -- h : (x :: xs).mapM f s = (some result, s')
    -- Use List.mapM_cons to unfold
    rw [List.mapM_cons] at h
    -- h : (f x >>= fun b => xs.mapM f >>= fun bs => pure (b :: bs)) s = (some result, s')
    -- Match on f x s before unfolding bind
    match hfx : f x s with
    | (some b, s1) =>
      -- Now unfold bind with hfx known
      simp only [bind, OptionT.bind, OptionT.mk, StateT.bind,
        pure, OptionT.pure, StateT.pure, hfx] at h
      match hxs : List.mapM f xs s1 with
      | (some bs, s2) =>
        simp only [hxs, pure, OptionT.pure, OptionT.mk, StateT.pure] at h
        have := Option.some.inj (Prod.mk.inj h).1; subst this
        simp [ih s1 bs s2 hxs]
      | (none, s2) =>
        simp only [hxs] at h
        exact absurd (Prod.mk.inj h).1 (by simp)
    | (none, s1) =>
      simp only [bind, OptionT.bind, OptionT.mk, StateT.bind, hfx] at h
      exact absurd (Prod.mk.inj h).1 (by simp)

/-! ## translateProcedureToFunction — axiom count preservation

The key property for P-Spec-2f: when translateProcedureToFunction succeeds,
the number of axioms in the Core.Function equals the number of postconditions
in the source procedure's Body.

`getPostconds` and `translateProcedureToFunction_axioms_length` are proved
inside the module block in `LaurelToCoreTranslator.lean` where `unfold` works
on `translateProcedureToFunction`. The proof uses a `bind_inv` lemma to invert
the monadic bind chain, then case-splits on `proc.body` variants and delegates
to `generateFunctionAxioms_length` for each case. -/

-- getPostconds and translateProcedureToFunction_axioms_length are exported
-- from LaurelToCoreTranslator.lean. No additional lemmas needed here.

/-! ## mapIdxM length preservation for OptionT/StateM -/

set_option linter.unusedSimpArgs false in
/-- mapIdxM.go through OptionT (StateM σ) preserves length:
    result.length = acc.size + l.length. -/
theorem mapIdxM_go_length {α β σ : Type}
    (f : Nat → α → OptionT (StateM σ) β)
    (l : List α) (acc : Array β) (s : σ)
    (result : List β) (s' : σ)
    (h : List.mapIdxM.go f l acc s = (some result, s')) :
    result.length = acc.size + l.length := by
  induction l generalizing acc s result s' with
  | nil =>
    simp [List.mapIdxM.go, pure, OptionT.pure, OptionT.mk, StateT.pure] at h
    have := Option.some.inj (Prod.mk.inj h).1; subst this; simp
  | cons x xs ih =>
    simp only [List.mapIdxM.go, bind, OptionT.bind, OptionT.mk, OptionT.lift,
      StateT.bind, StateT.get, StateT.pure,
      liftM, monadLift, MonadLift.monadLift] at h
    generalize hpair : f acc.size x s = p at h
    obtain ⟨optB, s1⟩ := p
    cases optB with
    | some b =>
      simp only [pure, OptionT.pure, OptionT.mk, StateT.pure] at h
      have hLen := ih (acc.push b) s1 result s' h
      rw [Array.size_push] at hLen; simp only [List.length_cons]; omega
    | none =>
      simp only [pure, OptionT.pure, OptionT.mk, StateT.pure] at h
      cases h

/-- mapIdxM through OptionT (StateM σ) preserves list length when it succeeds. -/
theorem mapIdxM_length {α β σ : Type}
    (f : Nat → α → OptionT (StateM σ) β)
    (l : List α) (s : σ) (result : List β) (s' : σ)
    (h : l.mapIdxM f s = (some result, s')) :
    result.length = l.length := by
  simp [List.mapIdxM] at h
  have := mapIdxM_go_length f l #[] s result s' h
  simp at this; exact this

end Strata.Laurel
