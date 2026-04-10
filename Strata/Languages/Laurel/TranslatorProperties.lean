/-
  Copyright Strata Contributors
  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
import Strata.Languages.Laurel.LaurelToCoreTranslator

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

open Strata.Core

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
theorem translateExpr_succeeds_staticCall_noArgs (callee : Identifier) (md : MetaData) (bv : List Identifier) (s : TranslateState) :
    (translateExpr ⟨.StaticCall callee [], md⟩ bv false s).1.isSome = true := by
  simp [translateExpr_eq_staticCall_noArgs]

/-! ### P-Struct-1b: Expression translation succeeds — compound expressions

Compound expressions succeed when their sub-expressions succeed. -/

/-- Static call with one arg succeeds when the arg succeeds. -/
theorem translateExpr_succeeds_staticCall_oneArg
    (callee : Identifier) (a1 : StmtExprMd) (md : MetaData) (bv : List Identifier)
    (s s1 : TranslateState) (r1 : Core.Expression.Expr)
    (h1 : translateExpr a1 bv false s = (some r1, s1)) :
    (translateExpr ⟨.StaticCall callee [a1], md⟩ bv false s).1.isSome = true := by
  simp [translateExpr_eq_staticCall_oneArg callee a1 md bv s s1 r1 h1]

/-- Static call with two args succeeds when both args succeed. -/
theorem translateExpr_succeeds_staticCall_twoArgs
    (callee : Identifier) (a1 a2 : StmtExprMd) (md : MetaData) (bv : List Identifier)
    (s s1 s2 : TranslateState) (r1 r2 : Core.Expression.Expr)
    (h1 : translateExpr a1 bv false s = (some r1, s1))
    (h2 : translateExpr a2 bv false s1 = (some r2, s2)) :
    (translateExpr ⟨.StaticCall callee [a1, a2], md⟩ bv false s).1.isSome = true := by
  simp [translateExpr_eq_staticCall_twoArgs callee a1 a2 md bv s s1 s2 r1 r2 h1 h2]

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
    (hNotReal : match (computeExprType s.model e1).val, (computeExprType s.model e2).val with
      | .TReal, _ | _, .TReal => False | _, _ => True) :
    (translateExpr ⟨.PrimitiveOp .Add [e1, e2], md⟩ bv pc s).1.isSome = true := by
  simp [translateExpr_eq_primAdd_int e1 e2 md bv pc s s1 s2 r1 r2 h1 h2 hNotReal]

/-- PrimitiveOp Sub (int) succeeds when both args succeed and types are not real. -/
theorem translateExpr_succeeds_primSub_int
    (e1 e2 : StmtExprMd) (md : MetaData) (bv : List Identifier) (pc : Bool)
    (s s1 s2 : TranslateState) (r1 r2 : Core.Expression.Expr)
    (h1 : translateExpr e1 bv pc s = (some r1, s1))
    (h2 : translateExpr e2 bv pc s1 = (some r2, s2))
    (hNotReal : match (computeExprType s.model e1).val, (computeExprType s.model e2).val with
      | .TReal, _ | _, .TReal => False | _, _ => True) :
    (translateExpr ⟨.PrimitiveOp .Sub [e1, e2], md⟩ bv pc s).1.isSome = true := by
  simp [translateExpr_eq_primSub_int e1 e2 md bv pc s s1 s2 r1 r2 h1 h2 hNotReal]

/-- PrimitiveOp Mul (int) succeeds when both args succeed and types are not real. -/
theorem translateExpr_succeeds_primMul_int
    (e1 e2 : StmtExprMd) (md : MetaData) (bv : List Identifier) (pc : Bool)
    (s s1 s2 : TranslateState) (r1 r2 : Core.Expression.Expr)
    (h1 : translateExpr e1 bv pc s = (some r1, s1))
    (h2 : translateExpr e2 bv pc s1 = (some r2, s2))
    (hNotReal : match (computeExprType s.model e1).val, (computeExprType s.model e2).val with
      | .TReal, _ | _, .TReal => False | _, _ => True) :
    (translateExpr ⟨.PrimitiveOp .Mul [e1, e2], md⟩ bv pc s).1.isSome = true := by
  simp [translateExpr_eq_primMul_int e1 e2 md bv pc s s1 s2 r1 r2 h1 h2 hNotReal]

/-- PrimitiveOp Lt (int) succeeds when both args succeed and types are not real. -/
theorem translateExpr_succeeds_primLt_int
    (e1 e2 : StmtExprMd) (md : MetaData) (bv : List Identifier) (pc : Bool)
    (s s1 s2 : TranslateState) (r1 r2 : Core.Expression.Expr)
    (h1 : translateExpr e1 bv pc s = (some r1, s1))
    (h2 : translateExpr e2 bv pc s1 = (some r2, s2))
    (hNotReal : match (computeExprType s.model e1).val, (computeExprType s.model e2).val with
      | .TReal, _ | _, .TReal => False | _, _ => True) :
    (translateExpr ⟨.PrimitiveOp .Lt [e1, e2], md⟩ bv pc s).1.isSome = true := by
  simp [translateExpr_eq_primLt_int e1 e2 md bv pc s s1 s2 r1 r2 h1 h2 hNotReal]

/-- PrimitiveOp Gt (int) succeeds when both args succeed and types are not real. -/
theorem translateExpr_succeeds_primGt_int
    (e1 e2 : StmtExprMd) (md : MetaData) (bv : List Identifier) (pc : Bool)
    (s s1 s2 : TranslateState) (r1 r2 : Core.Expression.Expr)
    (h1 : translateExpr e1 bv pc s = (some r1, s1))
    (h2 : translateExpr e2 bv pc s1 = (some r2, s2))
    (hNotReal : match (computeExprType s.model e1).val, (computeExprType s.model e2).val with
      | .TReal, _ | _, .TReal => False | _, _ => True) :
    (translateExpr ⟨.PrimitiveOp .Gt [e1, e2], md⟩ bv pc s).1.isSome = true := by
  simp [translateExpr_eq_primGt_int e1 e2 md bv pc s s1 s2 r1 r2 h1 h2 hNotReal]

/-- PrimitiveOp Leq (int) succeeds when both args succeed and types are not real. -/
theorem translateExpr_succeeds_primLeq_int
    (e1 e2 : StmtExprMd) (md : MetaData) (bv : List Identifier) (pc : Bool)
    (s s1 s2 : TranslateState) (r1 r2 : Core.Expression.Expr)
    (h1 : translateExpr e1 bv pc s = (some r1, s1))
    (h2 : translateExpr e2 bv pc s1 = (some r2, s2))
    (hNotReal : match (computeExprType s.model e1).val, (computeExprType s.model e2).val with
      | .TReal, _ | _, .TReal => False | _, _ => True) :
    (translateExpr ⟨.PrimitiveOp .Leq [e1, e2], md⟩ bv pc s).1.isSome = true := by
  simp [translateExpr_eq_primLeq_int e1 e2 md bv pc s s1 s2 r1 r2 h1 h2 hNotReal]

/-- PrimitiveOp Geq (int) succeeds when both args succeed and types are not real. -/
theorem translateExpr_succeeds_primGeq_int
    (e1 e2 : StmtExprMd) (md : MetaData) (bv : List Identifier) (pc : Bool)
    (s s1 s2 : TranslateState) (r1 r2 : Core.Expression.Expr)
    (h1 : translateExpr e1 bv pc s = (some r1, s1))
    (h2 : translateExpr e2 bv pc s1 = (some r2, s2))
    (hNotReal : match (computeExprType s.model e1).val, (computeExprType s.model e2).val with
      | .TReal, _ | _, .TReal => False | _, _ => True) :
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

theorem translateExpr_state_staticCall_noArgs (callee : Identifier) (md : MetaData) (bv : List Identifier) (s : TranslateState) :
    (translateExpr ⟨.StaticCall callee [], md⟩ bv false s).2 = s := by
  simp [translateExpr_eq_staticCall_noArgs]

/-! ### P-Struct-1d: Statement translation succeeds -/

/-- Return none always translates. -/
theorem translateStmt_succeeds_return_none (outParams : List Parameter) (md : MetaData) (s : TranslateState) :
    (translateStmt outParams ⟨.Return none, md⟩ s).1.isSome = true := by
  simp [translateStmt_eq_return_none]

/-- LocalVariable with no initializer always translates. -/
theorem translateStmt_succeeds_localVar_noInit
    (outParams : List Parameter) (name : Identifier) (ty : WithMetadata HighType) (md : MetaData) (s : TranslateState) :
    (translateStmt outParams ⟨.LocalVariable name ty none, md⟩ s).1.isSome = true := by
  simp [translateStmt_eq_localVar_noInit]

/-- IfThenElse (no else) succeeds when condition and then-branch succeed. -/
theorem translateStmt_succeeds_ite_noElse
    (cond thenB : StmtExprMd) (md : MetaData) (outParams : List Parameter)
    (s s1 s2 : TranslateState) (rc : Core.Expression.Expr) (rt : List Core.Statement)
    (hc : translateExpr cond [] false s = (some rc, s1))
    (ht : translateStmt outParams thenB s1 = (some rt, s2)) :
    (translateStmt outParams ⟨.IfThenElse cond thenB none, md⟩ s).1.isSome = true := by
  simp [translateStmt_eq_ite_noElse cond thenB md outParams s s1 s2 rc rt hc ht]

/-- IfThenElse (with else) succeeds when all branches succeed. -/
theorem translateStmt_succeeds_ite_withElse
    (cond thenB elseB : StmtExprMd) (md : MetaData) (outParams : List Parameter)
    (s s1 s2 s3 : TranslateState) (rc : Core.Expression.Expr) (rt re : List Core.Statement)
    (hc : translateExpr cond [] false s = (some rc, s1))
    (ht : translateStmt outParams thenB s1 = (some rt, s2))
    (he : translateStmt outParams elseB s2 = (some re, s3)) :
    (translateStmt outParams ⟨.IfThenElse cond thenB (some elseB), md⟩ s).1.isSome = true := by
  simp [translateStmt_eq_ite_withElse cond thenB elseB md outParams s s1 s2 s3 rc rt re hc ht he]

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
  simp [translateStmt_eq_block_unlabeled stmts md outParams s s1 result hInner]

/-- While loop succeeds when condition, invariants, decreases, and body all succeed. -/
theorem translateStmt_succeeds_while
    (cond : StmtExprMd) (invariants : List StmtExprMd) (decreasesExpr : Option StmtExprMd)
    (body : StmtExprMd) (md : MetaData) (outParams : List Parameter)
    (s s1 s2 s3 s4 : TranslateState)
    (condExpr : Core.Expression.Expr) (invExprs : List Core.Expression.Expr)
    (decExprCore : Option Core.Expression.Expr) (bodyStmts : List Core.Statement)
    (hCond : translateExpr cond [] false s = (some condExpr, s1))
    (hInvs : invariants.mapM translateExpr s1 = (some invExprs, s2))
    (hDec : decreasesExpr.mapM translateExpr s2 = (some decExprCore, s3))
    (hBody : translateStmt outParams body s3 = (some bodyStmts, s4)) :
    (translateStmt outParams ⟨.While cond invariants decreasesExpr body, md⟩ s).1.isSome = true := by
  simp [translateStmt_eq_while cond invariants decreasesExpr body md outParams
    s s1 condExpr s2 invExprs s3 decExprCore s4 bodyStmts hCond hInvs hDec hBody]

/-! ### P-Struct-2: Signature preservation for translateProcedure

When translateProcedure succeeds on a transparent procedure with no
preconditions, the output Core.Procedure preserves the input/output
parameter structure. -/

/-- The output procedure's name matches the input procedure's name. -/
theorem translateProcedure_preserves_name
    (proc : Procedure) (bodyExpr : StmtExprMd) (s s1 : TranslateState)
    (bodyStmts : List Core.Statement) (coreProc : Core.Procedure)
    (hTransparent : proc.body = .Transparent bodyExpr)
    (hNoPre : proc.preconditions = [])
    (hBody : (translateStmt proc.outputs bodyExpr s).1 = some bodyStmts)
    (hState : (translateStmt proc.outputs bodyExpr s).2 = s1)
    (hSucc : (translateProcedure proc s).1 = some coreProc) :
    coreProc.header.name = proc.name.text := by
  have hEq := translateProcedure_eq_transparent proc bodyExpr s s1 bodyStmts
    hTransparent hNoPre hBody hState
  have := Option.some.inj (hSucc.symm.trans hEq)
  subst this; rfl

/-- The output procedure has the same number of inputs as the source. -/
theorem translateProcedure_preserves_input_count
    (proc : Procedure) (bodyExpr : StmtExprMd) (s s1 : TranslateState)
    (bodyStmts : List Core.Statement) (coreProc : Core.Procedure)
    (hTransparent : proc.body = .Transparent bodyExpr)
    (hNoPre : proc.preconditions = [])
    (hBody : (translateStmt proc.outputs bodyExpr s).1 = some bodyStmts)
    (hState : (translateStmt proc.outputs bodyExpr s).2 = s1)
    (hSucc : (translateProcedure proc s).1 = some coreProc) :
    coreProc.header.inputs.length = proc.inputs.length := by
  have hEq := translateProcedure_eq_transparent proc bodyExpr s s1 bodyStmts
    hTransparent hNoPre hBody hState
  have := Option.some.inj (hSucc.symm.trans hEq)
  subst this; simp [List.length_map]

/-- The output procedure has outputs = source outputs + $result. -/
theorem translateProcedure_preserves_output_count
    (proc : Procedure) (bodyExpr : StmtExprMd) (s s1 : TranslateState)
    (bodyStmts : List Core.Statement) (coreProc : Core.Procedure)
    (hTransparent : proc.body = .Transparent bodyExpr)
    (hNoPre : proc.preconditions = [])
    (hBody : (translateStmt proc.outputs bodyExpr s).1 = some bodyStmts)
    (hState : (translateStmt proc.outputs bodyExpr s).2 = s1)
    (hSucc : (translateProcedure proc s).1 = some coreProc) :
    coreProc.header.outputs.length = proc.outputs.length + 1 := by
  have hEq := translateProcedure_eq_transparent proc bodyExpr s s1 bodyStmts
    hTransparent hNoPre hBody hState
  have := Option.some.inj (hSucc.symm.trans hEq)
  subst this
  show (proc.outputs.map (translateParameterToCore s.model) ++ [_]).length = proc.outputs.length + 1
  simp [List.length_append, List.length_map]

/-- The output procedure always has $result as its last output. -/
theorem translateProcedure_has_result_output
    (proc : Procedure) (bodyExpr : StmtExprMd) (s s1 : TranslateState)
    (bodyStmts : List Core.Statement) (coreProc : Core.Procedure)
    (hTransparent : proc.body = .Transparent bodyExpr)
    (hNoPre : proc.preconditions = [])
    (hBody : (translateStmt proc.outputs bodyExpr s).1 = some bodyStmts)
    (hState : (translateStmt proc.outputs bodyExpr s).2 = s1)
    (hSucc : (translateProcedure proc s).1 = some coreProc) :
    coreProc.header.outputs.getLast? =
      some (⟨"$result", ()⟩, Lambda.LMonoTy.tcons "ExceptionResult" []) := by
  have hEq := translateProcedure_eq_transparent proc bodyExpr s s1 bodyStmts
    hTransparent hNoPre hBody hState
  have := Option.some.inj (hSucc.symm.trans hEq)
  subst this
  show (proc.outputs.map (translateParameterToCore s.model) ++ [_]).getLast? = some _
  simp [List.getLast?_append]

/-- The output procedure's body starts with $result := Success(). -/
theorem translateProcedure_sets_result_success
    (proc : Procedure) (bodyExpr : StmtExprMd) (s s1 : TranslateState)
    (bodyStmts : List Core.Statement) (coreProc : Core.Procedure)
    (hTransparent : proc.body = .Transparent bodyExpr)
    (hNoPre : proc.preconditions = [])
    (hBody : (translateStmt proc.outputs bodyExpr s).1 = some bodyStmts)
    (hState : (translateStmt proc.outputs bodyExpr s).2 = s1)
    (hSucc : (translateProcedure proc s).1 = some coreProc) :
    coreProc.body.head? =
      some (Core.Statement.set ⟨"$result", ()⟩ (.op () ⟨"Success", ()⟩ none) .empty) := by
  have hEq := translateProcedure_eq_transparent proc bodyExpr s s1 bodyStmts
    hTransparent hNoPre hBody hState
  have := Option.some.inj (hSucc.symm.trans hEq)
  subst this; rfl

/-! ### P-Name-1: Instance call qualification

When translateExpr encounters an InstanceCall and the SemanticModel
resolves the callee, the output is a qualified call `TypeName..callee`
applied to the target (self) and arguments. This is the exhaustiveness
tripwire for the 7-bug name qualification cluster. -/

/-- Instance call with no extra args succeeds when the callee resolves
    and the target translates. -/
theorem translateExpr_succeeds_instanceCall_noArgs
    (target : StmtExprMd) (callee : Identifier) (md : MetaData)
    (bv : List Identifier) (pc : Bool)
    (s s1 : TranslateState) (coreTarget : Core.Expression.Expr)
    (coreName : String)
    (hResolve : resolveInstanceCallName s.model callee = some coreName)
    (hTarget : translateExpr target bv pc s = (some coreTarget, s1)) :
    (translateExpr ⟨.InstanceCall target callee [], md⟩ bv pc s).1.isSome = true := by
  simp [translateExpr_eq_instanceCall_noArgs target callee md bv pc s s1 coreTarget coreName
    hResolve hTarget]

/-- Instance call with no extra args produces a qualified call name. -/
theorem translateExpr_instanceCall_noArgs_uses_qualified_name
    (target : StmtExprMd) (callee : Identifier) (md : MetaData)
    (bv : List Identifier) (pc : Bool)
    (s s1 : TranslateState) (coreTarget : Core.Expression.Expr)
    (coreName : String)
    (hResolve : resolveInstanceCallName s.model callee = some coreName)
    (hTarget : translateExpr target bv pc s = (some coreTarget, s1)) :
    ∃ r, (translateExpr ⟨.InstanceCall target callee [], md⟩ bv pc s).1 = some r ∧
      r = .app () (.op () ⟨coreName, ()⟩ none) coreTarget := by
  exact ⟨_, by simp [translateExpr_eq_instanceCall_noArgs target callee md bv pc s s1
    coreTarget coreName hResolve hTarget], rfl⟩

/-- Instance call with one arg succeeds when callee resolves and
    target + arg translate. -/
theorem translateExpr_succeeds_instanceCall_oneArg
    (target : StmtExprMd) (callee : Identifier) (a1 : StmtExprMd) (md : MetaData)
    (bv : List Identifier) (pc : Bool)
    (s s1 s2 : TranslateState) (coreTarget r1 : Core.Expression.Expr)
    (coreName : String)
    (hResolve : resolveInstanceCallName s.model callee = some coreName)
    (hTarget : translateExpr target bv pc s = (some coreTarget, s1))
    (h1 : translateExpr a1 bv pc s1 = (some r1, s2)) :
    (translateExpr ⟨.InstanceCall target callee [a1], md⟩ bv pc s).1.isSome = true := by
  simp [translateExpr_eq_instanceCall_oneArg target callee a1 md bv pc s s1 s2 coreTarget r1
    coreName hResolve hTarget h1]

/-- Instance call with one arg produces the correct application structure:
    app(app(op(qualifiedName), self), arg). -/
theorem translateExpr_instanceCall_oneArg_structure
    (target : StmtExprMd) (callee : Identifier) (a1 : StmtExprMd) (md : MetaData)
    (bv : List Identifier) (pc : Bool)
    (s s1 s2 : TranslateState) (coreTarget r1 : Core.Expression.Expr)
    (coreName : String)
    (hResolve : resolveInstanceCallName s.model callee = some coreName)
    (hTarget : translateExpr target bv pc s = (some coreTarget, s1))
    (h1 : translateExpr a1 bv pc s1 = (some r1, s2)) :
    ∃ r, (translateExpr ⟨.InstanceCall target callee [a1], md⟩ bv pc s).1 = some r ∧
      r = .app () (.app () (.op () ⟨coreName, ()⟩ none) coreTarget) r1 := by
  exact ⟨_, by simp [translateExpr_eq_instanceCall_oneArg target callee a1 md bv pc s s1 s2
    coreTarget r1 coreName hResolve hTarget h1], rfl⟩

/-- P-Name-1 core: the qualified name in the Core output equals
    `instanceProcCoreName typeName callee`, connecting call sites
    to definition sites (extends IM1). -/
theorem translateExpr_instanceCall_name_is_qualified
    (target : StmtExprMd) (callee : Identifier) (md : MetaData)
    (bv : List Identifier) (pc : Bool)
    (s s1 : TranslateState) (coreTarget : Core.Expression.Expr)
    (typeName : Identifier) (proc : Procedure)
    (hModel : s.model.get callee = .instanceProcedure typeName proc)
    (hTarget : translateExpr target bv pc s = (some coreTarget, s1)) :
    ∃ r, (translateExpr ⟨.InstanceCall target callee [], md⟩ bv pc s).1 = some r ∧
      r = .app () (.op () ⟨instanceProcCoreName typeName.text callee.text, ()⟩ none) coreTarget := by
  have hResolve : resolveInstanceCallName s.model callee = some (instanceProcCoreName typeName.text callee.text) := by
    unfold resolveInstanceCallName; rw [hModel]
  exact ⟨_, by simp [translateExpr_eq_instanceCall_noArgs target callee md bv pc s s1
    coreTarget _ hResolve hTarget], rfl⟩

/-! ### P-Exception-1: Throw translation

Throw(e) produces `[$result := Failure(), exit <exceptionTarget>]`.
This composes with E1 (exit preserves store) and E2 (exit skips
remaining statements) from ExitProperties.lean. -/

/-- Throw always translates successfully (unconditionally). -/
theorem translateStmt_succeeds_throw
    (exception : StmtExprMd) (md : MetaData) (outParams : List Parameter)
    (s : TranslateState) :
    (translateStmt outParams ⟨.Throw exception, md⟩ s).1.isSome = true := by
  simp [translateStmt_eq_throw]

/-- Throw does not modify translation state. -/
theorem translateStmt_throw_preserves_state
    (exception : StmtExprMd) (md : MetaData) (outParams : List Parameter)
    (s : TranslateState) :
    (translateStmt outParams ⟨.Throw exception, md⟩ s).2 = s := by
  simp [translateStmt_eq_throw]

/-- Throw produces [$result := Failure(), exit exceptionTarget]. -/
theorem translateStmt_throw_structure
    (exception : StmtExprMd) (md : MetaData) (outParams : List Parameter)
    (s : TranslateState) :
    (translateStmt outParams ⟨.Throw exception, md⟩ s).1 =
      some [Core.Statement.set ⟨"$result", ()⟩ (.op () ⟨"Failure", ()⟩ none) md,
            Imperative.Stmt.exit (some s.exceptionTarget) md] := by
  simp [translateStmt_eq_throw]

/-! ### P-Spec-1: Postcondition preservation for opaque procedures

When an opaque procedure's preconditions and postconditions both
translate successfully, the Core output contains exactly those
translated postconditions. This catches the "postcondition silently
dropped" bug class (bugs #28, #30, #35). -/

/-- An opaque procedure with implementation preserves its postconditions
    in the Core spec. -/
theorem translateProcedure_opaque_withImpl_preserves_postconditions
    (proc : Procedure) (postconds : List StmtExprMd) (impl : StmtExprMd)
    (modif : List StmtExprMd)
    (s s1 s2 s3 : TranslateState)
    (corePre : ListMap Core.CoreLabel Core.Procedure.Check)
    (corePost : ListMap Core.CoreLabel Core.Procedure.Check)
    (bodyStmts : List Core.Statement)
    (coreProc : Core.Procedure)
    (hOpaque : proc.body = .Opaque postconds (some impl) modif)
    (hPre : translateChecks proc.preconditions "requires" s = (some corePre, s1))
    (hPost : translateChecks postconds "postcondition" s1 = (some corePost, s2))
    (hBody : translateStmt proc.outputs impl s2 = (some bodyStmts, s3))
    (hSucc : (translateProcedure proc s).1 = some coreProc) :
    coreProc.spec.postconditions = corePost := by
  have hEq := translateProcedure_eq_opaque_withImpl proc postconds impl modif
    s s1 s2 s3 corePre corePost bodyStmts hOpaque hPre hPost hBody
  have := Option.some.inj (hSucc.symm.trans hEq)
  subst this; rfl

/-- An opaque procedure with implementation preserves its preconditions
    in the Core spec. -/
theorem translateProcedure_opaque_withImpl_preserves_preconditions
    (proc : Procedure) (postconds : List StmtExprMd) (impl : StmtExprMd)
    (modif : List StmtExprMd)
    (s s1 s2 s3 : TranslateState)
    (corePre : ListMap Core.CoreLabel Core.Procedure.Check)
    (corePost : ListMap Core.CoreLabel Core.Procedure.Check)
    (bodyStmts : List Core.Statement)
    (coreProc : Core.Procedure)
    (hOpaque : proc.body = .Opaque postconds (some impl) modif)
    (hPre : translateChecks proc.preconditions "requires" s = (some corePre, s1))
    (hPost : translateChecks postconds "postcondition" s1 = (some corePost, s2))
    (hBody : translateStmt proc.outputs impl s2 = (some bodyStmts, s3))
    (hSucc : (translateProcedure proc s).1 = some coreProc) :
    coreProc.spec.preconditions = corePre := by
  have hEq := translateProcedure_eq_opaque_withImpl proc postconds impl modif
    s s1 s2 s3 corePre corePost bodyStmts hOpaque hPre hPost hBody
  have := Option.some.inj (hSucc.symm.trans hEq)
  subst this; rfl

/-- An opaque procedure without implementation preserves its postconditions. -/
theorem translateProcedure_opaque_noImpl_preserves_postconditions
    (proc : Procedure) (postconds : List StmtExprMd) (modif : List StmtExprMd)
    (s s1 s2 : TranslateState)
    (corePre : ListMap Core.CoreLabel Core.Procedure.Check)
    (corePost : ListMap Core.CoreLabel Core.Procedure.Check)
    (coreProc : Core.Procedure)
    (hOpaque : proc.body = .Opaque postconds none modif)
    (hPre : translateChecks proc.preconditions "requires" s = (some corePre, s1))
    (hPost : translateChecks postconds "postcondition" s1 = (some corePost, s2))
    (hSucc : (translateProcedure proc s).1 = some coreProc) :
    coreProc.spec.postconditions = corePost := by
  have hEq := translateProcedure_eq_opaque_noImpl proc postconds modif
    s s1 s2 corePre corePost hOpaque hPre hPost
  have := Option.some.inj (hSucc.symm.trans hEq)
  subst this; rfl

/-- An opaque procedure without implementation preserves its preconditions. -/
theorem translateProcedure_opaque_noImpl_preserves_preconditions
    (proc : Procedure) (postconds : List StmtExprMd) (modif : List StmtExprMd)
    (s s1 s2 : TranslateState)
    (corePre : ListMap Core.CoreLabel Core.Procedure.Check)
    (corePost : ListMap Core.CoreLabel Core.Procedure.Check)
    (coreProc : Core.Procedure)
    (hOpaque : proc.body = .Opaque postconds none modif)
    (hPre : translateChecks proc.preconditions "requires" s = (some corePre, s1))
    (hPost : translateChecks postconds "postcondition" s1 = (some corePost, s2))
    (hSucc : (translateProcedure proc s).1 = some coreProc) :
    coreProc.spec.preconditions = corePre := by
  have hEq := translateProcedure_eq_opaque_noImpl proc postconds modif
    s s1 s2 corePre corePost hOpaque hPre hPost
  have := Option.some.inj (hSucc.symm.trans hEq)
  subst this; rfl

/-- An opaque procedure (with impl) preserves its name. -/
theorem translateProcedure_opaque_withImpl_preserves_name
    (proc : Procedure) (postconds : List StmtExprMd) (impl : StmtExprMd)
    (modif : List StmtExprMd)
    (s s1 s2 s3 : TranslateState)
    (corePre : ListMap Core.CoreLabel Core.Procedure.Check)
    (corePost : ListMap Core.CoreLabel Core.Procedure.Check)
    (bodyStmts : List Core.Statement)
    (coreProc : Core.Procedure)
    (hOpaque : proc.body = .Opaque postconds (some impl) modif)
    (hPre : translateChecks proc.preconditions "requires" s = (some corePre, s1))
    (hPost : translateChecks postconds "postcondition" s1 = (some corePost, s2))
    (hBody : translateStmt proc.outputs impl s2 = (some bodyStmts, s3))
    (hSucc : (translateProcedure proc s).1 = some coreProc) :
    coreProc.header.name = proc.name.text := by
  have hEq := translateProcedure_eq_opaque_withImpl proc postconds impl modif
    s s1 s2 s3 corePre corePost bodyStmts hOpaque hPre hPost hBody
  have := Option.some.inj (hSucc.symm.trans hEq)
  subst this; rfl

/-- An opaque procedure (no impl) body is assume false (havoc). -/
theorem translateProcedure_opaque_noImpl_body_is_havoc
    (proc : Procedure) (postconds : List StmtExprMd) (modif : List StmtExprMd)
    (s s1 s2 : TranslateState)
    (corePre : ListMap Core.CoreLabel Core.Procedure.Check)
    (corePost : ListMap Core.CoreLabel Core.Procedure.Check)
    (coreProc : Core.Procedure)
    (hOpaque : proc.body = .Opaque postconds none modif)
    (hPre : translateChecks proc.preconditions "requires" s = (some corePre, s1))
    (hPost : translateChecks postconds "postcondition" s1 = (some corePost, s2))
    (hSucc : (translateProcedure proc s).1 = some coreProc) :
    coreProc.body = [Core.Statement.set ⟨"$result", ()⟩ (.op () ⟨"Success", ()⟩ none) .empty,
      .block "$body" [Core.Statement.assume "no_body" (.const () (.boolConst false)) .empty] .empty] := by
  have hEq := translateProcedure_eq_opaque_noImpl proc postconds modif
    s s1 s2 corePre corePost hOpaque hPre hPost
  have := Option.some.inj (hSucc.symm.trans hEq)
  subst this; rfl

end Strata.Laurel
