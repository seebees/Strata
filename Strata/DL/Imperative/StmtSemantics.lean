/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Imperative.CmdSemantics
public import Strata.DL.Imperative.Stmt
import Strata.Util.Tactics

---------------------------------------------------------------------

namespace Imperative

public section

/-- Type of a function that extends the semantic evaluator with a new function definition. -/
@[expose] abbrev ExtendEval (P : PureExpr) := SemanticEval P → SemanticStore P → PureFunc P → SemanticEval P

/-- The outcome of evaluating a block: either normal completion or an exit propagating. -/
inductive BlockResult where
  /-- All statements completed normally. -/
  | normal
  /-- An `exit` statement transferred control. `none` = exit nearest block,
      `some L` = exit block labeled L. -/
  | exited (label : Option String)
  deriving DecidableEq, Repr

/-- A labeled block consumes a matching exit, producing normal completion.
    Non-matching exits propagate unchanged. -/
def consumeExit (blockLabel : String) : BlockResult → BlockResult
  | .normal => .normal
  | .exited .none => .normal
  | .exited (.some l) => if l == blockLabel then .normal else .exited (.some l)


@[simp] theorem consumeExit_normal (L : String) : consumeExit L .normal = .normal := by
  unfold consumeExit; rfl
@[simp] theorem consumeExit_exited_none (L : String) : consumeExit L (.exited .none) = .normal := by
  unfold consumeExit; rfl
@[simp] theorem consumeExit_exited_same (L : String) : consumeExit L (.exited (.some L)) = .normal := by
  simp [consumeExit]
theorem consumeExit_exited_ne {M L : String} (h : M ≠ L) : consumeExit L (.exited (.some M)) = .exited (.some M) := by
  simp [consumeExit, bne_iff_ne, h]
mutual

/--
An inductively-defined operational semantics that depends on
environment lookup and evaluation functions for expressions.

Note that `EvalStmt` is parameterized by commands `Cmd` as well as their
evaluation relation `EvalCmd`, and by `extendEval` which specifies how
`funcDecl` statements extend the evaluator.

The expression evaluator `δ` is threaded as state to support `funcDecl`,
which extends the evaluator with new function definitions. Commands do not
modify the evaluator, only `funcDecl` statements do.

The `BlockResult` indicates whether the statement completed normally or
produced an exit that is propagating upward through enclosing blocks.
-/
inductive EvalStmt (P : PureExpr) (Cmd : Type) (EvalCmd : EvalCmdParam P Cmd)
  (extendEval : ExtendEval P)
  [DecidableEq P.Ident]
  [HasVarsImp P (List (Stmt P Cmd))] [HasVarsImp P Cmd] [HasFvar P] [HasVal P] [HasBool P] [HasNot P] :
  SemanticEval P → SemanticStore P → Stmt P Cmd → SemanticStore P → BlockResult → SemanticEval P → Prop where
  | cmd_sem :
    EvalCmd δ σ c σ' →
    isDefinedOver (HasVarsImp.modifiedVars) σ c →
    ----
    EvalStmt P Cmd EvalCmd extendEval δ σ (Stmt.cmd c) σ' .normal δ

  | block_sem :
    EvalBlock P Cmd EvalCmd extendEval δ σ b σ' br δ' →
    consumeExit label br = br' →
    ----
    EvalStmt P Cmd EvalCmd extendEval δ σ (.block label b md) σ' br' δ'

  | ite_true_sem :
    δ σ c = .some HasBool.tt →
    WellFormedSemanticEvalBool δ →
    EvalBlock P Cmd EvalCmd extendEval δ σ t σ' br δ' →
    ----
    EvalStmt P Cmd EvalCmd extendEval δ σ (.ite c t e md) σ' br δ'

  | ite_false_sem :
    δ σ c = .some HasBool.ff →
    WellFormedSemanticEvalBool δ →
    EvalBlock P Cmd EvalCmd extendEval δ σ e σ' br δ' →
    ----
    EvalStmt P Cmd EvalCmd extendEval δ σ (.ite c t e md) σ' br δ'

  | exit_sem :
    EvalStmt P Cmd EvalCmd extendEval δ σ (.exit label md) σ (.exited label) δ

  | funcDecl_sem [HasSubstFvar P] [HasVarsPure P P.Expr] :
    EvalStmt P Cmd EvalCmd extendEval δ σ (.funcDecl decl md) σ .normal
      (extendEval δ σ decl)

  | typeDecl_sem :
    EvalStmt P Cmd EvalCmd extendEval δ σ (.typeDecl tc md) σ .normal δ

inductive EvalBlock (P : PureExpr) (Cmd : Type) (EvalCmd : EvalCmdParam P Cmd)
  (extendEval : ExtendEval P)
  [DecidableEq P.Ident]
  [HasVarsImp P (List (Stmt P Cmd))] [HasVarsImp P Cmd] [HasFvar P] [HasVal P] [HasBool P] [HasNot P] :
    SemanticEval P → SemanticStore P → List (Stmt P Cmd) → SemanticStore P → BlockResult → SemanticEval P → Prop where
  | stmts_none_sem :
    EvalBlock P _ _ _ δ σ [] σ .normal δ
  | stmts_normal_sem :
    EvalStmt P Cmd EvalCmd extendEval δ σ s σ' .normal δ' →
    EvalBlock P Cmd EvalCmd extendEval δ' σ' ss σ'' br δ'' →
    EvalBlock P Cmd EvalCmd extendEval δ σ (s :: ss) σ'' br δ''
  | stmts_exit_sem :
    EvalStmt P Cmd EvalCmd extendEval δ σ s σ' (.exited label) δ' →
    -- remaining statements are SKIPPED
    EvalBlock P Cmd EvalCmd extendEval δ σ (s :: ss) σ' (.exited label) δ'

end

theorem eval_stmts_singleton
  [DecidableEq P.Ident]
  [HasVarsImp P (List (Stmt P (Cmd P)))] [HasVarsImp P (Cmd P)] [HasFvar P] [HasVal P] [HasBool P] [HasNot P] :
  EvalBlock P (Cmd P) (EvalCmd P) extendEval δ σ [cmd] σ' br δ' ↔
  EvalStmt P (Cmd P) (EvalCmd P) extendEval δ σ cmd σ' br δ' := by
  constructor <;> intro Heval
  · cases Heval with
    | stmts_normal_sem Heval Hempty => cases Hempty; exact Heval
    | stmts_exit_sem Heval => exact Heval
  · match br with
    | .normal => exact EvalBlock.stmts_normal_sem Heval EvalBlock.stmts_none_sem
    | .exited _ => exact EvalBlock.stmts_exit_sem Heval

theorem eval_stmts_concat
  [DecidableEq P.Ident]
  [HasVarsImp P (List (Stmt P (Cmd P)))] [HasVarsImp P (Cmd P)] [HasFvar P] [HasVal P] [HasBool P] [HasNot P] :
  EvalBlock P (Cmd P) (EvalCmd P) extendEval δ σ cmds1 σ' .normal δ' →
  EvalBlock P (Cmd P) (EvalCmd P) extendEval δ' σ' cmds2 σ'' br δ'' →
  EvalBlock P (Cmd P) (EvalCmd P) extendEval δ σ (cmds1 ++ cmds2) σ'' br δ'' := by
  intro Heval1 Heval2
  induction cmds1 generalizing cmds2 σ δ
  · simp only [List.nil_append]
    cases Heval1; exact Heval2
  · rename_i cmd cmds ind
    cases Heval1 with
    | stmts_normal_sem Hstmt Hrest =>
      apply EvalBlock.stmts_normal_sem Hstmt
      exact ind Hrest Heval2

theorem EvalCmdDefMonotone [HasFvar P] [HasBool P] [HasNot P] :
  isDefined σ v →
  EvalCmd P δ σ c σ' →
  isDefined σ' v := by
  intros Hdef Heval
  cases Heval <;> try exact Hdef
  next _ Hup => exact InitStateDefMonotone Hdef Hup  -- eval_init
  next Hup => exact InitStateDefMonotone Hdef Hup    -- eval_init_unconstrained
  next _ Hup => exact UpdateStateDefMonotone Hdef Hup
  next Hup => exact UpdateStateDefMonotone Hdef Hup

theorem EvalBlockEmpty {P : PureExpr} {Cmd : Type} {EvalCmd : EvalCmdParam P Cmd}
  {extendEval : ExtendEval P}
  { σ σ': SemanticStore P } { δ δ' : SemanticEval P } { br : BlockResult }
  [DecidableEq P.Ident]
  [HasVarsImp P (List (Stmt P Cmd))] [HasVarsImp P Cmd] [HasFvar P] [HasVal P] [HasBool P] [HasNot P] :
  EvalBlock P Cmd EvalCmd extendEval δ σ ([]: (List (Stmt P Cmd))) σ' br δ' → σ = σ' ∧ δ = δ' ∧ br = .normal := by
  intros H; cases H <;> simp

mutual
theorem EvalStmtDefMonotone
  [DecidableEq P.Ident]
  [HasVal P] [HasFvar P] [HasBool P] [HasBoolVal P] [HasNot P]
  :
  isDefined σ v →
  EvalStmt P (Cmd P) (EvalCmd P) extendEval δ σ s σ' br δ' →
  isDefined σ' v := by
  intros Hdef Heval
  match s with
  | .cmd c =>
    cases Heval; next Hwf Hup =>
    exact EvalCmdDefMonotone Hdef Hup
  | .block l bss  _ =>
    cases Heval; next Hwf Hup =>
    apply EvalBlockDefMonotone <;> assumption
  | .ite c tss bss _ => cases Heval with
    | ite_true_sem Hsome Hwf Heval =>
      apply EvalBlockDefMonotone <;> assumption
    | ite_false_sem Hsome Hwf Heval =>
      apply EvalBlockDefMonotone <;> assumption
  | .exit _ _ => cases Heval; assumption
  | .loop _ _ _ _ _ => cases Heval
  | .funcDecl _ _ => cases Heval; assumption
  | .typeDecl _ _ => cases Heval; assumption

theorem EvalBlockDefMonotone
  [DecidableEq P.Ident]
  [HasVal P] [HasFvar P] [HasBool P] [HasBoolVal P] [HasNot P]
  :
  isDefined σ v →
  EvalBlock P (Cmd P) (EvalCmd P) extendEval δ σ ss σ' br δ' →
  isDefined σ' v := by
  intros Hdef Heval
  cases ss with
  | nil =>
    have Heq := EvalBlockEmpty Heval
    simp [← Heq.1]
    assumption
  | cons h t =>
    cases Heval with
    | stmts_normal_sem Heval1 Heval2 =>
      apply EvalBlockDefMonotone (σ:=_) (δ:=_)
      · apply EvalStmtDefMonotone <;> assumption
      · assumption
    | stmts_exit_sem Heval1 =>
      apply EvalStmtDefMonotone <;> assumption
end

end -- public section
