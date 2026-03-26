/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

import Strata.DL.Imperative.StmtSemantics

/-!
# Exception Translation Properties

Formal proofs of correctness properties P1, P2, P4, P6 for the
Throw/TryCatch translation, as specified in
`docs/design/laurel-exceptions/spec.md`.

All proofs use the exit semantics constructors directly.
-/

namespace Imperative

open BlockResult

variable {P : PureExpr} {Cmd : Type} {EvalCmd : EvalCmdParam P Cmd}
  {extendEval : ExtendEval P}
  [DecidableEq P.Ident]
  [HasVarsImp P (List (Stmt P Cmd))] [HasVarsImp P Cmd]
  [HasFvar P] [HasVal P] [HasBool P] [HasNot P]

/-- **P1: Throw Produces Exit.**
    Throw translates to [setFlag, exit $body]. The sequence produces
    .exited with the flag store preserved. -/
theorem throw_produces_exit
    (Hset : EvalStmt P Cmd EvalCmd extendEval δ σ setFlagStmt σ₁ .normal δ₁) :
    EvalBlock P Cmd EvalCmd extendEval δ σ
      [setFlagStmt, .exit (.some bodyLabel) md]
      σ₁ (.exited (.some bodyLabel)) δ₁ :=
  .stmts_normal_sem Hset (.stmts_exit_sem .exit_sem)

/-- **P1 (corollary): Exit preserves the flag store.** -/
theorem throw_exit_preserves_store :
    EvalStmt P Cmd EvalCmd extendEval δ σ (.exit label md) σ (.exited label) δ :=
  .exit_sem

/-- **P2: Success Path Isolation.**
    If a block completes normally, every statement completed normally.
    No Throw (which uses exit) executed on this path. -/
theorem success_path_head_normal
    (H : EvalBlock P Cmd EvalCmd extendEval δ σ (s :: rest) σ' .normal δ') :
    ∃ σ₁ δ₁, EvalStmt P Cmd EvalCmd extendEval δ σ s σ₁ .normal δ₁ ∧
              EvalBlock P Cmd EvalCmd extendEval δ₁ σ₁ rest σ' .normal δ' := by
  cases H with
  | stmts_normal_sem Hs Hrest => exact ⟨_, _, Hs, Hrest⟩

/-- **P4 Step 1: Body + exit produces .exited tryEndLabel.** -/
theorem normal_body_then_exit
    (HbodyEval : EvalBlock P Cmd EvalCmd extendEval δ σ bodyStmts σ₁ .normal δ₁) :
    EvalBlock P Cmd EvalCmd extendEval δ σ
      (bodyStmts ++ [.exit (.some tryEndLabel) md_exit])
      σ₁ (.exited (.some tryEndLabel)) δ₁ := by
  induction bodyStmts generalizing σ δ with
  | nil =>
    cases HbodyEval
    exact .stmts_exit_sem .exit_sem
  | cons h t ih =>
    cases HbodyEval with
    | stmts_normal_sem Hh Ht =>
      exact .stmts_normal_sem Hh (ih Ht)

/-- **P4 Step 2: Handlers block propagates exit (label mismatch).** -/
theorem handlers_block_propagates_exit
    (Hne : tryEndLabel ≠ handlersLabel)
    (HinnerEval : EvalBlock P Cmd EvalCmd extendEval δ σ innerStmts
      σ₁ (.exited (.some tryEndLabel)) δ₁) :
    EvalStmt P Cmd EvalCmd extendEval δ σ
      (.block handlersLabel innerStmts md_handlers)
      σ₁ (.exited (.some tryEndLabel)) δ₁ :=
  .block_sem HinnerEval (consumeExit_exited_ne Hne)

/-- **P4 Step 3: Try_end block consumes exit → normal.** -/
theorem try_end_consumes_exit
    (HhandlersEval : EvalStmt P Cmd EvalCmd extendEval δ σ handlersBlockStmt
      σ₁ (.exited (.some tryEndLabel)) δ₁)
    (catchStmts : List (Stmt P Cmd)) :
    EvalStmt P Cmd EvalCmd extendEval δ σ
      (.block tryEndLabel (handlersBlockStmt :: catchStmts) md_try)
      σ₁ .normal δ₁ :=
  .block_sem (.stmts_exit_sem HhandlersEval) (consumeExit_exited_same tryEndLabel)

/-- **P6: Finally Execution.**
    Finally is after the try block. The try block completes normally
    (by P4 or E5), so sequential evaluation continues with finally. -/
theorem finally_executes_after_try
    (HtryEval : EvalStmt P Cmd EvalCmd extendEval δ σ tryBlock σ₁ .normal δ₁)
    (HfinallyEval : EvalBlock P Cmd EvalCmd extendEval δ₁ σ₁ finallyStmts σ₂ br₂ δ₂) :
    EvalBlock P Cmd EvalCmd extendEval δ σ (tryBlock :: finallyStmts) σ₂ br₂ δ₂ :=
  .stmts_normal_sem HtryEval HfinallyEval

end Imperative
