/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

import Strata.DL.Imperative.StmtSemantics

/-!
# Exit Semantics Properties

Formal proofs of the correctness properties for exit and labeled blocks,
as specified in `docs/design/exit-semantics/spec.md`.
-/

namespace Imperative

open BlockResult

section ExitProperties

variable {P : PureExpr} {Cmd : Type} {EvalCmd : EvalCmdParam P Cmd}
  {extendEval : ExtendEval P}
  [DecidableEq P.Ident]
  [HasVarsImp P (List (Stmt P Cmd))] [HasVarsImp P Cmd]
  [HasFvar P] [HasVal P] [HasBool P] [HasNot P]

/-- **E1: Exit Preserves Store.**
    An exit statement does not modify the store or evaluation context. -/
theorem exit_preserves_store
    (H : EvalStmt P Cmd EvalCmd extendEval δ σ (.exit label md) σ' br δ') :
    σ' = σ ∧ δ' = δ ∧ br = .exited label := by
  cases H with
  | exit_sem => exact ⟨rfl, rfl, rfl⟩

/-- **E2: Exit Skips Remaining Statements.**
    If a block produces an exit, the exiting statement determines the store.
    (The stmts_exit_sem constructor guarantees remaining statements are skipped.) -/
theorem exit_skips_remaining
    (H : EvalBlock P Cmd EvalCmd extendEval δ σ (s :: rest) σ' (.exited label) δ') :
    EvalStmt P Cmd EvalCmd extendEval δ σ s σ' (.exited label) δ'
    ∨ ∃ σ₁ δ₁, EvalStmt P Cmd EvalCmd extendEval δ σ s σ₁ .normal δ₁ ∧
        EvalBlock P Cmd EvalCmd extendEval δ₁ σ₁ rest σ' (.exited label) δ' := by
  cases H with
  | stmts_exit_sem Hstmt => exact Or.inl Hstmt
  | stmts_normal_sem Hstmt Hrest => exact Or.inr ⟨_, _, Hstmt, Hrest⟩

/-- **E3: Matching Block Consumes Exit.**
    A block with label L that contains exit (some L) completes normally. -/
theorem matching_block_consumes
    (Heval : EvalBlock P Cmd EvalCmd extendEval δ σ body σ' (.exited (.some L)) δ') :
    EvalStmt P Cmd EvalCmd extendEval δ σ (.block L body md) σ' .normal δ' :=
  .block_sem Heval (consumeExit_exited_same L)

/-- **E4: Non-Matching Exit Propagates.**
    A block with label L that contains exit (some M) where M ≠ L
    propagates the exit unchanged. -/
theorem nonmatching_exit_propagates
    (Hne : M ≠ L)
    (Heval : EvalBlock P Cmd EvalCmd extendEval δ σ body σ' (.exited (.some M)) δ') :
    EvalStmt P Cmd EvalCmd extendEval δ σ (.block L body md) σ' (.exited (.some M)) δ' :=
  .block_sem Heval (consumeExit_exited_ne Hne)

/-- **E5: Normal Block Completion.**
    If a block's body completes normally, the block completes normally. -/
theorem normal_block_completion
    (Heval : EvalBlock P Cmd EvalCmd extendEval δ σ body σ' .normal δ') :
    EvalStmt P Cmd EvalCmd extendEval δ σ (.block L body md) σ' .normal δ' :=
  .block_sem Heval (consumeExit_normal L)

/-- **E6a: Exit Propagates Through Conditionals (true branch).** -/
theorem exit_propagates_through_ite_true
    {c : P.Expr}
    (Hcond : δ σ c = .some HasBool.tt)
    (Hwf : WellFormedSemanticEvalBool δ)
    (Heval : EvalBlock P Cmd EvalCmd extendEval δ σ thenBranch σ' (.exited label) δ') :
    EvalStmt P Cmd EvalCmd extendEval δ σ (.ite c thenBranch elseBranch md) σ' (.exited label) δ' :=
  .ite_true_sem Hcond Hwf Heval

/-- **E6b: Exit Propagates Through Conditionals (false branch).** -/
theorem exit_propagates_through_ite_false
    {c : P.Expr}
    (Hcond : δ σ c = .some HasBool.ff)
    (Hwf : WellFormedSemanticEvalBool δ)
    (Heval : EvalBlock P Cmd EvalCmd extendEval δ σ elseBranch σ' (.exited label) δ') :
    EvalStmt P Cmd EvalCmd extendEval δ σ (.ite c thenBranch elseBranch md) σ' (.exited label) δ' :=
  .ite_false_sem Hcond Hwf Heval

/-- **E7: Determinism of Exit Consumption.**
    consumeExit is a function — the output is uniquely determined. -/
theorem consumeExit_deterministic (L : String) (br : BlockResult) :
    ∀ br₁ br₂, consumeExit L br = br₁ → consumeExit L br = br₂ → br₁ = br₂ :=
  fun _ _ h₁ h₂ => h₁ ▸ h₂ ▸ rfl

/-- **Unlabeled exit consumed by any block.** -/
theorem unlabeled_exit_consumed
    (Heval : EvalBlock P Cmd EvalCmd extendEval δ σ body σ' (.exited .none) δ') :
    EvalStmt P Cmd EvalCmd extendEval δ σ (.block L body md) σ' .normal δ' :=
  .block_sem Heval (consumeExit_exited_none L)

/-- **Empty block completes normally.** -/
theorem empty_block_normal
    (H : EvalBlock P Cmd EvalCmd extendEval δ σ ([] : List (Stmt P Cmd)) σ' br δ') :
    σ' = σ ∧ δ' = δ ∧ br = .normal := by
  cases H with
  | stmts_none_sem => exact ⟨rfl, rfl, rfl⟩

end ExitProperties

end Imperative
