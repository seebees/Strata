/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Imperative.Stmt
public import Strata.DL.Imperative.StmtSemantics
public import Strata.DL.Imperative.NondetStmt
public import Strata.DL.Imperative.NondetStmtSemantics
public import Strata.Transform.DetToNondet
import all Strata.DL.Imperative.Stmt
import all Strata.DL.Imperative.NondetStmt
import all Strata.DL.Imperative.CmdSemantics
import all Strata.DL.Imperative.Cmd
import all Strata.DL.Imperative.HasVars
import all Strata.Transform.DetToNondet

/-! # Deterministic-to-Nondeterministic Transformation Correctness Proof
  This file contains the main proof that the deterministic-to-nondeterministic
  transformation is semantics preserving (see `StmtToNondetStmtCorrect` and
  `BlockToNondetStmtCorrect`)

  Note: The proof requires that the program contains no function declarations
  (`noFuncDecl`). This is because `funcDecl` changes the evaluator `δ`, but the
  nondeterministic statements don't have function declarations.
  -/

public section

open Imperative Core

/-- Helper for proving noFuncDecl preserves δ for blocks, given IH for statements. -/
private theorem noFuncDecl_preserves_δ_block_aux
  [HasVal P] [HasFvar P] [HasBool P] [HasNot P] [DecidableEq P.Ident]
  (extendEval : ExtendEval P)
  (ss : Block P (Cmd P)) (δ δ' : SemanticEval P) (σ σ' : SemanticStore P) (br : BlockResult)
  (ih : ∀ s, s ∈ ss → ∀ (δ δ' : SemanticEval P) (σ σ' : SemanticStore P) (br : BlockResult),
    Stmt.noFuncDecl s → EvalStmt P (Cmd P) (EvalCmd P) extendEval δ σ s σ' br δ' → δ' = δ)
  (Hno : Block.noFuncDecl ss)
  (Heval : EvalBlock P (Cmd P) (EvalCmd P) extendEval δ σ ss σ' br δ') :
  δ' = δ := by
  induction ss generalizing σ σ' δ δ' br with
  | nil =>
    cases Heval with
    | stmts_none_sem => rfl
  | cons h t ih_list =>
    cases Heval with
    | stmts_normal_sem Heval_h Heval_t =>
      next σ₁ δ₁ =>
      simp [Block.noFuncDecl] at Hno
      have h_mem : h ∈ h :: t := by simp
      have Hδ₁ : δ₁ = δ := ih h h_mem δ δ₁ σ σ₁ .normal Hno.1 Heval_h
      have ih_t : ∀ s, s ∈ t → ∀ (δ δ' : SemanticEval P) (σ σ' : SemanticStore P) (br : BlockResult),
        Stmt.noFuncDecl s → EvalStmt P (Cmd P) (EvalCmd P) extendEval δ σ s σ' br δ' → δ' = δ :=
        fun s hs => ih s (by simp [hs])
      have Hδ' : δ' = δ₁ := ih_list δ₁ δ' σ₁ σ' _ ih_t Hno.2 Heval_t
      simp [Hδ₁, Hδ']
    | stmts_exit_sem Heval_h =>
      simp [Block.noFuncDecl] at Hno
      exact ih h (by simp) δ δ' σ σ' _ Hno.1 Heval_h

/-- When a statement has no function declarations, evaluating it preserves the evaluator. -/
theorem EvalStmt_noFuncDecl_preserves_δ
  [HasVal P] [HasFvar P] [HasBool P] [HasNot P] [DecidableEq P.Ident]
  (extendEval : ExtendEval P)
  (st : Stmt P (Cmd P)) (δ δ' : SemanticEval P) (σ σ' : SemanticStore P) (br : BlockResult) :
  Stmt.noFuncDecl st →
  EvalStmt P (Cmd P) (EvalCmd P) extendEval δ σ st σ' br δ' →
  δ' = δ := by
  induction st using Stmt.inductionOn generalizing δ δ' σ σ' br with
  | cmd_case c =>
    intros Hno Heval
    cases Heval with
    | cmd_sem _ _ => rfl
  | block_case label bss md ih =>
    intros Hno Heval
    cases Heval with
    | block_sem Heval _ =>
    simp [Stmt.noFuncDecl] at Hno
    exact noFuncDecl_preserves_δ_block_aux extendEval bss _ _ _ _ _ ih Hno Heval
  | ite_case cond tss ess md ih_t ih_e =>
    intros Hno Heval
    cases Heval with
    | ite_true_sem _ _ Heval =>
      simp [Stmt.noFuncDecl] at Hno
      exact noFuncDecl_preserves_δ_block_aux extendEval tss _ _ _ _ _ ih_t Hno.1 Heval
    | ite_false_sem _ _ Heval =>
      simp [Stmt.noFuncDecl] at Hno
      exact noFuncDecl_preserves_δ_block_aux extendEval ess _ _ _ _ _ ih_e Hno.2 Heval
  | loop_case guard measure invariant body md ih =>
    intros Hno Heval
    cases Heval
  | exit_case label md =>
    intros Hno Heval
    cases Heval with
    | exit_sem => rfl
  | funcDecl_case decl md =>
    intros Hno Heval
    simp [Stmt.noFuncDecl] at Hno
  | typeDecl_case tc md =>
    intros Hno Heval
    cases Heval with
    | typeDecl_sem => rfl

/-- When a block has no function declarations, evaluating it preserves the evaluator. -/
theorem EvalBlock_noFuncDecl_preserves_δ
  [HasVal P] [HasFvar P] [HasBool P] [HasNot P] [DecidableEq P.Ident]
  (extendEval : ExtendEval P)
  (ss : Block P (Cmd P)) (δ δ' : SemanticEval P) (σ σ' : SemanticStore P) (br : BlockResult) :
  Block.noFuncDecl ss →
  EvalBlock P (Cmd P) (EvalCmd P) extendEval δ σ ss σ' br δ' →
  δ' = δ := by
  induction ss generalizing δ δ' σ σ' br with
  | nil =>
    intros Hno Heval
    cases Heval with
    | stmts_none_sem => rfl
  | cons h t ih =>
    intros Hno Heval
    cases Heval with
    | stmts_normal_sem Heval_h Heval_t =>
      next σ₁ δ₁ =>
      simp [Block.noFuncDecl] at Hno
      have Hδ₁ : δ₁ = δ := EvalStmt_noFuncDecl_preserves_δ extendEval h δ δ₁ σ σ₁ .normal Hno.1 Heval_h
      have Hδ' : δ' = δ₁ := ih δ₁ δ' σ₁ σ' _ Hno.2 Heval_t
      simp [Hδ₁, Hδ']
    | stmts_exit_sem Heval_h =>
      simp [Block.noFuncDecl] at Hno
      exact EvalStmt_noFuncDecl_preserves_δ extendEval h δ δ' σ σ' _ Hno.1 Heval_h

/--
  The proof implementation for `StmtToNondetStmtCorrect` and
  `BlockToNondetStmtCorrect`.

  Since the definitions involve mutual recursion, `Nat.strongRecOn` is used to
  do induction on the size of the structure (see `StmtToNondetCorrect`). From
  experience, `mutual` theorems in Lean sometimes does not work well with
  implicit arguments, and it can be hard to find the cause from the generic
  error message similar to "(kernel) application type mismatch".

  The proof requires that the program contains no function declarations.
  When `noFuncDecl` holds, the evaluator `δ` is preserved (δ' = δ).

  Note: These theorems only apply to normal completion (br = .normal).
  Exit statements have no nondeterministic counterpart since the
  NondetStmt type does not model exit.
-/
theorem StmtToNondetCorrect
  [HasVal P] [HasFvar P] [HasBool P] [HasBoolVal P] [HasNot P] [DecidableEq P.Ident]
  (extendEval : ExtendEval P) :
  WellFormedSemanticEvalBool δ →
  WellFormedSemanticEvalVal δ →
  (∀ st,
    Stmt.sizeOf st ≤ m →
    Stmt.noFuncDecl st →
    EvalStmt P (Cmd P) (EvalCmd P) extendEval δ σ st σ' .normal δ →
    EvalNondetStmt P (Cmd P) (EvalCmd P) δ σ (StmtToNondetStmt st) σ') ∧
  (∀ ss,
    Block.sizeOf ss ≤ m →
    Block.noFuncDecl ss →
    EvalBlock P (Cmd P) (EvalCmd P) extendEval δ σ ss σ' .normal δ →
    EvalNondetStmt P (Cmd P) (EvalCmd P) δ σ (BlockToNondetStmt ss) σ') := by sorry

/-- Proof that the Deterministic-to-nondeterministic transformation is correct
for a single (deterministic) statement that contains no function declarations. -/
theorem StmtToNondetStmtCorrect
  [HasVal P] [HasFvar P] [HasBool P] [HasBoolVal P] [HasNot P] [DecidableEq P.Ident]
  (extendEval : ExtendEval P) :
  WellFormedSemanticEvalBool δ →
  WellFormedSemanticEvalVal δ →
  Stmt.noFuncDecl st →
  EvalStmt P (Cmd P) (EvalCmd P) extendEval δ σ st σ' .normal δ →
  EvalNondetStmt P (Cmd P) (EvalCmd P) δ σ (StmtToNondetStmt st) σ' := by sorry

/-- Proof that the Deterministic-to-nondeterministic transformation is correct
for multiple (deterministic) statements that contain no function declarations. -/
theorem BlockToNondetStmtCorrect
  [HasVal P] [HasFvar P] [HasBool P] [HasBoolVal P] [HasNot P] [DecidableEq P.Ident]
  (extendEval : ExtendEval P) :
  WellFormedSemanticEvalBool δ →
  WellFormedSemanticEvalVal δ →
  Block.noFuncDecl ss →
  EvalBlock P (Cmd P) (EvalCmd P) extendEval δ σ ss σ' .normal δ →
  EvalNondetStmt P (Cmd P) (EvalCmd P) δ σ (BlockToNondetStmt ss) σ' := by sorry

end
