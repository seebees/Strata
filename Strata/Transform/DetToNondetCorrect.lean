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
  (ss : Block P (Cmd P)) (δ δ' : SemanticEval P) (σ σ' : SemanticStore P)
  (ih : ∀ s, s ∈ ss → ∀ (δ δ' : SemanticEval P) (σ σ' : SemanticStore P),
    Stmt.noFuncDecl s → EvalStmt P (Cmd P) (EvalCmd P) extendEval δ σ s σ' _br1 δ' → δ' = δ)
  (Hno : Block.noFuncDecl ss)
  (Heval : EvalBlock P (Cmd P) (EvalCmd P) extendEval δ σ ss σ' _br2 δ') :
  δ' = δ := by sorry

/-- When a statement has no function declarations, evaluating it preserves the evaluator. -/
theorem EvalStmt_noFuncDecl_preserves_δ
  [HasVal P] [HasFvar P] [HasBool P] [HasNot P] [DecidableEq P.Ident]
  (extendEval : ExtendEval P)
  (st : Stmt P (Cmd P)) (δ δ' : SemanticEval P) (σ σ' : SemanticStore P) :
  Stmt.noFuncDecl st →
  EvalStmt P (Cmd P) (EvalCmd P) extendEval δ σ st σ' _br3 δ' →
  δ' = δ := by sorry

/-- When a block has no function declarations, evaluating it preserves the evaluator. -/
theorem EvalBlock_noFuncDecl_preserves_δ
  [HasVal P] [HasFvar P] [HasBool P] [HasNot P] [DecidableEq P.Ident]
  (extendEval : ExtendEval P)
  (ss : Block P (Cmd P)) (δ δ' : SemanticEval P) (σ σ' : SemanticStore P) :
  Block.noFuncDecl ss →
  EvalBlock P (Cmd P) (EvalCmd P) extendEval δ σ ss σ' _br4 δ' →
  δ' = δ := by sorry

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
-/
theorem StmtToNondetCorrect
  [HasVal P] [HasFvar P] [HasBool P] [HasBoolVal P] [HasNot P] [DecidableEq P.Ident]
  (extendEval : ExtendEval P) :
  WellFormedSemanticEvalBool δ →
  WellFormedSemanticEvalVal δ →
  (∀ st,
    Stmt.sizeOf st ≤ m →
    Stmt.noFuncDecl st →
    EvalStmt P (Cmd P) (EvalCmd P) extendEval δ σ st σ' _br5 δ →
    EvalNondetStmt P (Cmd P) (EvalCmd P) δ σ (StmtToNondetStmt st) σ') ∧
  (∀ ss,
    Block.sizeOf ss ≤ m →
    Block.noFuncDecl ss →
    EvalBlock P (Cmd P) (EvalCmd P) extendEval δ σ ss σ' _br6 δ →
    EvalNondetStmt P (Cmd P) (EvalCmd P) δ σ (BlockToNondetStmt ss) σ') := by sorry

/-- Proof that the Deterministic-to-nondeterministic transformation is correct
for a single (deterministic) statement that contains no function declarations. -/
theorem StmtToNondetStmtCorrect
  [HasVal P] [HasFvar P] [HasBool P] [HasBoolVal P] [HasNot P] [DecidableEq P.Ident]
  (extendEval : ExtendEval P) :
  WellFormedSemanticEvalBool δ →
  WellFormedSemanticEvalVal δ →
  Stmt.noFuncDecl st →
  EvalStmt P (Cmd P) (EvalCmd P) extendEval δ σ st σ' _br5 δ →
  EvalNondetStmt P (Cmd P) (EvalCmd P) δ σ (StmtToNondetStmt st) σ' := by sorry

/-- Proof that the Deterministic-to-nondeterministic transformation is correct
for multiple (deterministic) statements that contain no function declarations. -/
theorem BlockToNondetStmtCorrect
  [HasVal P] [HasFvar P] [HasBool P] [HasBoolVal P] [HasNot P] [DecidableEq P.Ident]
  (extendEval : ExtendEval P) :
  WellFormedSemanticEvalBool δ →
  WellFormedSemanticEvalVal δ →
  Block.noFuncDecl ss →
  EvalBlock P (Cmd P) (EvalCmd P) extendEval δ σ ss σ' _br6 δ →
  EvalNondetStmt P (Cmd P) (EvalCmd P) δ σ (BlockToNondetStmt ss) σ' := by sorry

end
