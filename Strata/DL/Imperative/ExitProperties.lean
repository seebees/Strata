/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Imperative.StmtSemantics

/-!
# Exit Semantics Properties (Small-Step)

Formal proofs of the correctness properties for exit and labeled blocks.
Rewritten for the small-step semantics (StepStmt / Config).
-/

namespace Imperative

section ExitProperties

variable {P : PureExpr} {CmdT : Type} {EvalCmd : EvalCmdParam P CmdT}
  {extendEval : ExtendEval P}
  [HasBool P] [HasNot P]

/-- **E1: Exit Preserves Store.**
    An exit statement steps to .exiting with the same environment. -/
public theorem exit_preserves_env (label : Option String) (md : MetaData P) (ρ : Env P) :
    StepStmt P EvalCmd extendEval
      (.stmt (.exit label md) ρ)
      (.exiting label ρ) :=
  .step_exit

/-- **E2: Exit Skips Remaining Statements.**
    When a seq's inner config exits, the remaining statements are skipped. -/
public theorem exit_skips_remaining (label : Option String) (ρ' : Env P)
    (ss : List (Stmt P CmdT)) :
    StepStmt P EvalCmd extendEval
      (.seq (.exiting label ρ') ss)
      (.exiting label ρ') :=
  .step_seq_exit

/-- **E3: Matching Block Consumes Exit.**
    A block with label L whose body exits with (some L) steps to terminal. -/
public theorem matching_block_consumes (L : String) (ρ' : Env P) :
    StepStmt P EvalCmd extendEval
      (.block L (.exiting (.some L) ρ'))
      (.terminal ρ') :=
  .step_block_exit_match rfl

/-- **E4: Non-Matching Exit Propagates.**
    A block with label L whose body exits with (some M) where M ≠ L
    propagates the exit unchanged. -/
public theorem nonmatching_exit_propagates (L M : String) (ρ' : Env P)
    (Hne : M ≠ L) :
    StepStmt P EvalCmd extendEval
      (.block L (.exiting (.some M) ρ'))
      (.exiting (.some M) ρ') :=
  .step_block_exit_mismatch Hne

/-- **E5: Normal Block Completion.**
    If a block's body reaches terminal, the block reaches terminal. -/
public theorem normal_block_completion (L : String) (ρ' : Env P) :
    StepStmt P EvalCmd extendEval
      (.block L (.terminal ρ'))
      (.terminal ρ') :=
  .step_block_done

/-- **E6: Unlabeled Exit Consumed by Any Block.**
    A block whose body exits with none steps to terminal. -/
public theorem unlabeled_exit_consumed (L : String) (ρ' : Env P) :
    StepStmt P EvalCmd extendEval
      (.block L (.exiting .none ρ'))
      (.terminal ρ') :=
  .step_block_exit_none

/-- **E7: Block Body Steps Forward.**
    A block context propagates inner steps. -/
public theorem block_body_steps (L : String)
    (inner inner' : Config P CmdT)
    (H : StepStmt P EvalCmd extendEval inner inner') :
    StepStmt P EvalCmd extendEval
      (.block L inner)
      (.block L inner') :=
  .step_block_body H

/-- **E8: Empty Statement List Terminates.**
    An empty list of statements steps to terminal immediately. -/
public theorem empty_stmts_terminal (ρ : Env P) :
    StepStmt P EvalCmd extendEval
      (.stmts ([] : List (Stmt P CmdT)) ρ)
      (.terminal ρ) :=
  .step_stmts_nil

/-- **E9: Exit statement evaluates to exiting (multi-step).**
    .stmt (.exit label md) ρ →* .exiting label ρ -/
public theorem exit_eval (label : Option String) (md : MetaData P) (ρ : Env P) :
    StepStmtStar P EvalCmd extendEval
      (.stmt (.exit label md) ρ)
      (.exiting label ρ) :=
  .step _ _ _ .step_exit (.refl _)

/-- **E10: Matching block with exiting body evaluates to terminal (multi-step).**
    .block L (.exiting (some L) ρ') →* .terminal ρ' -/
public theorem matching_block_eval (L : String) (ρ' : Env P) :
    StepStmtStar P EvalCmd extendEval
      (.block L (.exiting (.some L) ρ'))
      (.terminal ρ') :=
  .step _ _ _ (.step_block_exit_match rfl) (.refl _)

end ExitProperties

end Imperative
