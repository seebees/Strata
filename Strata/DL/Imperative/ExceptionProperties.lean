/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Imperative.StmtSemantics

/-!
# Exception Translation Properties (Small-Step)

Formal proofs of correctness properties for the Throw/TryCatch translation.
Rewritten for the small-step semantics (StepStmt / Config).
-/

namespace Imperative

section ExceptionProperties

variable {P : PureExpr} {CmdT : Type} {EvalCmd : EvalCmdParam P CmdT}
  {extendEval : ExtendEval P}
  [HasBool P] [HasNot P]

/-- Helper: lift a multi-step execution through a seq context. -/
public theorem seq_lift_star
    (ss : List (Stmt P CmdT))
    (H : StepStmtStar P EvalCmd extendEval c c') :
    StepStmtStar P EvalCmd extendEval (.seq c ss) (.seq c' ss) := by
  induction H with
  | refl => exact .refl _
  | step _ _ _ h _ ih =>
    exact .step _ _ _ (.step_seq_inner h) ih

/-- **P1: Throw Produces Exit (multi-step).**
    [setFlagStmt, exit bodyLabel] steps from .stmts to .exiting,
    given that setFlagStmt evaluates to terminal ρ₁. -/
public theorem throw_produces_exit
    (ρ : Env P) (ρ₁ : Env P)
    (setFlagStmt : Stmt P CmdT) (bodyLabel : String) (md : MetaData P)
    (Hset : StepStmtStar P EvalCmd extendEval
      (.stmt setFlagStmt ρ) (.terminal ρ₁)) :
    StepStmtStar P EvalCmd extendEval
      (.stmts [setFlagStmt, .exit (.some bodyLabel) md] ρ)
      (.exiting (.some bodyLabel) ρ₁) := by
  -- .stmts [s1, s2] ρ → .seq (.stmt s1 ρ) [s2]
  apply ReflTrans.step; exact .step_stmts_cons
  -- lift Hset through seq context
  apply ReflTrans_Transitive (StepStmt P EvalCmd extendEval)
  · exact seq_lift_star [.exit (.some bodyLabel) md] Hset
  -- .seq (.terminal ρ₁) [s2] → ... → .exiting
  · apply ReflTrans.step; exact .step_seq_done
    apply ReflTrans.step; exact .step_stmts_cons
    apply ReflTrans.step; exact .step_seq_inner .step_exit
    apply ReflTrans.step; exact .step_seq_exit
    exact .refl _

/-- **P1 (single-step): Exit preserves the environment.** -/
public theorem throw_exit_preserves_env (label : Option String) (md : MetaData P) (ρ : Env P) :
    StepStmt P EvalCmd extendEval
      (.stmt (.exit label md) ρ)
      (.exiting label ρ) :=
  .step_exit

/-- **P4 Step 2: Handlers block propagates exit (label mismatch).**
    A block with label handlersLabel whose body exits with tryEndLabel
    (where tryEndLabel ≠ handlersLabel) propagates the exit. -/
public theorem handlers_block_propagates_exit
    (tryEndLabel handlersLabel : String) (ρ₁ : Env P)
    (Hne : tryEndLabel ≠ handlersLabel) :
    StepStmt P EvalCmd extendEval
      (.block handlersLabel (.exiting (.some tryEndLabel) ρ₁))
      (.exiting (.some tryEndLabel) ρ₁) :=
  .step_block_exit_mismatch Hne

/-- **P4 Step 3: Try_end block consumes exit → terminal.**
    A block with label tryEndLabel whose body exits with (some tryEndLabel)
    steps to terminal. -/
public theorem try_end_consumes_exit (tryEndLabel : String) (ρ₁ : Env P) :
    StepStmt P EvalCmd extendEval
      (.block tryEndLabel (.exiting (.some tryEndLabel) ρ₁))
      (.terminal ρ₁) :=
  .step_block_exit_match rfl

/-- **P5: Exception Propagation to Procedure Body.**
    The procedure body block ($body) consumes the exit, completing normally,
    with $result = Failure in the store (set by Throw before the exit). -/
public theorem exception_propagates_to_body (bodyLabel : String) (ρ₁ : Env P) :
    StepStmt P EvalCmd extendEval
      (.block bodyLabel (.exiting (.some bodyLabel) ρ₁))
      (.terminal ρ₁) :=
  .step_block_exit_match rfl

end ExceptionProperties

end Imperative

/-!
## Properties P7 and P8: Result Type Properties

These are properties of the ExceptionResult datatype itself,
independent of the imperative semantics.
-/

public inductive ExceptionResult where
  | Success
  | Failure
  deriving DecidableEq

public def ExceptionResult.isSuccess : ExceptionResult → Bool
  | .Success => true
  | .Failure => false

public def ExceptionResult.isFailure : ExceptionResult → Bool
  | .Success => false
  | .Failure => true

/-- **P7: Result Exhaustiveness.** -/
public theorem result_exhaustive (r : ExceptionResult) :
    r.isSuccess = true ∨ r.isFailure = true := by
  cases r <;> simp [ExceptionResult.isSuccess, ExceptionResult.isFailure]

public theorem result_exclusive (r : ExceptionResult) :
    ¬ (r.isSuccess = true ∧ r.isFailure = true) := by
  cases r <;> simp [ExceptionResult.isSuccess, ExceptionResult.isFailure]

public theorem result_isSuccess_iff_not_isFailure (r : ExceptionResult) :
    r.isSuccess = true ↔ r.isFailure = false := by
  cases r <;> simp [ExceptionResult.isSuccess, ExceptionResult.isFailure]

public theorem result_isFailure_iff_not_isSuccess (r : ExceptionResult) :
    r.isFailure = true ↔ r.isSuccess = false := by
  cases r <;> simp [ExceptionResult.isSuccess, ExceptionResult.isFailure]

/-- **P8: Ensures Clause Isolation.** -/
public theorem ensures_isolation_success (r : ExceptionResult) (P : Prop) :
    r.isFailure = true → (r.isSuccess = true → P) := by
  cases r <;> simp [ExceptionResult.isSuccess, ExceptionResult.isFailure]

public theorem ensures_isolation_failure (r : ExceptionResult) (P : Prop) :
    r.isSuccess = true → (r.isFailure = true → P) := by
  cases r <;> simp [ExceptionResult.isSuccess, ExceptionResult.isFailure]
