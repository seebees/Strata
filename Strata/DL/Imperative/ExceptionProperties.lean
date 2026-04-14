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

These are properties of the Result<T> algebraic datatype (spec §1.1),
independent of the imperative semantics.

The Core-level `Result<T>` is defined as an `LDatatype` in
`CoreDefinitionsForLaurel.lean` with constructors `Success(value: T)`
and `Failure()`. The TypeFactory generates testers, destructors, and
eliminators automatically.

These Lean-level proofs mirror the Core-level properties and serve as
the foundation for composing with the translator proofs (Arrow 2 + Arrow 3).
-/

/-- Result<T>: a method either succeeds with a value or fails. -/
public inductive Result (T : Type) where
  | Success (value : T)
  | Failure
  deriving DecidableEq

public def Result.isSuccess : Result T → Bool
  | .Success _ => true
  | .Failure => false

public def Result.isFailure : Result T → Bool
  | .Success _ => false
  | .Failure => true

/-- Extract the value from a Success result. Partial — undefined on Failure. -/
public def Result.value! [Inhabited T] : Result T → T
  | .Success v => v
  | .Failure => default

/-- **P7: Result Exhaustiveness.** Every Result is either Success or Failure. -/
public theorem result_exhaustive (r : Result T) :
    r.isSuccess = true ∨ r.isFailure = true := by
  cases r <;> simp [Result.isSuccess, Result.isFailure]

/-- **P7b: Result Exclusivity.** A Result cannot be both Success and Failure. -/
public theorem result_exclusive (r : Result T) :
    ¬ (r.isSuccess = true ∧ r.isFailure = true) := by
  cases r <;> simp [Result.isSuccess, Result.isFailure]

/-- isSuccess ↔ ¬isFailure -/
public theorem result_isSuccess_iff_not_isFailure (r : Result T) :
    r.isSuccess = true ↔ r.isFailure = false := by
  cases r <;> simp [Result.isSuccess, Result.isFailure]

/-- isFailure ↔ ¬isSuccess -/
public theorem result_isFailure_iff_not_isSuccess (r : Result T) :
    r.isFailure = true ↔ r.isSuccess = false := by
  cases r <;> simp [Result.isSuccess, Result.isFailure]

/-- **P7c: Constructor Disjointness.** Success and Failure are distinct. -/
public theorem result_success_ne_failure (v : T) :
    Result.Success v ≠ Result.Failure := by
  intro h; cases h

/-- **P7d: Value Extraction.** Extracting the value from Success recovers the original. -/
public theorem result_value_of_success [Inhabited T] (v : T) :
    (Result.Success v).value! = v := by
  simp [Result.value!]

/-- **P7e: Constructor Injectivity.** Success is injective on its value. -/
public theorem result_success_injective (v₁ v₂ : T) :
    Result.Success v₁ = Result.Success v₂ → v₁ = v₂ := by
  intro h; cases h; rfl

/-- **P7f: isSuccess characterization.** isSuccess is true iff the result is Success. -/
public theorem result_isSuccess_iff (r : Result T) :
    r.isSuccess = true ↔ ∃ v, r = .Success v := by
  cases r with
  | Success v => simp [Result.isSuccess]
  | Failure => simp [Result.isSuccess]

/-- **P7g: isFailure characterization.** isFailure is true iff the result is Failure. -/
public theorem result_isFailure_iff (r : Result T) :
    r.isFailure = true ↔ r = .Failure := by
  cases r with
  | Success _ => simp [Result.isFailure]
  | Failure => simp [Result.isFailure]

/-- **P8: Ensures Clause Isolation (Success).** If r is Failure, any Success-guarded
    postcondition holds vacuously. -/
public theorem ensures_isolation_success (r : Result T) (P : Prop) :
    r.isFailure = true → (r.isSuccess = true → P) := by
  cases r <;> simp [Result.isSuccess, Result.isFailure]

/-- **P8b: Ensures Clause Isolation (Failure).** If r is Success, any Failure-guarded
    postcondition holds vacuously. -/
public theorem ensures_isolation_failure (r : Result T) (P : Prop) :
    r.isSuccess = true → (r.isFailure = true → P) := by
  cases r <;> simp [Result.isSuccess, Result.isFailure]
