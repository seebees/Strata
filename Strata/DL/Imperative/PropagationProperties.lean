/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Imperative.StmtSemantics
public import Strata.DL.Imperative.ExceptionProperties

/-!
# Cross-Method Propagation Properties (Small-Step)

Formal proofs of correctness properties for cross-method exception
propagation. Rewritten for the small-step semantics (StepStmt / Config).

The key insight: the propagation check exits to `$handlers` (the try
body's label), which the block consumes, allowing the catch dispatch
to run. This is Decision 7 in the design decisions.
-/

namespace Imperative

section PropagationProperties

variable {P : PureExpr} {CmdT : Type} {EvalCmd : EvalCmdParam P CmdT}
  {extendEval : ExtendEval P}
  [HasBool P] [HasNot P]

/-- **P9: Cross-Method Propagation Into Try.**
    If a propagation check exits to handlersLabel, the handlers block
    consumes the matching exit and steps to terminal. The catch dispatch
    after it can then run. -/
public theorem propagation_exits_to_handlers (handlersLabel : String) (ρ₁ : Env P) :
    StepStmt P EvalCmd extendEval
      (.block handlersLabel (.exiting (.some handlersLabel) ρ₁))
      (.terminal ρ₁) :=
  .step_block_exit_match rfl

/-- **P10: Cross-Method Propagation Outside Try.**
    If a propagation check exits to bodyLabel (outside any try block),
    the procedure body block consumes it. Same as P5. -/
public theorem propagation_outside_try_exits_body (bodyLabel : String) (ρ₁ : Env P) :
    StepStmt P EvalCmd extendEval
      (.block bodyLabel (.exiting (.some bodyLabel) ρ₁))
      (.terminal ρ₁) :=
  .step_block_exit_match rfl

/-- **P11: Nested Try — Inner Block Consumes First.**
    If the inner handlers block has a matching exit, it consumes it
    and steps to terminal. The outer block sees terminal (not exiting),
    so it also steps to terminal via step_block_done. -/
public theorem nested_try_inner_consumes
    (innerLabel outerLabel : String) (ρ₁ : Env P) :
    StepStmt P EvalCmd extendEval
      (.block outerLabel (.block innerLabel (.exiting (.some innerLabel) ρ₁)))
      (.block outerLabel (.terminal ρ₁)) :=
  .step_block_body (.step_block_exit_match rfl)

/-- **P12: Non-Matching Exit Propagates Through Blocks.**
    If the inner exit doesn't match the inner block's label, it propagates
    to the outer block. -/
public theorem nonmatching_propagates_through
    (innerLabel outerLabel exitLabel : String) (ρ₁ : Env P)
    (Hne : exitLabel ≠ innerLabel) :
    StepStmt P EvalCmd extendEval
      (.block innerLabel (.exiting (.some exitLabel) ρ₁))
      (.exiting (.some exitLabel) ρ₁) :=
  .step_block_exit_mismatch Hne

end PropagationProperties

end Imperative
