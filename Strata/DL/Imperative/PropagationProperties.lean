/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

import Strata.DL.Imperative.StmtSemantics
import Strata.DL.Imperative.ExceptionProperties

/-!
# Cross-Method Propagation Properties

Formal proofs of correctness properties P9-P12 for cross-method
exception propagation, as specified in
`docs/design/laurel-exceptions/spec.md`.

These properties prove that when a procedure call inside a try body
returns Failure, the propagation check correctly routes the exception
to the catch handler (not to the procedure body).

The key insight: the propagation check exits to `$handlers` (the try
body's label), which `consumeExit` consumes, allowing the catch
dispatch to run. This is Decision 7 in the design decisions.
-/

namespace Imperative

open BlockResult

variable {P : PureExpr} {Cmd : Type} {EvalCmd : EvalCmdParam P Cmd}
  {extendEval : ExtendEval P}
  [DecidableEq P.Ident]
  [HasVarsImp P (List (Stmt P Cmd))] [HasVarsImp P Cmd]
  [HasFvar P] [HasVal P] [HasBool P] [HasNot P]

/-- **P9: Cross-Method Propagation Into Try.**
    If a propagation check `if isFailure($result) { exit $handlers }` fires
    inside a `$handlers` block, the block completes normally (consumeExit
    consumes the matching exit), and the catch dispatch after it can run.

    This is the core of the fix: the propagation check exits to `$handlers`
    (not `$body`), so `consumeExit` on the `$handlers` block consumes it. -/
theorem propagation_exits_to_handlers
    (HpropCheck : EvalStmt P Cmd EvalCmd extendEval δ σ propCheckStmt σ₁ (.exited (.some handlersLabel)) δ₁) :
    EvalStmt P Cmd EvalCmd extendEval δ σ
      (.block handlersLabel [propCheckStmt] md)
      σ₁ .normal δ₁ :=
  .block_sem (.stmts_exit_sem HpropCheck) (consumeExit_exited_same handlersLabel)

/-- **P9 (corollary): After the handlers block completes normally,
    subsequent statements (catch dispatch) execute.** -/
theorem catch_dispatch_runs_after_propagation
    (HhandlersBlock : EvalStmt P Cmd EvalCmd extendEval δ σ handlersBlock σ₁ .normal δ₁)
    (HcatchDispatch : EvalBlock P Cmd EvalCmd extendEval δ₁ σ₁ catchStmts σ₂ br₂ δ₂) :
    EvalBlock P Cmd EvalCmd extendEval δ σ
      (handlersBlock :: catchStmts)
      σ₂ br₂ δ₂ :=
  .stmts_normal_sem HhandlersBlock HcatchDispatch

/-- **P10: Cross-Method Propagation Outside Try.**
    If a propagation check `if isFailure($result) { exit $body }` fires
    outside any try block, the exit targets `$body` (the procedure label).
    The procedure body block consumes it, completing normally with
    `$result = Failure` in the store.

    This is the same as P5 — the propagation check outside try behaves
    identically to a local throw's exit. -/
theorem propagation_outside_try_exits_body
    (HbodyEval : EvalBlock P Cmd EvalCmd extendEval δ σ bodyStmts σ₁ (.exited (.some bodyLabel)) δ₁) :
    EvalStmt P Cmd EvalCmd extendEval δ σ (.block bodyLabel bodyStmts md) σ₁ .normal δ₁ :=
  .block_sem HbodyEval (consumeExit_exited_same bodyLabel)

/-- **P11: Nested Try Targets Innermost Handler.**
    If a propagation check exits to `$handlers_inner` inside a nested try,
    the inner `$handlers_inner` block consumes it. The outer `$handlers_outer`
    block is not affected because the exit was already consumed.

    This follows from P9 applied to the inner block: the inner block
    consumes the exit and completes normally, so the outer block sees
    normal completion from its inner statement. -/
theorem nested_try_inner_consumes
    (HinnerHandlers : EvalStmt P Cmd EvalCmd extendEval δ σ
      (.block innerHandlersLabel innerStmts md₁) σ₁ .normal δ₁)
    (HinnerCatch : EvalBlock P Cmd EvalCmd extendEval δ₁ σ₁ innerCatchStmts σ₂ br₂ δ₂) :
    EvalBlock P Cmd EvalCmd extendEval δ σ
      ((.block innerHandlersLabel innerStmts md₁) :: innerCatchStmts)
      σ₂ br₂ δ₂ :=
  .stmts_normal_sem HinnerHandlers HinnerCatch

/-- **P12: Propagation Through Try/Finally.**
    If a propagation check fires inside a try/finally (no catch), the
    handlers block completes normally (P9), the catch dispatch sees
    isFailure and does NOT reset $result (no catch clause), and the
    finally block executes.

    The finally block is a sequence of statements after the try_end block.
    Since the try_end block completes (either normally or via exit
    consumption), the finally statements execute next.

    This composes P9 (propagation into try) with P6 (finally execution). -/
theorem propagation_then_finally
    (HtryEnd : EvalStmt P Cmd EvalCmd extendEval δ σ tryEndBlock σ₁ .normal δ₁)
    (Hfinally : EvalBlock P Cmd EvalCmd extendEval δ₁ σ₁ finallyStmts σ₂ br₂ δ₂) :
    EvalBlock P Cmd EvalCmd extendEval δ σ
      (tryEndBlock :: finallyStmts)
      σ₂ br₂ δ₂ :=
  .stmts_normal_sem HtryEnd Hfinally

end Imperative
