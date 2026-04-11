/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Imperative.StmtSemantics
public import Strata.DL.Imperative.ExitProperties

/-!
# Exit Well-Formedness and Structural Properties (Small-Step)

Defines well-formedness predicates for labeled blocks and exit statements,
and proves E8 (uniqueness of exit target) from
`docs/design/exit-semantics/spec.md`.
-/

namespace Imperative

section WellFormedness

variable {P : PureExpr} {CmdT : Type}

mutual
/-- A statement is well-formed with respect to labels if:
    - Every `exit (some L)` targets a label in `enclosing`
    - Every `exit none` has at least one enclosing block
    - No block label shadows an enclosing label
    - Sub-statements are well-formed with updated label context -/
inductive WFLabels : List String → Stmt P CmdT → Prop where
  | cmd : WFLabels labels (.cmd c)
  | block :
      label ∉ labels →
      WFLabelsBlock (label :: labels) body →
      WFLabels labels (.block label body md)
  | ite :
      WFLabelsBlock labels thenBranch →
      WFLabelsBlock labels elseBranch →
      WFLabels labels (.ite c thenBranch elseBranch md)
  | exit_labeled :
      l ∈ labels →
      WFLabels labels (.exit (.some l) md)
  | exit_unlabeled :
      labels ≠ [] →
      WFLabels labels (.exit .none md)
  | loop :
      WFLabelsBlock labels body →
      WFLabels labels (.loop g m i body md)
  | funcDecl : WFLabels labels (.funcDecl d md)
  | typeDecl : WFLabels labels (.typeDecl t md)

/-- A block (list of statements) is well-formed if every statement is. -/
inductive WFLabelsBlock : List String → List (Stmt P CmdT) → Prop where
  | nil : WFLabelsBlock labels []
  | cons :
      WFLabels labels s →
      WFLabelsBlock labels rest →
      WFLabelsBlock labels (s :: rest)
end

/-- **E8: Uniqueness of Exit Target.**
    In a well-formed program, `exit (some L)` implies L is in the
    enclosing labels. -/
theorem exit_target_in_labels
    {labels : List String} {L : String} {md : MetaData P}
    (Hwf : @WFLabels P CmdT labels (.exit (.some L) md)) :
    L ∈ labels := by
  cases Hwf with
  | exit_labeled Hmem => exact Hmem

end WellFormedness

section Completeness

variable {P : PureExpr} {CmdT : Type} {EvalCmd : EvalCmdParam P CmdT}
  {extendEval : ExtendEval P}
  [HasBool P] [HasNot P]

/-- **E9: Exit Resolution — Matching Exit Consumed.**
    If a block's body reaches .exiting (some L) and the block has label L,
    the block steps to terminal. -/
public theorem exit_resolution_matching (L : String) (ρ' : Env P) :
    StepStmt P EvalCmd extendEval
      (.block L (.exiting (.some L) ρ'))
      (.terminal ρ') :=
  .step_block_exit_match rfl

/-- **E9: Exit Resolution — Unlabeled Exit Consumed.**
    If a block's body reaches .exiting none, any block consumes it. -/
public theorem exit_resolution_unlabeled (L : String) (ρ' : Env P) :
    StepStmt P EvalCmd extendEval
      (.block L (.exiting .none ρ'))
      (.terminal ρ') :=
  .step_block_exit_none

/-- **E9: Exit Resolution — Normal Completion.**
    If a block's body reaches terminal, the block reaches terminal. -/
public theorem exit_resolution_normal (L : String) (ρ' : Env P) :
    StepStmt P EvalCmd extendEval
      (.block L (.terminal ρ'))
      (.terminal ρ') :=
  .step_block_done

end Completeness

end Imperative
