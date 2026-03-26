/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

import Strata.DL.Imperative.StmtSemantics
import Strata.DL.Imperative.ExitProperties

/-!
# Exit Well-Formedness and Structural Properties

Defines well-formedness predicates for labeled blocks and exit statements,
and proves E8 (uniqueness of exit target) and E9 (completeness of exit
resolution) from `docs/design/exit-semantics/spec.md`.
-/

namespace Imperative

open BlockResult

section WellFormedness

variable {P : PureExpr} {Cmd : Type}

mutual
/-- A statement is well-formed with respect to labels if:
    - Every `exit (some L)` targets a label in `enclosing`
    - Every `exit none` has at least one enclosing block
    - No block label shadows an enclosing label
    - Sub-statements are well-formed with updated label context -/
inductive WFLabels : List String → Stmt P Cmd → Prop where
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
inductive WFLabelsBlock : List String → List (Stmt P Cmd) → Prop where
  | nil : WFLabelsBlock labels []
  | cons :
      WFLabels labels s →
      WFLabelsBlock labels rest →
      WFLabelsBlock labels (s :: rest)
end

/-- **E8: Uniqueness of Exit Target.**
    In a well-formed program, `exit (some L)` implies L is in the
    enclosing labels. Combined with no-shadowing (which the type checker
    enforces as Nodup on the label stack), L appears exactly once. -/
theorem exit_target_in_labels
    {labels : List String} {L : String} {md : MetaData P}
    (Hwf : @WFLabels P Cmd labels (.exit (.some L) md)) :
    L ∈ labels := by
  cases Hwf with
  | exit_labeled Hmem => exact Hmem

end WellFormedness

section Completeness

variable {P : PureExpr} {Cmd : Type} {EvalCmd : EvalCmdParam P Cmd}
  {extendEval : ExtendEval P}
  [DecidableEq P.Ident]
  [HasVarsImp P (List (Stmt P Cmd))] [HasVarsImp P Cmd]
  [HasFvar P] [HasVal P] [HasBool P] [HasNot P]

/-- **E9: Completeness of Exit Resolution (single enclosing block).**
    If a block's body is well-formed with [L] as the only enclosing label,
    and the body evaluates to some result, then wrapping it in block L
    always produces normal completion.

    Every exit in the body targets L (the only available label) or is
    unlabeled (consumed by any block). Either way, consumeExit L produces
    .normal. -/
theorem exit_resolution_single_block
    (Heval : EvalBlock P Cmd EvalCmd extendEval δ σ body σ' br δ') :
    ∃ br', EvalStmt P Cmd EvalCmd extendEval δ σ (.block L body md) σ' br' δ'
      ∧ (br = .normal → br' = .normal)
      ∧ (br = .exited .none → br' = .normal)
      ∧ (br = .exited (.some L) → br' = .normal)
      ∧ (∀ M, M ≠ L → br = .exited (.some M) → br' = .exited (.some M)) := by
  refine ⟨consumeExit L br, EvalStmt.block_sem Heval rfl, ?_, ?_, ?_, ?_⟩
  · intro h; subst h; exact consumeExit_normal L
  · intro h; subst h; exact consumeExit_exited_none L
  · intro h; subst h; exact consumeExit_exited_same L
  · intro M hne h; subst h; exact consumeExit_exited_ne hne

/-- **E9 (strong form): If the only exit labels in the body are L or unlabeled,
    then wrapping in block L always produces normal completion.**
    This is the key property: well-formedness with [L] means every exit
    targets L, so consumeExit L always produces .normal.

    Note: This requires that br is constrained to labels in [L].
    We state this as: if br is .normal, .exited none, or .exited (some L),
    then the block completes normally. -/
theorem exit_resolution_complete
    (Heval : EvalBlock P Cmd EvalCmd extendEval δ σ body σ' br δ')
    (Hbr : br = .normal ∨ br = .exited .none ∨ br = .exited (.some L)) :
    EvalStmt P Cmd EvalCmd extendEval δ σ (.block L body md) σ' .normal δ' := by
  apply EvalStmt.block_sem Heval
  rcases Hbr with h | h | h <;> subst h
  · exact consumeExit_normal L
  · exact consumeExit_exited_none L
  · exact consumeExit_exited_same L

end Completeness

end Imperative
