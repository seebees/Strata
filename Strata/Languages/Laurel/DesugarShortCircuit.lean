/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Laurel.Laurel
public import Strata.Languages.Laurel.LiftImperativeExpressions
import Strata.Util.Tactics

/-!
# Desugar Short-Circuit Operators

Rewrites `AndThen`, `OrElse`, and `Implies` to `IfThenElse` when the second
operand contains imperative calls (assignments or non-functional procedure calls).
This must run before `LiftImperativeExpressions` to prevent the lifter from
hoisting imperative calls out of the short-circuited branch.

Pure operands pass through unchanged and are handled by the Core translator.
-/

namespace Strata.Laurel

public section

private def bare (v : StmtExpr) : StmtExprMd := ⟨v, default⟩

/-- Desugar short-circuit operators to IfThenElse when the second operand is imperative. -/
def desugarShortCircuitExpr (model : SemanticModel) (expr : StmtExprMd) : StmtExprMd :=
  let md := expr.md
  match expr with
  | WithMetadata.mk val _ =>
  match val with
  | .PrimitiveOp op args =>
    let args' := args.attach.map fun ⟨a, _⟩ => desugarShortCircuitExpr model a
    match op, args with
    | .AndThen, [_, b] | .Implies, [_, b] =>
      if containsAssignmentOrImperativeCall model b then
        let elseVal := match op with | .AndThen => false | _ => true
        ⟨.IfThenElse args'[0]! args'[1]! (some (bare (.LiteralBool elseVal))), md⟩
      else ⟨.PrimitiveOp op args', md⟩
    | .OrElse, [_, b] =>
      if containsAssignmentOrImperativeCall model b then
        ⟨.IfThenElse args'[0]! (bare (.LiteralBool true)) (some args'[1]!), md⟩
      else ⟨.PrimitiveOp op args', md⟩
    | _, _ => ⟨.PrimitiveOp op args', md⟩
  | .IfThenElse cond th el =>
    ⟨.IfThenElse (desugarShortCircuitExpr model cond) (desugarShortCircuitExpr model th)
      (match el with | some e => some (desugarShortCircuitExpr model e) | none => none), md⟩
  | .Block stmts label =>
    ⟨.Block (stmts.attach.map fun ⟨s, _⟩ => desugarShortCircuitExpr model s) label, md⟩
  | .While c invs dec body =>
    ⟨.While (desugarShortCircuitExpr model c)
      (invs.attach.map fun ⟨i, _⟩ => desugarShortCircuitExpr model i)
      (match dec with | some d => some (desugarShortCircuitExpr model d) | none => none)
      (desugarShortCircuitExpr model body), md⟩
  | .LocalVariable name ty init =>
    ⟨.LocalVariable name ty (match init with | some i => some (desugarShortCircuitExpr model i) | none => none), md⟩
  | .Assign targets value =>
    ⟨.Assign (targets.attach.map fun ⟨t, _⟩ => desugarShortCircuitExpr model t) (desugarShortCircuitExpr model value), md⟩
  | .StaticCall callee args =>
    ⟨.StaticCall callee (args.attach.map fun ⟨a, _⟩ => desugarShortCircuitExpr model a), md⟩
  | .Return v =>
    ⟨.Return (match v with | some v' => some (desugarShortCircuitExpr model v') | none => none), md⟩
  | _ => expr
termination_by expr
decreasing_by all_goals ((try cases x); simp_all; try term_by_mem)

private def desugarShortCircuitProcedure (model : SemanticModel) (proc : Procedure) : Procedure :=
  { proc with body := match proc.body with
    | .Transparent b => .Transparent (desugarShortCircuitExpr model b)
    | .Opaque posts impl mods => .Opaque (posts.map (desugarShortCircuitExpr model)) (impl.map (desugarShortCircuitExpr model)) mods
    | other => other }

/-- Desugar short-circuit operators in a program. -/
def desugarShortCircuit (model : SemanticModel) (program : Program) : Program :=
  { program with staticProcedures := program.staticProcedures.map (desugarShortCircuitProcedure model) }

end -- public section

/-! ## No-op proof -/

private theorem attach_map_id' (l : List StmtExprMd) (f : StmtExprMd → StmtExprMd)
    (hf : ∀ a ∈ l, f a = a) : l.attach.map (fun ⟨a, _⟩ => f a) = l := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.attach_cons, List.map_cons, List.map_map, Function.comp]
    rw [hf x (.head xs)]; congr 1
    simp only [Function.comp] at *; exact ih (fun a ha => hf a (.tail x ha))

private theorem attach_all_imp' {l : List StmtExprMd} {p : StmtExprMd → Bool}
    (h : l.attach.all (fun ⟨a, _⟩ => p a) = true) {a : StmtExprMd} (ha : a ∈ l) :
    p a = true := List.all_eq_true.mp h ⟨a, ha⟩ (List.mem_attach l ⟨a, ha⟩)

private theorem bl {a b : Bool} (h : (a && b) = true) : a = true := by cases a <;> simp_all
private theorem br {a b : Bool} (h : (a && b) = true) : b = true := by cases a <;> simp_all

private theorem map_id_of_all' {α : Type} (l : List α) (f : α → α)
    (hf : ∀ a ∈ l, f a = a) : l.map f = l := by
  induction l with
  | nil => rfl
  | cons x xs ih => simp [hf x (.head xs), ih (fun a ha => hf a (.tail x ha))]

public def pureShortCircuits (model : SemanticModel) (expr : StmtExprMd) : Bool :=
  match expr with | WithMetadata.mk val _ => match val with
  | .PrimitiveOp op args =>
    args.attach.all (fun ⟨a, _⟩ => pureShortCircuits model a) &&
    (match op, args with
    | .AndThen, [_, b] | .Implies, [_, b] | .OrElse, [_, b] =>
      !containsAssignmentOrImperativeCall model b
    | _, _ => true)
  | .IfThenElse c t e => pureShortCircuits model c && pureShortCircuits model t &&
    (match e with | some e' => pureShortCircuits model e' | none => true)
  | .Block stmts _ => stmts.attach.all (fun ⟨a, _⟩ => pureShortCircuits model a)
  | .While c invs dec body => pureShortCircuits model c &&
    invs.attach.all (fun ⟨a, _⟩ => pureShortCircuits model a) &&
    (match dec with | some d => pureShortCircuits model d | none => true) &&
    pureShortCircuits model body
  | .LocalVariable _ _ init => match init with | some i => pureShortCircuits model i | none => true
  | .Assign targets value =>
    targets.attach.all (fun ⟨a, _⟩ => pureShortCircuits model a) && pureShortCircuits model value
  | .StaticCall _ args => args.attach.all (fun ⟨a, _⟩ => pureShortCircuits model a)
  | .Return (some v) => pureShortCircuits model v
  | _ => true
  termination_by expr
  decreasing_by all_goals ((try cases x); simp_all; try term_by_mem)

public theorem desugarShortCircuitExpr_id (model : SemanticModel) (expr : StmtExprMd)
    (h : pureShortCircuits model expr = true) :
    desugarShortCircuitExpr model expr = expr := by
  unfold desugarShortCircuitExpr
  match expr, h with
  | ⟨.PrimitiveOp op args, md⟩, h =>
    unfold pureShortCircuits at h
    have ih : ∀ a ∈ args, desugarShortCircuitExpr model a = a :=
      fun a ha => desugarShortCircuitExpr_id model a (attach_all_imp' (bl h) ha)
    simp only [attach_map_id' args _ ih]
    match op, args, br h with
    | .AndThen, [_, b], hsc => simp [Bool.not_eq_true'] at hsc; simp [hsc]
    | .Implies, [_, b], hsc => simp [Bool.not_eq_true'] at hsc; simp [hsc]
    | .OrElse, [_, b], hsc => simp [Bool.not_eq_true'] at hsc; simp [hsc]
    | .Eq, _, _ | .Neq, _, _ | .And, _, _ | .Or, _, _ | .Not, _, _
    | .Neg, _, _ | .Add, _, _ | .Sub, _, _ | .Mul, _, _ | .Div, _, _
    | .Mod, _, _ | .DivT, _, _ | .ModT, _, _ | .Lt, _, _ | .Leq, _, _
    | .Gt, _, _ | .Geq, _, _ | .StrConcat, _, _ => rfl
    | .AndThen, [], _ | .AndThen, [_], _ | .AndThen, _ :: _ :: _ :: _, _ => rfl
    | .Implies, [], _ | .Implies, [_], _ | .Implies, _ :: _ :: _ :: _, _ => rfl
    | .OrElse, [], _ | .OrElse, [_], _ | .OrElse, _ :: _ :: _ :: _, _ => rfl
  | ⟨.IfThenElse c t e, md⟩, h =>
    unfold pureShortCircuits at h
    simp only [desugarShortCircuitExpr_id _ c (bl (bl h)), desugarShortCircuitExpr_id _ t (br (bl h))]
    cases e with | none => rfl | some e' => simp [desugarShortCircuitExpr_id _ e' (br h)]
  | ⟨.Block stmts label, md⟩, h =>
    unfold pureShortCircuits at h
    simp only [attach_map_id' stmts _ (fun a ha => desugarShortCircuitExpr_id _ a (attach_all_imp' h ha))]
  | ⟨.While c invs dec body, md⟩, h =>
    unfold pureShortCircuits at h
    simp only [desugarShortCircuitExpr_id _ c (bl (bl (bl h))),
      attach_map_id' invs _ (fun a ha => desugarShortCircuitExpr_id _ a (attach_all_imp' (br (bl (bl h))) ha)),
      desugarShortCircuitExpr_id _ body (br h)]
    cases dec with | none => rfl | some d => simp [desugarShortCircuitExpr_id _ d (br (bl h))]
  | ⟨.LocalVariable _ _ init, md⟩, h =>
    unfold pureShortCircuits at h
    cases init with | none => rfl | some i => simp [desugarShortCircuitExpr_id _ i h]
  | ⟨.Assign targets value, md⟩, h =>
    unfold pureShortCircuits at h
    simp only [attach_map_id' targets _ (fun a ha => desugarShortCircuitExpr_id _ a (attach_all_imp' (bl h) ha)),
      desugarShortCircuitExpr_id _ value (br h)]
  | ⟨.StaticCall _ args, md⟩, h =>
    unfold pureShortCircuits at h
    simp only [attach_map_id' args _ (fun a ha => desugarShortCircuitExpr_id _ a (attach_all_imp' h ha))]
  | ⟨.Return v, md⟩, h =>
    unfold pureShortCircuits at h
    cases v with | none => rfl | some v' => simp [desugarShortCircuitExpr_id _ v' h]
  | ⟨.LiteralBool _, _⟩, _ | ⟨.LiteralInt _, _⟩, _ | ⟨.LiteralString _, _⟩, _
  | ⟨.LiteralDecimal _, _⟩, _ | ⟨.Identifier _, _⟩, _
  | ⟨.FieldSelect _ _, _⟩, _ | ⟨.PureFieldUpdate _ _ _, _⟩, _
  | ⟨.New _, _⟩, _ | ⟨.This, _⟩, _ | ⟨.ReferenceEquals _ _, _⟩, _
  | ⟨.AsType _ _, _⟩, _ | ⟨.IsType _ _, _⟩, _ | ⟨.InstanceCall _ _ _, _⟩, _
  | ⟨.Forall _ _ _, _⟩, _ | ⟨.Exists _ _ _, _⟩, _
  | ⟨.Assigned _, _⟩, _ | ⟨.Old _, _⟩, _ | ⟨.Fresh _, _⟩, _
  | ⟨.Assert _, _⟩, _ | ⟨.Assume _, _⟩, _ | ⟨.ProveBy _ _, _⟩, _
  | ⟨.ContractOf _ _, _⟩, _ | ⟨.Abstract, _⟩, _ | ⟨.All, _⟩, _
  | ⟨.Hole _ _, _⟩, _ | ⟨.Throw _, _⟩, _ | ⟨.TryCatch _ _ _, _⟩, _
  | ⟨.Exit _, _⟩, _ => rfl
  termination_by expr
  decreasing_by all_goals ((try cases x); simp_all; try term_by_mem)

public theorem desugarShortCircuit_noop (model : SemanticModel) (program : Program)
    (h : ∀ proc ∈ program.staticProcedures,
      match proc.body with
      | .Transparent b => pureShortCircuits model b = true
      | .Opaque posts impl _ =>
        posts.all (pureShortCircuits model) = true ∧
        (match impl with | some i => pureShortCircuits model i = true | none => True)
      | _ => True) :
    desugarShortCircuit model program = program := by
  unfold desugarShortCircuit
  suffices program.staticProcedures.map (desugarShortCircuitProcedure model) =
    program.staticProcedures by cases program; simp_all
  apply map_id_of_all'; intro proc hp; have hproc := h proc hp
  show desugarShortCircuitProcedure model proc = proc
  unfold desugarShortCircuitProcedure
  cases hb : proc.body with
  | Transparent b =>
    simp only [hb] at hproc
    show { proc with body := .Transparent (desugarShortCircuitExpr model b) } = proc
    rw [desugarShortCircuitExpr_id model b hproc, show Body.Transparent b = proc.body from hb.symm]
    cases proc; rfl
  | Opaque posts impl mods =>
    simp only [hb] at hproc; obtain ⟨hposts, himpl⟩ := hproc
    show { proc with body := .Opaque (posts.map _) (impl.map _) mods } = proc
    rw [map_id_of_all' _ _ (fun a ha => desugarShortCircuitExpr_id model a (List.all_eq_true.mp hposts a ha))]
    rw [show impl.map (desugarShortCircuitExpr model) = impl from by
      cases impl with | none => rfl | some i => exact congrArg some (desugarShortCircuitExpr_id model i himpl)]
    rw [show Body.Opaque posts impl mods = proc.body from hb.symm]; cases proc; rfl
  | Abstract _ => cases proc; simp_all
  | External => cases proc; simp_all

end Strata.Laurel

