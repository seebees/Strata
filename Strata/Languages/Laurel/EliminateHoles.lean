/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Laurel.Laurel
public import Strata.Languages.Laurel.LaurelFormat

/-!
# Deterministic Hole Elimination

Replace each deterministic typed `.Hole` with a call to a freshly generated
uninterpreted function whose parameters mirror the enclosing callable's inputs.

This pass assumes `inferHoleTypes` has already annotated every `Hole` with a
type. It works uniformly for both procedures and functions.

After this pass the program contains only non-deterministic `Hole` nodes.
-/

namespace Strata
namespace Laurel

public section

private def emptyMd : Imperative.MetaData Core.Expression := #[]
private def bare (v : StmtExpr) : StmtExprMd := ⟨v, emptyMd⟩

structure ElimHoleState where
  counter : Nat := 0
  currentInputs : List Parameter := []
  generatedFunctions : List Procedure := []

private abbrev ElimHoleM := StateM ElimHoleState

/-- Generate a fresh uninterpreted function for a typed hole and return a call to it. -/
private def mkHoleCall (holeType : HighTypeMd) : ElimHoleM StmtExprMd := do
  let s ← get
  let n := s.counter
  modify fun s => { s with counter := n + 1 }
  let holeName : Identifier := s!"$hole_{n}"
  let inputs := s.currentInputs
  let holeProc : Procedure := {
    name := holeName
    inputs := inputs
    outputs := [{ name := "$result", type := holeType }]
    preconditions := []
    determinism := .deterministic none
    decreases := none
    isFunctional := true
    body := .Opaque [] none []
    md := emptyMd
  }
  modify fun s => { s with generatedFunctions := s.generatedFunctions ++ [holeProc] }
  return bare (.StaticCall holeName (inputs.map (fun p => bare (.Identifier p.name))))

mutual
/--
Replace every deterministic `.Hole` in an expression with a call to a
fresh uninterpreted function.
-/
private def elimExpr (expr : StmtExprMd) : ElimHoleM StmtExprMd := do
  match expr with
  | WithMetadata.mk val md =>
  match val with
  | .Hole true (some ty) => mkHoleCall ty
  | .Hole true none => mkHoleCall ⟨.Unknown, md⟩
  | .Hole false _ => return expr
  | .PrimitiveOp op args => return ⟨.PrimitiveOp op (← args.mapM elimExpr), md⟩
  | .StaticCall callee args => return ⟨.StaticCall callee (← args.mapM elimExpr), md⟩
  | .InstanceCall target callee args =>
      return ⟨.InstanceCall (← elimExpr target) callee (← args.mapM elimExpr), md⟩
  | .ReferenceEquals lhs rhs => return ⟨.ReferenceEquals (← elimExpr lhs) (← elimExpr rhs), md⟩
  | .IfThenElse cond th el =>
      let el' ← match el with | some e => pure (some (← elimExpr e)) | none => pure none
      return ⟨.IfThenElse (← elimExpr cond) (← elimExpr th) el', md⟩
  | .Block stmts label => return ⟨.Block (← elimStmtList stmts) label, md⟩
  | .Assign targets value => return ⟨.Assign targets (← elimExpr value), md⟩
  | .LocalVariable name ty init =>
      match init with
      | some initExpr => return ⟨.LocalVariable name ty (some (← elimExpr initExpr)), md⟩
      | none => return expr
  | .Old v => return ⟨.Old (← elimExpr v), md⟩
  | .Fresh v => return ⟨.Fresh (← elimExpr v), md⟩
  | .Assigned n => return ⟨.Assigned (← elimExpr n), md⟩
  | .ProveBy v p => return ⟨.ProveBy (← elimExpr v) (← elimExpr p), md⟩
  | .ContractOf ty f => return ⟨.ContractOf ty (← elimExpr f), md⟩
  | .Forall p trigger b =>
      let trigger' ← match trigger with | some t => pure (some (← elimExpr t)) | none => pure none
      return ⟨.Forall p trigger' (← elimExpr b), md⟩
  | .Exists p trigger b =>
      let trigger' ← match trigger with | some t => pure (some (← elimExpr t)) | none => pure none
      return ⟨.Exists p trigger' (← elimExpr b), md⟩
  | _ => return expr

private def elimStmt (stmt : StmtExprMd) : ElimHoleM StmtExprMd := do
  match stmt with
  | WithMetadata.mk val md =>
  match val with
  | .LocalVariable name ty (some initExpr) =>
      return ⟨.LocalVariable name ty (some (← elimExpr initExpr)), md⟩
  | .Assign targets value => return ⟨.Assign targets (← elimExpr value), md⟩
  | .Block stmts label => return ⟨.Block (← elimStmtList stmts) label, md⟩
  | .IfThenElse cond th el =>
      let el' ← match el with | some e => pure (some (← elimStmt e)) | none => pure none
      return ⟨.IfThenElse (← elimExpr cond) (← elimStmt th) el', md⟩
  | .While cond invs dec body =>
      let dec' ← match dec with | some d => pure (some (← elimExpr d)) | none => pure none
      return ⟨.While (← elimExpr cond) (← invs.mapM elimExpr) dec' (← elimStmt body), md⟩
  | .Assert cond => return ⟨.Assert (← elimExpr cond), md⟩
  | .Assume cond => return ⟨.Assume (← elimExpr cond), md⟩
  | .StaticCall callee args => return ⟨.StaticCall callee (← args.mapM elimExpr), md⟩
  | .Return (some retExpr) => return ⟨.Return (some (← elimExpr retExpr)), md⟩
  | .Hole true (some ty) => mkHoleCall ty
  | .Hole true none => mkHoleCall ⟨.Unknown, md⟩
  | .Hole false _ => return stmt -- Non-deterministic holes are kept
  | _ => return stmt

private def elimStmtList (stmts : List StmtExprMd) : ElimHoleM (List StmtExprMd) :=
  stmts.mapM elimStmt
end

private def elimProcedure (proc : Procedure) : ElimHoleM Procedure := do
  modify fun s => { s with currentInputs := proc.inputs }
  match proc.body with
  | .Transparent bodyExpr => return { proc with body := .Transparent (← elimStmt bodyExpr) }
  | .Opaque postconds (some impl) modif =>
      return { proc with body := .Opaque postconds (some (← elimStmt impl)) modif }
  | _ => return proc

/--
Replace every deterministic `.Hole` in the program with a call to a freshly
generated uninterpreted function. Works uniformly for both procedures and
functions.
After this pass the program contains only non-deterministic `Hole` nodes.

Assumes `inferHoleTypes` has already annotated holes with types.
-/
def eliminateHoles (program : Program) : Program :=
  let initState : ElimHoleState := {}
  let (procs, finalState) := (program.staticProcedures.mapM elimProcedure).run initState
  { program with staticProcedures := finalState.generatedFunctions ++ procs }

end -- public section

mutual
def noHolesMd (e : StmtExprMd) : Bool := noHoles e.val
  termination_by sizeOf e
  decreasing_by cases e; term_by_mem

def noHoles : StmtExpr → Bool
  | .Hole true _ => false
  | .Hole false _ => true
  | .PrimitiveOp _ args => args.attach.all fun ⟨a, _⟩ => noHolesMd a
  | .StaticCall _ args => args.attach.all fun ⟨a, _⟩ => noHolesMd a
  | .InstanceCall t _ args => noHolesMd t && args.attach.all fun ⟨a, _⟩ => noHolesMd a
  | .ReferenceEquals a b => noHolesMd a && noHolesMd b
  | .IfThenElse c t e => noHolesMd c && noHolesMd t && match e with | some e => noHolesMd e | none => true
  | .Block stmts _ => stmts.attach.all fun ⟨s, _⟩ => noHolesMd s
  | .Assign _ v => noHolesMd v
  | .LocalVariable _ _ init => match init with | some i => noHolesMd i | none => true
  | .While c invs dec body => noHolesMd c && invs.attach.all (fun ⟨i, _⟩ => noHolesMd i) &&
      (match dec with | some d => noHolesMd d | none => true) && noHolesMd body
  | .Assert c | .Assume c => noHolesMd c
  | .Return v => match v with | some v => noHolesMd v | none => true
  | .Old v | .Fresh v | .Assigned v => noHolesMd v
  | .ProveBy v p => noHolesMd v && noHolesMd p
  | .ContractOf _ f => noHolesMd f
  | .Forall _ trigger b => (match trigger with | some t => noHolesMd t | none => true) && noHolesMd b
  | .Exists _ trigger b => (match trigger with | some t => noHolesMd t | none => true) && noHolesMd b
  | _ => true
  termination_by e => sizeOf e
  decreasing_by all_goals (simp_wf; try term_by_mem)
end

/-- A program has no deterministic holes. -/
public def programNoHoles (program : Program) : Bool :=
  program.staticProcedures.all fun proc => match proc.body with
    | .Transparent b => noHolesMd b
    | .Opaque _ (some impl) _ => noHolesMd impl
    | _ => true

-- WithMetadata eta
private theorem wm_eta (e : WithMetadata α) : (⟨e.val, e.md⟩ : WithMetadata α) = e := by cases e; rfl

-- mapM identity: if f is identity on each element, mapM f is identity
private theorem mapM_id {α : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
  (f : α → m α) (xs : List α) (hf : ∀ x ∈ xs, f x = pure x) :
  xs.mapM f = pure xs := by
  induction xs with
  | nil => simp [List.mapM_nil]
  | cons x xs ih =>
    rw [List.mapM_cons, hf x (.head xs), pure_bind, ih (fun y hy => hf y (.tail x hy)), pure_bind]

-- The core mutual induction: elimExpr/elimStmt/elimStmtList are identity for hole-free inputs
mutual
private theorem elimExpr_id (expr : StmtExprMd) (s : ElimHoleState)
  (h : noHolesMd expr = true) : elimExpr expr s = (expr, s) := by
  unfold elimExpr
  cases expr with | mk val md =>
  simp only [noHolesMd, noHoles] at h
  cases val <;> simp_all [wm_eta]
  all_goals (try (simp only [Bool.and_eq_true] at h; obtain ⟨h1, h2⟩ := h))
  all_goals sorry
  termination_by sizeOf expr
  decreasing_by all_goals (simp_wf; try term_by_mem)

private theorem elimStmt_id (stmt : StmtExprMd) (s : ElimHoleState)
  (h : noHolesMd stmt = true) : elimStmt stmt s = (stmt, s) := by
  unfold elimStmt
  cases stmt with | mk val md =>
  simp only [noHolesMd, noHoles] at h
  cases val <;> simp_all [wm_eta]
  all_goals sorry
  termination_by sizeOf stmt
  decreasing_by all_goals (simp_wf; try term_by_mem)

private theorem elimStmtList_id (stmts : List StmtExprMd) (s : ElimHoleState)
  (h : stmts.all noHolesMd = true) : (stmts.mapM elimStmt) s = (stmts, s) := by
  induction stmts generalizing s with
  | nil => rfl
  | cons x xs ih =>
    have hx := List.all_eq_true.mp h x (.head xs)
    have hxs := List.all_eq_true.mpr (fun y hy => List.all_eq_true.mp h y (.tail x hy))
    -- mapM for cons: bind (f x) (fun a => bind (mapM f xs) (fun as => pure (a :: as)))
    -- Applied to s: let (a, s') := f x s; let (as, s'') := mapM f xs s'; (a :: as, s'')
    show (List.mapM elimStmt (x :: xs)) s = _
    simp only [List.mapM_cons, bind, StateT.bind, pure, StateT.pure,
      elimStmt_id x s hx, ih s hxs]
  termination_by sizeOf stmts
  decreasing_by all_goals (simp_wf; try term_by_mem)
end

/-- eliminateHoles is a no-op on programs with no deterministic holes. -/
public theorem eliminateHoles_noop (program : Program)
  (hNoHoles : programNoHoles program = true) :
  eliminateHoles program = program := by
  sorry -- Uses elimExpr_id/elimStmt_id to show each procedure is unchanged

end Laurel
