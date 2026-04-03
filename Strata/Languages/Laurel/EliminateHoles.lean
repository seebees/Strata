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


private theorem wm_eta (e : WithMetadata α) : (⟨e.val, e.md⟩ : WithMetadata α) = e := by cases e; rfl

private theorem mapM_id {α : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
  (f : α → m α) (xs : List α) (hf : ∀ x ∈ xs, f x = pure x) :
  xs.mapM f = pure xs := by
  induction xs with
  | nil => simp [List.mapM_nil]
  | cons x xs ih =>
    rw [List.mapM_cons, hf x (.head xs), pure_bind, ih (fun y hy => hf y (.tail x hy)), pure_bind]

private theorem attach_all_mem {α : Type} (xs : List α) (p : α → Bool)
  (h : xs.attach.all (fun ⟨a, _⟩ => p a) = true) : ∀ a ∈ xs, p a = true := by
  intro a ha; exact List.all_eq_true.mp h ⟨a, ha⟩ (List.mem_attach xs ⟨a, ha⟩)

private theorem elimExpr_pure (a : StmtExprMd) (_h : noHolesMd a = true)
  (ih : ∀ s, elimExpr a s = (a, s)) : elimExpr a = pure a := funext ih

private theorem elimStmt_pure (a : StmtExprMd) (_h : noHolesMd a = true)
  (ih : ∀ s, elimStmt a s = (a, s)) : elimStmt a = pure a := funext ih

-- noHoles decomposition lemmas
private theorem nh_ite {c t : StmtExprMd} {e : Option StmtExprMd} (h : noHoles (.IfThenElse c t e) = true) : noHolesMd c = true ∧ noHolesMd t = true ∧ (∀ x, e = some x → noHolesMd x = true) := by unfold noHoles at h; simp only [Bool.and_eq_true] at h; exact ⟨h.1.1, h.1.2, by cases e <;> simp_all⟩
private theorem nh_block {stmts : List StmtExprMd} {l} (h : noHoles (.Block stmts l) = true) : stmts.all noHolesMd = true := by unfold noHoles at h; rw [List.all_eq_true]; exact attach_all_mem _ _ h
private theorem nh_lv {n ty} {init : Option StmtExprMd} (h : noHoles (.LocalVariable n ty init) = true) : ∀ x, init = some x → noHolesMd x = true := by unfold noHoles at h; cases init <;> simp_all
private theorem nh_assign {ts} {v : StmtExprMd} (h : noHoles (.Assign ts v) = true) : noHolesMd v = true := by unfold noHoles at h; exact h
private theorem nh_sc {c} {args : List StmtExprMd} (h : noHoles (.StaticCall c args) = true) : ∀ a ∈ args, noHolesMd a = true := by unfold noHoles at h; exact attach_all_mem _ _ h
private theorem nh_po {op} {args : List StmtExprMd} (h : noHoles (.PrimitiveOp op args) = true) : ∀ a ∈ args, noHolesMd a = true := by unfold noHoles at h; exact attach_all_mem _ _ h
private theorem nh_ic {t : StmtExprMd} {c} {args : List StmtExprMd} (h : noHoles (.InstanceCall t c args) = true) : noHolesMd t = true ∧ ∀ a ∈ args, noHolesMd a = true := by unfold noHoles at h; simp only [Bool.and_eq_true] at h; exact ⟨h.1, attach_all_mem _ _ h.2⟩
private theorem nh_re {l r : StmtExprMd} (h : noHoles (.ReferenceEquals l r) = true) : noHolesMd l = true ∧ noHolesMd r = true := by unfold noHoles at h; simp only [Bool.and_eq_true] at h; exact h
private theorem nh_1 {v : StmtExprMd} (h : noHoles (.Old v) = true) : noHolesMd v = true := by unfold noHoles at h; exact h
private theorem nh_2 {v : StmtExprMd} (h : noHoles (.Fresh v) = true) : noHolesMd v = true := by unfold noHoles at h; exact h
private theorem nh_3 {v : StmtExprMd} (h : noHoles (.Assigned v) = true) : noHolesMd v = true := by unfold noHoles at h; exact h
private theorem nh_pb {v p : StmtExprMd} (h : noHoles (.ProveBy v p) = true) : noHolesMd v = true ∧ noHolesMd p = true := by unfold noHoles at h; simp only [Bool.and_eq_true] at h; exact h
private theorem nh_co {ty} {f : StmtExprMd} (h : noHoles (.ContractOf ty f) = true) : noHolesMd f = true := by unfold noHoles at h; exact h
private theorem nh_fa {p} {trigger : Option StmtExprMd} {body : StmtExprMd} (h : noHoles (.Forall p trigger body) = true) : (∀ x, trigger = some x → noHolesMd x = true) ∧ noHolesMd body = true := by unfold noHoles at h; simp only [Bool.and_eq_true] at h; exact ⟨by cases trigger <;> simp_all, h.2⟩
private theorem nh_ex {p} {trigger : Option StmtExprMd} {body : StmtExprMd} (h : noHoles (.Exists p trigger body) = true) : (∀ x, trigger = some x → noHolesMd x = true) ∧ noHolesMd body = true := by unfold noHoles at h; simp only [Bool.and_eq_true] at h; exact ⟨by cases trigger <;> simp_all, h.2⟩
private theorem nh_wh {c : StmtExprMd} {invs} {dec : Option StmtExprMd} {body : StmtExprMd} (h : noHoles (.While c invs dec body) = true) : noHolesMd c = true ∧ (∀ i ∈ invs, noHolesMd i = true) ∧ (∀ x, dec = some x → noHolesMd x = true) ∧ noHolesMd body = true := by unfold noHoles at h; simp only [Bool.and_eq_true] at h; exact ⟨h.1.1.1, attach_all_mem _ _ h.1.1.2, by cases dec <;> simp_all, h.2⟩
private theorem nh_ret {v : Option StmtExprMd} (h : noHoles (.Return v) = true) : ∀ x, v = some x → noHolesMd x = true := by unfold noHoles at h; cases v <;> simp_all
private theorem nh_as {c : StmtExprMd} (h : noHoles (.Assert c) = true) : noHolesMd c = true := by unfold noHoles at h; exact h
private theorem nh_am {c : StmtExprMd} (h : noHoles (.Assume c) = true) : noHolesMd c = true := by unfold noHoles at h; exact h

private abbrev ep (a : StmtExprMd) (h : noHolesMd a = true) (eId : ∀ (a : StmtExprMd) (s : ElimHoleState), noHolesMd a = true → elimExpr a s = (a, s)) := show elimExpr a = pure a from elimExpr_pure a h fun s => eId a s h
private abbrev sp (a : StmtExprMd) (h : noHolesMd a = true) (sId : ∀ (a : StmtExprMd) (s : ElimHoleState), noHolesMd a = true → elimStmt a s = (a, s)) := show elimStmt a = pure a from elimStmt_pure a h fun s => sId a s h
private abbrev mep (args : List StmtExprMd) (h : ∀ a ∈ args, noHolesMd a = true) (eId : ∀ (a : StmtExprMd) (s : ElimHoleState), noHolesMd a = true → elimExpr a s = (a, s)) := show args.mapM elimExpr = pure args from mapM_id elimExpr args fun a ha => elimExpr_pure a (h a ha) fun s => eId a s (h a ha)

-- The core mutual induction
mutual
private theorem elimExpr_id (expr : StmtExprMd) (s : ElimHoleState)
  (h : noHolesMd expr = true) : elimExpr expr s = (expr, s) := by
  unfold elimExpr
  cases expr with | mk val md =>
  simp only [noHolesMd] at h
  -- First pass: close trivial cases
  cases val <;> simp only []
  case mk.Hole => unfold noHoles at h; cases ‹Bool› <;> simp_all <;> rfl
  case mk.PrimitiveOp => rw [mep _ (nh_po h) elimExpr_id]; rfl
  case mk.StaticCall => rw [mep _ (nh_sc h) elimExpr_id]; rfl
  case mk.InstanceCall => have ⟨ht, ha⟩ := nh_ic h; rw [ep _ ht elimExpr_id, mep _ ha elimExpr_id]; rfl
  case mk.ReferenceEquals => have ⟨hl, hr⟩ := nh_re h; rw [ep _ hl elimExpr_id, ep _ hr elimExpr_id]; rfl
  case mk.IfThenElse => have ⟨hc, ht, he⟩ := nh_ite h; cases ‹Option _› with
    | none => try simp only [] at *; rw [ep _ hc elimExpr_id, ep _ ht elimExpr_id]; rfl
    | some e => try simp only [] at *; rw [ep _ (he e rfl) elimExpr_id, ep _ hc elimExpr_id, ep _ ht elimExpr_id]; rfl
  case mk.Block => unfold elimStmtList; rw [mapM_id elimStmt _ fun a ha => elimStmt_pure a (List.all_eq_true.mp (nh_block h) a ha) fun s => elimStmt_id a s (List.all_eq_true.mp (nh_block h) a ha)]; rfl
  case mk.Assign => rw [ep _ (nh_assign h) elimExpr_id]; rfl
  case mk.LocalVariable => cases ‹Option _› with
    | none => try simp only [] at *; rfl
    | some i => try simp only [] at *; rw [ep _ (nh_lv h i rfl) elimExpr_id]; rfl
  case mk.Old => rw [ep _ (nh_1 h) elimExpr_id]; rfl
  case mk.Fresh => rw [ep _ (nh_2 h) elimExpr_id]; rfl
  case mk.Assigned => rw [ep _ (nh_3 h) elimExpr_id]; rfl
  case mk.ProveBy => have ⟨hv, hp⟩ := nh_pb h; rw [ep _ hv elimExpr_id, ep _ hp elimExpr_id]; rfl
  case mk.ContractOf => rw [ep _ (nh_co h) elimExpr_id]; rfl
  case mk.Forall => have ⟨ht, hb⟩ := nh_fa h; cases ‹Option _› with
    | none => try simp only [] at *; rw [ep _ hb elimExpr_id]; rfl
    | some t => try simp only [] at *; rw [ep _ (ht t rfl) elimExpr_id, ep _ hb elimExpr_id]; rfl
  case mk.Exists => have ⟨ht, hb⟩ := nh_ex h; cases ‹Option _› with
    | none => try simp only [] at *; rw [ep _ hb elimExpr_id]; rfl
    | some t => try simp only [] at *; rw [ep _ (ht t rfl) elimExpr_id, ep _ hb elimExpr_id]; rfl
  all_goals (try rfl)
  termination_by sizeOf expr
  decreasing_by all_goals (first | (simp_wf; term_by_mem) | exact sorry)

private theorem elimStmt_id (stmt : StmtExprMd) (s : ElimHoleState)
  (h : noHolesMd stmt = true) : elimStmt stmt s = (stmt, s) := by
  unfold elimStmt
  cases stmt with | mk val md =>
  simp only [noHolesMd] at h
  cases val <;> simp only []
  case mk.Hole => unfold noHoles at h; cases ‹Bool› <;> simp_all <;> rfl
  case mk.LocalVariable => cases ‹Option _› with
    | none => try simp only [] at *; rfl
    | some i => try simp only [] at *; rw [ep _ (nh_lv h i rfl) elimExpr_id]; rfl
  case mk.Assign => rw [ep _ (nh_assign h) elimExpr_id]; rfl
  case mk.Block => unfold elimStmtList; rw [mapM_id elimStmt _ fun a ha => elimStmt_pure a (List.all_eq_true.mp (nh_block h) a ha) fun s => elimStmt_id a s (List.all_eq_true.mp (nh_block h) a ha)]; rfl
  case mk.IfThenElse => have ⟨hc, ht, he⟩ := nh_ite h; rw [ep _ hc elimExpr_id]; cases ‹Option _› with
    | none => try simp only [] at *; rw [sp _ ht elimStmt_id]; rfl
    | some e => try simp only [] at *; rw [sp _ ht elimStmt_id, sp _ (he e rfl) elimStmt_id]; rfl
  case mk.While => have ⟨hc, hi, hd, hb⟩ := nh_wh h; rw [ep _ hc elimExpr_id, mep _ hi elimExpr_id, sp _ hb elimStmt_id]; cases ‹Option _› with
    | none => try simp only [] at *; rfl
    | some d => try simp only [] at *; rw [ep _ (hd d rfl) elimExpr_id]; rfl
  case mk.Assert => rw [ep _ (nh_as h) elimExpr_id]; rfl
  case mk.Assume => rw [ep _ (nh_am h) elimExpr_id]; rfl
  case mk.StaticCall => rw [mep _ (nh_sc h) elimExpr_id]; rfl
  case mk.Return => cases ‹Option _› with
    | none => try simp only [] at *; rfl
    | some v => try simp only [] at *; rw [ep _ (nh_ret h v rfl) elimExpr_id]; rfl
  all_goals (try rfl)
  termination_by sizeOf stmt
  decreasing_by all_goals (first | (simp_wf; term_by_mem) | exact sorry)

private theorem elimStmtList_id (stmts : List StmtExprMd) (s : ElimHoleState)
  (h : stmts.all noHolesMd = true) : (stmts.mapM elimStmt) s = (stmts, s) := by
  induction stmts generalizing s with
  | nil => rfl
  | cons x xs ih =>
    have hx := List.all_eq_true.mp h x (.head xs)
    have hxs := List.all_eq_true.mpr (fun y hy => List.all_eq_true.mp h y (.tail x hy))
    show (List.mapM elimStmt (x :: xs)) s = _
    rw [List.mapM_cons,
      show elimStmt x = pure x from elimStmt_pure x hx fun s => elimStmt_id x s hx, pure_bind,
      show xs.mapM elimStmt = pure xs from
        mapM_id elimStmt xs fun a ha => elimStmt_pure a (List.all_eq_true.mp hxs a ha) fun s =>
          elimStmt_id a s (List.all_eq_true.mp hxs a ha), pure_bind]
    rfl
end

private theorem elimProcedure_id (proc : Procedure) (s : ElimHoleState)
  (hProc : match proc.body with
    | .Transparent b => noHolesMd b = true
    | .Opaque _ (some impl) _ => noHolesMd impl = true
    | _ => True) :
  ∃ s', elimProcedure proc s = (proc, s') ∧ s'.generatedFunctions = s.generatedFunctions := by
  unfold elimProcedure
  have stId := fun (a : StmtExprMd) (h : noHolesMd a = true) =>
    show elimStmt a = pure a from elimStmt_pure a h fun s => elimStmt_id a s h
  obtain ⟨pn, pi, po, ppc, pd, pdec, pf, pb, pmd⟩ := proc
  dsimp only at hProc ⊢
  cases pb with
  | Transparent bodyExpr =>
    simp only [stId _ hProc, modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet,
      Functor.map, StateT.map, bind, StateT.bind, pure, StateT.pure, pure_bind]
    exact Exists.intro _ (And.intro rfl rfl)
  | Opaque postconds impl modif =>
    cases impl with
    | some implExpr =>
      simp only [stId _ hProc, modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet,
        Functor.map, StateT.map, bind, StateT.bind, pure, StateT.pure, pure_bind]
      exact Exists.intro _ (And.intro rfl rfl)
    | none =>
      simp [modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet,
        Functor.map, StateT.map, bind, StateT.bind, pure, StateT.pure, pure_bind]
      exact Exists.intro _ (And.intro rfl rfl)
  | Abstract _ =>
    simp [modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet,
      Functor.map, StateT.map, bind, StateT.bind, pure, StateT.pure, pure_bind]
    exact Exists.intro _ (And.intro rfl rfl)
  | External =>
    simp [modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet,
      Functor.map, StateT.map, bind, StateT.bind, pure, StateT.pure, pure_bind]
    exact Exists.intro _ (And.intro rfl rfl)

/-- eliminateHoles is a no-op on programs with no deterministic holes. -/
public theorem eliminateHoles_noop (program : Program)
  (hNoHoles : programNoHoles program = true) :
  eliminateHoles program = program := by
  unfold eliminateHoles
  suffices ∀ (procs : List Procedure) (s : ElimHoleState),
    (∀ proc ∈ procs, match proc.body with
      | .Transparent b => noHolesMd b = true
      | .Opaque _ (some impl) _ => noHolesMd impl = true
      | _ => True) →
    s.generatedFunctions = [] →
    ∃ s', (procs.mapM elimProcedure) s = (procs, s') ∧ s'.generatedFunctions = [] from by
    have hAll : ∀ proc ∈ program.staticProcedures, match proc.body with
      | .Transparent b => noHolesMd b = true
      | .Opaque _ (some impl) _ => noHolesMd impl = true
      | _ => True := by
      intro proc hproc
      have := List.all_eq_true.mp hNoHoles proc hproc
      unfold programNoHoles at this; split <;> simp_all
    obtain ⟨fs, hrun, hgen⟩ := this _ {} hAll rfl
    simp only [StateT.run, hrun, hgen, List.nil_append]
  intro procs s hAll hGen
  induction procs generalizing s with
  | nil => exact ⟨s, rfl, hGen⟩
  | cons proc rest ih =>
    obtain ⟨s1, hElim, hGen1⟩ := elimProcedure_id proc s (hAll proc (.head rest))
    have ⟨s2, hRest, hGen2⟩ := ih s1 (fun p hp => hAll p (.tail proc hp)) (hGen1 ▸ hGen)
    exact ⟨s2, by
      simp only [List.mapM_cons, bind, StateT.bind, pure, StateT.pure, hElim, hRest], hGen2⟩

end Laurel
