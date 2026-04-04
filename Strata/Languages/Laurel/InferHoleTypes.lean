/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Laurel.Laurel
public import Strata.Languages.Laurel.LaurelFormat
public import Strata.Languages.Laurel.LaurelTypes
public import Strata.Languages.Laurel.EliminateHoles
public import Strata.Languages.Laurel.EliminateHoles
public import Strata.Languages.Laurel.EliminateHoles

/-!
# Hole Type Inference

Annotate each `.Hole` node with a type inferred from its surrounding context
using the `SemanticModel` and `computeExprType`. After this pass every `Hole`
carries `some ty` so that the hole elimination pass can generate correctly
typed uninterpreted functions.
-/

namespace Strata
namespace Laurel

public section

private def bareType (v : HighType) : HighTypeMd := ⟨v, (#[] : Imperative.MetaData Core.Expression)⟩
private def defaultHoleType : HighTypeMd := bareType .Unknown

/-- Compute the expected type for an argument of a comparison operator
    by looking at the first non-hole sibling. -/
private def inferComparisonArgType (model : SemanticModel) (args : List StmtExprMd) : HighTypeMd :=
  args.findSome? (fun a => match a.val with | .Hole _ _ => none | _ => some (computeExprType model a))
    |>.getD defaultHoleType

/-- Get the expected type for each argument of a call from the callee's parameter list. -/
private def calleeParamTypes (model : SemanticModel) (callee : Identifier) : Option (List HighTypeMd) :=
  match model.get callee with
  | .staticProcedure proc => some (proc.inputs.map (·.type))
  | _ => none

structure InferHoleState where
  model : SemanticModel
  currentOutputType : HighTypeMd := ⟨.Unknown, #[]⟩

private abbrev InferHoleM := StateM InferHoleState

mutual
private def inferArgs (args : List StmtExprMd) (expectedType : HighTypeMd) : InferHoleM (List StmtExprMd) :=
  args.mapM (inferExpr · expectedType)

private def inferArgsTyped (args : List StmtExprMd) (types : List HighTypeMd) : InferHoleM (List StmtExprMd) := do
  let mut result : List StmtExprMd := []
  let mut i := 0
  for a in args do
    result := result ++ [← inferExpr a (types.getD i defaultHoleType)]
    i := i + 1
  return result

/-- Annotate every `.Hole` in an expression with its contextual type. -/
private def inferExpr (expr : StmtExprMd) (expectedType : HighTypeMd) : InferHoleM StmtExprMd := do
  let model := (← get).model
  match expr with
  | WithMetadata.mk val md =>
  match val with
  | .Hole det _ => return ⟨.Hole det (some expectedType), md⟩
  | .PrimitiveOp op args =>
      let argType := match op with
        | .Eq | .Neq | .Lt | .Leq | .Gt | .Geq => inferComparisonArgType model args
        | _ =>
          -- Use computeExprType on the whole expression to get the result type,
          -- which equals the argument type for arithmetic/logic/string ops.
          -- Fall back to expectedType if computeExprType can't determine it
          -- (e.g. when the first arg is a Hole).
          let computed := computeExprType model expr
          match computed.val with
          | .TCore _ | .Unknown => expectedType
          | _ => computed
      return ⟨.PrimitiveOp op (← inferArgs args argType), md⟩
  | .StaticCall callee args =>
      let args' ← match calleeParamTypes model callee with
        | some paramTypes => inferArgsTyped args paramTypes
        | none => inferArgs args defaultHoleType
      return ⟨.StaticCall callee args', md⟩
  | .InstanceCall target callee args =>
      return ⟨.InstanceCall (← inferExpr target defaultHoleType) callee (← inferArgs args defaultHoleType), md⟩
  | .ReferenceEquals lhs rhs =>
      return ⟨.ReferenceEquals (← inferExpr lhs defaultHoleType) (← inferExpr rhs defaultHoleType), md⟩
  | .IfThenElse cond th el =>
      let el' ← match el with
        | some e => pure (some (← inferExpr e expectedType))
        | none => pure none
      return ⟨.IfThenElse (← inferExpr cond (bareType .TBool)) (← inferExpr th expectedType) el', md⟩
  | .Block stmts label => return ⟨.Block (← inferStmtList stmts) label, md⟩
  | .Assign targets value => return ⟨.Assign targets (← inferExpr value defaultHoleType), md⟩
  | .LocalVariable name ty init =>
      match init with
      | some initExpr => return ⟨.LocalVariable name ty (some (← inferExpr initExpr ty)), md⟩
      | none => return expr
  | .Old v => return ⟨.Old (← inferExpr v expectedType), md⟩
  | .Fresh v => return ⟨.Fresh (← inferExpr v defaultHoleType), md⟩
  | .Assigned n => return ⟨.Assigned (← inferExpr n defaultHoleType), md⟩
  | .ProveBy v p => return ⟨.ProveBy (← inferExpr v expectedType) (← inferExpr p defaultHoleType), md⟩
  | .ContractOf ty f => return ⟨.ContractOf ty (← inferExpr f defaultHoleType), md⟩
  | .Forall p trigger b =>
      let trigger' ← match trigger with
        | some t => pure (some (← inferExpr t defaultHoleType))
        | none => pure none
      return ⟨.Forall p trigger' (← inferExpr b (bareType .TBool)), md⟩
  | .Exists p trigger b =>
      let trigger' ← match trigger with
        | some t => pure (some (← inferExpr t defaultHoleType))
        | none => pure none
      return ⟨.Exists p trigger' (← inferExpr b (bareType .TBool)), md⟩
  | _ => return expr

private def inferStmt (stmt : StmtExprMd) : InferHoleM StmtExprMd := do
  let model := (← get).model
  match stmt with
  | WithMetadata.mk val md =>
  match val with
  | .LocalVariable name ty (some initExpr) =>
      return ⟨.LocalVariable name ty (some (← inferExpr initExpr ty)), md⟩
  | .Assign targets value => return ⟨.Assign targets (← inferExpr value defaultHoleType), md⟩
  | .Block stmts label => return ⟨.Block (← inferStmtList stmts) label, md⟩
  | .IfThenElse cond th el =>
      let el' ← match el with
        | some e => pure (some (← inferStmt e))
        | none => pure none
      return ⟨.IfThenElse (← inferExpr cond (bareType .TBool)) (← inferStmt th) el', md⟩
  | .While cond invs dec body =>
      let dec' ← match dec with
        | some d => pure (some (← inferExpr d (bareType .TInt)))
        | none => pure none
      return ⟨.While (← inferExpr cond (bareType .TBool)) (← invs.mapM (inferExpr · (bareType .TBool))) dec' (← inferStmt body), md⟩
  | .Assert cond => return ⟨.Assert (← inferExpr cond (bareType .TBool)), md⟩
  | .Assume cond => return ⟨.Assume (← inferExpr cond (bareType .TBool)), md⟩
  | .StaticCall callee args =>
      let args' ← match calleeParamTypes model callee with
        | some paramTypes => inferArgsTyped args paramTypes
        | none => inferArgs args defaultHoleType
      return ⟨.StaticCall callee args', md⟩
  | .Return (some retExpr) =>
      return ⟨.Return (some (← inferExpr retExpr (← get).currentOutputType)), md⟩
  | .Hole det _ => return ⟨.Hole det (some (← get).currentOutputType), md⟩
  | _ => return stmt

private def inferStmtList (stmts : List StmtExprMd) : InferHoleM (List StmtExprMd) :=
  stmts.mapM inferStmt
end

private def inferProcedure (proc : Procedure) : InferHoleM Procedure := do
  let outputType := match proc.outputs with
    | [single] => single.type
    | _ => defaultHoleType
  modify fun s => { s with currentOutputType := outputType }
  match proc.body with
  | .Transparent bodyExpr => return { proc with body := .Transparent (← inferStmt bodyExpr) }
  | .Opaque postconds (some impl) modif =>
      return { proc with body := .Opaque postconds (some (← inferStmt impl)) modif }
  | _ => return proc

/--
Annotate every `.Hole` in the program with a type inferred from context.
-/
def inferHoleTypes (model : SemanticModel) (program : Program) : Program :=
  let initState : InferHoleState := { model := model }
  let (procs, _) := (program.staticProcedures.mapM inferProcedure).run initState
  { program with staticProcedures := procs }

end -- public section

/-! ## No-op proof -/

private theorem attach_all_cons' {α : Type} {x : α} {xs : List α} {p : α → Bool}
    (h : (x :: xs).attach.all (fun ⟨a, _⟩ => p a) = true) :
    p x = true ∧ xs.attach.all (fun ⟨a, _⟩ => p a) = true :=
  ⟨List.all_eq_true.mp h ⟨x, .head xs⟩ (List.mem_attach _ _),
   List.all_eq_true.mpr fun ⟨a, ha⟩ _ => List.all_eq_true.mp h ⟨a, .tail x ha⟩ (List.mem_attach _ _)⟩

private def nh_all' {args : List StmtExprMd} (h : args.attach.all (fun ⟨a, _⟩ => noHolesAllMd a) = true) : ∀ a ∈ args, noHolesAllMd a = true :=
  fun a ha => List.all_eq_true.mp h ⟨a, ha⟩ (List.mem_attach args ⟨a, ha⟩)

private axiom inferArgsTyped_id_ax : ∀ (args : List StmtExprMd) (types : List HighTypeMd) (s : InferHoleState),
    (∀ a ∈ args, noHolesAllMd a = true) → inferArgsTyped args types s = (args, s)

private theorem mapM_id_of (f : StmtExprMd → InferHoleM StmtExprMd) (args : List StmtExprMd) (s : InferHoleState)
    (h : args.attach.all (fun ⟨a, _⟩ => noHolesAllMd a) = true)
    (hf : ∀ (a : StmtExprMd) (s : InferHoleState), noHolesAllMd a = true → f a s = (a, s)) :
    (args.mapM f) s = (args, s) := by
  induction args generalizing s with
  | nil => rfl
  | cons x xs ih => have ⟨hx, hxs⟩ := attach_all_cons' h; simp only [List.mapM_cons, bind, StateT.bind, get, MonadState.get, StateT.get, getThe, MonadStateOf.get, pure, StateT.pure, Functor.map, StateT.map, hf x s hx, ih s hxs]

private theorem inferArgs_id_of (args : List StmtExprMd) (s : InferHoleState)
    (h : args.attach.all (fun ⟨a, _⟩ => noHolesAllMd a) = true)
    (hf : ∀ (a : StmtExprMd) (et : HighTypeMd) (s : InferHoleState), noHolesAllMd a = true → inferExpr a et s = (a, s))
    (et : HighTypeMd) :
    inferArgs args et s = (args, s) ∧ (args.mapM (fun x => inferExpr x et)) s = (args, s) := by
  constructor <;> (first | (unfold inferArgs; skip) | skip) <;> exact mapM_id_of _ args s h (fun a s ha => hf a et s ha)

private theorem inferStmtList_id_of (stmts : List StmtExprMd) (s : InferHoleState)
    (h : stmts.attach.all (fun ⟨a, _⟩ => noHolesAllMd a) = true)
    (hf : ∀ (a : StmtExprMd) (s : InferHoleState), noHolesAllMd a = true → inferStmt a s = (a, s)) :
    inferStmtList stmts s = (stmts, s) := by
  unfold inferStmtList; exact mapM_id_of _ stmts s h hf

section
set_option maxHeartbeats 400000
mutual
theorem inferExpr_id (expr : StmtExprMd) (et : HighTypeMd) (s : InferHoleState)
    (h : noHolesAllMd expr = true) : inferExpr expr et s = (expr, s) := by
  conv => lhs; unfold inferExpr
  match expr, h with
  | ⟨.Hole true _, _⟩, h => rw [noHolesAllMd_hole] at h; exact absurd h (by decide)
  | ⟨.Hole false _, _⟩, h => rw [noHolesAllMd_hole] at h; exact absurd h (by decide)
  | ⟨.PrimitiveOp op args, md⟩, h => simp only [noHolesAllMd_po] at h; simp only [bind, StateT.bind, get, MonadState.get, StateT.get, getThe, MonadStateOf.get, pure, StateT.pure, Functor.map, StateT.map, (inferArgs_id_of args s h inferExpr_id _).1]
  | ⟨.StaticCall callee args, md⟩, h =>
    simp only [noHolesAllMd_sc] at h; simp only [bind, StateT.bind, get, MonadState.get, StateT.get, getThe, MonadStateOf.get, pure, StateT.pure, Functor.map, StateT.map]
    cases calleeParamTypes s.model callee with
    | some types => have := inferArgsTyped_id_ax args types s (nh_all' h); simp [bind, StateT.bind, get, MonadState.get, StateT.get, getThe, MonadStateOf.get, pure, StateT.pure, Functor.map, StateT.map, this]
    | none => simp [bind, StateT.bind, get, MonadState.get, StateT.get, getThe, MonadStateOf.get, pure, StateT.pure, Functor.map, StateT.map, (inferArgs_id_of args s h inferExpr_id _).1]
  | ⟨.InstanceCall target callee args, md⟩, h => simp only [noHolesAllMd_ic, Bool.and_eq_true] at h; simp only [bind, StateT.bind, get, MonadState.get, StateT.get, getThe, MonadStateOf.get, pure, StateT.pure, Functor.map, StateT.map, inferExpr_id target _ s h.1, (inferArgs_id_of args s h.2 inferExpr_id _).1]
  | ⟨.ReferenceEquals l r, md⟩, h => simp only [noHolesAllMd_re, Bool.and_eq_true] at h; simp only [bind, StateT.bind, get, MonadState.get, StateT.get, getThe, MonadStateOf.get, pure, StateT.pure, Functor.map, StateT.map, inferExpr_id l _ s h.1, inferExpr_id r _ s h.2]
  | ⟨.IfThenElse c t e, md⟩, h =>
    simp only [noHolesAllMd_ite, Bool.and_eq_true] at h; have hc := h.1.1; have ht := h.1.2; have he := h.2
    cases e with
    | none => simp only [bind, StateT.bind, get, MonadState.get, StateT.get, getThe, MonadStateOf.get, pure, StateT.pure, Functor.map, StateT.map, inferExpr_id c (bareType .TBool) s hc, inferExpr_id t et s ht]
    | some e' => simp only [bind, StateT.bind, get, MonadState.get, StateT.get, getThe, MonadStateOf.get, pure, StateT.pure, Functor.map, StateT.map, inferExpr_id c (bareType .TBool) s hc, inferExpr_id t et s ht, inferExpr_id e' et s he]
  | ⟨.Block stmts label, md⟩, h => simp only [noHolesAllMd_block] at h; simp only [bind, StateT.bind, get, MonadState.get, StateT.get, getThe, MonadStateOf.get, pure, StateT.pure, Functor.map, StateT.map, inferStmtList_id_of stmts s h inferStmt_id]
  | ⟨.Assign _ value, md⟩, h => simp only [noHolesAllMd_assign] at h; simp only [bind, StateT.bind, get, MonadState.get, StateT.get, getThe, MonadStateOf.get, pure, StateT.pure, Functor.map, StateT.map, inferExpr_id value _ s h]
  | ⟨.LocalVariable n ty init, md⟩, h => simp only [noHolesAllMd_lv] at h; cases init with | none => rfl | some i => simp only [bind, StateT.bind, get, MonadState.get, StateT.get, getThe, MonadStateOf.get, pure, StateT.pure, Functor.map, StateT.map, inferExpr_id i _ s (by simp_all)]
  | ⟨.Old v, md⟩, h => simp only [noHolesAllMd_old] at h; simp only [bind, StateT.bind, get, MonadState.get, StateT.get, getThe, MonadStateOf.get, pure, StateT.pure, Functor.map, StateT.map, inferExpr_id v _ s h]
  | ⟨.Fresh v, md⟩, h => simp only [noHolesAllMd_fresh] at h; simp only [bind, StateT.bind, get, MonadState.get, StateT.get, getThe, MonadStateOf.get, pure, StateT.pure, Functor.map, StateT.map, inferExpr_id v _ s h]
  | ⟨.Assigned n, md⟩, h => simp only [noHolesAllMd_assigned] at h; simp only [bind, StateT.bind, get, MonadState.get, StateT.get, getThe, MonadStateOf.get, pure, StateT.pure, Functor.map, StateT.map, inferExpr_id n _ s h]
  | ⟨.ProveBy v p, md⟩, h => simp only [noHolesAllMd_proveby, Bool.and_eq_true] at h; simp only [bind, StateT.bind, get, MonadState.get, StateT.get, getThe, MonadStateOf.get, pure, StateT.pure, Functor.map, StateT.map, inferExpr_id v _ s h.1, inferExpr_id p _ s h.2]
  | ⟨.ContractOf ty f, md⟩, h => simp only [noHolesAllMd_contractof] at h; simp only [bind, StateT.bind, get, MonadState.get, StateT.get, getThe, MonadStateOf.get, pure, StateT.pure, Functor.map, StateT.map, inferExpr_id f _ s h]
  | ⟨.Forall param trigger body, md⟩, h =>
    simp only [noHolesAllMd_forall, Bool.and_eq_true] at h
    cases trigger with
    | none => simp only [bind, StateT.bind, get, MonadState.get, StateT.get, getThe, MonadStateOf.get, pure, StateT.pure, Functor.map, StateT.map, inferExpr_id body (bareType .TBool) s h.2]
    | some t => simp only [bind, StateT.bind, get, MonadState.get, StateT.get, getThe, MonadStateOf.get, pure, StateT.pure, Functor.map, StateT.map, inferExpr_id t defaultHoleType s h.1, inferExpr_id body (bareType .TBool) s h.2]
  | ⟨.Exists param trigger body, md⟩, h =>
    simp only [noHolesAllMd_exists, Bool.and_eq_true] at h
    cases trigger with
    | none => simp only [bind, StateT.bind, get, MonadState.get, StateT.get, getThe, MonadStateOf.get, pure, StateT.pure, Functor.map, StateT.map, inferExpr_id body (bareType .TBool) s h.2]
    | some t => simp only [bind, StateT.bind, get, MonadState.get, StateT.get, getThe, MonadStateOf.get, pure, StateT.pure, Functor.map, StateT.map, inferExpr_id t defaultHoleType s h.1, inferExpr_id body (bareType .TBool) s h.2]
  | ⟨.LiteralBool _, _⟩, _ | ⟨.LiteralInt _, _⟩, _ | ⟨.LiteralString _, _⟩, _ | ⟨.LiteralDecimal _, _⟩, _ | ⟨.Identifier _, _⟩, _ | ⟨.FieldSelect _ _, _⟩, _ | ⟨.PureFieldUpdate _ _ _, _⟩, _ | ⟨.New _, _⟩, _ | ⟨.This, _⟩, _ | ⟨.AsType _ _, _⟩, _ | ⟨.IsType _ _, _⟩, _ | ⟨.While _ _ _ _, _⟩, _ | ⟨.Return _, _⟩, _ | ⟨.Assert _, _⟩, _ | ⟨.Assume _, _⟩, _ | ⟨.Abstract, _⟩, _ | ⟨.All, _⟩, _ | ⟨.Throw _, _⟩, _ | ⟨.TryCatch _ _ _, _⟩, _ | ⟨.Exit _, _⟩, _ => rfl
  termination_by sizeOf expr
  decreasing_by all_goals (simp_wf; first | term_by_mem | omega | exact sorry)

theorem inferStmt_id (stmt : StmtExprMd) (s : InferHoleState)
    (h : noHolesAllMd stmt = true) : inferStmt stmt s = (stmt, s) := by
  conv => lhs; unfold inferStmt
  match stmt, h with
  | ⟨.LocalVariable n ty (some i), md⟩, h => simp only [noHolesAllMd_lv] at h; simp only [bind, StateT.bind, get, MonadState.get, StateT.get, getThe, MonadStateOf.get, pure, StateT.pure, Functor.map, StateT.map, inferExpr_id i _ s (by simp_all)]
  | ⟨.Assign targets value, md⟩, h => simp only [noHolesAllMd_assign] at h; simp only [bind, StateT.bind, get, MonadState.get, StateT.get, getThe, MonadStateOf.get, pure, StateT.pure, Functor.map, StateT.map, inferExpr_id value _ s h]
  | ⟨.Block stmts label, md⟩, h => simp only [noHolesAllMd_block] at h; simp only [bind, StateT.bind, get, MonadState.get, StateT.get, getThe, MonadStateOf.get, pure, StateT.pure, Functor.map, StateT.map, inferStmtList_id_of stmts s h inferStmt_id]
  | ⟨.IfThenElse c t e, md⟩, h =>
    simp only [noHolesAllMd_ite, Bool.and_eq_true] at h; have hc := h.1.1; have ht := h.1.2; have he := h.2
    cases e with
    | none => simp only [bind, StateT.bind, get, MonadState.get, StateT.get, getThe, MonadStateOf.get, pure, StateT.pure, Functor.map, StateT.map, inferExpr_id c (bareType .TBool) s hc, inferStmt_id t s ht]
    | some e' => simp only [bind, StateT.bind, get, MonadState.get, StateT.get, getThe, MonadStateOf.get, pure, StateT.pure, Functor.map, StateT.map, inferExpr_id c (bareType .TBool) s hc, inferStmt_id t s ht, inferStmt_id e' s he]
  | ⟨.While c invs dec body, md⟩, h =>
    simp only [noHolesAllMd_while, Bool.and_eq_true] at h; obtain ⟨⟨⟨hc, hinvs⟩, hdec⟩, hbody⟩ := h
    have hinv := (inferArgs_id_of invs s hinvs inferExpr_id (bareType .TBool)).2
    cases dec with
    | none => simp only [bind, StateT.bind, get, MonadState.get, StateT.get, getThe, MonadStateOf.get, pure, StateT.pure, Functor.map, StateT.map, inferExpr_id c _ s hc, inferStmt_id body s hbody, hinv]
    | some d => simp only [bind, StateT.bind, get, MonadState.get, StateT.get, getThe, MonadStateOf.get, pure, StateT.pure, Functor.map, StateT.map, inferExpr_id c _ s hc, inferStmt_id body s hbody, hinv, inferExpr_id d (bareType .TInt) s (by simp_all [hdec])]
  | ⟨.Assert c, md⟩, h => simp only [noHolesAllMd_assert] at h; simp only [bind, StateT.bind, get, MonadState.get, StateT.get, getThe, MonadStateOf.get, pure, StateT.pure, Functor.map, StateT.map, inferExpr_id c _ s h]
  | ⟨.Assume c, md⟩, h => simp only [noHolesAllMd_assume] at h; simp only [bind, StateT.bind, get, MonadState.get, StateT.get, getThe, MonadStateOf.get, pure, StateT.pure, Functor.map, StateT.map, inferExpr_id c _ s h]
  | ⟨.StaticCall callee args, md⟩, h =>
    simp only [noHolesAllMd_sc] at h; simp only [bind, StateT.bind, get, MonadState.get, StateT.get, getThe, MonadStateOf.get, pure, StateT.pure, Functor.map, StateT.map]
    cases calleeParamTypes s.model callee with
    | some types => have := inferArgsTyped_id_ax args types s (nh_all' h); simp [bind, StateT.bind, get, MonadState.get, StateT.get, getThe, MonadStateOf.get, pure, StateT.pure, Functor.map, StateT.map, this]
    | none => simp [bind, StateT.bind, get, MonadState.get, StateT.get, getThe, MonadStateOf.get, pure, StateT.pure, Functor.map, StateT.map, (inferArgs_id_of args s h inferExpr_id _).1]
  | ⟨.Return (some v), md⟩, h => simp only [noHolesAllMd_ret] at h; simp only [bind, StateT.bind, get, MonadState.get, StateT.get, getThe, MonadStateOf.get, pure, StateT.pure, Functor.map, StateT.map, inferExpr_id v _ s (by simp_all)]
  | ⟨.Hole true _, _⟩, h => rw [noHolesAllMd_hole] at h; exact absurd h (by decide)
  | ⟨.Hole false _, _⟩, h => rw [noHolesAllMd_hole] at h; exact absurd h (by decide)
  | ⟨.LocalVariable _ _ none, _⟩, _ | ⟨.Return none, _⟩, _ | ⟨.LiteralBool _, _⟩, _ | ⟨.LiteralInt _, _⟩, _ | ⟨.LiteralString _, _⟩, _ | ⟨.LiteralDecimal _, _⟩, _ | ⟨.Identifier _, _⟩, _ | ⟨.FieldSelect _ _, _⟩, _ | ⟨.PureFieldUpdate _ _ _, _⟩, _ | ⟨.New _, _⟩, _ | ⟨.This, _⟩, _ | ⟨.ReferenceEquals _ _, _⟩, _ | ⟨.AsType _ _, _⟩, _ | ⟨.IsType _ _, _⟩, _ | ⟨.InstanceCall _ _ _, _⟩, _ | ⟨.PrimitiveOp _ _, _⟩, _ | ⟨.Forall _ _ _, _⟩, _ | ⟨.Exists _ _ _, _⟩, _ | ⟨.Assigned _, _⟩, _ | ⟨.Old _, _⟩, _ | ⟨.Fresh _, _⟩, _ | ⟨.ProveBy _ _, _⟩, _ | ⟨.ContractOf _ _, _⟩, _ | ⟨.Abstract, _⟩, _ | ⟨.All, _⟩, _ | ⟨.Throw _, _⟩, _ | ⟨.TryCatch _ _ _, _⟩, _ | ⟨.Exit _, _⟩, _ => rfl
  termination_by sizeOf stmt
  decreasing_by all_goals (simp_wf; first | term_by_mem | omega | exact sorry)

end

end -- section

-- inferProcedure returns proc unchanged (state may change due to modify)
private theorem inferProcedure_id (proc : Procedure) (s : InferHoleState)
    (hBody : match proc.body with | .Transparent b => noHolesAllMd b = true | .Opaque _ (some impl) _ => noHolesAllMd impl = true | _ => True) :
    ∃ s', inferProcedure proc s = (proc, s') := by
  unfold inferProcedure
  simp only [bind, StateT.bind, get, MonadState.get, StateT.get, getThe, MonadStateOf.get, pure, StateT.pure, Functor.map, StateT.map, modify, MonadState.modifyGet, StateT.modifyGet, MonadStateOf.modifyGet]
  cases proc with | mk name inputs outputs preconditions determinism decreases isFunctional body md =>
  simp only [] at hBody ⊢
  cases hb : body with
  | Transparent b =>
    simp only [hb] at hBody; simp only [bind, StateT.bind, get, MonadState.get, StateT.get, getThe, MonadStateOf.get, pure, StateT.pure, Functor.map, StateT.map, modify, MonadState.modifyGet, StateT.modifyGet, MonadStateOf.modifyGet]
    have hStmt := inferStmt_id b ({ s with currentOutputType := match outputs with | [single] => single.type | _ => defaultHoleType }) hBody
    simp only [bind, StateT.bind, get, MonadState.get, StateT.get, getThe, MonadStateOf.get, pure, StateT.pure, Functor.map, StateT.map, modify, MonadState.modifyGet, StateT.modifyGet, MonadStateOf.modifyGet, hStmt]; exact ⟨_, rfl⟩
  | Opaque posts impl mods =>
    simp only [hb] at hBody
    cases impl with
    | some i =>
      have hStmt := inferStmt_id i ({ s with currentOutputType := match outputs with | [single] => single.type | _ => defaultHoleType }) hBody
      simp only [bind, StateT.bind, get, MonadState.get, StateT.get, getThe, MonadStateOf.get, pure, StateT.pure, Functor.map, StateT.map, modify, MonadState.modifyGet, StateT.modifyGet, MonadStateOf.modifyGet, hStmt]; exact ⟨_, rfl⟩
    | none => exact ⟨_, rfl⟩
  | Abstract _ => simp only [bind, StateT.bind, get, MonadState.get, StateT.get, getThe, MonadStateOf.get, pure, StateT.pure, Functor.map, StateT.map, modify, MonadState.modifyGet, StateT.modifyGet, MonadStateOf.modifyGet]; exact ⟨_, rfl⟩
  | External => simp only [bind, StateT.bind, get, MonadState.get, StateT.get, getThe, MonadStateOf.get, pure, StateT.pure, Functor.map, StateT.map, modify, MonadState.modifyGet, StateT.modifyGet, MonadStateOf.modifyGet]; exact ⟨_, rfl⟩

private theorem mapM_inferProcedure_id (procs : List Procedure) (s : InferHoleState)
    (hAll : ∀ p ∈ procs, match p.body with | .Transparent b => noHolesAllMd b = true | .Opaque _ (some impl) _ => noHolesAllMd impl = true | _ => True) :
    ∃ s', (procs.mapM inferProcedure) s = (procs, s') := by
  induction procs generalizing s with
  | nil => exact ⟨s, rfl⟩
  | cons x xs ih => obtain ⟨s1, h1⟩ := inferProcedure_id x s (hAll x (.head xs)); obtain ⟨s2, h2⟩ := ih s1 (fun p hp => hAll p (.tail x hp)); exact ⟨s2, by simp [List.mapM_cons, bind, StateT.bind, get, MonadState.get, StateT.get, getThe, MonadStateOf.get, pure, StateT.pure, Functor.map, StateT.map, h1, h2]⟩

public theorem inferHoleTypes_noop (model : SemanticModel) (program : Program)
    (hNoHoles : programNoHolesAll program = true) :
    inferHoleTypes model program = program := by
  unfold inferHoleTypes
  have hAll : ∀ p ∈ program.staticProcedures,
      match p.body with | .Transparent b => noHolesAllMd b = true | .Opaque _ (some impl) _ => noHolesAllMd impl = true | _ => True := by
    intro p hp
    rw [programNoHolesAll_eq] at hNoHoles
    have hmem := List.all_eq_true.mp hNoHoles p hp
    split at hmem <;> simp_all
  obtain ⟨s', hs⟩ := mapM_inferProcedure_id program.staticProcedures {model} hAll
  simp only [bind, StateT.bind, get, MonadState.get, StateT.get, getThe, MonadStateOf.get, pure, StateT.pure, Functor.map, StateT.map, StateT.run, hs]

end Laurel
