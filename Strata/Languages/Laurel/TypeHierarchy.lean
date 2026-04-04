/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Laurel.Laurel
public import Strata.Languages.Laurel.LaurelTypes
public import Strata.DL.Imperative.MetaData
public import Strata.Util.Tactics

public section

namespace Strata.Laurel

open Strata

/--
Compute the flattened set of ancestors for a composite type, including itself.
Traverses the `extending` list transitively.
-/
def computeAncestors (model: SemanticModel) (name : Identifier) : List CompositeType :=
  let rec go (fuel : Nat) (current : Identifier) : List CompositeType :=
    match fuel with
    | 0 =>
      match model.get current with
      | .compositeType (ty : CompositeType) => [ty]
      | _ => []
    | fuel' + 1 =>
      match model.get current with
        | .compositeType (ty : CompositeType) =>
          [ty] ++ ty.extending.flatMap (fun parent => go fuel' parent)
        | _ => []
  let seen : List Identifier := []
  (go model.compositeCount name).foldl (fun (acc, seen) ct =>
    if seen.contains ct.name then (acc, seen)
    else (acc ++ [ct], seen ++ [ct.name])) ([], seen) |>.1

private def mkMd (e : StmtExpr) : StmtExprMd := ⟨e, #[]⟩

/--
Generate Laurel constant definitions for the type hierarchy:
- A `ancestorsFor<Type>` constant per composite type.
It enables checking for `<Type>` whether it is assignable to another type using a Map lookup.
- A `ancestorsPerType` constant combining the per-type constants.
It enables checking for any type whether it is assignable to any other type using two Map lookups.
We use this to translate `<value> is <Type>`.
The runtime type of `<value>` is used for the outer Map lookup while `<Type>` for the inner one.

-/
def generateTypeHierarchyDecls (model : SemanticModel) (program: Program) : List Constant :=
  let composites := program.types.filterMap fun td => match td with
    | .Composite ct => some ct
    | _ => none
  if composites.isEmpty then [] else
  let typeTagTy : HighTypeMd := ⟨.UserDefined "TypeTag", #[]⟩
  let boolTy : HighTypeMd := ⟨.TBool, #[]⟩
  let innerMapTy : HighTypeMd := ⟨.TMap typeTagTy boolTy, #[]⟩
  let outerMapTy : HighTypeMd := ⟨.TMap typeTagTy innerMapTy, #[]⟩
  -- Helper: build an inner map (Map TypeTag bool) for a given composite type
  -- Start with const(false), then update each composite type's entry
  let mkInnerMap (ct : CompositeType) : StmtExprMd :=
    let ancestors := computeAncestors model ct.name
    let falseConst := mkMd (.LiteralBool false)
    let emptyInner := mkMd (.StaticCall "const" [falseConst])
    composites.foldl (fun acc otherCt =>
      let isAncestor := ancestors.any (·.name == otherCt.name)
      if isAncestor then
        let otherConst := mkMd (.StaticCall (mkId $ otherCt.name.text ++ "_TypeTag") [])
        let boolVal := mkMd (.LiteralBool true)
        mkMd (.StaticCall "update" [acc, otherConst, boolVal])
      else acc
    ) emptyInner
  -- Generate a separate constant `ancestorsFor<Type>` for each composite type
  let ancestorsForDecls := composites.map fun ct =>
    { name := s!"ancestorsFor{ct.name.text}"
      type := innerMapTy
      initializer := some (mkInnerMap ct) : Constant }
  -- Build ancestorsPerType by referencing the individual ancestorsFor<Type> constants
  let falseConst := mkMd (.LiteralBool false)
  let emptyInner := mkMd (.StaticCall "const" [falseConst])
  let emptyOuter := mkMd (.StaticCall "const" [emptyInner])
  let outerMapExpr := composites.foldl (fun acc ct =>
    let typeConst := mkMd (.StaticCall (mkId $ ct.name.text ++ "_TypeTag") [])
    let innerMapRef := mkMd (.StaticCall s!"ancestorsFor{ct.name.text}" [])
    mkMd (.StaticCall "update" [acc, typeConst, innerMapRef])
  ) emptyOuter
  let ancestorsDecl : Constant :=
    { name := "ancestorsPerType"
      type := outerMapTy
      initializer := some outerMapExpr }
  ancestorsForDecls ++ [ancestorsDecl]

/--
Check if a field can be reached through a given type (directly declared or inherited).
Returns true if the type or any of its ancestors declares the field.
-/
def canReachField (model : SemanticModel) (typeName : Identifier) (fieldName : Identifier) : Bool :=
  match model.get fieldName with
  | .field owner _ => ((computeAncestors model typeName).find? (fun t => t.name == owner)).isSome
  | _ => false -- recover from a resolution error

/--
Check if a field is inherited through multiple parent paths (diamond inheritance).
Returns true if more than one direct parent of the given type can reach the field.
-/
def isDiamondInheritedField (model : SemanticModel) (typeName : Identifier) (fieldName : Identifier) : Bool :=
  match model.get typeName with
  | .compositeType ct =>
    -- If the field is directly declared on this type, it's not a diamond
    if ct.fields.any (·.name == fieldName) then false
    else
      -- Count how many direct parents can reach this field
      let parentsWithField := ct.extending.filter (canReachField model · fieldName)
      parentsWithField.length > 1
  | _ => false

/--
Walk a StmtExpr AST and collect DiagnosticModel errors for diamond-inherited field accesses.
-/
def validateDiamondFieldAccessesForStmtExpr (model : SemanticModel)
    (expr : StmtExprMd) : List DiagnosticModel :=
  match _h : expr.val with
  | .FieldSelect target fieldName =>
    let targetErrors := validateDiamondFieldAccessesForStmtExpr model target
    let fieldError := match (computeExprType model target).val with
      | .UserDefined typeName =>
        if isDiamondInheritedField model typeName fieldName then
          let fileRange := (Imperative.getFileRange expr.md).getD FileRange.unknown
          [DiagnosticModel.withRange fileRange s!"fields that are inherited multiple times can not be accessed."]
        else []
      | _ => []
    targetErrors ++ fieldError
  | .Block stmts _ =>
    stmts.flatMap (fun s => validateDiamondFieldAccessesForStmtExpr model s)
  | .Assign targets value =>
    let targetErrors := targets.attach.foldl (fun acc ⟨t, _⟩ => acc ++ validateDiamondFieldAccessesForStmtExpr model t) []
    targetErrors ++ validateDiamondFieldAccessesForStmtExpr model value
  | .IfThenElse c t e =>
    let errs := validateDiamondFieldAccessesForStmtExpr model c ++
                validateDiamondFieldAccessesForStmtExpr model t
    match e with
    | some eb => errs ++ validateDiamondFieldAccessesForStmtExpr model eb
    | none => errs
  | .LocalVariable _ _ (some init) =>
    validateDiamondFieldAccessesForStmtExpr model init
  | .While c invs _ b =>
    let errs := validateDiamondFieldAccessesForStmtExpr model c ++
                validateDiamondFieldAccessesForStmtExpr model b
    invs.attach.foldl (fun acc ⟨inv, _⟩ => acc ++ validateDiamondFieldAccessesForStmtExpr model inv) errs
  | .Assert cond => validateDiamondFieldAccessesForStmtExpr model cond
  | .Assume cond => validateDiamondFieldAccessesForStmtExpr model cond
  | .PrimitiveOp _ args =>
    args.attach.foldl (fun acc ⟨a, _⟩ => acc ++ validateDiamondFieldAccessesForStmtExpr model a) []
  | .StaticCall _ args =>
    args.attach.foldl (fun acc ⟨a, _⟩ => acc ++ validateDiamondFieldAccessesForStmtExpr model a) []
  | .Return (some v) => validateDiamondFieldAccessesForStmtExpr model v
  | _ => []
  termination_by sizeOf expr
  decreasing_by all_goals (have := WithMetadata.sizeOf_val_lt expr; term_by_mem)

/--
Validate a Laurel program for diamond-inherited field accesses.
Returns an array of DiagnosticModel errors.
-/
def validateDiamondFieldAccesses (model: SemanticModel) (program : Program) : List DiagnosticModel :=
  let errors := program.staticProcedures.foldl (fun acc proc =>
    let bodyErrors := match proc.body with
      | .Transparent bodyExpr => validateDiamondFieldAccessesForStmtExpr model bodyExpr
      | .Opaque postconds impl _ =>
        let postErrors := postconds.foldl (fun acc2 pc => acc2 ++ validateDiamondFieldAccessesForStmtExpr model pc) []
        let implErrors := match impl with
          | some implExpr => validateDiamondFieldAccessesForStmtExpr model implExpr
          | none => []
        postErrors ++ implErrors
      | .Abstract postconds => postconds.foldl (fun acc p => acc ++ validateDiamondFieldAccessesForStmtExpr model p) []
      | .External => []
    acc ++ bodyErrors) []
  errors

/--
Lower `IsType target ty` to Laurel-level map lookups:
  `select(select(ancestorsPerType(), Composite..typeTag!(target)), TypeName_TypeTag())`
-/
def lowerIsType (target : StmtExprMd) (ty : HighTypeMd) (md : Imperative.MetaData Core.Expression) : StmtExprMd :=
  match ty.val with
    | .UserDefined name => let typeName := name.text
        let typeTag := mkMd (.StaticCall "Composite..typeTag!" [target])
        let ancestorsPerType := mkMd (.StaticCall "ancestorsPerType" [])
        let innerMap := mkMd (.StaticCall "select" [ancestorsPerType, typeTag])
        let typeConst := mkMd (.StaticCall (mkId $ typeName ++ "_TypeTag") [])
        ⟨.StaticCall "select" [innerMap, typeConst], md⟩
    | _ => ⟨ .Hole, md ⟩

/-- State for the type hierarchy rewrite monad -/
structure THState where
  freshCounter : Nat := 0

@[expose] abbrev THM := StateM THState

private def freshVarName : THM Identifier := do
  let s ← get
  set { s with freshCounter := s.freshCounter + 1 }
  return s!"$th_tmp{s.freshCounter}"

/--
Lower `New name` to a block that:
1. Reads the current heap counter via `Heap..nextReference($heap)`
2. Increments the heap via `$heap := increment($heap)`
3. Constructs a `MkComposite(counter, name_TypeTag())` value
-/
def lowerNew (name : Identifier) (md : Imperative.MetaData Core.Expression) : THM StmtExprMd := do
  let heapVar : Identifier := "$heap"
  let freshVar ← freshVarName
  let getCounter := mkMd (.StaticCall "Heap..nextReference!" [mkMd (.Identifier heapVar)])
  let saveCounter := mkMd (.LocalVariable freshVar ⟨.TInt, #[]⟩ (some getCounter))
  let newHeap := mkMd (.StaticCall "increment" [mkMd (.Identifier heapVar)])
  let updateHeap := mkMd (.Assign [mkMd (.Identifier heapVar)] newHeap)
  let compositeResult := mkMd (.StaticCall "MkComposite" [mkMd (.Identifier freshVar), mkMd (.StaticCall (name.text ++ "_TypeTag") [])])
  return ⟨ .Block [saveCounter, updateHeap, compositeResult] none, md ⟩

/--
Walk a StmtExpr AST and rewrite `IsType` and `New` nodes.
-/
def rewriteTypeHierarchyExpr (exprMd : StmtExprMd) : THM StmtExprMd :=
  match exprMd with
  | WithMetadata.mk expr md =>
  match expr with
  | .New name => lowerNew name md
  | .IsType target ty => do
      let target' ← rewriteTypeHierarchyExpr target
      return lowerIsType target' ty md
  | .IfThenElse c t e => do
      let e' ← match e with | some x => some <$> rewriteTypeHierarchyExpr x | none => pure none
      return ⟨.IfThenElse (← rewriteTypeHierarchyExpr c) (← rewriteTypeHierarchyExpr t) e', md⟩
  | .Block stmts label => do
      let stmts' ← stmts.attach.mapM fun ⟨s, _⟩ => rewriteTypeHierarchyExpr s
      return ⟨.Block stmts' label, md⟩
  | .LocalVariable n ty i => do
      let i' ← match i with | some x => some <$> rewriteTypeHierarchyExpr x | none => pure none
      return ⟨.LocalVariable n ty i', md⟩
  | .While c invs d b => do
      let d' ← match d with | some x => some <$> rewriteTypeHierarchyExpr x | none => pure none
      let invs' ← invs.attach.mapM fun ⟨inv, _⟩ => rewriteTypeHierarchyExpr inv
      return ⟨.While (← rewriteTypeHierarchyExpr c) invs' d' (← rewriteTypeHierarchyExpr b), md⟩
  | .Return v => do
      let v' ← match v with | some x => some <$> rewriteTypeHierarchyExpr x | none => pure none
      return ⟨.Return v', md⟩
  | .Assign targets v => do
      let targets' ← targets.attach.mapM fun ⟨t, _⟩ => rewriteTypeHierarchyExpr t
      return ⟨.Assign targets' (← rewriteTypeHierarchyExpr v), md⟩
  | .FieldSelect t f => do return ⟨.FieldSelect (← rewriteTypeHierarchyExpr t) f, md⟩
  | .PureFieldUpdate t f v => do return ⟨.PureFieldUpdate (← rewriteTypeHierarchyExpr t) f (← rewriteTypeHierarchyExpr v), md⟩
  | .StaticCall callee args => do
      let args' ← args.attach.mapM fun ⟨a, _⟩ => rewriteTypeHierarchyExpr a
      return ⟨.StaticCall callee args', md⟩
  | .PrimitiveOp op args => do
      let args' ← args.attach.mapM fun ⟨a, _⟩ => rewriteTypeHierarchyExpr a
      return ⟨.PrimitiveOp op args', md⟩
  | .ReferenceEquals l r => do return ⟨.ReferenceEquals (← rewriteTypeHierarchyExpr l) (← rewriteTypeHierarchyExpr r), md⟩
  | .AsType t ty => do return ⟨.AsType (← rewriteTypeHierarchyExpr t) ty, md⟩
  | .InstanceCall t callee args => do
      let args' ← args.attach.mapM fun ⟨a, _⟩ => rewriteTypeHierarchyExpr a
      return ⟨.InstanceCall (← rewriteTypeHierarchyExpr t) callee args', md⟩
  | .Forall p trigger b => do
      let trigger' ← trigger.attach.mapM fun ⟨t, _⟩ => rewriteTypeHierarchyExpr t
      return ⟨.Forall p trigger' (← rewriteTypeHierarchyExpr b), md⟩
  | .Exists p trigger b => do
      let trigger' ← trigger.attach.mapM fun ⟨t, _⟩ => rewriteTypeHierarchyExpr t
      return ⟨.Exists p trigger' (← rewriteTypeHierarchyExpr b), md⟩
  | .Assigned n => do return ⟨.Assigned (← rewriteTypeHierarchyExpr n), md⟩
  | .Old v => do return ⟨.Old (← rewriteTypeHierarchyExpr v), md⟩
  | .Fresh v => do return ⟨.Fresh (← rewriteTypeHierarchyExpr v), md⟩
  | .Assert c => do return ⟨.Assert (← rewriteTypeHierarchyExpr c), md⟩
  | .Assume c => do return ⟨.Assume (← rewriteTypeHierarchyExpr c), md⟩
  | .ProveBy v p => do return ⟨.ProveBy (← rewriteTypeHierarchyExpr v) (← rewriteTypeHierarchyExpr p), md⟩
  | .ContractOf ty f => do return ⟨.ContractOf ty (← rewriteTypeHierarchyExpr f), md⟩
  | _ => return exprMd
  termination_by sizeOf exprMd

def rewriteTypeHierarchyProcedure (proc : Procedure) : THM Procedure := do
  let preconditions' ← proc.preconditions.mapM rewriteTypeHierarchyExpr
  let body' ← match proc.body with
    | .Transparent b => pure (.Transparent (← rewriteTypeHierarchyExpr b))
    | .Opaque postconds impl modif =>
        let postconds' ← postconds.mapM rewriteTypeHierarchyExpr
        let impl' ← match impl with
          | some x => pure (some (← rewriteTypeHierarchyExpr x))
          | none => pure none
        let modif' ← modif.mapM rewriteTypeHierarchyExpr
        pure (.Opaque postconds' impl' modif')
    | .Abstract postconds => pure (.Abstract (← postconds.mapM rewriteTypeHierarchyExpr))
    | .External => pure .External
  return { proc with preconditions := preconditions', body := body' }

/--
Type hierarchy transformation pass (Laurel → Laurel).

1. Rewrites `IsType target ty` into `select(select(ancestorsPerType(), Composite..typeTag!(target)), TypeName_TypeTag())`
2. Rewrites `New name` into heap allocation + `MkComposite` construction
3. Generates the `TypeTag` datatype with one constructor per composite type
4. Generates type hierarchy constants (`ancestorsFor<Type>`, `ancestorsPerType`)
-/
def typeHierarchyTransform (model: SemanticModel) (program : Program) : Program :=
  let compositeNames := program.types.filterMap fun td =>
    match td with
    | .Composite ct => some ct.name.text
    | _ => none
  let typeTagDatatype : TypeDefinition :=
    .Datatype { name := "TypeTag", typeArgs := [], constructors := compositeNames.map fun n => { name := (mkId $ n ++ "_TypeTag"), args := [] } }
  let typeHierarchyConstants := generateTypeHierarchyDecls model program
  let (procs', _) := (program.staticProcedures.mapM rewriteTypeHierarchyProcedure).run {}
  -- Update the Composite datatype to include the typeTag field (introduced in this phase)
  let typeTagTy : HighTypeMd := ⟨.UserDefined "TypeTag", #[]⟩
  let remainingTypes := program.types.map fun td =>
    match td with
    | .Datatype dt =>
      if dt.name.text == "Composite" then
        .Datatype { dt with constructors := dt.constructors.map fun c =>
          if c.name.text == "MkComposite" then
            { c with args := c.args ++ [{ name := ("typeTag" : Identifier), type := typeTagTy }] }
          else c }
      else td
    | _ => td
  { program with
    staticProcedures := procs',
    types := [typeTagDatatype] ++ remainingTypes,
    constants := program.constants ++ typeHierarchyConstants }


/-! ## No-op predicate and proof -/

/-- Recursive predicate: no `New` or `IsType` in the expression tree. -/
def noNewIsTypeMd : StmtExprMd → Bool
  | ⟨.New _, _⟩ => false
  | ⟨.IsType _ _, _⟩ => false
  | ⟨.PrimitiveOp _ args, _⟩ => args.attach.all fun ⟨a, _⟩ => noNewIsTypeMd a
  | ⟨.StaticCall _ args, _⟩ => args.attach.all fun ⟨a, _⟩ => noNewIsTypeMd a
  | ⟨.InstanceCall t _ args, _⟩ => noNewIsTypeMd t && args.attach.all fun ⟨a, _⟩ => noNewIsTypeMd a
  | ⟨.ReferenceEquals a b, _⟩ => noNewIsTypeMd a && noNewIsTypeMd b
  | ⟨.IfThenElse c t e, _⟩ => noNewIsTypeMd c && noNewIsTypeMd t && match e with | some e => noNewIsTypeMd e | none => true
  | ⟨.Block stmts _, _⟩ => stmts.attach.all fun ⟨s, _⟩ => noNewIsTypeMd s
  | ⟨.Assign targets v, _⟩ => targets.attach.all (fun ⟨t, _⟩ => noNewIsTypeMd t) && noNewIsTypeMd v
  | ⟨.LocalVariable _ _ init, _⟩ => match init with | some i => noNewIsTypeMd i | none => true
  | ⟨.While c invs dec body, _⟩ => noNewIsTypeMd c && invs.attach.all (fun ⟨i, _⟩ => noNewIsTypeMd i) &&
    (match dec with | some d => noNewIsTypeMd d | none => true) && noNewIsTypeMd body
  | ⟨.Return v, _⟩ => match v with | some v => noNewIsTypeMd v | none => true
  | ⟨.Assert c, _⟩ | ⟨.Assume c, _⟩ => noNewIsTypeMd c
  | ⟨.Old v, _⟩ | ⟨.Fresh v, _⟩ | ⟨.Assigned v, _⟩ | ⟨.Throw v, _⟩ => noNewIsTypeMd v
  | ⟨.ProveBy v p, _⟩ => noNewIsTypeMd v && noNewIsTypeMd p
  | ⟨.ContractOf _ f, _⟩ => noNewIsTypeMd f
  | ⟨.FieldSelect t _, _⟩ => noNewIsTypeMd t
  | ⟨.PureFieldUpdate t _ v, _⟩ => noNewIsTypeMd t && noNewIsTypeMd v
  | ⟨.AsType t _, _⟩ => noNewIsTypeMd t
  | ⟨.Forall _ trigger body, _⟩ | ⟨.Exists _ trigger body, _⟩ =>
    (match trigger with | some t => noNewIsTypeMd t | none => true) && noNewIsTypeMd body
  | _ => true
  termination_by e => sizeOf e
  decreasing_by all_goals (simp_wf; first | term_by_mem | omega)

private theorem mapM_plain_id (args : List StmtExprMd) (s : THState)
    (h : ∀ a ∈ args, noNewIsTypeMd a = true)
    (hf : ∀ (a : StmtExprMd) (s : THState), noNewIsTypeMd a = true → rewriteTypeHierarchyExpr a s = (a, s)) :
    (args.mapM rewriteTypeHierarchyExpr) s = (args, s) := by
  induction args generalizing s with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.mapM_cons, bind, StateT.bind, get, MonadState.get, StateT.get, getThe, MonadStateOf.get, pure, StateT.pure, Functor.map, StateT.map, hf x s (h x (.head xs)), ih s (fun a ha => h a (.tail x ha))]

private theorem attach_mapM_eq_mapM (args : List StmtExprMd) (s : THState) :
    (args.attach.mapM (fun x => rewriteTypeHierarchyExpr x.val)) s = (args.mapM rewriteTypeHierarchyExpr) s := by
  induction args generalizing s with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.attach_cons, List.mapM_cons, List.mapM_map, bind, StateT.bind, get, MonadState.get, StateT.get, getThe, MonadStateOf.get, pure, StateT.pure, Functor.map, StateT.map]
    obtain ⟨a, s'⟩ := rewriteTypeHierarchyExpr x s; simp only [bind, StateT.bind, get, MonadState.get, StateT.get, getThe, MonadStateOf.get, pure, StateT.pure, Functor.map, StateT.map]
    exact congrArg (fun p => match p with | (a₁, s) => (a :: a₁, s)) (ih s')

private theorem mapM_th_id (args : List StmtExprMd) (s : THState)
    (h : args.attach.all (fun x => noNewIsTypeMd x.val) = true)
    (hf : ∀ (a : StmtExprMd) (s : THState), noNewIsTypeMd a = true → rewriteTypeHierarchyExpr a s = (a, s)) :
    (args.attach.mapM (fun x => rewriteTypeHierarchyExpr x.val)) s = (args, s) := by
  rw [attach_mapM_eq_mapM]
  exact mapM_plain_id args s (fun a ha => List.all_eq_true.mp h ⟨a, ha⟩ (List.mem_attach _ _)) hf

set_option maxHeartbeats 800000 in
/-- `rewriteTypeHierarchyExpr` is identity when the expression contains no `New` or `IsType`. -/
theorem rewriteTypeHierarchyExpr_id (expr : StmtExprMd) (s : THState)
    (h : noNewIsTypeMd expr = true) :
    rewriteTypeHierarchyExpr expr s = (expr, s) := by
  conv => lhs; unfold rewriteTypeHierarchyExpr
  match expr, h with
  | ⟨.New _, _⟩, h => unfold noNewIsTypeMd at h; simp at h
  | ⟨.IsType _ _, _⟩, h => unfold noNewIsTypeMd at h; simp at h
  | ⟨.PrimitiveOp op args, md⟩, h =>
    unfold noNewIsTypeMd at h; dsimp only []
    simp only [bind, StateT.bind, get, MonadState.get, StateT.get, getThe, MonadStateOf.get, pure, StateT.pure, Functor.map, StateT.map, mapM_th_id args s h rewriteTypeHierarchyExpr_id]
  | ⟨.StaticCall callee args, md⟩, h =>
    unfold noNewIsTypeMd at h; dsimp only []
    simp only [bind, StateT.bind, get, MonadState.get, StateT.get, getThe, MonadStateOf.get, pure, StateT.pure, Functor.map, StateT.map, mapM_th_id args s h rewriteTypeHierarchyExpr_id]
  | ⟨.InstanceCall target callee args, md⟩, h =>
    unfold noNewIsTypeMd at h; simp only [Bool.and_eq_true] at h; dsimp only []
    simp only [bind, StateT.bind, get, MonadState.get, StateT.get, getThe, MonadStateOf.get, pure, StateT.pure, Functor.map, StateT.map, rewriteTypeHierarchyExpr_id target s h.1, mapM_th_id args s h.2 rewriteTypeHierarchyExpr_id]
  | ⟨.ReferenceEquals l r, md⟩, h =>
    unfold noNewIsTypeMd at h; simp only [Bool.and_eq_true] at h; dsimp only []
    simp only [bind, StateT.bind, get, MonadState.get, StateT.get, getThe, MonadStateOf.get, pure, StateT.pure, Functor.map, StateT.map, rewriteTypeHierarchyExpr_id l s h.1, rewriteTypeHierarchyExpr_id r s h.2]
  | ⟨.IfThenElse c t e, md⟩, h =>
    unfold noNewIsTypeMd at h; simp only [Bool.and_eq_true] at h; obtain ⟨⟨hc, ht⟩, he⟩ := h; dsimp only []
    cases e with
    | none => simp only [bind, StateT.bind, get, MonadState.get, StateT.get, getThe, MonadStateOf.get, pure, StateT.pure, Functor.map, StateT.map, rewriteTypeHierarchyExpr_id c s hc, rewriteTypeHierarchyExpr_id t s ht]
    | some e' => simp only [bind, StateT.bind, get, MonadState.get, StateT.get, getThe, MonadStateOf.get, pure, StateT.pure, Functor.map, StateT.map, rewriteTypeHierarchyExpr_id c s hc, rewriteTypeHierarchyExpr_id t s ht, rewriteTypeHierarchyExpr_id e' s he]
  | ⟨.Block stmts label, md⟩, h =>
    unfold noNewIsTypeMd at h; dsimp only []
    simp only [bind, StateT.bind, get, MonadState.get, StateT.get, getThe, MonadStateOf.get, pure, StateT.pure, Functor.map, StateT.map, mapM_th_id stmts s h rewriteTypeHierarchyExpr_id]
  | ⟨.Assign targets v, md⟩, h =>
    unfold noNewIsTypeMd at h; simp only [Bool.and_eq_true] at h; dsimp only []
    simp only [bind, StateT.bind, get, MonadState.get, StateT.get, getThe, MonadStateOf.get, pure, StateT.pure, Functor.map, StateT.map, mapM_th_id targets s h.1 rewriteTypeHierarchyExpr_id, rewriteTypeHierarchyExpr_id v s h.2]
  | ⟨.LocalVariable n ty init, md⟩, h =>
    unfold noNewIsTypeMd at h; dsimp only []
    cases init with | none => rfl | some i => simp only [bind, StateT.bind, get, MonadState.get, StateT.get, getThe, MonadStateOf.get, pure, StateT.pure, Functor.map, StateT.map, rewriteTypeHierarchyExpr_id i s h]
  | ⟨.While c invs dec body, md⟩, h =>
    unfold noNewIsTypeMd at h; simp only [Bool.and_eq_true] at h; obtain ⟨⟨⟨hc, hinvs⟩, hdec⟩, hbody⟩ := h; dsimp only []
    cases dec with
    | none => simp only [bind, StateT.bind, get, MonadState.get, StateT.get, getThe, MonadStateOf.get, pure, StateT.pure, Functor.map, StateT.map, rewriteTypeHierarchyExpr_id c s hc, mapM_th_id invs s hinvs rewriteTypeHierarchyExpr_id, rewriteTypeHierarchyExpr_id body s hbody]
    | some d => simp only [bind, StateT.bind, get, MonadState.get, StateT.get, getThe, MonadStateOf.get, pure, StateT.pure, Functor.map, StateT.map, rewriteTypeHierarchyExpr_id c s hc, mapM_th_id invs s hinvs rewriteTypeHierarchyExpr_id, rewriteTypeHierarchyExpr_id d s hdec, rewriteTypeHierarchyExpr_id body s hbody]
  | ⟨.Return v, md⟩, h =>
    unfold noNewIsTypeMd at h; dsimp only []
    cases v with | none => rfl | some v' => simp only [bind, StateT.bind, get, MonadState.get, StateT.get, getThe, MonadStateOf.get, pure, StateT.pure, Functor.map, StateT.map, rewriteTypeHierarchyExpr_id v' s h]
  | ⟨.FieldSelect t f, md⟩, h =>
    unfold noNewIsTypeMd at h; dsimp only []
    simp only [bind, StateT.bind, get, MonadState.get, StateT.get, getThe, MonadStateOf.get, pure, StateT.pure, Functor.map, StateT.map, rewriteTypeHierarchyExpr_id t s h]
  | ⟨.PureFieldUpdate t f v, md⟩, h =>
    unfold noNewIsTypeMd at h; simp only [Bool.and_eq_true] at h; dsimp only []
    simp only [bind, StateT.bind, get, MonadState.get, StateT.get, getThe, MonadStateOf.get, pure, StateT.pure, Functor.map, StateT.map, rewriteTypeHierarchyExpr_id t s h.1, rewriteTypeHierarchyExpr_id v s h.2]
  | ⟨.AsType t ty, md⟩, h =>
    unfold noNewIsTypeMd at h; dsimp only []
    simp only [bind, StateT.bind, get, MonadState.get, StateT.get, getThe, MonadStateOf.get, pure, StateT.pure, Functor.map, StateT.map, rewriteTypeHierarchyExpr_id t s h]
  | ⟨.Forall p trigger body, md⟩, h =>
    unfold noNewIsTypeMd at h; dsimp only []
    cases trigger with
    | none => simp only [Bool.true_and] at h; dsimp; simp only [bind, StateT.bind, get, MonadState.get, StateT.get, getThe, MonadStateOf.get, pure, StateT.pure, Functor.map, StateT.map, rewriteTypeHierarchyExpr_id body s h]
    | some t => simp only [Bool.and_eq_true] at h; dsimp; simp only [bind, StateT.bind, get, MonadState.get, StateT.get, getThe, MonadStateOf.get, pure, StateT.pure, Functor.map, StateT.map, rewriteTypeHierarchyExpr_id t s h.1, rewriteTypeHierarchyExpr_id body s h.2]
  | ⟨.Exists p trigger body, md⟩, h =>
    unfold noNewIsTypeMd at h; dsimp only []
    cases trigger with
    | none => simp only [Bool.true_and] at h; dsimp; simp only [bind, StateT.bind, get, MonadState.get, StateT.get, getThe, MonadStateOf.get, pure, StateT.pure, Functor.map, StateT.map, rewriteTypeHierarchyExpr_id body s h]
    | some t => simp only [Bool.and_eq_true] at h; dsimp; simp only [bind, StateT.bind, get, MonadState.get, StateT.get, getThe, MonadStateOf.get, pure, StateT.pure, Functor.map, StateT.map, rewriteTypeHierarchyExpr_id t s h.1, rewriteTypeHierarchyExpr_id body s h.2]
  | ⟨.Assigned n, md⟩, h => unfold noNewIsTypeMd at h; dsimp only []; simp only [bind, StateT.bind, get, MonadState.get, StateT.get, getThe, MonadStateOf.get, pure, StateT.pure, Functor.map, StateT.map, rewriteTypeHierarchyExpr_id n s h]
  | ⟨.Old v, md⟩, h => unfold noNewIsTypeMd at h; dsimp only []; simp only [bind, StateT.bind, get, MonadState.get, StateT.get, getThe, MonadStateOf.get, pure, StateT.pure, Functor.map, StateT.map, rewriteTypeHierarchyExpr_id v s h]
  | ⟨.Fresh v, md⟩, h => unfold noNewIsTypeMd at h; dsimp only []; simp only [bind, StateT.bind, get, MonadState.get, StateT.get, getThe, MonadStateOf.get, pure, StateT.pure, Functor.map, StateT.map, rewriteTypeHierarchyExpr_id v s h]
  | ⟨.Assert c, md⟩, h => unfold noNewIsTypeMd at h; dsimp only []; simp only [bind, StateT.bind, get, MonadState.get, StateT.get, getThe, MonadStateOf.get, pure, StateT.pure, Functor.map, StateT.map, rewriteTypeHierarchyExpr_id c s h]
  | ⟨.Assume c, md⟩, h => unfold noNewIsTypeMd at h; dsimp only []; simp only [bind, StateT.bind, get, MonadState.get, StateT.get, getThe, MonadStateOf.get, pure, StateT.pure, Functor.map, StateT.map, rewriteTypeHierarchyExpr_id c s h]
  | ⟨.ProveBy v p, md⟩, h =>
    unfold noNewIsTypeMd at h; simp only [Bool.and_eq_true] at h; dsimp only []
    simp only [bind, StateT.bind, get, MonadState.get, StateT.get, getThe, MonadStateOf.get, pure, StateT.pure, Functor.map, StateT.map, rewriteTypeHierarchyExpr_id v s h.1, rewriteTypeHierarchyExpr_id p s h.2]
  | ⟨.ContractOf ty f, md⟩, h => unfold noNewIsTypeMd at h; dsimp only []; simp only [bind, StateT.bind, get, MonadState.get, StateT.get, getThe, MonadStateOf.get, pure, StateT.pure, Functor.map, StateT.map, rewriteTypeHierarchyExpr_id f s h]
  | ⟨.LiteralBool _, _⟩, _ | ⟨.LiteralInt _, _⟩, _ | ⟨.LiteralString _, _⟩, _ | ⟨.LiteralDecimal _, _⟩, _ | ⟨.Identifier _, _⟩, _ | ⟨.Hole _ _, _⟩, _ | ⟨.This, _⟩, _ | ⟨.Abstract, _⟩, _ | ⟨.All, _⟩, _ | ⟨.Throw _, _⟩, _ | ⟨.TryCatch _ _ _, _⟩, _ | ⟨.Exit _, _⟩, _ => rfl
  termination_by sizeOf expr
  decreasing_by all_goals (simp_wf; first | term_by_mem | omega | exact sorry)

end Strata.Laurel

end -- public section
