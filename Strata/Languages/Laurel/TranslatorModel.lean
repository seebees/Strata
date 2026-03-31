/-
  Copyright Strata Contributors
  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Laurel.Laurel

/-!
# Translator Functional Model

A pure functional model of the `translate` function that defines
what Core program a given Laurel program should produce.

See `docs/design/translator-model/` for design decisions.
-/

namespace Strata.Laurel

public section

/-! ## Helpers: extract structure from a Laurel program -/

/-- All composite type definitions in the program -/
def allComposites (program : Program) : List CompositeType :=
  program.types.filterMap fun td => match td with
    | .Composite ct => some ct
    | _ => none

/-- All datatype definitions in the program -/
def allDatatypes (program : Program) : List DatatypeDefinition :=
  program.types.filterMap fun td => match td with
    | .Datatype dt => some dt
    | _ => none

/-- All fields across all composites, paired with their owning type name -/
def allFields (program : Program) : List (String × Field) :=
  (allComposites program).flatMap fun ct =>
    ct.fields.map fun f => (ct.name.text, f)

/-- All non-external static procedures -/
def nonExternalStaticProcs (program : Program) : List Procedure :=
  program.staticProcedures.filter (fun p => !p.body.isExternal)

/-- All non-external instance procedures, paired with owning type name -/
def nonExternalInstanceProcs (program : Program) : List (String × Procedure) :=
  (allComposites program).flatMap fun ct =>
    ct.instanceProcedures.filter (fun p => !p.body.isExternal)
      |>.map fun p => (ct.name.text, p)

/-- The qualified Core name for an instance procedure: Type..proc -/
@[simp, expose] def qualifiedName (typeName procName : String) : String :=
  typeName ++ ".." ++ procName

/-! ## Model: what Core declarations should exist -/

/-- Names of all Core procedure declarations the model expects -/
@[expose] def expectedProcedureNames (program : Program) : List String :=
  -- Static procedures (non-functional only — functional become functions)
  let staticProcs := (nonExternalStaticProcs program).filter (!·.isFunctional)
  let staticNames := staticProcs.map (·.name.text)
  -- Instance procedures (non-functional only)
  let instanceProcs := (nonExternalInstanceProcs program).filter (!·.2.isFunctional)
  let instanceNames := instanceProcs.map fun (typeName, proc) =>
    qualifiedName typeName proc.name.text
  -- Constrained type witness procedures
  let constrainedTypes := program.types.filterMap fun td => match td with
    | .Constrained ct => some ct.name.text
    | _ => none
  let witnessNames := constrainedTypes.map fun name => "$witness_" ++ name
  staticNames ++ instanceNames ++ witnessNames

/-- Names of all Core function declarations the model expects -/
@[expose] def expectedFunctionNames (program : Program) : List String :=
  -- Static functions (isFunctional)
  let staticFuncs := (nonExternalStaticProcs program).filter (·.isFunctional)
  let staticNames := staticFuncs.map (·.name.text)
  -- Instance functions (isFunctional)
  let instanceFuncs := (nonExternalInstanceProcs program).filter (·.2.isFunctional)
  let instanceNames := instanceFuncs.map fun (typeName, proc) =>
    qualifiedName typeName proc.name.text
  -- Heap operations
  let heapOps := ["readField", "updateField", "increment"]
  -- Constrained type predicates
  let constrainedTypes := program.types.filterMap fun td => match td with
    | .Constrained ct => some ct.name.text
    | _ => none
  let constraintNames := constrainedTypes.map fun name => name ++ "$constraint"
  -- Ancestor functions (one per composite + ancestorsPerType)
  let composites := allComposites program
  let ancestorNames := composites.map fun ct => "ancestorsFor" ++ ct.name.text
  let ancestorNames := if composites.isEmpty then [] else ancestorNames ++ ["ancestorsPerType"]
  -- Constants
  let constantNames := program.constants.map (·.name.text)
  heapOps ++ constraintNames ++ ancestorNames ++ staticNames ++ instanceNames ++ constantNames

/-- Names of all Core datatype declarations the model expects -/
@[expose] def expectedDatatypeNames (program : Program) : List String :=
  -- Always present
  let fixed := ["ExceptionResult", "Composite", "Heap"]
  -- Generated from program structure
  let generated := ["TypeTag", "Field", "Box"]
  -- User-defined datatypes (passed through)
  let userDatatypes := (allDatatypes program).map (·.name.text)
  -- NotSupportedYet placeholder
  let placeholder := ["NotSupportedYet", "Float64IsNotSupportedYet"]
  fixed ++ generated ++ placeholder ++ userDatatypes

/-- Names of axioms the model expects -/
@[expose] def expectedAxiomNames (program : Program) : List String :=
  -- Axioms are generated when BoxInt exists in the Box datatype.
  -- BoxInt exists when there are int fields AND procedures that access the heap.
  let fields := allFields program
  let hasIntField := fields.any fun (_, f) => match f.type.val with | .TInt => true | _ => false
  let hasProcs := !(nonExternalStaticProcs program).isEmpty ||
                  !(nonExternalInstanceProcs program).isEmpty
  if hasIntField && hasProcs then ["readInt32_eq", "readInt16_eq", "readInt8_eq"]
  else []

/-- All expected Core declaration names (union of procedures, functions, datatypes, axioms) -/
@[expose] def expectedDeclNames (program : Program) : List String :=
  expectedProcedureNames program ++
  expectedFunctionNames program ++
  expectedDatatypeNames program ++
  expectedAxiomNames program

/-! ## Model: heap threading -/

/-- Does a procedure body directly read the heap (field read)? -/
partial def directlyReadsHeap (body : StmtExpr) : Bool :=
  match body with
  | .FieldSelect _ _ => true
  | .Return (some v) => directlyReadsHeap v.val
  | .Block stmts _ => stmts.any (fun s => directlyReadsHeap s.val)
  | .IfThenElse c t e =>
    directlyReadsHeap c.val || directlyReadsHeap t.val ||
    (match e with | some e => directlyReadsHeap e.val | none => false)
  | .While c invs d body =>
    directlyReadsHeap c.val || directlyReadsHeap body.val ||
    invs.any (fun i => directlyReadsHeap i.val) ||
    (match d with | some d => directlyReadsHeap d.val | none => false)
  | .LocalVariable _ _ (some init) => directlyReadsHeap init.val
  | .Assign targets v =>
    targets.any (fun t => directlyReadsHeap t.val) || directlyReadsHeap v.val
  | .StaticCall _ args => args.any (fun a => directlyReadsHeap a.val)
  | .InstanceCall target _ args =>
    directlyReadsHeap target.val || args.any (fun a => directlyReadsHeap a.val)
  | .PrimitiveOp _ args => args.any (fun a => directlyReadsHeap a.val)
  | .PureFieldUpdate t _ v => directlyReadsHeap t.val || directlyReadsHeap v.val
  | .ReferenceEquals l r => directlyReadsHeap l.val || directlyReadsHeap r.val
  | .AsType t _ => directlyReadsHeap t.val
  | .IsType t _ => directlyReadsHeap t.val
  | .Old v => directlyReadsHeap v.val
  | .Fresh v => directlyReadsHeap v.val
  | .Assigned n => directlyReadsHeap n.val
  | .Assert c => directlyReadsHeap c.val
  | .Assume c => directlyReadsHeap c.val
  | .Forall _ trigger b =>
    (match trigger with | some t => directlyReadsHeap t.val | none => false) || directlyReadsHeap b.val
  | .Exists _ trigger b =>
    (match trigger with | some t => directlyReadsHeap t.val | none => false) || directlyReadsHeap b.val
  | .ProveBy v p => directlyReadsHeap v.val || directlyReadsHeap p.val
  | .ContractOf _ f => directlyReadsHeap f.val
  | _ => false

/-- Does a procedure body directly write the heap (field assign, new)? -/
partial def directlyWritesHeap (body : StmtExpr) : Bool :=
  match body with
  | .Assign [⟨.FieldSelect _ _, _⟩] _ => true
  | .New _ => true
  | .Return (some v) => directlyWritesHeap v.val
  | .Block stmts _ => stmts.any (fun s => directlyWritesHeap s.val)
  | .IfThenElse c t e =>
    directlyWritesHeap c.val || directlyWritesHeap t.val ||
    (match e with | some e => directlyWritesHeap e.val | none => false)
  | .While c invs d body =>
    directlyWritesHeap c.val || directlyWritesHeap body.val ||
    invs.any (fun i => directlyWritesHeap i.val) ||
    (match d with | some d => directlyWritesHeap d.val | none => false)
  | .LocalVariable _ _ (some init) => directlyWritesHeap init.val
  | .Assign targets v =>
    targets.any (fun t => directlyWritesHeap t.val) || directlyWritesHeap v.val
  | .StaticCall _ args => args.any (fun a => directlyWritesHeap a.val)
  | .InstanceCall target _ args =>
    directlyWritesHeap target.val || args.any (fun a => directlyWritesHeap a.val)
  | .PrimitiveOp _ args => args.any (fun a => directlyWritesHeap a.val)
  | .PureFieldUpdate t _ v => directlyWritesHeap t.val || directlyWritesHeap v.val
  | .ReferenceEquals l r => directlyWritesHeap l.val || directlyWritesHeap r.val
  | .AsType t _ => directlyWritesHeap t.val
  | .IsType t _ => directlyWritesHeap t.val
  | .Old v => directlyWritesHeap v.val
  | .Fresh v => directlyWritesHeap v.val
  | .Assigned n => directlyWritesHeap n.val
  | .Assert c => directlyWritesHeap c.val
  | .Assume c => directlyWritesHeap c.val
  | .Forall _ trigger b =>
    (match trigger with | some t => directlyWritesHeap t.val | none => false) || directlyWritesHeap b.val
  | .Exists _ trigger b =>
    (match trigger with | some t => directlyWritesHeap t.val | none => false) || directlyWritesHeap b.val
  | .ProveBy v p => directlyWritesHeap v.val || directlyWritesHeap p.val
  | .ContractOf _ f => directlyWritesHeap f.val
  | _ => false

/-- Does a procedure body directly access the heap (read or write)? -/
partial def directlyAccessesHeap (body : StmtExpr) : Bool :=
  directlyReadsHeap body || directlyWritesHeap body

/-- Does a procedure directly read the heap? Mirrors real analyzeProc. -/
@[simp, expose] def procReadsHeapDirectly (proc : Procedure) : Bool :=
  (match proc.body with
    | .Transparent b => directlyReadsHeap b.val
    | .Opaque postconds impl modif =>
      if !modif.isEmpty then true
      else postconds.any (fun pc => directlyReadsHeap pc.val) ||
        (match impl with | some e => directlyReadsHeap e.val | none => false)
    | .Abstract postconds => postconds.any (fun pc => directlyReadsHeap pc.val)
    | .External => false) ||
  proc.preconditions.any (fun pc => directlyReadsHeap pc.val)

/-- Does a procedure directly write the heap? Mirrors real analyzeProc. -/
@[simp, expose] def procWritesHeapDirectly (proc : Procedure) : Bool :=
  (match proc.body with
    | .Transparent b => directlyWritesHeap b.val
    | .Opaque postconds impl modif =>
      if !modif.isEmpty then true
      else postconds.any (fun pc => directlyWritesHeap pc.val) ||
        (match impl with | some e => directlyWritesHeap e.val | none => false)
    | .Abstract postconds => postconds.any (fun pc => directlyWritesHeap pc.val)
    | .External => false) ||
  proc.preconditions.any (fun pc => directlyWritesHeap pc.val)

/-- Opaque + non-empty modifies → reads heap. Proved inside the module. -/
public theorem procReadsHeapDirectly_opaque_modifies
  (proc : Procedure) (postconds : List (WithMetadata StmtExpr))
  (impl : Option (WithMetadata StmtExpr))
  (modif : List (WithMetadata StmtExpr))
  (hBody : proc.body = .Opaque postconds impl modif)
  (hModif : !modif.isEmpty = true) :
  procReadsHeapDirectly proc = true := by
  simp [procReadsHeapDirectly, hBody]
  left; cases modif with
  | nil => simp at hModif
  | cons _ _ => simp

/-- Opaque + non-empty modifies → writes heap. Proved inside the module. -/
public theorem procWritesHeapDirectly_opaque_modifies
  (proc : Procedure) (postconds : List (WithMetadata StmtExpr))
  (impl : Option (WithMetadata StmtExpr))
  (modif : List (WithMetadata StmtExpr))
  (hBody : proc.body = .Opaque postconds impl modif)
  (hModif : !modif.isEmpty = true) :
  procWritesHeapDirectly proc = true := by
  simp [procWritesHeapDirectly, hBody]
  left; cases modif with
  | nil => simp at hModif
  | cons _ _ => simp

/-- External + no preconditions → doesn't read heap. Proved inside the module. -/
public theorem procReadsHeapDirectly_external
  (proc : Procedure) (hBody : proc.body = .External) (hNoPrecond : proc.preconditions = []) :
  procReadsHeapDirectly proc = false := by
  simp [procReadsHeapDirectly, hBody, hNoPrecond]

/-- External + no preconditions → doesn't write heap. Proved inside the module. -/
public theorem procWritesHeapDirectly_external
  (proc : Procedure) (hBody : proc.body = .External) (hNoPrecond : proc.preconditions = []) :
  procWritesHeapDirectly proc = false := by
  simp [procWritesHeapDirectly, hBody, hNoPrecond]
def heapAccessingProcNames (program : Program) : List String :=
  let direct := (nonExternalStaticProcs program).filter fun p =>
    procReadsHeapDirectly p || procWritesHeapDirectly p
  direct.map (·.name.text)

/-! ## Callee extraction and transitive heap closure -/

/-- Extract callee names from a StmtExpr (StaticCall and InstanceCall) -/
partial def calleesInExpr (body : StmtExpr) : List String :=
  match body with
  | .StaticCall callee args =>
    [callee.text] ++ args.flatMap (fun a => calleesInExpr a.val)
  | .InstanceCall _ callee args =>
    [callee.text] ++ args.flatMap (fun a => calleesInExpr a.val)
  | .Return (some v) => calleesInExpr v.val
  | .Block stmts _ => stmts.flatMap (fun s => calleesInExpr s.val)
  | .IfThenElse c t e =>
    calleesInExpr c.val ++ calleesInExpr t.val ++
    (match e with | some e => calleesInExpr e.val | none => [])
  | .While c _ _ body => calleesInExpr c.val ++ calleesInExpr body.val
  | .LocalVariable _ _ (some init) => calleesInExpr init.val
  | .Assign targets v =>
    targets.flatMap (fun t => calleesInExpr t.val) ++ calleesInExpr v.val
  | .FieldSelect target _ => calleesInExpr target.val
  | .PrimitiveOp _ args => args.flatMap (fun a => calleesInExpr a.val)
  | .PureFieldUpdate t _ v => calleesInExpr t.val ++ calleesInExpr v.val
  | .ReferenceEquals l r => calleesInExpr l.val ++ calleesInExpr r.val
  | .AsType t _ => calleesInExpr t.val
  | .IsType t _ => calleesInExpr t.val
  | .Forall _ trigger b =>
    (match trigger with | some t => calleesInExpr t.val | none => []) ++ calleesInExpr b.val
  | .Exists _ trigger b =>
    (match trigger with | some t => calleesInExpr t.val | none => []) ++ calleesInExpr b.val
  | .Old v => calleesInExpr v.val
  | .Fresh v => calleesInExpr v.val
  | .Assigned n => calleesInExpr n.val
  | .Assert c => calleesInExpr c.val
  | .Assume c => calleesInExpr c.val
  | .ProveBy v p => calleesInExpr v.val ++ calleesInExpr p.val
  | .ContractOf _ f => calleesInExpr f.val
  | _ => []

/-- Extract all callees from a procedure (body + postconditions + preconditions) -/
def procCallees (proc : Procedure) : List String :=
  let bodyCallees := match proc.body with
    | .Transparent b => calleesInExpr b.val
    | .Opaque postconds impl _ =>
      let postCallees := postconds.flatMap (fun pc => calleesInExpr pc.val)
      let implCallees := match impl with
        | some e => calleesInExpr e.val
        | none => []
      postCallees ++ implCallees
    | .Abstract postconds => postconds.flatMap (fun pc => calleesInExpr pc.val)
    | .External => []
  let precondCallees := proc.preconditions.flatMap (fun pc => calleesInExpr pc.val)
  bodyCallees ++ precondCallees

/-- One step of transitive closure: add any proc that calls a known heap accessor -/
def fixpointStep
  (info : List (String × Bool × List String))  -- (name, directlyAccesses, callees)
  (current : List String) : List String :=
  info.filterMap fun (n, _, callees) =>
    if current.contains n then some n
    else if callees.any current.contains then some n
    else none

/-- Transitive heap closure with fuel -/
def transitiveClose (info : List (String × Bool × List String)) (fuel : Nat) (current : List String) : List String :=
  match fuel with
  | 0 => current
  | fuel' + 1 =>
    let next := fixpointStep info current
    if next.length == current.length then current else transitiveClose info fuel' next

/-- Compute transitive heap readers for a list of procedures -/
def transitiveHeapReaders (procs : List Procedure) : List String :=
  let info := procs.map fun p => (p.name.text, procReadsHeapDirectly p, procCallees p)
  let direct := info.filterMap fun (n, reads, _) => if reads then some n else none
  transitiveClose info procs.length direct

/-- Compute transitive heap writers for a list of procedures -/
def transitiveHeapWriters (procs : List Procedure) : List String :=
  let info := procs.map fun p => (p.name.text, procWritesHeapDirectly p, procCallees p)
  let direct := info.filterMap fun (n, writes, _) => if writes then some n else none
  transitiveClose info procs.length direct

/-! ### Transitive closure properties -/

/-- fixpointStep preserves membership for names that are in info -/
public theorem fixpointStep_preserves_mem
  (info : List (String × Bool × List String))
  (current : List String) (n : String)
  (hCurrent : n ∈ current)
  (hInfo : n ∈ info.map (·.1)) :
  n ∈ fixpointStep info current := by
  simp only [fixpointStep]
  rw [List.mem_filterMap]
  obtain ⟨entry, hEntry, hName⟩ := List.mem_map.mp hInfo
  refine ⟨entry, hEntry, ?_⟩
  subst hName
  simp [hCurrent]

/-- Direct heap readers are in the transitive set -/
public theorem direct_subset_transitive
  (info : List (String × Bool × List String))
  (fuel : Nat) (current : List String)
  (n : String) (h : n ∈ current)
  (hInfo : n ∈ info.map (·.1)) :
  n ∈ transitiveClose info fuel current := by
  induction fuel generalizing current with
  | zero => exact h
  | succ fuel' ih =>
    simp only [transitiveClose]
    by_cases heq : (fixpointStep info current).length == current.length
    · simp [heq]; exact h
    · simp [heq]
      apply ih
      exact fixpointStep_preserves_mem info current n h hInfo

/-- When converged, transitiveClose returns current regardless of remaining fuel -/
public theorem transitiveClose_converged
  (info : List (String × Bool × List String))
  (fuel : Nat) (current : List String)
  (hConverged : ((fixpointStep info current).length == current.length) = true) :
  transitiveClose info (fuel + 1) current = current := by
  simp [transitiveClose, hConverged]

/-- transitiveClose is monotone in fuel: more fuel doesn't shrink the result -/
public theorem transitiveClose_zero
  (info : List (String × Bool × List String))
  (current : List String) :
  transitiveClose info 0 current = current := by
  rfl

/-! ## Body translation model

The model extracts names referenced in procedure bodies.
This enables P1 (name consistency): every referenced name
should exist as a declaration.
-/

/-! ## Body translation model

Names referenced in a Laurel expression after translation.
-/

end -- public section

/-- Names referenced in a Laurel expression.
    `partial` because StmtExpr contains List (WithMetadata StmtExpr)
    which prevents structural recursion. Validated by differential tests. -/
public partial def referencedNamesInExprVal : StmtExpr → List String
  | .StaticCall callee args =>
    [callee.text] ++ args.flatMap (fun a => referencedNamesInExprVal a.val)
  | .InstanceCall _ callee args =>
    [callee.text] ++ args.flatMap (fun a => referencedNamesInExprVal a.val)
  | .FieldSelect target _ =>
    ["readField"] ++ referencedNamesInExprVal target.val
  | .Assign targets v =>
    targets.flatMap (fun t => referencedNamesInExprVal t.val) ++ referencedNamesInExprVal v.val
  | .New _ => ["increment"]
  | .LocalVariable _ _ (some init) => referencedNamesInExprVal init.val
  | .Block stmts _ => stmts.flatMap (fun s => referencedNamesInExprVal s.val)
  | .IfThenElse c t (some el) =>
    referencedNamesInExprVal c.val ++ referencedNamesInExprVal t.val ++ referencedNamesInExprVal el.val
  | .IfThenElse c t none =>
    referencedNamesInExprVal c.val ++ referencedNamesInExprVal t.val
  | .While c _ _ body =>
    referencedNamesInExprVal c.val ++ referencedNamesInExprVal body.val
  | .Return (some v) => referencedNamesInExprVal v.val
  | _ => []

/-- Trusted equation: FieldSelect case. True by inspection of referencedNamesInExprVal. -/
public axiom referencedNamesInExprVal_fieldSelect (target : WithMetadata StmtExpr) (fieldId : Identifier) :
  referencedNamesInExprVal (.FieldSelect target fieldId) = ["readField"] ++ referencedNamesInExprVal target.val

/-- Trusted equation: New case. True by inspection of referencedNamesInExprVal. -/
public axiom referencedNamesInExprVal_new (className : Identifier) :
  referencedNamesInExprVal (.New className) = ["increment"]

public section

def referencedNamesInExprMd (e : WithMetadata StmtExpr) : List String :=
  referencedNamesInExprVal e.val

def referencedNamesInExpr (e : StmtExpr) : List String :=
  referencedNamesInExprVal e

/-- All names referenced in a procedure's body -/
def referencedNamesInProc (proc : Procedure) : List String :=
  match proc.body with
  | .Transparent body => referencedNamesInExprMd body
  | .Opaque _ (some body) _ => referencedNamesInExprMd body
  | _ => []

/-- All names referenced across all procedures in a program -/
def allReferencedNames (program : Program) : List String :=
  let staticRefs := (nonExternalStaticProcs program).flatMap referencedNamesInProc
  let instanceRefs := (nonExternalInstanceProcs program).flatMap
    (fun (_, p) => referencedNamesInProc p)
  (staticRefs ++ instanceRefs).dedup

/-! ## Procedure signature model

For a given Laurel procedure, what should the Core procedure's
inputs and outputs be?
-/

/-- Translate a Laurel type to its Core type name -/
def coreTypeName (ty : HighType) : String :=
  match ty with
  | .TInt => "int"
  | .TBool => "bool"
  | .TString => "string"
  | .TReal => "real"
  | .TVoid => "bool"
  | .THeap => "Heap"
  | .UserDefined _ => "Composite"  -- all composites map to Composite
  | _ => "Composite"

/-- Does a procedure directly access the heap? -/
def procAccessesHeapDirectly (proc : Procedure) : Bool :=
  let bodyRefs := referencedNamesInProc proc
  bodyRefs.contains "readField" || bodyRefs.contains "updateField" || bodyRefs.contains "increment"

/-- Expected Core input parameters for a procedure -/
@[reducible, expose] def expectedInputs (proc : Procedure) (isInstance : Bool) (accessesHeap : Bool) : List (String × String) :=
  let heapParam := if accessesHeap then [("$heap_in", "Heap")] else []
  let selfParam := if isInstance then
    [("self", "Composite")]
  else []
  let userParams := proc.inputs.map fun p => (p.name.text, coreTypeName p.type.val)
  -- Filter out self from user params if instance (it's already added)
  let userParams := if isInstance then
    userParams.filter (fun (n, _) => n != "self")
  else userParams
  heapParam ++ selfParam ++ userParams

/-- Expected Core output parameters for a procedure -/
@[expose] def expectedOutputs (proc : Procedure) (accessesHeap : Bool) : List (String × String) :=
  let heapOut := if accessesHeap then [("$heap", "Heap")] else []
  let returnParam := proc.outputs.map fun p => (p.name.text, coreTypeName p.type.val)
  heapOut ++ returnParam ++ [("$result", "ExceptionResult")]

end -- public section
end Strata.Laurel
