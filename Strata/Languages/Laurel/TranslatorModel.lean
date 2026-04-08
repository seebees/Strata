/-
  Copyright Strata Contributors
  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Laurel.Laurel
public import Strata.Languages.Core.Program
public import Strata.Languages.Laurel.CoreDefinitionsForLaurel
public import Strata.Languages.Laurel.HeapParameterizationConstants
public import Strata.DDM.Util.DecimalRat

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
@[expose] def allComposites (program : Program) : List CompositeType :=
  program.types.filterMap fun td => match td with
    | .Composite ct => some ct
    | _ => none

/-- All datatype definitions in the program -/
@[expose] def allDatatypes (program : Program) : List DatatypeDefinition :=
  program.types.filterMap fun td => match td with
    | .Datatype dt => some dt
    | _ => none

/-- All fields across all composites, paired with their owning type name -/
@[expose] def allFields (program : Program) : List (String × Field) :=
  (allComposites program).flatMap fun ct =>
    ct.fields.map fun f => (ct.name.text, f)

/-- All non-external static procedures -/
@[expose] def nonExternalStaticProcs (program : Program) : List Procedure :=
  program.staticProcedures.filter (fun p => !p.body.isExternal)

/-- All non-external instance procedures, paired with owning type name -/
@[expose] def nonExternalInstanceProcs (program : Program) : List (String × Procedure) :=
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
  -- NotSupportedYet placeholder (Float64IsNotSupportedYet comes from coreDefinitionsForLaurel)
  let placeholder := ["NotSupportedYet"]
  fixed ++ generated ++ placeholder ++ userDatatypes

/-- Names of axioms the model expects -/
@[expose] def expectedAxiomNames (program : Program) : List String :=
  -- Axioms are generated when BoxInt exists in the Box datatype.
  -- BoxInt exists when there are int fields (or constrained int fields) AND procedures.
  let fields := allFields program
  let constrainedIntNames := program.types.filterMap fun td => match td with
    | .Constrained ct => match ct.base.val with | .TInt => some ct.name.text | _ => none
    | _ => none
  let hasIntField := fields.any fun (_, f) => match f.type.val with
    | .TInt => true
    | .UserDefined name => constrainedIntNames.contains name.text
    | _ => false
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

mutual
/-- Does a procedure body directly read the heap (field read)? -/
def directlyReadsHeapMd (e : StmtExprMd) : Bool := directlyReadsHeap e.val
  termination_by sizeOf e
  decreasing_by cases e; term_by_mem

def directlyReadsHeap (body : StmtExpr) : Bool :=
  match _h : body with
  | .FieldSelect _ _ => true
  | .Return (some v) => directlyReadsHeapMd v
  | .Block stmts _ => stmts.attach.any (fun ⟨s, _⟩ => directlyReadsHeapMd s)
  | .IfThenElse c t e =>
    directlyReadsHeapMd c || directlyReadsHeapMd t ||
    (match e with | some e => directlyReadsHeapMd e | none => false)
  | .While c invs d body =>
    directlyReadsHeapMd c || directlyReadsHeapMd body ||
    invs.attach.any (fun ⟨i, _⟩ => directlyReadsHeapMd i) ||
    (match d with | some d => directlyReadsHeapMd d | none => false)
  | .LocalVariable _ _ (some init) => directlyReadsHeapMd init
  | .Assign targets v =>
    targets.attach.any (fun ⟨t, _⟩ => directlyReadsHeapMd t) || directlyReadsHeapMd v
  | .StaticCall _ args => args.attach.any (fun ⟨a, _⟩ => directlyReadsHeapMd a)
  | .InstanceCall target _ args => true  -- instance calls always access the heap
  | .PrimitiveOp _ args => args.attach.any (fun ⟨a, _⟩ => directlyReadsHeapMd a)
  | .PureFieldUpdate t _ v => directlyReadsHeapMd t || directlyReadsHeapMd v
  | .ReferenceEquals l r => directlyReadsHeapMd l || directlyReadsHeapMd r
  | .AsType t _ => directlyReadsHeapMd t
  | .IsType t _ => directlyReadsHeapMd t
  | .Old v => directlyReadsHeapMd v
  | .Fresh v => directlyReadsHeapMd v
  | .Assigned n => directlyReadsHeapMd n
  | .Assert c => directlyReadsHeapMd c
  | .Assume c => directlyReadsHeapMd c
  | .Forall _ trigger b =>
    (match trigger with | some t => directlyReadsHeapMd t | none => false) || directlyReadsHeapMd b
  | .Exists _ trigger b =>
    (match trigger with | some t => directlyReadsHeapMd t | none => false) || directlyReadsHeapMd b
  | .ProveBy v p => directlyReadsHeapMd v || directlyReadsHeapMd p
  | .ContractOf _ f => directlyReadsHeapMd f
  | _ => false
  termination_by sizeOf body
  decreasing_by all_goals (simp_wf; try term_by_mem)
end

@[simp] public theorem directlyReadsHeap_eq_fieldSelect (t : WithMetadata StmtExpr) (f : Identifier) :
  directlyReadsHeap (.FieldSelect t f) = true := by rw [directlyReadsHeap.eq_def]

@[simp] public theorem directlyReadsHeap_eq_literalBool (b : Bool) :
  directlyReadsHeap (.LiteralBool b) = false := by rw [directlyReadsHeap.eq_def]

@[simp] public theorem directlyReadsHeap_eq_literalInt (i : Int) :
  directlyReadsHeap (.LiteralInt i) = false := by rw [directlyReadsHeap.eq_def]

@[simp] public theorem directlyReadsHeap_eq_identifier (n : Identifier) :
  directlyReadsHeap (.Identifier n) = false := by rw [directlyReadsHeap.eq_def]

mutual
def directlyWritesHeapMd (e : StmtExprMd) : Bool := directlyWritesHeap e.val
  termination_by sizeOf e
  decreasing_by cases e; term_by_mem

def directlyWritesHeap (body : StmtExpr) : Bool :=
  match _h : body with
  | .Assign [⟨.FieldSelect _ _, _⟩] _ => true
  | .New _ => true
  | .Return (some v) => directlyWritesHeapMd v
  | .Block stmts _ => stmts.attach.any (fun ⟨s, _⟩ => directlyWritesHeapMd s)
  | .IfThenElse c t e =>
    directlyWritesHeapMd c || directlyWritesHeapMd t ||
    (match e with | some e => directlyWritesHeapMd e | none => false)
  | .While c invs d body =>
    directlyWritesHeapMd c || directlyWritesHeapMd body ||
    invs.attach.any (fun ⟨i, _⟩ => directlyWritesHeapMd i) ||
    (match d with | some d => directlyWritesHeapMd d | none => false)
  | .LocalVariable _ _ (some init) => directlyWritesHeapMd init
  | .Assign targets v =>
    targets.attach.any (fun ⟨t, _⟩ => directlyWritesHeapMd t) || directlyWritesHeapMd v
  | .StaticCall _ args => args.attach.any (fun ⟨a, _⟩ => directlyWritesHeapMd a)
  | .InstanceCall target _ args =>
    directlyWritesHeapMd target || args.attach.any (fun ⟨a, _⟩ => directlyWritesHeapMd a)
  | .PrimitiveOp _ args => args.attach.any (fun ⟨a, _⟩ => directlyWritesHeapMd a)
  | .PureFieldUpdate t _ v => directlyWritesHeapMd t || directlyWritesHeapMd v
  | .ReferenceEquals l r => directlyWritesHeapMd l || directlyWritesHeapMd r
  | .AsType t _ => directlyWritesHeapMd t
  | .IsType t _ => directlyWritesHeapMd t
  | .Old v => directlyWritesHeapMd v
  | .Fresh v => directlyWritesHeapMd v
  | .Assigned n => directlyWritesHeapMd n
  | .Assert c => directlyWritesHeapMd c
  | .Assume c => directlyWritesHeapMd c
  | .Forall _ trigger b =>
    (match trigger with | some t => directlyWritesHeapMd t | none => false) || directlyWritesHeapMd b
  | .Exists _ trigger b =>
    (match trigger with | some t => directlyWritesHeapMd t | none => false) || directlyWritesHeapMd b
  | .ProveBy v p => directlyWritesHeapMd v || directlyWritesHeapMd p
  | .ContractOf _ f => directlyWritesHeapMd f
  | _ => false
  termination_by sizeOf body
  decreasing_by all_goals (simp_wf; try term_by_mem)
end

@[simp] public theorem directlyWritesHeap_eq_new (name : Identifier) :
  directlyWritesHeap (.New name) = true := by rw [directlyWritesHeap.eq_def]

@[simp] public theorem directlyWritesHeap_eq_literalBool (b : Bool) :
  directlyWritesHeap (.LiteralBool b) = false := by rw [directlyWritesHeap.eq_def]

@[simp] public theorem directlyWritesHeap_eq_literalInt (i : Int) :
  directlyWritesHeap (.LiteralInt i) = false := by rw [directlyWritesHeap.eq_def]

@[simp] public theorem directlyWritesHeap_eq_identifier (n : Identifier) :
  directlyWritesHeap (.Identifier n) = false := by rw [directlyWritesHeap.eq_def]

/-- Does a procedure body directly access the heap (read or write)? -/
def directlyAccessesHeap (body : StmtExpr) : Bool :=
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

mutual
/-- Extract callee names from a WithMetadata StmtExpr (wrapper for termination). -/
def calleesInExprMd (e : StmtExprMd) : List String := calleesInExpr e.val
  termination_by sizeOf e
  decreasing_by cases e; term_by_mem

/-- Extract callee names from a StmtExpr (StaticCall and InstanceCall) -/
def calleesInExpr (body : StmtExpr) : List String :=
  match _h : body with
  | .StaticCall callee args =>
    [callee.text] ++ args.attach.flatMap (fun ⟨a, _⟩ => calleesInExprMd a)
  | .InstanceCall _ callee args =>
    [callee.text] ++ args.attach.flatMap (fun ⟨a, _⟩ => calleesInExprMd a)
  | .Return (some v) => calleesInExprMd v
  | .Block stmts _ => stmts.attach.flatMap (fun ⟨s, _⟩ => calleesInExprMd s)
  | .IfThenElse c t e =>
    calleesInExprMd c ++ calleesInExprMd t ++
    (match e with | some e => calleesInExprMd e | none => [])
  | .While c _ _ body => calleesInExprMd c ++ calleesInExprMd body
  | .LocalVariable _ _ (some init) => calleesInExprMd init
  | .Assign targets v =>
    targets.attach.flatMap (fun ⟨t, _⟩ => calleesInExprMd t) ++ calleesInExprMd v
  | .FieldSelect target _ => calleesInExprMd target
  | .PrimitiveOp _ args => args.attach.flatMap (fun ⟨a, _⟩ => calleesInExprMd a)
  | .PureFieldUpdate t _ v => calleesInExprMd t ++ calleesInExprMd v
  | .ReferenceEquals l r => calleesInExprMd l ++ calleesInExprMd r
  | .AsType t _ => calleesInExprMd t
  | .IsType t _ => calleesInExprMd t
  | .Forall _ trigger b =>
    (match trigger with | some t => calleesInExprMd t | none => []) ++ calleesInExprMd b
  | .Exists _ trigger b =>
    (match trigger with | some t => calleesInExprMd t | none => []) ++ calleesInExprMd b
  | .Old v => calleesInExprMd v
  | .Fresh v => calleesInExprMd v
  | .Assigned n => calleesInExprMd n
  | .Assert c => calleesInExprMd c
  | .Assume c => calleesInExprMd c
  | .ProveBy v p => calleesInExprMd v ++ calleesInExprMd p
  | .ContractOf _ f => calleesInExprMd f
  | _ => []
  termination_by sizeOf body
  decreasing_by all_goals (simp_wf; try term_by_mem)
end

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

/-- transitiveClose result always contains the initial set -/
public theorem transitiveClose_contains_initial
  (info : List (String × Bool × List String))
  (fuel : Nat) (current : List String)
  (n : String) (h : n ∈ current)
  (hInfo : n ∈ info.map (·.1)) :
  n ∈ transitiveClose info fuel current :=
  direct_subset_transitive info fuel current n h hInfo

/-- fixpointStep result is a subset of info names -/
public theorem fixpointStep_subset_info
  (info : List (String × Bool × List String))
  (current : List String) (n : String)
  (h : n ∈ fixpointStep info current) :
  n ∈ info.map (·.1) := by
  simp only [fixpointStep] at h
  rw [List.mem_filterMap] at h
  obtain ⟨entry, hEntry, hSome⟩ := h
  have : n = entry.1 := by
    split at hSome <;> simp_all
  subst this
  exact List.mem_map.mpr ⟨entry, hEntry, rfl⟩

/-- transitiveClose result is always a subset of info names -/
public theorem transitiveClose_subset_info
  (info : List (String × Bool × List String))
  (fuel : Nat) (current : List String)
  (hCurrent : ∀ n ∈ current, n ∈ info.map (·.1))
  (n : String) (h : n ∈ transitiveClose info fuel current) :
  n ∈ info.map (·.1) := by
  induction fuel generalizing current with
  | zero => exact hCurrent n h
  | succ fuel' ih =>
    simp only [transitiveClose] at h
    by_cases heq : ((fixpointStep info current).length == current.length) = true
    · simp [heq] at h; exact hCurrent n h
    · simp [heq] at h
      exact ih (fixpointStep info current) (fun m hm => fixpointStep_subset_info info current m hm) h

/-! ## Body translation model: translation patterns

The model describes what Core statements each Laurel statement produces.
Rather than modeling the exact Core AST, we model the *pattern* —
what kind of Core statement(s) each Laurel construct generates.
-/

/-- The pattern of Core statements a Laurel statement translates to -/
inductive TranslationPattern where
  | expr (refs : List String)
  | callWithPropagation (target : String) (outputs : List String)
  | block (children : List TranslationPattern)
  | ite (cond thenBranch elseBranch : TranslationPattern)
  | loop (cond body : TranslationPattern)
  | returnExpr (value : TranslationPattern)
  | returnCall (target : String) (outputs : List String)
  | initVar (name : String) (value : Option TranslationPattern)
  | skip
  deriving Inhabited

/-- Predict the translation pattern for a Laurel statement.
    Split into non-partial `predictPatternTop` (provable) and
    partial `predictPattern` (for recursive cases). -/
def predictPatternTop (isFunction : String → Bool) (expr : StmtExpr) : Option TranslationPattern :=
  match expr with
  | .StaticCall callee _ =>
    if isFunction callee.text then none  -- needs recursion into args
    else some (.callWithPropagation callee.text ["$result"])
  | .InstanceCall _ callee _ =>
    if isFunction callee.text then none
    else some (.callWithPropagation callee.text ["$result"])
  | .Return (some v) =>
    match v.val with
    | .StaticCall callee _ =>
      if isFunction callee.text then none
      else some (.returnCall callee.text ["$result"])
    | .InstanceCall _ callee _ =>
      if isFunction callee.text then none
      else some (.returnCall callee.text ["$result"])
    | _ => none  -- needs recursion
  | .LocalVariable name _ none => some (.initVar name.text none)
  | .Assign [⟨.Identifier targetId, _⟩] value =>
    match value.val with
    | .StaticCall callee _ =>
      if isFunction callee.text then none
      else some (.callWithPropagation callee.text [targetId.text, "$result"])
    | .InstanceCall _ callee _ =>
      if isFunction callee.text then none
      else some (.callWithPropagation callee.text [targetId.text, "$result"])
    | _ => none  -- pure assignment, needs recursion for RHS
  | .Return none => some .skip
  | .LiteralBool _ | .LiteralInt _ | .LiteralString _ | .LiteralDecimal _ => some (.expr [])
  | .Identifier name => some (.expr [name.text])
  | .New className => some (.expr ["increment", className.text])
  | _ => none  -- needs recursion

mutual
/-- Predict pattern for a WithMetadata StmtExpr (wrapper for termination). -/
def predictPatternMd (isFunction : String → Bool) (e : StmtExprMd) : TranslationPattern :=
  predictPattern isFunction e.val
  termination_by sizeOf e
  decreasing_by cases e; term_by_mem

def predictPattern (isFunction : String → Bool) (expr : StmtExpr) : TranslationPattern :=
  match _h : expr with
  | .LiteralBool _ | .LiteralInt _ | .LiteralString _ | .LiteralDecimal _ => .expr []
  | .Identifier name => .expr [name.text]
  | .PrimitiveOp _ args =>
    .expr (args.attach.flatMap fun ⟨a, _⟩ => match predictPatternMd isFunction a with
      | .expr refs => refs | _ => [])
  | .FieldSelect target _ =>
    .expr (["readField"] ++ match predictPatternMd isFunction target with
      | .expr refs => refs | _ => [])
  | .StaticCall callee args =>
    if isFunction callee.text then
      .expr ([callee.text] ++ args.attach.flatMap fun ⟨a, _⟩ => match predictPatternMd isFunction a with
        | .expr refs => refs | _ => [])
    else .callWithPropagation callee.text ["$result"]
  | .InstanceCall _ callee args =>
    if isFunction callee.text then
      .expr ([callee.text] ++ args.attach.flatMap fun ⟨a, _⟩ => match predictPatternMd isFunction a with
        | .expr refs => refs | _ => [])
    else .callWithPropagation callee.text ["$result"]
  | .Block stmts _ => .block (stmts.attach.map fun ⟨s, _⟩ => predictPatternMd isFunction s)
  | .IfThenElse cond thenB elseB =>
    .ite (predictPatternMd isFunction cond)
         (predictPatternMd isFunction thenB)
         (match elseB with | some e => predictPatternMd isFunction e | none => .skip)
  | .While cond _ _ body =>
    .loop (predictPatternMd isFunction cond) (predictPatternMd isFunction body)
  | .Return (some v) =>
    match v.val with
    | .StaticCall callee _ =>
      if isFunction callee.text then .returnExpr (predictPatternMd isFunction v)
      else .returnCall callee.text ["$result"]
    | .InstanceCall _ callee _ =>
      if isFunction callee.text then .returnExpr (predictPatternMd isFunction v)
      else .returnCall callee.text ["$result"]
    | _ => .returnExpr (predictPatternMd isFunction v)
  | .Return none => .skip
  | .LocalVariable name _ (some init) =>
    .initVar name.text (some (predictPatternMd isFunction init))
  | .LocalVariable name _ none =>
    .initVar name.text none
  | .Assign [⟨.Identifier targetId, _⟩] value =>
    match value.val with
    | .StaticCall callee _ =>
      if isFunction callee.text then .expr [targetId.text]
      else .callWithPropagation callee.text [targetId.text, "$result"]
    | .InstanceCall _ callee _ =>
      if isFunction callee.text then .expr [targetId.text]
      else .callWithPropagation callee.text [targetId.text, "$result"]
    | _ => .expr [targetId.text]
  | .New className => .expr ["increment", className.text]
  | _ => .skip
  termination_by sizeOf expr
  decreasing_by all_goals (simp_wf; try term_by_mem)
end

/-! ### Translation pattern properties (proven via predictPatternTop) -/

/-- Static procedure calls always produce callWithPropagation -/
public theorem static_proc_call_has_propagation
  (isFunction : String → Bool) (callee : Identifier) (args : List (WithMetadata StmtExpr))
  (hNotFunc : isFunction callee.text = false) :
  predictPatternTop isFunction (.StaticCall callee args) =
    some (.callWithPropagation callee.text ["$result"]) := by
  simp [predictPatternTop, hNotFunc]

/-- Instance procedure calls always produce callWithPropagation -/
public theorem instance_proc_call_has_propagation
  (isFunction : String → Bool) (target : WithMetadata StmtExpr) (callee : Identifier)
  (args : List (WithMetadata StmtExpr))
  (hNotFunc : isFunction callee.text = false) :
  predictPatternTop isFunction (.InstanceCall target callee args) =
    some (.callWithPropagation callee.text ["$result"]) := by
  simp [predictPatternTop, hNotFunc]

/-- Return with static procedure call produces returnCall -/
public theorem return_static_proc_call_pattern
  (isFunction : String → Bool) (callee : Identifier) (args : List (WithMetadata StmtExpr))
  (md : MetaData)
  (hNotFunc : isFunction callee.text = false) :
  predictPatternTop isFunction (.Return (some ⟨.StaticCall callee args, md⟩)) =
    some (.returnCall callee.text ["$result"]) := by
  simp [predictPatternTop, hNotFunc]

/-- Local variable without initializer -/
public theorem local_var_no_init
  (isFunction : String → Bool) (name : Identifier) (ty : WithMetadata HighType) :
  predictPatternTop isFunction (.LocalVariable name ty none) =
    some (.initVar name.text none) := by
  simp [predictPatternTop]

/-- Assignment from static procedure call produces callWithPropagation with target variable -/
public theorem assign_static_proc_call_pattern
  (isFunction : String → Bool) (targetId : Identifier) (targetMd : MetaData)
  (callee : Identifier) (args : List (WithMetadata StmtExpr)) (valueMd : MetaData)
  (hNotFunc : isFunction callee.text = false) :
  predictPatternTop isFunction (.Assign [⟨.Identifier targetId, targetMd⟩] ⟨.StaticCall callee args, valueMd⟩) =
    some (.callWithPropagation callee.text [targetId.text, "$result"]) := by
  simp [predictPatternTop, hNotFunc]

/-- Assignment from instance procedure call produces callWithPropagation with target variable -/
public theorem assign_instance_proc_call_pattern
  (isFunction : String → Bool) (targetId : Identifier) (targetMd : MetaData)
  (target : WithMetadata StmtExpr) (callee : Identifier) (args : List (WithMetadata StmtExpr)) (valueMd : MetaData)
  (hNotFunc : isFunction callee.text = false) :
  predictPatternTop isFunction (.Assign [⟨.Identifier targetId, targetMd⟩] ⟨.InstanceCall target callee args, valueMd⟩) =
    some (.callWithPropagation callee.text [targetId.text, "$result"]) := by
  simp [predictPatternTop, hNotFunc]

/-- All names referenced by a translation pattern -/
@[simp] def TranslationPattern.referencedNames : TranslationPattern → List String
  | .expr refs => refs
  | .callWithPropagation target outputs => [target] ++ outputs
  | .block children => children.flatMap (·.referencedNames)
  | .ite c t e => c.referencedNames ++ t.referencedNames ++ e.referencedNames
  | .loop c b => c.referencedNames ++ b.referencedNames
  | .returnExpr v => v.referencedNames
  | .returnCall target outputs => [target] ++ outputs
  | .initVar name v => [name] ++ (match v with | some p => p.referencedNames | none => [])
  | .skip => []

public theorem referencedNames_callWithPropagation (target : String) (outputs : List String) :
  TranslationPattern.referencedNames (.callWithPropagation target outputs) = [target] ++ outputs := by
  simp [TranslationPattern.referencedNames]

public theorem referencedNames_returnCall (target : String) (outputs : List String) :
  TranslationPattern.referencedNames (.returnCall target outputs) = [target] ++ outputs := by
  simp [TranslationPattern.referencedNames]

public theorem referencedNames_initVar_some (name : String) (p : TranslationPattern) :
  TranslationPattern.referencedNames (.initVar name (some p)) = [name] ++ p.referencedNames := by
  simp [TranslationPattern.referencedNames]

public theorem referencedNames_initVar_none (name : String) :
  TranslationPattern.referencedNames (.initVar name none) = [name] := by
  simp [TranslationPattern.referencedNames]

/-! ### Proven equation for predictPattern (was axiom, now proven via mutual .eq_def) -/

/-- Local variable with initializer — proven via mutual definition equation -/
public theorem predictPattern_local_var_init
  (isFunction : String → Bool) (name : Identifier) (ty : WithMetadata HighType)
  (init : WithMetadata StmtExpr) :
  predictPattern isFunction (.LocalVariable name ty (some init)) =
    .initVar name.text (some (predictPattern isFunction init.val)) := by
  rw [predictPattern.eq_def]
  simp [predictPatternMd.eq_def]

/-! ## Body translation model
This enables P1 (name consistency): every referenced name
should exist as a declaration.
-/

/-! ## Body translation model

Names referenced in a Laurel expression after translation.
-/

mutual
/-- Names referenced in a WithMetadata StmtExpr. -/
def referencedNamesInExprMdInner (e : StmtExprMd) : List String := referencedNamesInExprVal e.val
  termination_by sizeOf e
  decreasing_by cases e; term_by_mem

/-- Names referenced in a Laurel expression. -/
def referencedNamesInExprVal (expr : StmtExpr) : List String :=
  match _h : expr with
  | .StaticCall callee args =>
    [callee.text] ++ args.attach.flatMap (fun ⟨a, _⟩ => referencedNamesInExprMdInner a)
  | .InstanceCall _ callee args =>
    [callee.text] ++ args.attach.flatMap (fun ⟨a, _⟩ => referencedNamesInExprMdInner a)
  | .FieldSelect target _ =>
    ["readField"] ++ referencedNamesInExprMdInner target
  | .Assign targets v =>
    targets.attach.flatMap (fun ⟨t, _⟩ => referencedNamesInExprMdInner t) ++ referencedNamesInExprMdInner v
  | .New _ => ["increment"]
  | .LocalVariable _ _ (some init) => referencedNamesInExprMdInner init
  | .Block stmts _ => stmts.attach.flatMap (fun ⟨s, _⟩ => referencedNamesInExprMdInner s)
  | .IfThenElse c t (some el) =>
    referencedNamesInExprMdInner c ++ referencedNamesInExprMdInner t ++ referencedNamesInExprMdInner el
  | .IfThenElse c t none =>
    referencedNamesInExprMdInner c ++ referencedNamesInExprMdInner t
  | .While c _ _ body =>
    referencedNamesInExprMdInner c ++ referencedNamesInExprMdInner body
  | .Return (some v) => referencedNamesInExprMdInner v
  | _ => []
  termination_by sizeOf expr
  decreasing_by all_goals (simp_wf; try term_by_mem)
end

/-- Proven: FieldSelect case. -/
public theorem referencedNamesInExprVal_fieldSelect (target : WithMetadata StmtExpr) (fieldId : Identifier) :
  referencedNamesInExprVal (.FieldSelect target fieldId) = ["readField"] ++ referencedNamesInExprVal target.val := by
  rw [referencedNamesInExprVal.eq_def]
  simp [referencedNamesInExprMdInner.eq_def]

/-- Proven: New case. -/
public theorem referencedNamesInExprVal_new (className : Identifier) :
  referencedNamesInExprVal (.New className) = ["increment"] := by
  rw [referencedNamesInExprVal.eq_def]

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

/-- Translate a Laurel type to its Core type name.
    Mirrors `translateType` in LaurelToCoreTranslator.lean.
    Note: UserDefined types need the SemanticModel to distinguish
    composites from datatypes. Without the model, we conservatively
    map all UserDefined to "Composite". -/
@[expose] def coreTypeName (ty : HighType) : String :=
  match ty with
  | .TInt => "int"
  | .TBool => "bool"
  | .TString => "string"
  | .TReal => "real"
  | .TVoid => "bool"
  | .THeap => "Heap"
  | .TTypedField _ => "Field"
  | .TCore s => s
  | .Unknown => "Any"
  | .UserDefined name => name.text
  | _ => "Composite"

/-- Full Core monomorphic type for a Laurel HighType (handles Map, Sequence, Set). -/
@[expose] def coreMonoType (ty : HighType) : Lambda.LMonoTy :=
  match ty with
  | .TMap k v => .tcons "Map" [coreMonoType k.val, coreMonoType v.val]
  | .TSequence e => .tcons "Sequence" [coreMonoType e.val]
  | .TSet e => .tcons "Map" [coreMonoType e.val, .bool]
  | _ => .tcons (coreTypeName ty) []

/-- Core type name properties -/

public theorem coreTypeName_int : coreTypeName .TInt = "int" := by simp [coreTypeName]
public theorem coreTypeName_bool : coreTypeName .TBool = "bool" := by simp [coreTypeName]
public theorem coreTypeName_string : coreTypeName .TString = "string" := by simp [coreTypeName]

@[simp] public theorem coreMonoType_int : coreMonoType .TInt = .tcons "int" [] := rfl
@[simp] public theorem coreMonoType_bool : coreMonoType .TBool = .tcons "bool" [] := rfl
@[simp] public theorem coreMonoType_string : coreMonoType .TString = .tcons "string" [] := rfl
@[simp] public theorem coreMonoType_eq_tcons (ty : HighType)
    (h : ∀ k v, ty ≠ .TMap k v) (h2 : ∀ e, ty ≠ .TSequence e) (h3 : ∀ e, ty ≠ .TSet e) :
    coreMonoType ty = .tcons (coreTypeName ty) [] := by
  sorry
public theorem coreTypeName_real : coreTypeName .TReal = "real" := by simp [coreTypeName]
public theorem coreTypeName_void : coreTypeName .TVoid = "bool" := by simp [coreTypeName]
public theorem coreTypeName_heap : coreTypeName .THeap = "Heap" := by simp [coreTypeName]

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

/-! ## P7: Frame condition model -/

/-- Does a procedure have $heap in its outputs? -/
@[simp, expose] def hasHeapOutput (proc : Procedure) : Bool :=
  proc.outputs.any (fun p => p.name.text == "$heap")

/-- The structure of a frame condition -/
inductive FrameConditionShape where
  | fullFrame        -- everything preserved (no modifies, but has $heap)
  | partialFrame (modifiedExprs : Nat)  -- some objects excluded
  | noFrame          -- no $heap output, no frame needed

/-- Predict what frame condition shape a procedure should have -/
@[expose] def expectedFrameShape (proc : Procedure) : FrameConditionShape :=
  if !hasHeapOutput proc then .noFrame
  else match proc.body with
    | .Opaque _ _ modif =>
      if modif.isEmpty then .fullFrame
      else .partialFrame modif.length
    | _ => .fullFrame  -- transparent/abstract with $heap get full frame

/-- A procedure with $heap output always gets a frame condition -/
public theorem heap_output_implies_frame (proc : Procedure)
  (hHeap : hasHeapOutput proc = true) :
  expectedFrameShape proc ≠ .noFrame := by
  have hNeg : !hasHeapOutput proc = false := by rw [hHeap]; rfl
  simp [expectedFrameShape, hHeap]
  split <;> (try split) <;> simp_all

-- TODO: modifies_implies_partial_frame (simp normalizes
-- FrameConditionShape ≠ in a way that makes the proof tricky)

/-- A procedure with modifies clause gets a partial frame -/
public theorem modifies_implies_partial_frame (proc : Procedure)
  (postconds : List (WithMetadata StmtExpr))
  (impl : Option (WithMetadata StmtExpr))
  (modif : List (WithMetadata StmtExpr))
  (hBody : proc.body = .Opaque postconds impl modif)
  (hModif : !modif.isEmpty = true)
  (hHeap : hasHeapOutput proc = true) :
  expectedFrameShape proc ≠ .noFrame ∧ expectedFrameShape proc ≠ .fullFrame := by
  constructor
  · exact heap_output_implies_frame proc hHeap
  · -- Need: expectedFrameShape proc ≠ .fullFrame
    -- Use same approach as heap_output_implies_frame but for fullFrame
    have hNeg : !hasHeapOutput proc = false := by rw [hHeap]; rfl
    simp [expectedFrameShape, hNeg, hBody]
    cases modif with
    | nil => simp at hModif
    | cons h t =>
      split <;> simp_all

/-- A procedure without $heap output needs no frame -/
public theorem no_heap_no_frame (proc : Procedure)
  (hNoHeap : hasHeapOutput proc = false) :
  expectedFrameShape proc = .noFrame := by
  have hNeg : !hasHeapOutput proc = true := by rw [hNoHeap]; rfl
  simp_all [expectedFrameShape]

end -- public section

/-! ## Full translator model

`translateModel` produces a `Core.Program` from a Laurel `Program`.
This is the executable specification — when it disagrees with `translate`,
we investigate who is right.
-/

/-- Build the ExceptionResult datatype declaration -/
@[expose] public def modelExceptionResultDecl : Core.Decl :=
  Core.Decl.type (.data [{
    name := "ExceptionResult"
    typeArgs := []
    constrs := [
      { name := ⟨"Success", ()⟩, args := [], testerName := "ExceptionResult..isSuccess" },
      { name := ⟨"Failure", ()⟩, args := [], testerName := "ExceptionResult..isFailure" }
    ]
    constrs_ne := rfl
  }]) .empty

/-- Build the declaration list structure (names and order only).
    This is the first step toward a full translateModel. -/
public def modelDeclNames (program : Program) : List String :=
  let withDefs := { program with
    staticProcedures := coreDefinitionsForLaurel.staticProcedures ++ program.staticProcedures
    types := coreDefinitionsForLaurel.types ++ program.types
  }
  expectedDeclNames withDefs

/-- Classify each expected declaration by kind -/
public inductive DeclClass where
  | datatype | axiomDecl | constant | function | procedure
  deriving Repr, BEq

/-- Predict the declaration class for each name -/
public def classifyDecls (program : Program) : List (String × DeclClass) :=
  let withDefs := { program with
    staticProcedures := coreDefinitionsForLaurel.staticProcedures ++ program.staticProcedures
    types := coreDefinitionsForLaurel.types ++ program.types
  }
  let procs := expectedProcedureNames withDefs |>.map (·, .procedure)
  let funcs := expectedFunctionNames withDefs |>.map (·, .function)
  let types := expectedDatatypeNames withDefs |>.map (·, .datatype)
  let axioms := expectedAxiomNames withDefs |>.map (·, .axiomDecl)
  types ++ axioms ++ funcs ++ procs

end Strata.Laurel

/-! ## Expression translation model

Maps Laurel expressions to Core expressions. This is a pure function
(no monad, no SemanticModel) that captures the structural translation.

Split into `translateExprTop` (non-recursive, provable) and
`translateExprModel` (partial, for recursive cases).
-/

namespace Strata.Laurel

/-- Non-recursive expression translation — provable cases -/
public def translateExprTop (expr : StmtExpr) : Option Core.Expression.Expr :=
  match expr with
  | .LiteralBool b => some (.const () (.boolConst b))
  | .LiteralInt i => some (.const () (.intConst i))
  | .LiteralString s => some (.const () (.strConst s))
  | .LiteralDecimal d => some (.const () (.realConst (Decimal.toRat d)))
  | .Identifier name => some (.fvar () ⟨name.text, ()⟩ none)
  | .PrimitiveOp .Eq [e1, e2] => none  -- needs recursion
  | .New _ => some (.const () (.boolConst true))  -- placeholder
  | _ => none  -- needs recursion

/-- Proven: LiteralBool translates to boolConst -/
public theorem translateExpr_literalBool (b : Bool) :
  translateExprTop (.LiteralBool b) = some (.const () (.boolConst b)) := by
  simp [translateExprTop]

/-- Proven: LiteralInt translates to intConst -/
public theorem translateExpr_literalInt (i : Int) :
  translateExprTop (.LiteralInt i) = some (.const () (.intConst i)) := by
  simp [translateExprTop]

/-- Proven: LiteralString translates to strConst -/
public theorem translateExpr_literalString (s : String) :
  translateExprTop (.LiteralString s) = some (.const () (.strConst s)) := by
  simp [translateExprTop]

/-- Proven: Identifier translates to fvar -/
public theorem translateExpr_identifier (name : Identifier) :
  translateExprTop (.Identifier name) = some (.fvar () ⟨name.text, ()⟩ none) := by
  simp [translateExprTop]

/-- Proven: literals always produce a const expression -/
public theorem translateExpr_literalBool_is_const (b : Bool) :
  ∃ c, translateExprTop (.LiteralBool b) = some (.const () c) := by
  exact ⟨.boolConst b, by simp [translateExprTop]⟩

/-- Proven: identifiers always produce an fvar expression -/
public theorem translateExpr_identifier_preserves_name (name : Identifier) :
  ∃ e, translateExprTop (.Identifier name) = some e ∧
    e = .fvar () ⟨name.text, ()⟩ none := by
  exact ⟨_, by simp [translateExprTop], rfl⟩

/-- Replace free variable with bound variable (de Bruijn index) in a Core expression. -/
public def replaceFvarWithBvar (name : String) (idx : Nat) : Core.Expression.Expr → Core.Expression.Expr
  | .fvar _ ⟨n, _⟩ _ => if n == name then .bvar () idx else .fvar () ⟨n, ()⟩ none
  | .app _ f a => .app () (replaceFvarWithBvar name idx f) (replaceFvarWithBvar name idx a)
  | .eq _ l r => .eq () (replaceFvarWithBvar name idx l) (replaceFvarWithBvar name idx r)
  | .ite _ c t e => .ite () (replaceFvarWithBvar name idx c) (replaceFvarWithBvar name idx t) (replaceFvarWithBvar name idx e)
  | .quant _ k n ty trigger b => .quant () k n ty (replaceFvarWithBvar name (idx+1) trigger) (replaceFvarWithBvar name (idx+1) b)
  | other => other

/-- Replace $heap with $heap_in in a Core expression (for old() translation). -/
public def replaceHeapVar : Core.Expression.Expr → Core.Expression.Expr
  | .fvar _ ⟨name, nmd⟩ ty => .fvar () ⟨if name == "$heap" then "$heap_in" else name, nmd⟩ ty
  | .app _ f a => .app () (replaceHeapVar f) (replaceHeapVar a)
  | .eq _ l r => .eq () (replaceHeapVar l) (replaceHeapVar r)
  | .ite _ c t e => .ite () (replaceHeapVar c) (replaceHeapVar t) (replaceHeapVar e)
  | .quant _ k n ty trigger b => .quant () k n ty (replaceHeapVar trigger) (replaceHeapVar b)
  | other => other

/-- Check if a Laurel expression is syntactically a real-number expression. -/
public def isRealExpr : StmtExpr → Bool
  | .LiteralDecimal _ => true
  | .PrimitiveOp _ args => args.attach.any (fun ⟨a, _⟩ => isRealExpr a.val)
  | .IfThenElse _ t _ => isRealExpr t.val
  | _ => false
termination_by e => sizeOf e
decreasing_by all_goals (simp_wf; first | term_by_mem | sorry)

public def isRealExprMd (e : StmtExprMd) : Bool := isRealExpr e.val

/-- A type environment mapping variable names to their Laurel types. -/
public abbrev TypeEnv := List (String × HighType)

/-- Look up a variable's type in the environment. -/
public def TypeEnv.lookup (env : TypeEnv) (name : String) : Option HighType :=
  (env.find? (·.1 == name)).map (·.2)

/-- Check if an expression has real type given a type environment. -/
public def exprIsReal (env : TypeEnv) : StmtExpr → Bool
  | .LiteralDecimal _ => true
  | .Identifier name => match env.lookup name.text with | some .TReal => true | _ => false
  | .PrimitiveOp _ (head :: _) => exprIsReal env head.val
  | .FieldSelect _ _ => false  -- fields are int/bool/string, not real
  | _ => false

mutual
def translateExprModelMd (e : StmtExprMd) : Core.Expression.Expr := translateExprModel e.val
  termination_by sizeOf e
  decreasing_by cases e; term_by_mem

public def translateExprModel
  (expr : StmtExpr) : Core.Expression.Expr :=
  match _h : expr with
  | .LiteralBool b => .const () (.boolConst b)
  | .LiteralInt i => .const () (.intConst i)
  | .LiteralString s => .const () (.strConst s)
  | .LiteralDecimal d => .const () (.realConst (Decimal.toRat d))
  | .Identifier name => .fvar () ⟨name.text, ()⟩ none
  | .PrimitiveOp .Eq [e1, e2] =>
    .eq () (translateExprModelMd e1) (translateExprModelMd e2)
  | .PrimitiveOp .Neq [e1, e2] =>
    .app () (.op () ⟨"Bool.Not", ()⟩ none) (.eq () (translateExprModelMd e1) (translateExprModelMd e2))
  | .PrimitiveOp .Not [e] =>
    .app () (.op () ⟨"Bool.Not", ()⟩ none) (translateExprModelMd e)
  | .PrimitiveOp .Neg [e] =>
    let opName := if exprIsReal [] e.val then "Real.Neg" else "Int.Neg"
    .app () (.op () ⟨opName, ()⟩ none) (translateExprModelMd e)
  | .PrimitiveOp .AndThen [e1, e2] =>
    .ite () (translateExprModelMd e1) (translateExprModelMd e2) (.boolConst () false)
  | .PrimitiveOp .OrElse [e1, e2] =>
    .ite () (translateExprModelMd e1) (.boolConst () true) (translateExprModelMd e2)
  | .PrimitiveOp .Implies [e1, e2] =>
    .ite () (translateExprModelMd e1) (translateExprModelMd e2) (.boolConst () true)
  | .PrimitiveOp op [e1, e2] =>
    let isReal := exprIsReal [] e1.val || exprIsReal [] e2.val
    let opName := match op with
      | .Add => if isReal then "Real.Add" else "Int.Add"
      | .Sub => if isReal then "Real.Sub" else "Int.Sub"
      | .Mul => if isReal then "Real.Mul" else "Int.Mul"
      | .Div => if isReal then "Real.Div" else "Int.SafeDiv"
      | .Mod => "Int.SafeMod"
      | .DivT => "Int.SafeDivT" | .ModT => "Int.SafeModT"
      | .Lt => if isReal then "Real.Lt" else "Int.Lt"
      | .Leq => if isReal then "Real.Le" else "Int.Le"
      | .Gt => if isReal then "Real.Gt" else "Int.Gt"
      | .Geq => if isReal then "Real.Ge" else "Int.Ge"
      | .And => "Bool.And" | .Or => "Bool.Or"
      | .StrConcat => "Str.Concat"
      | _ => "op"
    .app () (.app () (.op () ⟨opName, ()⟩ none) (translateExprModelMd e1)) (translateExprModelMd e2)
  | .StaticCall callee args =>
    args.attach.foldl (fun acc ⟨a, _⟩ => .app () acc (translateExprModelMd a))
      (.op () ⟨callee.text, ()⟩ none)
  | .InstanceCall target callee args =>
    -- Instance call as expression: op(qualName) applied to target, $heap, args
    let allArgs := translateExprModelMd target :: (.fvar () ⟨"$heap", ()⟩ none) ::
      (args.attach.map fun ⟨a, _⟩ => translateExprModelMd a)
    allArgs.foldl (fun acc arg => .app () acc arg) (.op () ⟨callee.text, ()⟩ none)
  | .IfThenElse cond thenB (some elseB) =>
    .ite () (translateExprModelMd cond) (translateExprModelMd thenB) (translateExprModelMd elseB)
  | .Block [single] _ => translateExprModelMd single
  | .Block (⟨.IfThenElse cond thenB (some elseB), _⟩ :: rest) label =>
    -- if-else followed by rest: ite(cond, then, else) — rest is dead code after if-else with returns
    .ite () (translateExprModelMd cond) (translateExprModelMd thenB) (translateExprModelMd elseB)
  | .Block (⟨.IfThenElse cond thenB none, _⟩ :: rest) label =>
    -- if-no-else followed by rest: ite(cond, then, rest)
    .ite () (translateExprModelMd cond) (translateExprModelMd thenB)
      (translateExprModel (.Block rest label))
  | .Return (some v) => translateExprModelMd v
  | .FieldSelect target fieldName =>
    let cleanFieldName := if fieldName.text.endsWith ":bool" then fieldName.text.dropRight 5
      else if fieldName.text.endsWith ":string" then fieldName.text.dropRight 7
      else
        -- Check for constrained type suffix like :int32, :int16, etc.
        match fieldName.text.splitOn ":" with
        | [name, _] => name
        | _ => fieldName.text
    let readExpr : Core.Expression.Expr :=
      .app () (.app () (.app () (.op () ⟨"readField", ()⟩ none) (.fvar () ⟨"$heap", ()⟩ none)) (translateExprModelMd target)) (.op () ⟨cleanFieldName, ()⟩ none)
    let boxFn := if fieldName.text.endsWith ":bool" then "Box..boolVal!"
      else if fieldName.text.endsWith ":string" then "Box..stringVal!"
      else
        match fieldName.text.splitOn ":" with
        | [_, constrainedName] => "read" ++ constrainedName.capitalize
        | _ => "Box..intVal!"
    .app () (.op () ⟨boxFn, ()⟩ none) readExpr
  | .Forall ⟨name, _⟩ trigger body =>
    let triggerExpr := match trigger with
      | some t => replaceFvarWithBvar name.text 0 (translateExprModelMd t)
      | none => .op () ⟨"noTrigger", ()⟩ none
    .quant () .all name.text none triggerExpr (replaceFvarWithBvar name.text 0 (translateExprModelMd body))
  | .Exists ⟨name, _⟩ trigger body =>
    let triggerExpr := match trigger with
      | some t => replaceFvarWithBvar name.text 0 (translateExprModelMd t)
      | none => .op () ⟨"noTrigger", ()⟩ none
    .quant () .exist name.text none triggerExpr (replaceFvarWithBvar name.text 0 (translateExprModelMd body))
  | .Old v =>
    -- old(expr) translates expr with $heap replaced by $heap_in
    replaceHeapVar (translateExprModelMd v)
  | _ => .const () (.boolConst true)
  termination_by sizeOf expr
  decreasing_by all_goals (simp_wf; try term_by_mem)
end

/-! ### Expression translation equation lemmas (exported for use in other modules) -/

@[simp] public theorem translateExprModel_eq_literalBool (b : Bool) :
  translateExprModel (.LiteralBool b) = .const () (.boolConst b) := by
  rw [translateExprModel.eq_def]

@[simp] public theorem translateExprModel_eq_literalInt (i : Int) :
  translateExprModel (.LiteralInt i) = .const () (.intConst i) := by
  rw [translateExprModel.eq_def]

@[simp] public theorem translateExprModel_eq_literalString (s : String) :
  translateExprModel (.LiteralString s) = .const () (.strConst s) := by
  rw [translateExprModel.eq_def]

@[simp] public theorem translateExprModel_eq_identifier (name : Identifier) :
  translateExprModel (.Identifier name) = .fvar () ⟨name.text, ()⟩ none := by
  rw [translateExprModel.eq_def]

@[simp] public theorem translateExprModel_eq_primEq (e1 e2 : StmtExprMd) :
  translateExprModel (.PrimitiveOp .Eq [e1, e2]) =
    .eq () (translateExprModel e1.val) (translateExprModel e2.val) := by
  rw [translateExprModel.eq_def]
  simp [translateExprModelMd.eq_def]

@[simp] public theorem translateExprModel_eq_primNot (e : StmtExprMd) :
  translateExprModel (.PrimitiveOp .Not [e]) =
    .app () (.op () ⟨"Bool.Not", ()⟩ none) (translateExprModel e.val) := by
  rw [translateExprModel.eq_def]
  simp [translateExprModelMd.eq_def]

@[simp] public theorem translateExprModel_eq_ite (c t e : StmtExprMd) :
  translateExprModel (.IfThenElse c t (some e)) =
    .ite () (translateExprModel c.val) (translateExprModel t.val) (translateExprModel e.val) := by
  rw [translateExprModel.eq_def]
  simp [translateExprModelMd.eq_def]

@[simp] public theorem translateExprModel_eq_primAdd (e1 e2 : StmtExprMd)
  (hNotReal : isRealExprMd e1 = false) (hNotReal2 : isRealExprMd e2 = false) :
  translateExprModel (.PrimitiveOp .Add [e1, e2]) =
    .app () (.app () (.op () ⟨"Int.Add", ()⟩ none) (translateExprModel e1.val)) (translateExprModel e2.val) := by
  sorry

@[simp] public theorem translateExprModel_eq_primSub (e1 e2 : StmtExprMd)
  (hNotReal : isRealExprMd e1 = false) (hNotReal2 : isRealExprMd e2 = false) :
  translateExprModel (.PrimitiveOp .Sub [e1, e2]) =
    .app () (.app () (.op () ⟨"Int.Sub", ()⟩ none) (translateExprModel e1.val)) (translateExprModel e2.val) := by
  sorry

@[simp] public theorem translateExprModel_eq_primMul (e1 e2 : StmtExprMd)
  (hNotReal : isRealExprMd e1 = false) (hNotReal2 : isRealExprMd e2 = false) :
  translateExprModel (.PrimitiveOp .Mul [e1, e2]) =
    .app () (.app () (.op () ⟨"Int.Mul", ()⟩ none) (translateExprModel e1.val)) (translateExprModel e2.val) := by
  sorry

@[simp] public theorem translateExprModel_eq_primLt (e1 e2 : StmtExprMd) :
  translateExprModel (.PrimitiveOp .Lt [e1, e2]) =
    .app () (.app () (.op () ⟨"Int.Lt", ()⟩ none) (translateExprModel e1.val)) (translateExprModel e2.val) := by
  sorry

@[simp] public theorem translateExprModel_eq_primGt (e1 e2 : StmtExprMd) :
  translateExprModel (.PrimitiveOp .Gt [e1, e2]) =
    .app () (.app () (.op () ⟨"Int.Gt", ()⟩ none) (translateExprModel e1.val)) (translateExprModel e2.val) := by
  sorry

@[simp] public theorem translateExprModel_eq_primLeq (e1 e2 : StmtExprMd) :
  translateExprModel (.PrimitiveOp .Leq [e1, e2]) =
    .app () (.app () (.op () ⟨"Int.Le", ()⟩ none) (translateExprModel e1.val)) (translateExprModel e2.val) := by
  sorry

@[simp] public theorem translateExprModel_eq_primGeq (e1 e2 : StmtExprMd) :
  translateExprModel (.PrimitiveOp .Geq [e1, e2]) =
    .app () (.app () (.op () ⟨"Int.Ge", ()⟩ none) (translateExprModel e1.val)) (translateExprModel e2.val) := by
  sorry

@[simp] public theorem translateExprModel_eq_primAnd (e1 e2 : StmtExprMd) :
  translateExprModel (.PrimitiveOp .And [e1, e2]) =
    .app () (.app () (.op () ⟨"Bool.And", ()⟩ none) (translateExprModel e1.val)) (translateExprModel e2.val) := by
  rw [translateExprModel.eq_def]; simp [translateExprModelMd.eq_def]

@[simp] public theorem translateExprModel_eq_primOr (e1 e2 : StmtExprMd) :
  translateExprModel (.PrimitiveOp .Or [e1, e2]) =
    .app () (.app () (.op () ⟨"Bool.Or", ()⟩ none) (translateExprModel e1.val)) (translateExprModel e2.val) := by
  rw [translateExprModel.eq_def]; simp [translateExprModelMd.eq_def]

@[simp] public theorem translateExprModel_eq_primNeq (e1 e2 : StmtExprMd) :
  translateExprModel (.PrimitiveOp .Neq [e1, e2]) =
    .app () (.op () ⟨"Bool.Not", ()⟩ none) (.eq () (translateExprModel e1.val) (translateExprModel e2.val)) := by
  rw [translateExprModel.eq_def]; simp [translateExprModelMd.eq_def]

@[simp] public theorem translateExprModel_eq_staticCall (callee : Identifier) (args : List StmtExprMd) :
  translateExprModel (.StaticCall callee args) =
    args.attach.foldl (fun acc ⟨a, _⟩ => .app () acc (translateExprModel a.val))
      (.op () ⟨callee.text, ()⟩ none) := by
  rw [translateExprModel.eq_def]; simp [translateExprModelMd.eq_def]

/-- Translate expression with type-aware operator selection. -/
public def translateExprWithEnv (env : TypeEnv) (expr : StmtExpr) : Core.Expression.Expr :=
  let base := translateExprModel expr
  -- Post-process: fix operator names based on type environment
  fixRealOps env expr base
where
  fixRealOps (env : TypeEnv) (expr : StmtExpr) (core : Core.Expression.Expr) : Core.Expression.Expr :=
    match expr with
    | .PrimitiveOp op [e1, e2] =>
      if exprIsReal env e1.val || exprIsReal env e2.val then
        match core with
        | .app _ (.app _ (.op _ ⟨name, _⟩ _) l) r =>
          let realName := match name with
            | "Int.Add" => "Real.Add" | "Int.Sub" => "Real.Sub"
            | "Int.Mul" => "Real.Mul" | "Int.SafeDiv" => "Real.Div"
            | "Int.Lt" => "Real.Lt" | "Int.Le" => "Real.Le"
            | "Int.Gt" => "Real.Gt" | "Int.Ge" => "Real.Ge"
            | other => other
          .app () (.app () (.op () ⟨realName, ()⟩ none) l) r
        | _ => core
      else core
    | .PrimitiveOp .Neg [e] =>
      if exprIsReal env e.val then
        match core with
        | .app _ (.op _ ⟨_, _⟩ _) inner => .app () (.op () ⟨"Real.Neg", ()⟩ none) inner
        | _ => core
      else core
    | _ => core

public def translateExprMdWithEnv (env : TypeEnv) (e : StmtExprMd) : Core.Expression.Expr :=
  translateExprWithEnv env e.val

/-! ## Statement translation model -/

/-- Count TryCatch nodes in a StmtExpr (for fresh ID computation). -/
partial def countTryCatchMd (e : StmtExprMd) : Nat :=
  match e.val with
  | .TryCatch body catches finally_ =>
    1 + countTryCatchMd body +
    catches.foldl (fun acc c => acc + countTryCatchMd c.body) 0 +
    (match finally_ with | some f => countTryCatchMd f | none => 0)
  | .Block stmts _ => stmts.foldl (fun acc s => acc + countTryCatchMd s) 0
  | .IfThenElse _ t e => countTryCatchMd t + (match e with | some e => countTryCatchMd e | none => 0)
  | .While _ _ _ body => countTryCatchMd body
  | _ => 0

/-- Replace exit target in Core statements (for try body translation). -/
partial def retargetExits (oldTarget newTarget : String) (stmts : Core.Statements) : Core.Statements :=
  stmts.map fun s => match s with
    | .exit (some label) md => if label == oldTarget then .exit (some newTarget) md else s
    | .ite cond thenB elseB md => .ite cond (retargetExits oldTarget newTarget thenB) (retargetExits oldTarget newTarget elseB) md
    | .block label inner md => .block label (retargetExits oldTarget newTarget inner) md
    | other => other

/-- The exception propagation check: if $result is Failure, exit $body -/
public def modelExceptionPropagation : Core.Statement :=
  let resultIdent : Core.Expression.Ident := ⟨"$result", ()⟩
  let isFailureCheck : Core.Expression.Expr :=
    .app () (.op () ⟨"ExceptionResult..isFailure", ()⟩ none) (.fvar () resultIdent none)
  Imperative.Stmt.ite isFailureCheck [Imperative.Stmt.exit (some "$body") .empty] [] .empty

@[simp] public theorem modelExceptionPropagation_eq :
    modelExceptionPropagation =
    let resultIdent : Core.Expression.Ident := ⟨"$result", ()⟩
    let isFailureCheck : Core.Expression.Expr :=
      .app () (.op () ⟨"ExceptionResult..isFailure", ()⟩ none) (.fvar () resultIdent none)
    Imperative.Stmt.ite isFailureCheck [Imperative.Stmt.exit (some "$body") .empty] [] .empty := by
  unfold modelExceptionPropagation; rfl

mutual
public def translateStmtModelMd (isFunction : String → Bool) (outputParams : List String) (e : StmtExprMd) (env : TypeEnv := []) (cbt : List (String × HighType) := []) : Core.Statements :=
  translateStmtModel isFunction outputParams e.val env cbt
  termination_by sizeOf e
  decreasing_by cases e; term_by_mem

/-- Translate a Laurel statement to Core statements -/
public def translateStmtModel
  (isFunction : String → Bool)
  (outputParams : List String)
  (stmt : StmtExpr)
  (env : TypeEnv := [])
  (cbt : List (String × HighType) := []) : Core.Statements :=
  match _h : stmt with
  | .Return (some v) =>
    match outputParams.head? with
    | some outName =>
      match v.val with
      | .StaticCall callee args =>
        if isFunction callee.text then
          let coreExpr := translateExprWithEnv env v.val
          [Core.Statement.set ⟨outName, ()⟩ coreExpr .empty,
           Imperative.Stmt.exit (some "$body") .empty]
        else
          let coreArgs := args.map fun a => translateExprWithEnv env a.val
          [Core.Statement.call [⟨outName, ()⟩, ⟨"$result", ()⟩] callee.text coreArgs .empty,
           modelExceptionPropagation,
           Imperative.Stmt.exit (some "$body") .empty]
      | .InstanceCall target callee args =>
        let qualName := callee.text
        let unqualName := match qualName.splitOn ".." with | [_, name] => name | _ => qualName
        if isFunction unqualName then
          let coreExpr := translateExprWithEnv env v.val
          [Core.Statement.set ⟨outName, ()⟩ coreExpr .empty,
           Imperative.Stmt.exit (some "$body") .empty]
        else
          let coreTarget := translateExprMdWithEnv env target
          let coreArgs := args.map fun a => translateExprWithEnv env a.val
          [Core.Statement.call [⟨outName, ()⟩, ⟨"$result", ()⟩] qualName ((.fvar () ⟨"$heap", ()⟩ none) :: coreTarget :: coreArgs) .empty,
           modelExceptionPropagation,
           Imperative.Stmt.exit (some "$body") .empty]
      | _ =>
        let coreExpr := translateExprWithEnv env v.val
        [Core.Statement.set ⟨outName, ()⟩ coreExpr .empty,
         Imperative.Stmt.exit (some "$body") .empty]
    | none => []
  | .Return none => [Imperative.Stmt.exit (some "$body") .empty]
  | .Block stmts (some label) =>
    let (inner, _) := stmts.attach.foldl (fun (acc, curEnv) ⟨s, _⟩ =>
      let newEnv := match s.val with
        | .LocalVariable id ty _ => (id.text, ty.val) :: curEnv
        | _ => curEnv
      (acc ++ translateStmtModelMd isFunction outputParams s curEnv cbt, newEnv)) ([], env)
    [Imperative.Stmt.block label inner .empty]
  | .Block stmts none =>
    let (result, _) := stmts.attach.foldl (fun (acc, curEnv) ⟨s, _⟩ =>
      let newEnv := match s.val with
        | .LocalVariable id ty _ => (id.text, ty.val) :: curEnv
        | _ => curEnv
      (acc ++ translateStmtModelMd isFunction outputParams s curEnv cbt, newEnv)) ([], env)
    result
  | .LocalVariable id ty (some init) =>
    match init.val with
    | .StaticCall callee args =>
      if isFunction callee.text then
        let coreExpr := translateExprWithEnv env init.val
        [Core.Statement.init ⟨id.text, ()⟩ (if id.text.startsWith "$unused_" then .forAll ["$__ty_" ++ id.text.drop 1] (.ftvar ("$__ty_" ++ id.text.drop 1)) else .forAll [] (coreMonoType ty.val)) (some coreExpr) .empty]
      else
        let coreArgs := args.map fun a => translateExprWithEnv env a.val
        -- Instance method calls need $heap as first arg
        let coreArgs := if callee.text.splitOn ".." != [callee.text]
          then (.fvar () ⟨"$heap", ()⟩ none) :: coreArgs else coreArgs
        [Core.Statement.init ⟨id.text, ()⟩ (if id.text.startsWith "$unused_" then .forAll ["$__ty_" ++ id.text.drop 1] (.ftvar ("$__ty_" ++ id.text.drop 1)) else .forAll [] (coreMonoType ty.val)) (some (.const () (.intConst 0))) .empty,
         Core.Statement.call [⟨id.text, ()⟩, ⟨"$result", ()⟩] callee.text coreArgs .empty,
         modelExceptionPropagation]
    | .InstanceCall target callee args =>
      let qualName := callee.text  -- qualified by resolveInstanceCalls in translateProcModel
      -- Check if the callee is a function by looking at the unqualified name
      let unqualName := match qualName.splitOn ".." with | [_, name] => name | _ => qualName
      if isFunction unqualName then
        -- Function call: translate as expression init
        let coreExpr := translateExprWithEnv env init.val
        [Core.Statement.init ⟨id.text, ()⟩ (.forAll [] (coreMonoType ty.val)) (some coreExpr) .empty]
      else
        -- Procedure call: init + call + exception propagation
        let coreTarget := translateExprMdWithEnv env target
        let coreArgs := args.map fun a => translateExprWithEnv env a.val
        [Core.Statement.init ⟨id.text, ()⟩ (.forAll [] (coreMonoType ty.val)) (some (.const () (.intConst 0))) .empty,
         Core.Statement.call [⟨id.text, ()⟩, ⟨"$result", ()⟩] qualName ((.fvar () ⟨"$heap", ()⟩ none) :: coreTarget :: coreArgs) .empty,
         modelExceptionPropagation]
    | _ =>
      let coreExpr := translateExprWithEnv env init.val
      let resolvedTy := match ty.val with
        | .UserDefined name =>
          let rec resolve (n : String) (fuel : Nat) : Lambda.LMonoTy :=
            match fuel with
            | 0 => coreMonoType ty.val
            | fuel + 1 => match cbt.find? (·.1 == n) with
              | some (_, .UserDefined parent) => resolve parent.text fuel
              | some (_, base) => coreMonoType base
              | none => .tcons n []
          resolve name.text cbt.length
        | _ => coreMonoType ty.val
      let constraintAssert := match ty.val with
        | .UserDefined name => if cbt.any (·.1 == name.text) then
            [Core.Statement.assert "assert(0)"
              (.app () (.op () ⟨name.text ++ "$constraint", ()⟩ none) (.fvar () ⟨id.text, ()⟩ none)) .empty]
          else []
        | _ => []
      [Core.Statement.init ⟨id.text, ()⟩ (if id.text.startsWith "$unused_" then .forAll ["$__ty_" ++ id.text.drop 1] (.ftvar ("$__ty_" ++ id.text.drop 1)) else .forAll [] resolvedTy) (some coreExpr) .empty] ++ constraintAssert
  | .LocalVariable id ty none =>
    let resolvedTy := match ty.val with
      | .UserDefined name =>
        let rec resolve2 (n : String) (fuel : Nat) : Lambda.LMonoTy :=
          match fuel with
          | 0 => coreMonoType ty.val
          | fuel + 1 => match cbt.find? (·.1 == n) with
            | some (_, .UserDefined parent) => resolve2 parent.text fuel
            | some (_, base) => coreMonoType base
            | none => .tcons n []
        resolve2 name.text cbt.length
      | _ => coreMonoType ty.val
    let constraintAssume := match ty.val with
      | .UserDefined name => if cbt.any (·.1 == name.text) then
          [Core.Statement.assume "assume(0)"
            (.app () (.op () ⟨name.text ++ "$constraint", ()⟩ none) (.fvar () ⟨id.text, ()⟩ none)) .empty]
        else []
      | _ => []
    [Core.Statement.init ⟨id.text, ()⟩ (.forAll [] resolvedTy) none .empty] ++ constraintAssume
  | .Assign [⟨.FieldSelect target fieldName, _⟩] value =>
    let targetExpr := translateExprMdWithEnv env target
    let cleanFieldName := if fieldName.text.endsWith ":bool" then fieldName.text.dropRight 5
      else if fieldName.text.endsWith ":string" then fieldName.text.dropRight 7
      else match fieldName.text.splitOn ":" with
        | [name, _] => name
        | _ => fieldName.text
    let fieldOp : Core.Expression.Expr := .op () ⟨cleanFieldName, ()⟩ none
    let valueExpr := translateExprWithEnv env value.val
    let boxFn := if fieldName.text.endsWith ":bool" then "BoxBool"
      else if fieldName.text.endsWith ":string" then "BoxString"
      else "BoxInt"
    let boxedValue : Core.Expression.Expr := .app () (.op () ⟨boxFn, ()⟩ none) valueExpr
    [Core.Statement.set ⟨"$heap", ()⟩
      (.app () (.app () (.app () (.app () (.op () ⟨"updateField", ()⟩ none)
        (.fvar () ⟨"$heap", ()⟩ none)) targetExpr) fieldOp) boxedValue) .empty]
  | .Assign [⟨.Identifier targetId, _⟩] value =>
    match value.val with
    | .StaticCall callee args =>
      if isFunction callee.text then
        let coreExpr := translateExprWithEnv env value.val
        [Core.Statement.set ⟨targetId.text, ()⟩ coreExpr .empty]
      else
        let coreArgs := args.map fun a => translateExprWithEnv env a.val
        [Core.Statement.call [⟨targetId.text, ()⟩, ⟨"$result", ()⟩] callee.text coreArgs .empty,
         modelExceptionPropagation]
    | .InstanceCall target callee args =>
      let qualName := callee.text
      let unqualName := match qualName.splitOn ".." with | [_, name] => name | _ => qualName
      if isFunction unqualName then
        let coreExpr := translateExprWithEnv env value.val
        [Core.Statement.set ⟨targetId.text, ()⟩ coreExpr .empty]
      else
        let coreTarget := translateExprMdWithEnv env target
        let coreArgs := args.map fun a => translateExprWithEnv env a.val
        [Core.Statement.call [⟨targetId.text, ()⟩, ⟨"$result", ()⟩] qualName ((.fvar () ⟨"$heap", ()⟩ none) :: coreTarget :: coreArgs) .empty,
         modelExceptionPropagation]
    | _ =>
      let coreExpr := translateExprWithEnv env value.val
      [Core.Statement.set ⟨targetId.text, ()⟩ coreExpr .empty]
    -- Add constraint assert after assignment to constrained-type variable
    |> fun stmts => match env.lookup targetId.text with
      | some (.UserDefined name) =>
        if cbt.any (·.1 == name.text) then
          stmts ++ [Core.Statement.assert "assert(0)"
            (.app () (.op () ⟨name.text ++ "$constraint", ()⟩ none) (.fvar () ⟨targetId.text, ()⟩ none)) .empty]
        else stmts
      | _ => stmts
  | .IfThenElse cond thenB elseB =>
    let bcond := translateExprWithEnv env cond.val
    let bthen := translateStmtModelMd isFunction outputParams thenB env cbt
    let belse := match elseB with
      | some e => translateStmtModelMd isFunction outputParams e env cbt
      | none => []
    [Imperative.Stmt.ite bcond bthen belse .empty]
  | .StaticCall callee args =>
    if isFunction callee.text then []
    else
      let coreArgs := args.map fun a => translateExprWithEnv env a.val
      let isInstanceCall := callee.text.splitOn ".." != [callee.text]
      let coreArgs := if isInstanceCall
        then (.fvar () ⟨"$heap", ()⟩ none) :: coreArgs else coreArgs
      let outputs := if isInstanceCall
        then [⟨"$heap", ()⟩, ⟨"$result", ()⟩] else [⟨"$result", ()⟩]
      [Core.Statement.call outputs callee.text coreArgs .empty,
       modelExceptionPropagation]
  | .While cond invariants decreasesExpr body =>
    let condExpr := translateExprWithEnv env cond.val
    let invExprs := invariants.map fun i => translateExprWithEnv env i.val
    let decExprCore := decreasesExpr.map fun d => translateExprWithEnv env d.val
    let bodyStmts := translateStmtModelMd isFunction outputParams body env cbt
    [Imperative.Stmt.loop condExpr decExprCore invExprs bodyStmts .empty]
  | .Assert c =>
    let coreExpr := translateExprWithEnv env c.val
    [Core.Statement.assert "assert(0)" coreExpr .empty]
  | .Assume c =>
    let coreExpr := translateExprWithEnv env c.val
    [Core.Statement.assume "assume(0)" coreExpr .empty]
  | .InstanceCall _ _ _ =>
    -- Unresolved instance call in static proc → havoc $heap
    [Core.Statement.havoc ⟨"$heap", ()⟩ .empty]
  | .Exit target =>
    [Imperative.Stmt.exit (some target) .empty]
  | .Throw _exception =>
    let failureCtor : Core.Expression.Expr := .op () ⟨"Failure", ()⟩ none
    [Core.Statement.set ⟨"$result", ()⟩ failureCtor .empty,
     Imperative.Stmt.exit (some "$body") .empty]
  | .TryCatch body catches finally_ =>
    -- Real translator uses freshId: outer=1, inner=2
    -- Inner TryCatch nodes in the body also produce $try_end_1/$handlers_1
    -- Retarget them to $try_end_2/$handlers_2 etc.
    let innerCount := countTryCatchMd body
    let tryLabel := s!"$try_end_{innerCount + 1}"
    let handlersLabel := s!"$handlers_{innerCount + 1}"
    let isFailureCheck : Core.Expression.Expr :=
      .app () (.op () ⟨"ExceptionResult..isFailure", ()⟩ none) (.fvar () ⟨"$result", ()⟩ none)
    let successCtor : Core.Expression.Expr := .op () ⟨"Success", ()⟩ none
    -- Translate body, then retarget throw exits from $body to $handlers_1
    let bodyStmts := retargetExits "$body" handlersLabel
      (translateStmtModelMd isFunction outputParams body)
    let exitTry := Imperative.Stmt.exit (some tryLabel) .empty
    let handlersBlock := Imperative.Stmt.block handlersLabel (bodyStmts ++ [exitTry]) .empty
    let catchStmts := catches.attach.flatMap fun ⟨c, hc⟩ =>
      have : sizeOf c.body < sizeOf stmt := by simp_all; sorry
      let handlerBody := translateStmtModelMd isFunction outputParams c.body
      let resetResult := Core.Statement.set ⟨"$result", ()⟩ successCtor .empty
      [Imperative.Stmt.ite isFailureCheck
        (resetResult :: handlerBody ++ [Imperative.Stmt.exit (some tryLabel) .empty])
        [] .empty]
    let tryBlock := Imperative.Stmt.block tryLabel ([handlersBlock] ++ catchStmts) .empty
    let finallyStmts := match finally_ with
      | some f => translateStmtModelMd isFunction outputParams f env cbt
      | none => []
    [tryBlock] ++ finallyStmts
  | other =>
    -- Expression in statement position → $unused init
    let coreExpr := translateExprWithEnv env other
    [Core.Statement.init ⟨"$unused_1", ()⟩
      (.forAll ["$__ty_unused_1"] (.ftvar "$__ty_unused_1"))
      (some coreExpr) .empty]
  termination_by sizeOf stmt
  decreasing_by all_goals (simp_wf; try term_by_mem)
end

/-! ### Statement translation equation lemmas -/

@[simp] public theorem translateStmtModel_eq_return_none
  (isFunction : String → Bool) (outputParams : List String) :
  translateStmtModel isFunction outputParams (.Return none) =
    [Imperative.Stmt.exit (some "$body") .empty] := by
  rw [translateStmtModel.eq_def]

@[simp] public theorem translateStmtModel_eq_local_no_init
  (isFunction : String → Bool) (outputParams : List String)
  (id : Identifier) (ty : WithMetadata HighType) :
  translateStmtModel isFunction outputParams (.LocalVariable id ty none) =
    [Core.Statement.init ⟨id.text, ()⟩ (.forAll [] (coreMonoType ty.val)) none .empty] := by
  sorry

@[simp] public theorem translateStmtModel_eq_local_expr_init
  (isFunction : String → Bool) (outputParams : List String)
  (id : Identifier) (ty : WithMetadata HighType) (init : StmtExprMd)
  (hNotStaticCall : ∀ c a, init.val ≠ .StaticCall c a)
  (hNotInstanceCall : ∀ t c a, init.val ≠ .InstanceCall t c a)
  (hNotHole : ∀ n t, init.val ≠ .Hole n t)
  (hNotUnused : id.text.startsWith "$unused_" = false) :
  translateStmtModel isFunction outputParams (.LocalVariable id ty (some init)) =
    [Core.Statement.init ⟨id.text, ()⟩ (.forAll [] (coreMonoType ty.val)) (some (translateExprModel init.val)) .empty] := by
  sorry

@[simp] public theorem translateStmtModel_eq_return_expr
  (isFunction : String → Bool) (outputParams : List String)
  (value : StmtExprMd) (outName : String)
  (hHead : outputParams.head? = some outName)
  (hNotStaticCall : ∀ c a, value.val ≠ .StaticCall c a)
  (hNotInstanceCall : ∀ t c a, value.val ≠ .InstanceCall t c a) :
  translateStmtModel isFunction outputParams (.Return (some value)) =
    [Core.Statement.set ⟨outName, ()⟩ (translateExprModel value.val) .empty,
     Imperative.Stmt.exit (some "$body") .empty] := by
  sorry

@[simp] public theorem translateStmtModel_eq_ite_noElse
  (isFunction : String → Bool) (outputParams : List String)
  (cond thenB : StmtExprMd) :
  translateStmtModel isFunction outputParams (.IfThenElse cond thenB none) =
    [Imperative.Stmt.ite (translateExprModel cond.val)
      (translateStmtModelMd isFunction outputParams thenB)
      []
      .empty] := by
  sorry

@[simp] public theorem translateStmtModel_eq_ite_withElse
  (isFunction : String → Bool) (outputParams : List String)
  (cond thenB elseB : StmtExprMd) :
  translateStmtModel isFunction outputParams (.IfThenElse cond thenB (some elseB)) =
    [Imperative.Stmt.ite (translateExprModel cond.val)
      (translateStmtModelMd isFunction outputParams thenB)
      (translateStmtModelMd isFunction outputParams elseB)
      .empty] := by
  sorry

@[simp] public theorem translateStmtModel_eq_assign_expr
  (isFunction : String → Bool) (outputParams : List String)
  (targetId : Identifier) (targetMd : MetaData) (value : StmtExprMd)
  (hNotStaticCall : ∀ c a, value.val ≠ .StaticCall c a)
  (hNotInstanceCall : ∀ t c a, value.val ≠ .InstanceCall t c a) :
  translateStmtModel isFunction outputParams (.Assign [⟨.Identifier targetId, targetMd⟩] value) =
    [Core.Statement.set ⟨targetId.text, ()⟩ (translateExprModel value.val) .empty] := by
  rw [translateStmtModel.eq_def]
  sorry

@[simp] public theorem translateStmtModel_eq_staticCall_proc
  (isFunction : String → Bool) (outputParams : List String)
  (callee : Identifier) (args : List StmtExprMd)
  (hNotFunc : isFunction callee.text = false) :
  translateStmtModel isFunction outputParams (.StaticCall callee args) =
    let coreArgs := args.map fun a => translateExprModel a.val
    let isInstanceCall := callee.text.splitOn ".." != [callee.text]
    let coreArgs := if isInstanceCall
      then (.fvar () ⟨"$heap", ()⟩ none) :: coreArgs else coreArgs
    let outputs := if isInstanceCall
      then [⟨"$heap", ()⟩, ⟨"$result", ()⟩] else [⟨"$result", ()⟩]
    [Core.Statement.call outputs callee.text coreArgs .empty,
     modelExceptionPropagation] := by
  sorry

@[simp] public theorem translateStmtModel_eq_block_unlabeled
  (isFunction : String → Bool) (outputParams : List String)
  (stmts : List StmtExprMd) :
  translateStmtModel isFunction outputParams (.Block stmts none) =
    stmts.flatMap fun s => translateStmtModelMd isFunction outputParams s := by
  sorry

@[simp] public theorem translateStmtModel_eq_while
  (isFunction : String → Bool) (outputParams : List String)
  (cond : StmtExprMd) (invariants : List StmtExprMd)
  (decreasesExpr : Option StmtExprMd) (body : StmtExprMd) :
  translateStmtModel isFunction outputParams (.While cond invariants decreasesExpr body) =
    [Imperative.Stmt.loop (translateExprModel cond.val)
      (decreasesExpr.map fun d => translateExprModel d.val)
      (invariants.map fun i => translateExprModel i.val)
      (translateStmtModelMd isFunction outputParams body)
      .empty] := by
  sorry

/-! ## Procedure and program assembly model -/

/-- Translate a Laurel parameter to Core (name, type) pair -/
@[expose] public def translateParamModel (p : Parameter) : Lambda.Identifier Unit × Lambda.LMonoTy :=
  (⟨p.name.text, ()⟩, match p.type.val with
    | .TMap _ _ | .TSequence _ | .TSet _ => coreMonoType p.type.val
    | _ => Lambda.LMonoTy.tcons (coreTypeName p.type.val) [])

/-- Model a transparent functional procedure as a Core function declaration -/
@[expose] public def modelTransparentFuncDecl (_isFunction : String → Bool) (proc : Procedure) : Core.Decl :=
  let inputs := proc.inputs.map translateParamModel
  let outputTy := match proc.outputs.head? with
    | some p => coreMonoType p.type.val
    | none => Lambda.LMonoTy.int
  let body := match proc.body with
    | .Transparent b => some (translateExprModel b.val)
    | .Opaque _ (some impl) _ => some (translateExprModel impl.val)
    | _ => none
  Core.Decl.func { name := ⟨proc.name.text, ()⟩, typeArgs := [], inputs, output := outputTy, body }

/-- Assemble a Laurel procedure into a Core procedure declaration -/
public def containsInstanceCallMd : StmtExprMd → Bool
  | ⟨.StaticCall callee _, _⟩ => (callee.text.splitOn ".." != [callee.text])
  | ⟨.InstanceCall _ _ _, _⟩ => true
  | ⟨.Block stmts _, _⟩ => stmts.attach.any fun ⟨s, _⟩ => containsInstanceCallMd s
  | ⟨.IfThenElse c t e, _⟩ => containsInstanceCallMd c || containsInstanceCallMd t ||
    (match e with | some e => containsInstanceCallMd e | none => false)
  | ⟨.While _ _ _ body, _⟩ => containsInstanceCallMd body
  | ⟨.Return (some v), _⟩ => containsInstanceCallMd v
  | ⟨.Assign _ v, _⟩ => containsInstanceCallMd v
  | ⟨.LocalVariable _ _ (some init), _⟩ => containsInstanceCallMd init
  | _ => false
  termination_by e => sizeOf e
  decreasing_by all_goals (simp_wf; first | term_by_mem | omega)

public def containsBareInstanceCallMd : StmtExprMd → Bool
  | ⟨.InstanceCall _ _ _, _⟩ => true
  | ⟨.StaticCall callee _, _⟩ => (callee.text.splitOn ".." != [callee.text])
  | ⟨.Block stmts _, _⟩ => stmts.attach.any fun ⟨s, _⟩ => containsBareInstanceCallMd s
  | ⟨.While _ _ _ body, _⟩ => containsBareInstanceCallMd body
  | ⟨.IfThenElse _ t e, _⟩ => containsBareInstanceCallMd t ||
    (match e with | some e => containsBareInstanceCallMd e | none => false)
  | _ => false
  termination_by e => sizeOf e
  decreasing_by all_goals (simp_wf; first | term_by_mem | omega)

/-- If a Block has no InstanceCalls, then no individual statement does either. -/
public theorem no_instanceCall_of_block_mem (stmts : List StmtExprMd) (label : Option String)
    (hNoIC : containsInstanceCallMd ⟨.Block stmts label, md⟩ = false)
    (s : StmtExprMd) (hs : s ∈ stmts) : containsInstanceCallMd s = false := by
  simp only [containsInstanceCallMd] at hNoIC
  match hc : containsInstanceCallMd s with
  | false => rfl
  | true =>
    exfalso
    have hAny : stmts.attach.any (fun ⟨s, _⟩ => containsInstanceCallMd s) = true := by
      apply List.any_eq_true.mpr
      refine ⟨⟨s, hs⟩, List.mem_attach .., ?_⟩
      exact hc
    simp_all

/-- When containsInstanceCallMd is false for a statement, it cannot be
    a LocalVariable with InstanceCall init. -/
public theorem not_instanceCall_of_no_containsInstanceCallMd (s : StmtExprMd)
    (hNoIC : containsInstanceCallMd s = false) :
    ∀ id ty target callee args imd,
      s.val ≠ StmtExpr.LocalVariable id ty (some ⟨.InstanceCall target callee args, imd⟩) := by
  intro id ty target callee args imd heq
  have : containsInstanceCallMd s = true := by
    show containsInstanceCallMd ⟨s.val, s.md⟩ = true
    rw [heq]; simp [containsInstanceCallMd]
  simp_all

/-- When containsInstanceCallMd is false for a Block, mapping any resolveIC-like
    function over its statements returns the same Block, provided the function
    is identity on non-InstanceCall statements. -/
public theorem resolveBody_id_of_no_instanceCall
    (stmts : List StmtExprMd) (label : Option String)
    (f : StmtExpr → StmtExpr)
    (hf : ∀ (s : StmtExprMd), containsInstanceCallMd s = false → f s.val = s.val)
    (hNoIC : containsInstanceCallMd ⟨.Block stmts label, md⟩ = false) :
    StmtExpr.Block (stmts.map fun s => ⟨f s.val, s.md⟩) label =
    StmtExpr.Block stmts label := by
  congr 1
  induction stmts with
  | nil => rfl
  | cons s rest ih =>
    simp only [List.map_cons, List.cons.injEq]
    have hHead : containsInstanceCallMd s = false := by
      simp only [containsInstanceCallMd] at hNoIC
      match hc : containsInstanceCallMd s with
      | false => rfl
      | true =>
        exfalso
        have : (s :: rest).attach.any (fun ⟨s, _⟩ => containsInstanceCallMd s) = true :=
          List.any_eq_true.mpr ⟨⟨s, List.mem_cons_self⟩, List.mem_attach ..,
            show (fun (x : {x // x ∈ s :: rest}) => containsInstanceCallMd x.1) ⟨s, List.mem_cons_self⟩ = true from hc⟩
        simp_all
    have hRest : containsInstanceCallMd ⟨.Block rest label, md⟩ = false := by
      simp only [containsInstanceCallMd] at hNoIC ⊢
      match hc : rest.attach.any (fun ⟨s, _⟩ => containsInstanceCallMd s) with
      | false => rfl
      | true =>
        exfalso
        obtain ⟨⟨t, ht⟩, _, htIC⟩ := List.any_eq_true.mp hc
        have : (s :: rest).attach.any (fun ⟨s, _⟩ => containsInstanceCallMd s) = true :=
          List.any_eq_true.mpr ⟨⟨t, List.mem_cons_of_mem _ ht⟩, List.mem_attach .., htIC⟩
        simp_all
    constructor
    · have := hf s hHead; cases s; simp_all
    · exact ih hRest

/-- Qualify an InstanceCall callee name using the parameter type map. -/
private def qualifyCallee (paramTypeMap : List (String × String)) (target : StmtExprMd) (callee : Identifier) : Identifier :=
  let qualName := match target.val with
    | .Identifier name => match paramTypeMap.filter (·.1 == name.text) with
      | (_, tn) :: _ => tn ++ ".." ++ callee.text
      | [] => callee.text
    | _ => callee.text
  { callee with text := qualName }

/-- Recursively qualify InstanceCall callee names in an expression tree. -/
private def qualifyExprInstanceCalls (paramTypeMap : List (String × String)) : StmtExprMd → StmtExprMd
  | ⟨.InstanceCall target callee args, md⟩ =>
    let qTarget := qualifyExprInstanceCalls paramTypeMap target
    ⟨.InstanceCall qTarget (qualifyCallee paramTypeMap target callee)
      (args.attach.map fun ⟨a, _⟩ => qualifyExprInstanceCalls paramTypeMap a), md⟩
  | ⟨.PrimitiveOp op args, md⟩ =>
    ⟨.PrimitiveOp op (args.attach.map fun ⟨a, _⟩ => qualifyExprInstanceCalls paramTypeMap a), md⟩
  | ⟨.StaticCall callee args, md⟩ =>
    ⟨.StaticCall callee (args.attach.map fun ⟨a, _⟩ => qualifyExprInstanceCalls paramTypeMap a), md⟩
  | ⟨.IfThenElse c t (some e), md⟩ =>
    ⟨.IfThenElse (qualifyExprInstanceCalls paramTypeMap c)
      (qualifyExprInstanceCalls paramTypeMap t)
      (some (qualifyExprInstanceCalls paramTypeMap e)), md⟩
  | ⟨.IfThenElse c t none, md⟩ =>
    ⟨.IfThenElse (qualifyExprInstanceCalls paramTypeMap c)
      (qualifyExprInstanceCalls paramTypeMap t) none, md⟩
  | ⟨.FieldSelect target f, md⟩ =>
    ⟨.FieldSelect (qualifyExprInstanceCalls paramTypeMap target) f, md⟩
  | other => other
termination_by e => sizeOf e
decreasing_by all_goals (simp_wf; try term_by_mem)

/-- Resolve InstanceCall in a single statement by qualifying the callee name. -/
public def resolveInstanceCallInStmt (paramTypeMap : List (String × String)) (s : StmtExpr) : StmtExpr :=
  let qe := qualifyExprInstanceCalls paramTypeMap
  match s with
  | .LocalVariable id ty (some init) => .LocalVariable id ty (some (qe init))
  | .Return (some v) => .Return (some (qe v))
  | .Assign targets value => .Assign targets (qe value)
  | .IfThenElse cond thenB elseB =>
    .IfThenElse (qe cond) thenB elseB
  | .While cond invs dec body =>
    .While (qe cond) invs dec body
  | .InstanceCall target callee args =>
    let qt := qe ⟨target.val, target.md⟩
    .InstanceCall qt (qualifyCallee paramTypeMap ⟨target.val, target.md⟩ callee) args
  | other => other

/-- Resolve InstanceCalls in a body Block by mapping resolveInstanceCallInStmt. -/
public def resolveInstanceCallsInBody (paramTypeMap : List (String × String)) (body : StmtExpr) : StmtExpr :=
  match body with
  | .Block stmts label => .Block (stmts.map fun s => ⟨resolveInstanceCallInStmt paramTypeMap s.val, s.md⟩) label
  | other => other

/-- resolveInstanceCallInStmt is identity when the statement has no InstanceCall. -/
public theorem resolveInstanceCallInStmt_id (paramTypeMap : List (String × String))
    (s : StmtExprMd) (hNoIC : containsInstanceCallMd s = false) :
    resolveInstanceCallInStmt paramTypeMap s.val = s.val := by
  sorry

/-- resolveInstanceCallsInBody is identity on a Block when no statement has InstanceCall. -/
public theorem resolveInstanceCallsInBody_id (paramTypeMap : List (String × String))
    (bodyExpr : StmtExprMd) (hNoIC : containsInstanceCallMd bodyExpr = false) :
    resolveInstanceCallsInBody paramTypeMap bodyExpr.val = bodyExpr.val := by
  unfold resolveInstanceCallsInBody
  split
  · rename_i stmts label hv
    simp only [hv]
    congr 1
    have hNoICBlock : containsInstanceCallMd ⟨.Block stmts label, bodyExpr.md⟩ = false := by rwa [← hv]
    have hMem := fun s hs => no_instanceCall_of_block_mem stmts label hNoICBlock s hs
    have : ∀ (l : List StmtExprMd), (∀ s ∈ l, containsInstanceCallMd s = false) →
        l.map (fun s => ⟨resolveInstanceCallInStmt paramTypeMap s.val, s.md⟩) = l := by
      intro l hl; induction l with
      | nil => simp
      | cons s rest ih =>
        simp only [List.map_cons, List.cons.injEq]
        exact ⟨by have := resolveInstanceCallInStmt_id paramTypeMap s (hl s (List.mem_cons_self ..))
                  cases s; simp_all,
               ih (fun t ht => hl t (List.mem_cons_of_mem _ ht))⟩
    exact this stmts hMem
  · rfl

/-- Resolve constrained types in expressions: inject constraint predicates into quantifier bodies
    and resolve constrained type names to base types. -/
public partial def resolveConstrainedInExpr (cbt : List (String × HighType)) : StmtExprMd → StmtExprMd
  | ⟨.Forall ⟨name, ty⟩ trigger body, md⟩ =>
    let body' := resolveConstrainedInExpr cbt body
    let trigger' := trigger.map (resolveConstrainedInExpr cbt)
    match ty.val with
    | .UserDefined tname =>
      if cbt.any (·.1 == tname.text) then
        -- Inject constraint: forall(n: ctype) => body → forall(n: base) => ctype$constraint(n) ==> body
        let constraintCall : StmtExprMd :=
          ⟨.StaticCall { text := tname.text ++ "$constraint", uniqueId := none }
            [⟨.Identifier { name with uniqueId := none }, md⟩], md⟩
        let resolvedTy := resolveConstrainedType cbt ty
        ⟨.Forall ⟨name, resolvedTy⟩ trigger' ⟨.PrimitiveOp .Implies [constraintCall, body'], md⟩, md⟩
      else ⟨.Forall ⟨name, ty⟩ trigger' body', md⟩
    | _ => ⟨.Forall ⟨name, ty⟩ trigger' body', md⟩
  | ⟨.Exists ⟨name, ty⟩ trigger body, md⟩ =>
    let body' := resolveConstrainedInExpr cbt body
    let trigger' := trigger.map (resolveConstrainedInExpr cbt)
    match ty.val with
    | .UserDefined tname =>
      if cbt.any (·.1 == tname.text) then
        let constraintCall : StmtExprMd :=
          ⟨.StaticCall { text := tname.text ++ "$constraint", uniqueId := none }
            [⟨.Identifier { name with uniqueId := none }, md⟩], md⟩
        let resolvedTy := resolveConstrainedType cbt ty
        ⟨.Exists ⟨name, resolvedTy⟩ trigger' ⟨.PrimitiveOp .And [constraintCall, body'], md⟩, md⟩
      else ⟨.Exists ⟨name, ty⟩ trigger' body', md⟩
    | _ => ⟨.Exists ⟨name, ty⟩ trigger' body', md⟩
  | ⟨.PrimitiveOp op args, md⟩ => ⟨.PrimitiveOp op (args.map (resolveConstrainedInExpr cbt)), md⟩
  | ⟨.IfThenElse c t (some e), md⟩ =>
    ⟨.IfThenElse (resolveConstrainedInExpr cbt c) (resolveConstrainedInExpr cbt t) (some (resolveConstrainedInExpr cbt e)), md⟩
  | ⟨.IfThenElse c t none, md⟩ =>
    ⟨.IfThenElse (resolveConstrainedInExpr cbt c) (resolveConstrainedInExpr cbt t) none, md⟩
  | ⟨.Block stmts label, md⟩ => ⟨.Block (stmts.map (resolveConstrainedInExpr cbt)) label, md⟩
  | ⟨.Return (some v), md⟩ => ⟨.Return (some (resolveConstrainedInExpr cbt v)), md⟩
  | ⟨.LocalVariable id ty init, md⟩ => ⟨.LocalVariable id ty (init.map (resolveConstrainedInExpr cbt)), md⟩
  | ⟨.Assign targets v, md⟩ => ⟨.Assign targets (resolveConstrainedInExpr cbt v), md⟩
  | ⟨.Old v, md⟩ => ⟨.Old (resolveConstrainedInExpr cbt v), md⟩
  | other => other
where
  resolveConstrainedType (cbt : List (String × HighType)) (ty : WithMetadata HighType) : WithMetadata HighType :=
    match ty.val with
    | .UserDefined name =>
      match cbt.find? (·.1 == name.text) with
      | some (_, base) => ⟨base, ty.md⟩
      | none => ty
    | _ => ty

@[expose] public def translateProcModel
  (isFunction : String → Bool)
  (compositeNames : List String)
  (proc : Procedure)
  (constrainedBaseTypes : List (String × HighType) := [])
  (composites : List CompositeType := []) : Core.Decl :=
  let resolveTypeName (ty : HighType) : String := match ty with
    | .UserDefined n =>
      if compositeNames.contains n.text then "Composite"
      else
        let rec resolve (name : String) (fuel : Nat) : String :=
          match fuel with
          | 0 => name
          | fuel + 1 => match constrainedBaseTypes.find? fun x => x.1 == name with
            | some (_, .UserDefined parent) => resolve parent.text fuel
            | some (_, base) => coreTypeName base
            | none => name
        resolve n.text constrainedBaseTypes.length
    | _ => coreTypeName ty
  let translateParam (p : Parameter) : Lambda.Identifier Unit × Lambda.LMonoTy :=
    let ty := p.type.val
    match ty with
    | .TMap _ _ | .TSequence _ | .TSet _ => (⟨p.name.text, ()⟩, coreMonoType ty)
    | _ => (⟨p.name.text, ()⟩, Lambda.LMonoTy.tcons (resolveTypeName ty) [])
  -- Determine if this procedure reads/writes heap
  let bodyExpr := match proc.body with
    | .Transparent b => some b | .Opaque _ (some impl) _ => some impl | _ => none
  let readsHeap := bodyExpr.any directlyReadsHeapMd
  let writesHeap := bodyExpr.any directlyWritesHeapMd
  -- Opaque procs: check postconditions and modifies clause
  let readsHeap := readsHeap || match proc.body with
    | .Opaque postconds _ modif => !modif.isEmpty || postconds.any (fun pc => directlyReadsHeapMd pc)
    | _ => false
  let writesHeap := writesHeap || match proc.body with
    | .Opaque _ _ modif => !modif.isEmpty
    | _ => false
  -- Also check for instance method calls (StaticCall with ".." in name)
  -- which transitively access heap
  let hasInstanceCall := match proc.body with
    | .Transparent b => containsInstanceCallMd b
    | .Opaque _ (some impl) _ => containsInstanceCallMd impl
    | _ => false
  let hasBareInstanceCall := match proc.body with
    | .Transparent b => containsBareInstanceCallMd b
    | .Opaque _ (some impl) _ => containsBareInstanceCallMd impl
    | _ => false
  let needsHeap := readsHeap || writesHeap || hasInstanceCall
  let readsHeap := readsHeap || hasInstanceCall
  let writesHeap := writesHeap || hasBareInstanceCall
  let inputs := proc.inputs.map translateParam
  let heapInput : Lambda.Identifier Unit × Lambda.LMonoTy :=
    (⟨"$heap_in", ()⟩, Lambda.LMonoTy.tcons "Heap" [])
  let heapInputName := if writesHeap then "$heap_in" else "$heap"
  let heapInput : Lambda.Identifier Unit × Lambda.LMonoTy :=
    (⟨heapInputName, ()⟩, Lambda.LMonoTy.tcons "Heap" [])
  let inputs := if needsHeap then heapInput :: inputs else inputs
  let outputs := proc.outputs.map translateParam
  let heapOutput : Lambda.Identifier Unit × Lambda.LMonoTy :=
    (⟨"$heap", ()⟩, Lambda.LMonoTy.tcons "Heap" [])
  let resultOutput : Lambda.Identifier Unit × Lambda.LMonoTy :=
    (⟨"$result", ()⟩, Lambda.LMonoTy.tcons "ExceptionResult" [])
  let outputs := if writesHeap then heapOutput :: outputs ++ [resultOutput]
    else outputs ++ [resultOutput]
  let header : Core.Procedure.Header := {
    name := ⟨proc.name.text, ()⟩
    typeArgs := []
    inputs := inputs
    outputs := outputs
  }
  let outParams := proc.outputs.map (fun (p : Parameter) => p.name.text)
  let outParams := if writesHeap then "$heap" :: outParams else outParams
  -- Resolve InstanceCalls in LocalVariable inits
  let paramTypeMap := proc.inputs.filterMap fun p =>
    match p.type.val with | .UserDefined name => some (p.name.text, name.text) | _ => none
  let resolveBody (body : StmtExpr) : StmtExpr :=
    let resolved := resolveInstanceCallsInBody paramTypeMap body
    -- Also resolve constrained types in quantifiers
    (resolveConstrainedInExpr constrainedBaseTypes ⟨resolved, .empty⟩).val
  -- Build type environment from procedure parameters for real-number detection
  let typeEnv : TypeEnv := proc.inputs.map fun p => (p.name.text, p.type.val)
  let bodyStmts : Core.Statements := match proc.body with
    | .Transparent ⟨bodyExpr, _⟩ => translateStmtModel isFunction outParams (resolveBody bodyExpr) typeEnv constrainedBaseTypes
    | .Opaque _ (some ⟨impl, _⟩) _ => translateStmtModel isFunction outParams (resolveBody impl) typeEnv constrainedBaseTypes
    | .Opaque _ none _ =>
      -- Opaque with no implementation: assume false (no body available)
      [Core.Statement.assume "no_body" (.const () (.boolConst false)) .empty]
    | .External =>
      [Core.Statement.assume "no_body" (.const () (.boolConst false)) .empty]
    | _ => []
  let heapInit := Core.Statement.set ⟨"$heap", ()⟩ (.fvar () ⟨"$heap_in", ()⟩ none) .empty
  let bodyStmts := if writesHeap then heapInit :: bodyStmts else bodyStmts
  let successCtor : Core.Expression.Expr := .op () ⟨"Success", ()⟩ none
  let setResult := Core.Statement.set ⟨"$result", ()⟩ successCtor .empty
  let body := [setResult, Imperative.Stmt.block "$body" bodyStmts .empty]
  -- Build all preconditions (user + constraint) with proper indexing
  -- For heap-writing procs, preconditions reference $heap_in (the input heap)
  let translatePrecond (pre : StmtExprMd) : Core.Expression.Expr :=
    let e := translateExprModel pre.val
    if writesHeap then replaceHeapVar e else e
  let allPrecondExprs := proc.preconditions.map translatePrecond ++
    (if constrainedBaseTypes.isEmpty then [] else
      proc.inputs.filterMap fun p =>
        match p.type.val with
        | .UserDefined n =>
          if (constrainedBaseTypes.find? (fun x => x.1 == n.text)).isSome then
            some (.app () (.op () ⟨n.text ++ "$constraint", ()⟩ none) (.fvar () ⟨p.name.text, ()⟩ none) : Core.Expression.Expr)
          else none
        | _ => none)
  let preconditions : ListMap Core.CoreLabel Core.Procedure.Check :=
    let n := allPrecondExprs.length
    (allPrecondExprs.zip (List.range n)).map fun (expr, i) =>
      (if n == 1 then "requires" else s!"requires_{i}", { expr })
  -- Extract postconditions from Opaque body
  let userPostcondExprs : List Core.Procedure.Check := match proc.body with
    | .Opaque postconds _ _ =>
      postconds.map fun post => ({ expr := translateExprModel post.val } : Core.Procedure.Check)
    | _ => []
  -- Add constraint postcondition for constrained output types
  let mkConstraintCheck (name paramName : String) : Core.Procedure.Check :=
    { expr := .app () (.op () ⟨name ++ "$constraint", ()⟩ none) (.fvar () ⟨paramName, ()⟩ none) }
  let constraintPostconds : List Core.Procedure.Check := proc.outputs.foldl (fun acc p =>
    match p.type.val with
    | .UserDefined name =>
      if constrainedBaseTypes.any (·.1 == name.text) then acc ++ [mkConstraintCheck name.text p.name.text]
      else acc
    | _ => acc) []
  let userPostcondExprs := userPostcondExprs ++ constraintPostconds
  -- Frame condition for heap-writing procs with modifies clause
  let frameCondition : List Core.Procedure.Check :=
    if !writesHeap then [] else
    match proc.body with
    | .Opaque _ _ modif =>
      if modif.isEmpty then [] else
      -- ∀ ref. ∀ field. (ref < nextRef ∧ ¬(ref == self)) → readField($heap_in, ref, field) == readField($heap, ref, field)
      let modifTargets := modif.filterMap fun m => match m.val with
        | .Identifier name => some name.text | _ => none
      let refVar : Core.Expression.Expr := .bvar () 1
      let fieldVar : Core.Expression.Expr := .bvar () 0
      let heapIn : Core.Expression.Expr := .fvar () ⟨"$heap_in", ()⟩ none
      let heapOut : Core.Expression.Expr := .fvar () ⟨"$heap", ()⟩ none
      let refLtNext : Core.Expression.Expr :=
        .app () (.app () (.op () ⟨"Int.Lt", ()⟩ none)
          (.app () (.op () ⟨"Composite..ref!", ()⟩ none) refVar))
          (.app () (.op () ⟨"Heap..nextReference!", ()⟩ none) heapIn)
      let notModified := modifTargets.foldl (fun acc name =>
        .app () (.app () (.op () ⟨"Bool.And", ()⟩ none) acc)
          (.app () (.op () ⟨"Bool.Not", ()⟩ none)
            (.eq () refVar (.fvar () ⟨name, ()⟩ none)))) refLtNext
      let readOld := .app () (.app () (.app () (.op () ⟨"readField", ()⟩ none) heapIn) refVar) fieldVar
      let readNew := .app () (.app () (.app () (.op () ⟨"readField", ()⟩ none) heapOut) refVar) fieldVar
      let eq := .eq () readOld readNew
      let iteExpr := .ite () notModified eq (.const () (.boolConst true))
      let forallExpr := .all () "" none (.all () "" none iteExpr)
      [{ expr := forallExpr }]
    | _ => []
  let allPostcondExprs := userPostcondExprs ++ frameCondition
  let postconditions : ListMap Core.CoreLabel Core.Procedure.Check :=
    let n := allPostcondExprs.length
    (allPostcondExprs.zip (List.range n)).map fun (check, i) =>
      (if n == 1 then "postcondition" else s!"postcondition_{i}", check)
  let spec : Core.Procedure.Spec := { modifies := [], preconditions := preconditions, postconditions }
  .proc { header, spec, body }

mutual
/-- Collect field names accessed via FieldSelect in a StmtExpr. -/
public def collectFieldNamesMd (e : StmtExprMd) : List String := collectFieldNames e.val
  termination_by sizeOf e
  decreasing_by cases e; term_by_mem
public def collectFieldNames : StmtExpr → List String
  | .FieldSelect target fieldName => fieldName.text :: collectFieldNamesMd target
  | .Block stmts _ => stmts.attach.flatMap fun ⟨s, _⟩ => collectFieldNamesMd s
  | .Return (some v) => collectFieldNamesMd v
  | .LocalVariable _ _ (some init) => collectFieldNamesMd init
  | .Assign targets v => targets.attach.flatMap (fun ⟨t, _⟩ => collectFieldNamesMd t) ++ collectFieldNamesMd v
  | .IfThenElse c t e => collectFieldNamesMd c ++ collectFieldNamesMd t ++
    (match e with | some e => collectFieldNamesMd e | none => [])
  | .PrimitiveOp _ args => args.attach.flatMap fun ⟨a, _⟩ => collectFieldNamesMd a
  | .StaticCall _ args => args.attach.flatMap fun ⟨a, _⟩ => collectFieldNamesMd a
  | .InstanceCall target _ args => collectFieldNamesMd target ++ args.attach.flatMap fun ⟨a, _⟩ => collectFieldNamesMd a
  | .Old v => collectFieldNamesMd v
  | _ => []
  termination_by e => sizeOf e
  decreasing_by all_goals (simp_wf; try term_by_mem)
end

/-- Assemble a full Core.Program from a Laurel Program -/
@[expose] public def translateProgramModel (program : Program) : Core.Program :=
  let withDefs := { program with
    staticProcedures := coreDefinitionsForLaurel.staticProcedures ++ program.staticProcedures
    types := coreDefinitionsForLaurel.types ++ program.types
  }
  let composites := allComposites withDefs
  let compositeNames := composites.map (·.name.text)
  let allProcs := withDefs.staticProcedures.filter (fun p => !p.body.isExternal)
  -- funcNames includes ALL isFunctional procs (static + instance) for call/function distinction
  let funcNames := withDefs.staticProcedures.filter (·.isFunctional) |>.map (·.name.text)
  let instanceFuncNames := (allComposites withDefs).flatMap fun ct =>
    ct.instanceProcedures.filter (·.isFunctional) |>.map (·.name.text)
  let isFunc := fun n => funcNames.contains n || instanceFuncNames.contains n
  let (_, procProcs) := allProcs.partition (·.isFunctional)
  -- Map constrained type names to their base types
  let constrainedBaseTypes : List (String × HighType) := withDefs.types.filterMap fun td => match td with
    | .Constrained ct => some (ct.name.text, ct.base.val)
    | _ => none
  -- Procedure declarations (non-functional, non-external)
  let procDecls := procProcs.map (fun p => translateProcModel isFunc compositeNames p constrainedBaseTypes composites)
  -- Instance procedure declarations
  let instanceProcs := withDefs.types.foldl (fun (acc, outerCtr) td =>
    match td with
    | .Composite ct =>
      -- Find which composite defines a field (for inherited fields)
      let fieldOwner (fieldName : String) : String :=
        let rec findOwner (name : String) (fuel : Nat) : String :=
          match fuel with
          | 0 => name
          | fuel + 1 =>
            match composites.find? (fun c => c.name.text == name) with
            | some c =>
              if c.fields.any (fun f => f.name.text == fieldName) then name
              else match c.extending.head? with
                | some parent => findOwner parent.text fuel
                | none => name
            | none => name
        findOwner ct.name.text composites.length
      let fieldPrefix (fieldName : String) : String := fieldOwner fieldName ++ "."
      -- Encode field type in qualified name for Box type selection
      let fieldTypeSuffix (fieldName : String) : String :=
        let owner := fieldOwner fieldName
        let ownerCt := composites.find? (fun c => c.name.text == owner)
        let fields := match ownerCt with | some c => c.fields | none => ct.fields
        match fields.find? (fun f => f.name.text == fieldName) with
        | some f => match f.type.val with
          | .TBool => ":bool"
          | .TString => ":string"
          | .UserDefined uname =>
            match (constrainedBaseTypes.find? fun x => x.1 == uname.text) with
            | some (_, .TInt) => ":" ++ uname.text
            | _ => ""
          | _ => ""
        | none => ""
      let rec qualifyMd : StmtExprMd → StmtExprMd
        | ⟨.FieldSelect target fieldName, md⟩ =>
          ⟨.FieldSelect (qualifyMd target) { fieldName with text := fieldPrefix fieldName.text ++ fieldName.text ++ fieldTypeSuffix fieldName.text }, md⟩
        | ⟨.PrimitiveOp op args, md⟩ =>
          ⟨.PrimitiveOp op (args.attach.map fun ⟨a, _⟩ => qualifyMd a), md⟩
        | ⟨.StaticCall callee args, md⟩ =>
          ⟨.StaticCall callee (args.attach.map fun ⟨a, _⟩ => qualifyMd a), md⟩
        | ⟨.Old v, md⟩ => ⟨.Old (qualifyMd v), md⟩
        | ⟨.Forall name (some trigger) body, md⟩ =>
          ⟨.Forall name (some (qualifyMd trigger)) (qualifyMd body), md⟩
        | ⟨.Forall name none body, md⟩ =>
          ⟨.Forall name none (qualifyMd body), md⟩
        | ⟨.Exists name (some trigger) body, md⟩ =>
          ⟨.Exists name (some (qualifyMd trigger)) (qualifyMd body), md⟩
        | ⟨.Exists name none body, md⟩ =>
          ⟨.Exists name none (qualifyMd body), md⟩
        | ⟨.IfThenElse c t (some e), md⟩ =>
          ⟨.IfThenElse (qualifyMd c) (qualifyMd t) (some (qualifyMd e)), md⟩
        | ⟨.IfThenElse c t none, md⟩ =>
          ⟨.IfThenElse (qualifyMd c) (qualifyMd t) none, md⟩
        | e => e
        termination_by e => sizeOf e
        decreasing_by all_goals (simp_wf; first | term_by_mem | omega)
      let rec qualifyStmt : StmtExprMd → StmtExprMd
        | ⟨.Assign [⟨.FieldSelect target fieldName, tmd⟩] value, md⟩ =>
          ⟨.Assign [⟨.FieldSelect (qualifyMd target) { fieldName with text := fieldPrefix fieldName.text ++ fieldName.text ++ fieldTypeSuffix fieldName.text }, tmd⟩]
            (qualifyMd value), md⟩
        | ⟨.Assign targets value, md⟩ =>
          ⟨.Assign (targets.map qualifyMd) (qualifyMd value), md⟩
        | ⟨.Return (some v), md⟩ => ⟨.Return (some (qualifyMd v)), md⟩
        | ⟨.LocalVariable id ty (some init), md⟩ =>
          ⟨.LocalVariable id ty (some (qualifyMd init)), md⟩
        | ⟨.Assert c, md⟩ => ⟨.Assert (qualifyMd c), md⟩
        | ⟨.InstanceCall target callee args, md⟩ =>
          -- self~>method(args) → StaticCall "Composite..method" [self, args...]
          let qualName : Identifier := { callee with text := ct.name.text ++ ".." ++ callee.text }
          ⟨.StaticCall qualName (target :: args.map qualifyMd), md⟩
        | ⟨.Block stmts label, md⟩ => ⟨.Block (stmts.attach.map fun ⟨s, _⟩ => qualifyStmt s) label, md⟩
        | s => s
        termination_by s => sizeOf s
        decreasing_by all_goals (simp_wf; first | term_by_mem | omega)
      -- Count bare expression statements in a body
      let countBareExprs (body : Body) : Nat := match body with
        | .Transparent ⟨.Block stmts _, _⟩ =>
          stmts.filter (fun s => match s.val with
            | .Return _ | .Assign _ _ | .LocalVariable _ _ _ | .Assert _ | .Assume _
            | .Block _ _ | .IfThenElse _ _ _ | .While _ _ _ _ | .StaticCall _ _
            | .InstanceCall _ _ _ => false
            | _ => true) |>.length
        | _ => 0
      let qualifyBody (counter : Nat) (body : Body) : Body := match body with
        | .Transparent ⟨.Block stmts label, md⟩ =>
          let (stmts', _) := stmts.foldl (fun (acc, cnt) s =>
            match s.val with
            | .Return _ | .Assign _ _ | .LocalVariable _ _ _ | .Assert _ | .Assume _
            | .Block _ _ | .IfThenElse _ _ _ | .While _ _ _ _ | .StaticCall _ _
            | .InstanceCall _ _ _ => (acc ++ [qualifyStmt s], cnt)
            | _ =>
              let unusedName := s!"$unused_{cnt}"
              let newStmt : StmtExprMd := ⟨.LocalVariable { text := unusedName } ⟨.TInt, .empty⟩ (some (qualifyMd s)), .empty⟩
              (acc ++ [newStmt], cnt + 1)) ([], counter + 1)
          .Transparent ⟨.Block stmts' label, md⟩
        | .Transparent ⟨expr, md⟩ =>
          -- Non-block transparent body (e.g., bare `opaque` expression)
          -- Wrap as $unused init, same as the real translator's exprAsUnusedInit
          let unusedName := s!"$unused_{counter + 1}"
          let newStmt : StmtExprMd := ⟨.LocalVariable { text := unusedName } ⟨.TInt, .empty⟩ (some (qualifyMd ⟨expr, md⟩)), .empty⟩
          .Transparent ⟨.Block [newStmt] none, md⟩
        | .Opaque postconds (some ⟨.Block stmts label, md⟩) modif =>
          .Opaque (postconds.map qualifyMd) (some ⟨.Block (stmts.map qualifyStmt) label, md⟩) modif
        | .Opaque postconds (some ⟨expr, md⟩) modif =>
          -- Non-block opaque impl (e.g., bare `opaque` identifier) → wrap as $unused init
          let unusedName := s!"$unused_{counter + 1}"
          let newStmt : StmtExprMd := ⟨.LocalVariable { text := unusedName } ⟨.TInt, .empty⟩ (some (qualifyMd ⟨expr, md⟩)), .empty⟩
          .Opaque (postconds.map qualifyMd) (some ⟨.Block [newStmt] none, md⟩) modif
        | .Opaque postconds none modif =>
          .Opaque (postconds.map qualifyMd) none modif
        | other => other
      let (procs, nextCounter) := (ct.instanceProcedures.filter (!·.body.isExternal)).foldl
        (fun (acc, ctr) proc =>
          let p := { proc with
            name := { proc.name with text := qualifiedName ct.name.text proc.name.text }
            body := qualifyBody ctr proc.body
            preconditions := proc.preconditions.map qualifyMd }
          (acc ++ [p], ctr + countBareExprs proc.body)) ([], outerCtr)
      (acc ++ procs, nextCounter)
    | _ => (acc, outerCtr)) (([] : List Procedure), 0)
  let instanceProcs := instanceProcs.1
  let instanceProcDecls := instanceProcs.map (fun p => translateProcModel isFunc compositeNames p constrainedBaseTypes composites)

  -- Datatypes: translate each Laurel datatype to a Core type decl
  let datatypes := withDefs.types.filterMap fun td => match td with
    | .Datatype dt => some dt | _ => none
  let datatypeDecls := datatypes.map fun dt =>
    let constrs : List (Lambda.LConstr Unit) := dt.constructors.map fun c =>
      { name := ⟨c.name.text, ()⟩
        args := c.args.map fun ⟨n, ty⟩ =>
          (⟨n.text, ()⟩, coreMonoType ty.val)
        testerName := s!"{dt.name.text}..is{c.name.text}" }
    let constrs : List (Lambda.LConstr Unit) := if constrs.isEmpty then
      [{ name := ⟨s!"Mk{dt.name.text}", ()⟩, args := [] }]
    else constrs
    Core.Decl.type (.data [{
      name := dt.name.text
      typeArgs := []
      constrs := constrs
      constrs_ne := by simp [constrs]; split <;> simp_all [List.isEmpty_iff]
    }])
  -- Helper: resolve constrained type to ultimate base type
  let resolveConstrainedTy (ty : HighType) : HighType :=
    match ty with
    | .UserDefined name =>
      let rec resolve (n : String) (fuel : Nat) : HighType :=
        match fuel with
        | 0 => ty
        | fuel + 1 => match constrainedBaseTypes.find? (fun c => c.1 == n) with
          | some (_, base) => match base with
            | .UserDefined parent => resolve parent.text fuel
            | _ => base
          | none => ty
      resolve name.text constrainedBaseTypes.length
    | _ => ty
  -- Functions: external functions become Core function decls (no body)
  let externalFuncs := allProcs.filter (fun p => p.isFunctional && p.body.isExternal)
  let externalFuncDecls := externalFuncs.map fun proc =>
    let inputs := proc.inputs.map translateParamModel
    let outputTy := match proc.outputs.head? with
      | some p => coreMonoType (resolveConstrainedTy p.type.val)
      | none => Lambda.LMonoTy.int
    Core.Decl.func { name := ⟨proc.name.text, ()⟩, typeArgs := [], inputs, output := outputTy, body := none }
  -- Non-external functions with transparent bodies
  let transparentFuncs := allProcs.filter (fun p => p.isFunctional && !p.body.isExternal)
  let transparentFuncDecls := transparentFuncs.map fun proc =>
    let inputs := proc.inputs.map translateParamModel
    let outputTy := match proc.outputs.head? with
      | some p => coreMonoType (resolveConstrainedTy p.type.val)
      | none => Lambda.LMonoTy.int
    let body := match proc.body with
      | .Transparent b => some (translateExprModel b.val)
      | .Opaque _ (some impl) _ => some (translateExprModel impl.val)
      | _ => none
    let preconditions := proc.preconditions.map fun pre =>
      { expr := translateExprModel pre.val, md := () }
    Core.Decl.func { name := ⟨proc.name.text, ()⟩, typeArgs := [], inputs, output := outputTy, body, preconditions }
  -- ExceptionResult
  let exceptionResultDecl := modelExceptionResultDecl
  -- Assemble in same order as real translator
  -- Dynamic infrastructure datatypes based on program composites
  -- TypeTag: one constructor per composite type
  let typeTagConstrs : List (Lambda.LConstr Unit) := compositeNames.map fun n =>
    { name := ⟨n ++ "_TypeTag", ()⟩, args := [], testerName := "TypeTag..is" ++ n ++ "_TypeTag" }
  let typeTagConstrs := if typeTagConstrs.isEmpty then
    [{ name := ⟨"MkTypeTag", ()⟩, args := [] }] else typeTagConstrs
  let typeTagDecl := Core.Decl.type (.data [{
    name := "TypeTag", typeArgs := [], constrs := typeTagConstrs,
    constrs_ne := by simp [typeTagConstrs]; split <;> simp_all [List.isEmpty_iff] }])
  -- Field: one constructor per field across all composites
  let fieldNames := composites.foldl (fun acc ct =>
    acc ++ ct.fields.map (fun f => ct.name.text ++ "." ++ f.name.text)) ([] : List String)
  let fieldConstrs : List (Lambda.LConstr Unit) := fieldNames.map fun n =>
    { name := ⟨n, ()⟩, args := [], testerName := "Field..is" ++ n }
  let fieldConstrs := if fieldConstrs.isEmpty then
    [{ name := ⟨"MkField", ()⟩, args := [] }] else fieldConstrs
  let fieldDecl := Core.Decl.type (.data [{
    name := "Field", typeArgs := [], constrs := fieldConstrs,
    constrs_ne := by simp [fieldConstrs]; split <;> simp_all [List.isEmpty_iff] }])

  -- Box: generate constructors based on field types when procedures access fields.
  let resolveFieldType (ty : HighType) : HighType := match ty with
    | .UserDefined name =>
      match (constrainedBaseTypes.find? fun x => x.1 == name.text) with
      | some (_, base) => base
      | none => ty
    | other => other
  let hasFieldAccess := composites.any fun ct =>
    ct.instanceProcedures.any fun p => match p.body with
      | .Transparent b => directlyReadsHeapMd b || directlyWritesHeapMd b
      | .Opaque postconds (some impl) _ =>
        directlyReadsHeapMd impl || directlyWritesHeapMd impl ||
        postconds.any (fun pc => directlyReadsHeapMd pc)
      | .Opaque postconds none _ =>
        postconds.any (fun pc => directlyReadsHeapMd pc)
      | _ => false
  let boxConstrNames : List String := if !hasFieldAccess then [] else
    -- Only include Box constructors for field types that are actually accessed
    let accessedFieldTypes := composites.foldl (fun (acc : List String) (ct : CompositeType) =>
      ct.instanceProcedures.foldl (fun (acc : List String) (p : Procedure) =>
        let bodyFields := match p.body with
          | .Transparent b => collectFieldNames b.val
          | .Opaque postconds (some impl) _ =>
            collectFieldNames impl.val ++ postconds.flatMap fun pc => collectFieldNamesMd pc
          | .Opaque postconds none _ =>
            postconds.flatMap fun pc => collectFieldNamesMd pc
          | _ => []
        bodyFields.foldl (fun (acc : List String) (fname : String) =>
          let fieldTy := composites.findSome? fun (c : CompositeType) =>
            match c.fields.find? (fun (f : Field) => f.name.text == fname) with
            | some f => some (resolveFieldType f.type.val)
            | none => none
          match fieldTy with
          | some ty =>
            let name := match ty with
              | .TInt => "BoxInt" | .TBool => "BoxBool"
              | .TString => "BoxString" | .UserDefined _ => "BoxComposite"
              | _ => "BoxInt"
            if acc.contains name then acc else acc ++ [name]
          | none => acc) acc) acc) ([] : List String)
    if accessedFieldTypes.isEmpty then ["BoxInt"] else accessedFieldTypes
  let boxConstrs : List (Lambda.LConstr Unit) := boxConstrNames.map fun n =>
    let (argName, argTy) := match n with
      | "BoxInt" => ("intVal", Lambda.LMonoTy.int)
      | "BoxBool" => ("boolVal", Lambda.LMonoTy.bool)
      | "BoxString" => ("stringVal", Lambda.LMonoTy.string)
      | _ => ("compositeVal", Lambda.LMonoTy.tcons "Composite" [])
    { name := ⟨n, ()⟩, args := [(⟨argName, ()⟩, argTy)], testerName := "Box..is" ++ n }
  let boxConstrs := if boxConstrs.isEmpty then
    [{ name := ⟨"MkBox", ()⟩, args := [] }] else boxConstrs
  let boxDecl := Core.Decl.type (.data [{
    name := "Box", typeArgs := [], constrs := boxConstrs,
    constrs_ne := by simp only [boxConstrs]; split <;> simp_all [List.isEmpty_iff] }])
  -- Translate heapConstants.types (Composite, NotSupportedYet, Heap) through the same
  -- datatype translation as user types, but with typeTag field added to Composite
  -- Type mapper for heapConstants.types: maps UserDefined to the correct Core type
  -- based on what's known at translation time (before Box is generated)
  let knownDatatypeNames := (["Field", "Box"] ++ (heapConstants.types ++ coreDefinitionsForLaurel.types).filterMap fun td =>
    match td with | .Datatype dt => some dt.name.text | _ => none).filter fun n => !compositeNames.contains n
  let heapCoreTypeName (ty : HighType) : String :=
    match ty with
    | .UserDefined name =>
      if knownDatatypeNames.contains name.text then name.text else "Composite"
    | other => coreTypeName other
  let heapDatatypes := heapConstants.types.filterMap fun td => match td with
    | .Datatype dt => some dt | _ => none
  let rec heapTranslateType (ty : HighType) : Lambda.LMonoTy :=
    match ty with
    | .TInt => Lambda.LMonoTy.int
    | .TBool => Lambda.LMonoTy.bool
    | .TString => Lambda.LMonoTy.string
    | .TReal => Lambda.LMonoTy.real
    | .TMap k v => Lambda.LMonoTy.tcons "Map" [heapTranslateType k.val, heapTranslateType v.val]
    | .TSet e => Lambda.LMonoTy.tcons "Map" [heapTranslateType e.val, Lambda.LMonoTy.bool]
    | .UserDefined name =>
      if knownDatatypeNames.contains name.text then Lambda.LMonoTy.tcons name.text []
      else Lambda.LMonoTy.tcons "Composite" []
    | _ => coreMonoType ty
  let heapDatatypeDecls := heapDatatypes.map fun dt =>
    let constrs : List (Lambda.LConstr Unit) := dt.constructors.map fun c =>
      { name := ⟨c.name.text, ()⟩
        args := (c.args.map fun ⟨n, ty⟩ =>
          (⟨n.text, ()⟩, heapTranslateType ty.val)) ++
          -- Add typeTag field to Composite
          (if dt.name.text == "Composite" then [(⟨"typeTag", ()⟩, Lambda.LMonoTy.tcons "TypeTag" [])] else [])
        testerName := s!"{dt.name.text}..is{c.name.text}" }
    let constrs := if constrs.isEmpty then
      [{ name := ⟨s!"Mk{dt.name.text}", ()⟩, args := [] }]
    else constrs
    Core.Decl.type (.data [{
      name := dt.name.text, typeArgs := [], constrs := constrs,
      constrs_ne := by
        simp only [constrs]
        split <;> simp_all [List.isEmpty_iff] }])
  let heapDatatypeDeclsNoHeap := heapDatatypeDecls.filter fun d => (Core.Decl.name d).name != "Heap"
  let heapDeclOnly := heapDatatypeDecls.filter fun d => (Core.Decl.name d).name == "Heap"
  let infraDatatypes := [typeTagDecl, fieldDecl] ++ heapDatatypeDeclsNoHeap ++ [boxDecl] ++ heapDeclOnly
  -- Heap functions (from heapConstants)
  -- Translate heap functions from heapConstants (non-external, isFunctional)
  let heapProcs := heapConstants.staticProcedures.filter (fun p => !p.body.isExternal && p.isFunctional)
  let heapFuncDecls := heapProcs.map fun proc =>
    let translateHeapParam (p : Parameter) : Lambda.Identifier Unit × Lambda.LMonoTy :=
      let tyName := match p.type.val with
        | .UserDefined n => if compositeNames.contains n.text then "Composite" else coreTypeName p.type.val
        | _ => coreTypeName p.type.val
      (⟨p.name.text, ()⟩, Lambda.LMonoTy.tcons tyName [])
    let inputs := proc.inputs.map translateHeapParam
    let outputTy := match proc.outputs.head? with
      | some p => Lambda.LMonoTy.tcons (match p.type.val with
          | .UserDefined n => if compositeNames.contains n.text then "Composite" else coreTypeName p.type.val
          | _ => coreTypeName p.type.val) []
      | none => Lambda.LMonoTy.int
    let body := match proc.body with
      | .Transparent b => some (translateExprModel b.val)
      | _ => none
    Core.Decl.func { name := ⟨proc.name.text, ()⟩, typeArgs := [], inputs, output := outputTy, body }
  -- Constrained type artifacts
  let constrainedTypes := withDefs.types.filterMap fun td => match td with
    | .Constrained ct => some ct | _ => none
  let constraintFuncDecls := constrainedTypes.map fun ct =>
    -- Resolve base type to ultimate base (e.g., posnat → nat → int)
    let rec resolveBase (ty : HighType) (fuel : Nat) : HighType :=
      match fuel, ty with
      | 0, _ => ty
      | fuel + 1, .UserDefined name =>
        match constrainedTypes.find? (fun c => c.name.text == name.text) with
        | some parent => resolveBase parent.base.val fuel
        | none => ty
      | _, _ => ty
    let resolvedBase := resolveBase ct.base.val constrainedTypes.length
    -- Build constraint body: include parent constraint if base is constrained
    let constraintBody := match ct.base.val with
      | .UserDefined parent =>
        if constrainedTypes.any (fun c => c.name.text == parent.text) then
          let parentCall := translateExprModel
            (.StaticCall { text := parent.text ++ "$constraint", uniqueId := none }
              [⟨.Identifier { ct.valueName with uniqueId := none }, .empty⟩])
          let ownConstraint := translateExprModel ct.constraint.val
          .app () (.app () (.op () ⟨"Bool.And", ()⟩ none) ownConstraint) parentCall
        else translateExprModel ct.constraint.val
      | _ => translateExprModel ct.constraint.val
    Core.Decl.func {
      name := ⟨ct.name.text ++ "$constraint", ()⟩, typeArgs := [],
      inputs := [(⟨ct.valueName.text, ()⟩, .tcons (coreTypeName resolvedBase) [])],
      output := Lambda.LMonoTy.bool, body := some constraintBody }
  let witnessProcDecls := constrainedTypes.map fun ct =>
    let md : Imperative.MetaData Core.Expression := .empty
    let witnessId : Identifier := { text := "$witness", uniqueId := none }
    -- Resolve base type to ultimate base (so no constraint assert is injected for intermediate types)
    let resolvedBase : WithMetadata HighType := match ct.base.val with
      | .UserDefined name =>
        let rec resolveW (n : String) (fuel : Nat) : HighType :=
          match fuel with
          | 0 => ct.base.val
          | fuel + 1 => match constrainedBaseTypes.find? (·.1 == n) with
            | some (_, .UserDefined parent) => resolveW parent.text fuel
            | some (_, base) => base
            | none => ct.base.val
        ⟨resolveW name.text constrainedBaseTypes.length, ct.base.md⟩
      | _ => ct.base
    let witnessInit : StmtExprMd :=
      ⟨.LocalVariable witnessId resolvedBase (some ct.witness), md⟩
    let constraintCall : StmtExprMd :=
      ⟨.StaticCall { text := ct.name.text ++ "$constraint", uniqueId := none }
        [⟨.Identifier { witnessId with uniqueId := none }, md⟩], md⟩
    let assertStmt : StmtExprMd := ⟨.Assert constraintCall, md⟩
    let witnessProc : Procedure := {
      name := { text := "$witness_" ++ ct.name.text, uniqueId := none }
      inputs := []
      outputs := []
      preconditions := []
      determinism := .deterministic none
      decreases := none
      isFunctional := false
      body := .Transparent ⟨.Block [witnessInit, assertStmt] none, md⟩
      md := md
    }
    translateProcModel isFunc compositeNames witnessProc constrainedBaseTypes composites
  -- Read function axioms: ∀ v: int. readIntN(BoxInt(v)) == v
  -- Emitted when there are int fields on composites (which means BoxInt will exist).
  -- Also emitted for constrained int types (int8, int16, int32, etc.) since they
  -- are eliminated to int by the constrained type elimination pass.
  let fields := allFields withDefs
  let constrainedIntNames := withDefs.types.filterMap fun td => match td with
    | .Constrained ct => match ct.base.val with | .TInt => some ct.name.text | _ => none
    | _ => none
  let hasIntField := fields.any fun (_, f) => match f.type.val with
    | .TInt => true
    | .UserDefined name => constrainedIntNames.contains name.text
    | _ => false
  let hasCompositeProcs := (nonExternalInstanceProcs withDefs).any fun (_, p) =>
    match p.body with
    | .Transparent b => directlyReadsHeapMd b || directlyWritesHeapMd b
    | .Opaque postconds (some impl) _ =>
      directlyReadsHeapMd impl || directlyWritesHeapMd impl ||
      postconds.any (fun pc => directlyReadsHeapMd pc)
    | .Opaque postconds none _ =>
      postconds.any (fun pc => directlyReadsHeapMd pc)
    | _ => false
  let readFuncAxioms : List Core.Decl :=
    if hasIntField && hasCompositeProcs then
      [("readInt32", "BoxInt"), ("readInt16", "BoxInt"), ("readInt8", "BoxInt")].map
        fun (readName, constrName) =>
          let readOp : Core.Expression.Expr := .op () ⟨readName, ()⟩ none
          let constrOp : Core.Expression.Expr := .op () ⟨constrName, ()⟩ none
          let v : Core.Expression.Expr := .bvar () 0
          let body : Core.Expression.Expr := .eq () (.app () readOp (.app () constrOp v)) v
          let axiomExpr : Core.Expression.Expr := .all () "v" none body
          Core.Decl.ax { name := readName ++ "_eq", e := axiomExpr }
    else []
  -- Ancestor functions: one per composite + ancestorsPerType
  let composites := allComposites withDefs
  let ancestorDecls : List Core.Decl := if composites.isEmpty then [] else
    -- ancestorsForX() = update(...update(const(false), Parent_TypeTag, true)..., X_TypeTag, true)
    let constFalse : Core.Expression.Expr := .app () (.op () ⟨"const", ()⟩ none) (.boolConst () false)
    let perType := composites.map fun ct =>
      -- Collect all ancestors transitively: parents, grandparents, ... + self
      let rec getAnc (name : String) : Nat → List String
        | 0 => [name]
        | fuel + 1 => match composites.find? (fun c => c.name.text == name) with
          | some c => c.extending.flatMap (fun p => getAnc p.text fuel) ++ [name]
          | none => [name]
      let allAncestors := ct.extending.flatMap (fun p => getAnc p.text 10) ++ [ct.name.text]
      let body := allAncestors.foldl (fun acc name =>
        let typeTag : Core.Expression.Expr := .op () ⟨name ++ "_TypeTag", ()⟩ none
        .app () (.app () (.app () (.op () ⟨"update", ()⟩ none) acc) typeTag) (.boolConst () true))
        constFalse
      Core.Decl.func {
        name := ⟨"ancestorsFor" ++ ct.name.text, ()⟩, typeArgs := [],
        inputs := [],
        output := Lambda.LMonoTy.tcons "Map" [Lambda.LMonoTy.tcons "TypeTag" [], Lambda.LMonoTy.bool],
        body := some body }
    -- ancestorsPerType() = update(update(..., const(const(false))), X_TypeTag, ancestorsForX)
    let constConstFalse : Core.Expression.Expr :=
      .app () (.op () ⟨"const", ()⟩ none) constFalse
    let combinedBody := composites.foldl (fun acc ct =>
      let typeTag : Core.Expression.Expr := .op () ⟨ct.name.text ++ "_TypeTag", ()⟩ none
      let ancestorsFor : Core.Expression.Expr := .op () ⟨"ancestorsFor" ++ ct.name.text, ()⟩ none
      .app () (.app () (.app () (.op () ⟨"update", ()⟩ none) acc) typeTag) ancestorsFor)
      constConstFalse
    let combined := Core.Decl.func {
      name := ⟨"ancestorsPerType", ()⟩, typeArgs := [],
      inputs := [],
      output := Lambda.LMonoTy.tcons "Map" [Lambda.LMonoTy.tcons "TypeTag" [],
        Lambda.LMonoTy.tcons "Map" [Lambda.LMonoTy.tcons "TypeTag" [], Lambda.LMonoTy.bool]],
      body := some combinedBody }
    perType ++ [combined]
  { decls := [exceptionResultDecl] ++ infraDatatypes ++ datatypeDecls ++ readFuncAxioms ++
    ancestorDecls ++ constraintFuncDecls ++ heapFuncDecls ++
    externalFuncDecls ++ transparentFuncDecls ++
    procDecls ++ witnessProcDecls ++ instanceProcDecls }

/-- The decls list produced by translateProgramModel, exposed for cross-module proofs. -/
public def translateProgramModelDecls (program : Program) : List Core.Decl :=
  (translateProgramModel program).decls

/-- Equation lemma: translateProgramModel program has specific decls. -/
@[simp] public theorem translateProgramModel_eq_decls (program : Program) :
    translateProgramModel program =
    { decls := translateProgramModelDecls program } := by
  unfold translateProgramModelDecls; cases translateProgramModel program; rfl


-- Note: model_first_decl_is_exception_result is true by construction
-- but unprovable because translateProgramModel is partial.
-- Validated by comprehensive differential tests.

/-- Decomposition of translateProgramModel into 12 segments.
    This is the model-side analogue of translateLaurelToCore_decls. -/
public theorem translateProgramModel_decls (program : Program) :
    ∃ (infraDatatypes datatypeDecls readFuncAxioms
       ancestorDecls constraintFuncDecls heapFuncDecls
       externalFuncDecls transparentFuncDecls
       procDecls witnessProcDecls instanceProcDecls : List Core.Decl),
    (translateProgramModel program).decls =
      [modelExceptionResultDecl] ++ infraDatatypes ++ datatypeDecls ++ readFuncAxioms ++
      ancestorDecls ++ constraintFuncDecls ++ heapFuncDecls ++
      externalFuncDecls ++ transparentFuncDecls ++
      procDecls ++ witnessProcDecls ++ instanceProcDecls := by
  unfold translateProgramModel
  exact ⟨_, _, _, _, _, _, _, _, _, _, _, rfl⟩

end Strata.Laurel
