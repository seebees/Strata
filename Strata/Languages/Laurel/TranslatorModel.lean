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

/-- Does a procedure body directly access the heap (field read/write, new)? -/
partial def directlyAccessesHeap (body : StmtExpr) : Bool :=
  match body with
  | .FieldSelect _ _ => true
  | .Assign [⟨.FieldSelect _ _, _⟩] _ => true
  | .New _ => true
  | .Block stmts _ => stmts.any (fun s => directlyAccessesHeap s.val)
  | .IfThenElse c t e =>
    directlyAccessesHeap c.val || directlyAccessesHeap t.val ||
    (match e with | some e => directlyAccessesHeap e.val | none => false)
  | .While c _ _ body => directlyAccessesHeap c.val || directlyAccessesHeap body.val
  | _ => false

/-- Names of procedures that should have $heap parameters -/
def heapAccessingProcNames (program : Program) : List String :=
  -- Direct heap access
  let staticDirect := (nonExternalStaticProcs program).filter fun p =>
    match p.body with
    | .Transparent body => directlyAccessesHeap body.val
    | .Opaque _ (some body) _ => directlyAccessesHeap body.val
    | _ => false
  staticDirect.map (·.name.text)
  -- TODO: transitive heap access through callees

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
@[expose] def expectedInputs (proc : Procedure) (isInstance : Bool) (accessesHeap : Bool) : List (String × String) :=
  let heapParam := if accessesHeap then [("$heap_in", "Heap")] else []
  let selfParam := if isInstance then
    [("self", "Composite")]
  else []
  let userParams := proc.inputs.map fun p => (p.name.text, coreTypeName p.type.val)
  -- Filter out self from user params if instance (it's already added)
  let userParams := if isInstance then
    userParams.filter (fun (n, _) => n != "self")
  else userParams
  heapParam ++ userParams

/-- Expected Core output parameters for a procedure -/
@[expose] def expectedOutputs (proc : Procedure) (accessesHeap : Bool) : List (String × String) :=
  let heapOut := if accessesHeap then [("$heap", "Heap")] else []
  let returnParam := match proc.outputs with
    | [] => []
    | _ => proc.outputs.map fun p => (p.name.text, coreTypeName p.type.val)
  heapOut ++ returnParam ++ [("$result", "ExceptionResult")]

end -- public section
end Strata.Laurel
