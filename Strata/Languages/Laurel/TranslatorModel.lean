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

end -- public section
end Strata.Laurel
