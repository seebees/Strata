/-
  Smoke test: verify that elimProc injects constraint preconditions.
-/
import Strata.Languages.Laurel.ConstrainedTypeElim

open Strata.Laurel

private def md : MetaData := #[]
private def id' (s : String) : Identifier := ⟨s, none⟩
private def mkE (e : StmtExpr) : StmtExprMd := ⟨e, md⟩

private def natCT : ConstrainedType := {
  name := id' "nat", base := ⟨.TInt, md⟩, valueName := id' "x"
  constraint := mkE (.PrimitiveOp .Geq [mkE (.Identifier (id' "x")), mkE (.LiteralInt 0)])
  witness := mkE (.LiteralInt 0)
}

private def emptyModel : SemanticModel := { nextId := 0, compositeCount := 0, refToDef := {} }

private def mkProgram (procs : List Procedure) : Program :=
  { staticProcedures := procs, staticFields := [], types := [.Constrained natCT] }

private def mkProc (name : String) (inputs : List Parameter) (preconds : List StmtExprMd := []) : Procedure :=
  { name := id' name, inputs, outputs := [], preconditions := preconds
    decreases := none, isFunctional := false
    body := .Transparent (mkE (.Return none)) [], md := md }

-- Test 1: one constrained input → 1 injected precondition
#eval! do
  let proc := mkProc "foo" [{ name := id' "n", type := ⟨.UserDefined (id' "nat"), md⟩ }]
  let (result, _) := constrainedTypeElim emptyModel (mkProgram [proc])
  let fooOpt := result.staticProcedures.find? (fun (p : Procedure) => p.name.text == "foo")
  match fooOpt with
  | some foo => IO.println s!"Test 1: preconditions={foo.preconditions.length} (expected 1)"
  | none => IO.println "Test 1: foo not found!"

-- Test 2: no constrained input → 0 injected preconditions
#eval! do
  let proc := mkProc "bar" [{ name := id' "x", type := ⟨.TInt, md⟩ }]
  let (result, _) := constrainedTypeElim emptyModel (mkProgram [proc])
  let barOpt := result.staticProcedures.find? (fun (p : Procedure) => p.name.text == "bar")
  match barOpt with
  | some bar => IO.println s!"Test 2: preconditions={bar.preconditions.length} (expected 0)"
  | none => IO.println "Test 2: bar not found!"

-- Test 3: existing precondition + constrained input → 2 preconditions
#eval! do
  let proc := mkProc "baz" [{ name := id' "n", type := ⟨.UserDefined (id' "nat"), md⟩ }]
    [mkE (.PrimitiveOp .Lt [mkE (.Identifier (id' "n")), mkE (.LiteralInt 100)])]
  let (result, _) := constrainedTypeElim emptyModel (mkProgram [proc])
  let bazOpt := result.staticProcedures.find? (fun (p : Procedure) => p.name.text == "baz")
  match bazOpt with
  | some baz => IO.println s!"Test 3: preconditions={baz.preconditions.length} (expected 2)"
  | none => IO.println "Test 3: baz not found!"

-- Test 4: two constrained inputs → 2 injected preconditions
#eval! do
  let proc := mkProc "add" [
    { name := id' "a", type := ⟨.UserDefined (id' "nat"), md⟩ },
    { name := id' "b", type := ⟨.UserDefined (id' "nat"), md⟩ }]
  let (result, _) := constrainedTypeElim emptyModel (mkProgram [proc])
  let addOpt := result.staticProcedures.find? (fun (p : Procedure) => p.name.text == "add")
  match addOpt with
  | some add => IO.println s!"Test 4: preconditions={add.preconditions.length} (expected 2)"
  | none => IO.println "Test 4: add not found!"
