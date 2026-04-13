/-
  Smoke test: verify that translateProcedureToFunction preserves axiom count
  on concrete Procedure values.
-/
import Strata.Languages.Laurel.LaurelToCoreTranslator

open Strata.Laurel
open Strata.Core

private def mkMd : MetaData := #[]
private def mkId' (s : String) : Identifier := ⟨s, none⟩
private def mkE (e : StmtExpr) : WithMetadata StmtExpr := ⟨e, mkMd⟩
private def emptyModel : SemanticModel := { nextId := 0, compositeCount := 0, refToDef := {} }
private def mkState : TranslateState := { model := emptyModel }

private def getPostconds' : Body → List (WithMetadata StmtExpr)
  | .Transparent _ posts => posts
  | .Opaque posts _ _ => posts
  | .Abstract posts => posts
  | .External => []

private def checkAxiomCount (label : String) (proc : Procedure) : IO Unit := do
  let (result, _) := translateProcedureToFunction {} false proc mkState
  let pLen := (getPostconds' proc.body).length
  match result with
  | some (.func f _) =>
    let aLen := f.axioms.length
    if aLen == pLen then
      IO.println s!"✓ {label}: axioms={aLen}, postconds={pLen}"
    else
      IO.println s!"✗ {label}: axioms={aLen} ≠ postconds={pLen} — MISMATCH!"
  | some _ => IO.println s!"? {label}: got non-func decl"
  | none   => IO.println s!"? {label}: returned none (translation failed)"

-- Test 1: Transparent body, 0 postconditions
#eval! checkAxiomCount "Transparent/0-post" {
  name := mkId' "f0", inputs := [], outputs := [], preconditions := [],
  decreases := none, isFunctional := true,
  body := .Transparent (mkE (.LiteralInt 42)) [], md := mkMd
}

-- Test 2: Opaque body, 1 postcondition, no impl
#eval! checkAxiomCount "Opaque/1-post" {
  name := mkId' "f1",
  inputs := [{ name := mkId' "x", type := ⟨.TInt, mkMd⟩ }],
  outputs := [{ name := mkId' "result", type := ⟨.TInt, mkMd⟩ }],
  preconditions := [], decreases := none, isFunctional := true,
  body := .Opaque
    [mkE (.PrimitiveOp .Gt [mkE (.Identifier (mkId' "result")), mkE (.LiteralInt 0)])]
    none [],
  md := mkMd
}

-- Test 3: Opaque body, 2 postconditions
#eval! checkAxiomCount "Opaque/2-post" {
  name := mkId' "f2",
  inputs := [{ name := mkId' "x", type := ⟨.TInt, mkMd⟩ }],
  outputs := [{ name := mkId' "result", type := ⟨.TInt, mkMd⟩ }],
  preconditions := [], decreases := none, isFunctional := true,
  body := .Opaque
    [ mkE (.PrimitiveOp .Gt [mkE (.Identifier (mkId' "result")), mkE (.LiteralInt 0)])
    , mkE (.PrimitiveOp .Lt [mkE (.Identifier (mkId' "result")), mkE (.LiteralInt 100)])
    ] none [],
  md := mkMd
}

-- Test 4: External body (0 postconditions)
#eval! checkAxiomCount "External/0-post" {
  name := mkId' "f_ext", inputs := [], outputs := [], preconditions := [],
  decreases := none, isFunctional := true, body := .External, md := mkMd
}

-- Test 5: Abstract body, 1 postcondition
#eval! checkAxiomCount "Abstract/1-post" {
  name := mkId' "f_abs",
  inputs := [{ name := mkId' "x", type := ⟨.TInt, mkMd⟩ }],
  outputs := [{ name := mkId' "result", type := ⟨.TInt, mkMd⟩ }],
  preconditions := [], decreases := none, isFunctional := true,
  body := .Abstract
    [mkE (.PrimitiveOp .Eq [mkE (.Identifier (mkId' "result")), mkE (.Identifier (mkId' "x"))])],
  md := mkMd
}

-- Test 6: Transparent body WITH postconditions (2 posts)
#eval! checkAxiomCount "Transparent/2-post" {
  name := mkId' "f_tp",
  inputs := [{ name := mkId' "x", type := ⟨.TInt, mkMd⟩ }],
  outputs := [{ name := mkId' "result", type := ⟨.TInt, mkMd⟩ }],
  preconditions := [], decreases := none, isFunctional := true,
  body := .Transparent (mkE (.Identifier (mkId' "x")))
    [ mkE (.PrimitiveOp .Eq [mkE (.Identifier (mkId' "result")), mkE (.Identifier (mkId' "x"))])
    , mkE (.PrimitiveOp .Gt [mkE (.Identifier (mkId' "result")), mkE (.LiteralInt 0)])
    ],
  md := mkMd
}
