/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Laurel.LaurelToCoreTranslator
import Strata.Languages.Core.Procedure

/-!
# Laurel-level Polymorphic Procedure Tests

Tests that Laurel procedures with `typeArgs` translate correctly through
the Laurel→Core pipeline. Validates:
1. Type parameters propagate to Core procedure headers
2. Type variable references (`UserDefined` matching a type param) become `ftvar`
3. `Applied` types (e.g., `Sequence<T>`) become `tcons` in Core
4. Non-generic procedures are unaffected (regression)
-/

open Strata.Laurel

private def wm (v : α) : WithMetadata α := ⟨v, .empty⟩
private def ident (s : String) : Identifier := ⟨s, none⟩

/-- Extract the first Core procedure from a translation result -/
private def getFirstProc (prog : Program) : Option Core.Procedure :=
  let (result, _) := translate {} prog
  result.bind fun coreProg =>
    coreProg.decls.findSome? fun d => d.getProc?

/-- Check that translation produces a Core program -/
private def translationSucceeds (prog : Program) : Bool :=
  let (result, _) := translate {} prog
  result.isSome

---------------------------------------------------------------------
-- Test 1: Opaque polymorphic identity<T> with postcondition
---------------------------------------------------------------------
section PolymorphicIdentity

private def identityProc : Procedure := {
  name := ident "identity"
  typeArgs := [⟨ident "T"⟩]
  inputs := [⟨ident "x", wm (.UserDefined (ident "T"))⟩]
  outputs := [⟨ident "r", wm (.UserDefined (ident "T"))⟩]
  preconditions := []
  decreases := none
  isFunctional := false
  body := .Opaque
    [wm (.PrimitiveOp .Eq [wm (.Identifier (ident "r")), wm (.Identifier (ident "x"))])]
    none []
  md := .empty
}

private def identityProg : Program := {
  staticProcedures := [identityProc]
  staticFields := []
  types := []
}

-- Translation succeeds with no resolution errors
#guard translationSucceeds identityProg

-- typeArgs propagate to Core
#guard (getFirstProc identityProg).any fun proc => proc.header.typeArgs == ["T"]

-- Input uses ftvar "T", output is Result-wrapped
#guard (getFirstProc identityProg).any fun proc =>
  proc.header.inputs.any (fun (_, ty) => ty == .ftvar "T") &&
  proc.header.outputs.any (fun (_, ty) => ty == .tcons "Result" [.ftvar "T"])

end PolymorphicIdentity

---------------------------------------------------------------------
-- Test 2: Multiple type parameters swap<A,B>
---------------------------------------------------------------------
section PolymorphicSwap

private def swapProc : Procedure := {
  name := ident "swap"
  typeArgs := [⟨ident "A"⟩, ⟨ident "B"⟩]
  inputs := [⟨ident "a", wm (.UserDefined (ident "A"))⟩,
             ⟨ident "b", wm (.UserDefined (ident "B"))⟩]
  outputs := [⟨ident "ra", wm (.UserDefined (ident "B"))⟩,
              ⟨ident "rb", wm (.UserDefined (ident "A"))⟩]
  preconditions := []
  decreases := none
  isFunctional := false
  body := .Opaque
    [wm (.PrimitiveOp .And [
      wm (.PrimitiveOp .Eq [wm (.Identifier (ident "ra")), wm (.Identifier (ident "b"))]),
      wm (.PrimitiveOp .Eq [wm (.Identifier (ident "rb")), wm (.Identifier (ident "a"))])])]
    none []
  md := .empty
}

private def swapProg : Program := {
  staticProcedures := [swapProc]
  staticFields := []
  types := []
}

-- Translation succeeds
#guard translationSucceeds swapProg

-- typeArgs = ["A", "B"]
#guard (getFirstProc swapProg).any fun proc => proc.header.typeArgs == ["A", "B"]

-- Inputs use ftvar A and B
#guard (getFirstProc swapProg).any fun proc =>
  let inTys := proc.header.inputs.map Prod.snd
  let outTys := proc.header.outputs.map Prod.snd
  inTys.contains (.ftvar "A") && inTys.contains (.ftvar "B") &&
  outTys.contains (.tcons "Result" [.ftvar "B"]) && outTys.contains (.ftvar "A")

end PolymorphicSwap

---------------------------------------------------------------------
-- Test 3: Applied type — fill<T> with Sequence<T>
---------------------------------------------------------------------
section PolymorphicFill

private def fillProc : Procedure := {
  name := ident "fill"
  typeArgs := [⟨ident "T"⟩]
  inputs := [⟨ident "arr", wm (.Applied (wm (.UserDefined (ident "Sequence"))) [wm (.UserDefined (ident "T"))])⟩,
             ⟨ident "val", wm (.UserDefined (ident "T"))⟩]
  outputs := [⟨ident "r", wm (.UserDefined (ident "T"))⟩]
  preconditions := []
  decreases := none
  isFunctional := false
  body := .Opaque
    [wm (.PrimitiveOp .Eq [wm (.Identifier (ident "r")), wm (.Identifier (ident "val"))])]
    none []
  md := .empty
}

private def fillProg : Program := {
  staticProcedures := [fillProc]
  staticFields := []
  types := [.Composite { name := ident "Sequence", extending := [], fields := [], instanceProcedures := [] }]
}

-- Translation succeeds
#guard translationSucceeds fillProg

-- Applied type: Sequence<T> → tcons "Sequence" [ftvar "T"]
#guard (getFirstProc fillProg).any fun proc =>
  proc.header.inputs.any (fun (_, ty) => ty == .tcons "Sequence" [.ftvar "T"])

end PolymorphicFill

---------------------------------------------------------------------
-- Test 4: Non-generic procedure (regression check)
---------------------------------------------------------------------
section NonGenericRegression

private def addProc : Procedure := {
  name := ident "add"
  inputs := [⟨ident "x", wm .TInt⟩, ⟨ident "y", wm .TInt⟩]
  outputs := [⟨ident "r", wm .TInt⟩]
  preconditions := []
  decreases := none
  isFunctional := false
  body := .Opaque
    [wm (.PrimitiveOp .Eq [
      wm (.Identifier (ident "r")),
      wm (.PrimitiveOp .Add [wm (.Identifier (ident "x")), wm (.Identifier (ident "y"))])])]
    none []
  md := .empty
}

private def addProg : Program := {
  staticProcedures := [addProc]
  staticFields := []
  types := []
}

-- Translation succeeds
#guard translationSucceeds addProg

-- Non-generic procedure has empty typeArgs
#guard (getFirstProc addProg).any fun proc => proc.header.typeArgs == []

end NonGenericRegression
