/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Laurel.Resolution

/-!
# Function Postcondition Check

A Laurel-to-Laurel pass that generates check procedures for function
postconditions. For each function with `ensures` clauses:

1. Generates a `$check` procedure that inlines the function body and
   asserts the postconditions hold.

Postconditions are NOT stripped from the function — they are consumed later by
the translator to generate axioms.

This pass runs after `ConstrainedTypeElim`, which converts constrained return
types into postconditions on `Transparent` bodies.
-/

namespace Strata.Laurel

open Strata

/-- Substitute all occurrences of `target` identifier with `replacement` in a StmtExpr tree. -/
public partial def substIdentifier (target : Identifier) (replacement : StmtExprMd)
    (expr : StmtExprMd) : StmtExprMd :=
  let md := expr.md
  let go := substIdentifier target replacement
  match expr.val with
  | .Identifier name =>
    if name.uniqueId == target.uniqueId then replacement else expr
  | .PrimitiveOp op args => ⟨.PrimitiveOp op (args.map go), md⟩
  | .StaticCall callee args => ⟨.StaticCall callee (args.map go), md⟩
  | .IfThenElse c t e => ⟨.IfThenElse (go c) (go t) (e.map go), md⟩
  | .Block stmts label => ⟨.Block (stmts.map go) label, md⟩
  | .Forall param trigger body =>
    ⟨.Forall param (trigger.map go) (go body), md⟩
  | .Exists param trigger body =>
    ⟨.Exists param (trigger.map go) (go body), md⟩
  | .Assign targets value => ⟨.Assign (targets.map go) (go value), md⟩
  | .LocalVariable name ty init => ⟨.LocalVariable name ty (init.map go), md⟩
  | .Return v => ⟨.Return (v.map go), md⟩
  | .Assert c => ⟨.Assert (go c), md⟩
  | .Assume c => ⟨.Assume (go c), md⟩
  | .Old v => ⟨.Old (go v), md⟩
  | .Fresh v => ⟨.Fresh (go v), md⟩
  | .ReferenceEquals l r => ⟨.ReferenceEquals (go l) (go r), md⟩
  | .AsType t ty => ⟨.AsType (go t) ty, md⟩
  | .IsType t ty => ⟨.IsType (go t) ty, md⟩
  | .ProveBy v p => ⟨.ProveBy (go v) (go p), md⟩
  | .FieldSelect t f => ⟨.FieldSelect (go t) f, md⟩
  | .PureFieldUpdate t f v => ⟨.PureFieldUpdate (go t) f (go v), md⟩
  | .InstanceCall t callee args => ⟨.InstanceCall (go t) callee (args.map go), md⟩
  | .While c inv dec body =>
    ⟨.While (go c) (inv.map go) (dec.map go) (go body), md⟩
  | .Assigned v => ⟨.Assigned (go v), md⟩
  | .ContractOf ty f => ⟨.ContractOf ty (go f), md⟩
  | .TryCatch body catches finally_ =>
    ⟨.TryCatch (go body) (catches.map fun c => { c with body := go c.body })
      (finally_.map go), md⟩
  | .Throw e => ⟨.Throw (go e), md⟩
  | _ => expr

/-- Conjoin a list of StmtExpr with `And`. -/
public def conjoin (exprs : List StmtExprMd) (md : MetaData) : StmtExprMd :=
  match exprs with
  | [] => ⟨.LiteralBool true, md⟩
  | [single] => single
  | first :: rest => rest.foldl (fun acc p => ⟨.PrimitiveOp .And [acc, p], md⟩) first

/-- Collected postconditions for a function -/
structure FuncPostconds where
  /-- The function procedure -/
  proc : Procedure
  /-- All postconditions (ensures clauses, including those derived from constrained return types) -/
  postconditions : List StmtExprMd
  /-- The output parameter (result) -/
  resultParam : Parameter
  /-- Whether the function has a body (used to decide if a check procedure is needed) -/
  hasBody : Bool

/-- Collect postconditions from a functional procedure.
    Returns `none` if the procedure has no postconditions or no output parameter. -/
def collectFuncPostconds (proc : Procedure) : Option FuncPostconds :=
  if !proc.isFunctional then none
  else
    let (posts, hasBody) := match proc.body with
      | .Transparent _ posts => (posts, true)
      | .Opaque posts (some _) _ => (posts, true)
      | .Opaque posts none _ => (posts, false)
      | _ => ([], false)
    match proc.outputs.head?, posts.isEmpty with
    | some resultParam, false => some { proc, postconditions := posts, resultParam, hasBody }
    | _, _ => none

/-- Generate a check procedure that inlines the function body and asserts the postconditions.
    Returns `none` for functions without a body. -/
def mkCheckProc (fpc : FuncPostconds) : Option Procedure :=
  if !fpc.hasBody then none
  else
    let md := fpc.proc.md
    let resultId := mkId "$result"
    let resultType := fpc.resultParam.type
    let initExpr := match fpc.proc.body with
      | .Opaque _ (some impl) _ => impl
      | .Transparent impl _ => impl
      | _ => ⟨.LiteralBool false, md⟩
    let initResult : StmtExprMd := ⟨.LocalVariable resultId resultType (some initExpr), md⟩
    -- Inline postconditions with result substituted by $result
    let substPosts := fpc.postconditions.map (substIdentifier fpc.resultParam.name ⟨.Identifier resultId, md⟩)
    let assertPost : StmtExprMd := ⟨.Assert (conjoin substPosts md), md⟩
    some {
      name := mkId s!"{fpc.proc.name.text}$check"
      inputs := fpc.proc.inputs
      outputs := []
      preconditions := fpc.proc.preconditions
      body := .Transparent ⟨.Block [initResult, assertPost] none, md⟩ []
      isFunctional := false
      decreases := none
      md := md }

/-- Main entry point: generate check procedures for function postconditions.
    Postconditions are left on the original functions for axiom generation. -/
public def functionPostcondCheck (program : Program)
    : Program × List DiagnosticModel :=
  let funcPostconds := program.staticProcedures.filterMap collectFuncPostconds
  if funcPostconds.isEmpty then (program, []) else
  let checkProcs := funcPostconds.filterMap mkCheckProc
  ({ program with
    staticProcedures := program.staticProcedures ++ checkProcs }, [])

end Strata.Laurel
