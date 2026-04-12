/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.Program
public import Strata.Languages.Core.Verifier
public import Strata.Languages.Core.Statement
public import Strata.Languages.Core.Procedure
public import Strata.Languages.Core.Options
public import Strata.Languages.Laurel.Laurel
public import Strata.Languages.Laurel.LiftImperativeExpressions
import Strata.Languages.Laurel.DesugarShortCircuit
public import Strata.Languages.Laurel.InferHoleTypes
public import Strata.Languages.Laurel.EliminateHoles
import Strata.Languages.Laurel.EliminateReturnsInExpression
public import Strata.Languages.Laurel.HeapParameterization
public import Strata.Languages.Laurel.TypeHierarchy
public import Strata.Languages.Laurel.LaurelTypes
public import Strata.Languages.Laurel.ModifiesClauses
public import Strata.Languages.Laurel.CoreDefinitionsForLaurel
import Strata.DDM.Util.DecimalRat
import Strata.DL.Imperative.Stmt
import Strata.DL.Imperative.MetaData
import Strata.DL.Lambda.LExpr
import Strata.Languages.Laurel.Grammar.AbstractToConcreteTreeTranslator
import Strata.Languages.Laurel.ConstrainedTypeElim
import Strata.Languages.Laurel.FunctionPostcondCheck
import Strata.Languages.Laurel.CoreGroupingAndOrdering
import Strata.Util.Tactics

open Core (VCResult VCResults VerifyOptions)
open Core (intAddOp intSubOp intMulOp intSafeDivOp intSafeModOp intSafeDivTOp intSafeModTOp intNegOp intLtOp intLeOp intGtOp intGeOp boolAndOp boolOrOp boolNotOp boolImpliesOp strConcatOp)
open Core (realAddOp realSubOp realMulOp realDivOp realNegOp realLtOp realLeOp realGtOp realGeOp)

namespace Strata.Laurel

open Std (Format ToFormat)
open Strata
open Lambda (LMonoTy LTy LExpr)

public section

@[expose] def mdWithUnknownLoc : Imperative.MetaData Core.Expression :=
  #[⟨Imperative.MetaData.fileRange, .fileRange FileRange.unknown⟩]

def isFieldName (fieldNames : List Identifier) (name : Identifier) : Bool :=
  fieldNames.contains name

/-- Set of names that are translated to Core functions (not procedures) -/
@[expose] abbrev FunctionNames := List Identifier

/-- State threaded through expression and statement translation -/
structure TranslateState where
  /-- Diagnostics accumulated during translation -/
  diagnostics : List DiagnosticModel := []
  /-- Next fresh ID to allocate. -/
  nextId : Nat := 1
  /-- Constants known to the program (field constants, etc.) -/
  model : SemanticModel
  /-- Do not process the produces Core program, since it has superfluous errors -/
  coreProgramHasSuperfluousErrors: Bool := false
  /-- The label that exception propagation should exit to.
      At procedure level this is "$body". Inside a try body, it's the
      try block's handlers label so the catch dispatch can run. -/
  exceptionTarget : String := "$body"

/-- The translation monad: state over Except, allowing both accumulated diagnostics and hard failures -/
@[expose] abbrev TranslateM := OptionT (StateM TranslateState)

/-- Emit a diagnostic into the translation state (soft warning, does not abort) -/
def emitDiagnostic (d : DiagnosticModel) : TranslateM Unit :=
  modify fun s => { s with diagnostics := s.diagnostics ++ [d] }

/-- Abort the Core program by setting the superfluous-errors flag and returning a dummy type. -/
private def throwTypeDiagnostic (ty : HighTypeMd) (msg : String) : TranslateM LMonoTy := do
  emitDiagnostic (ty.md.toDiagnostic msg)
  modify fun s => { s with coreProgramHasSuperfluousErrors := true }
  return .tcons "Error" []

/-
Translate Laurel HighType to Core Type
-/
def translateType (ty : HighTypeMd) : TranslateM LMonoTy := do
  let model := (← get).model
  match _h : ty.val with
  | .TInt => return LMonoTy.int
  | .TBool => return LMonoTy.bool
  | .TString => return LMonoTy.string
  | .TVoid => return LMonoTy.bool -- Using bool as placeholder for void
  | .THeap => return .tcons "Heap" []
  | .TTypedField _ => return .tcons "Field" []
  | .TSet elementType => return Core.mapTy (← translateType elementType) LMonoTy.bool
  | .TMap keyType valueType => return Core.mapTy (← translateType keyType) (← translateType valueType)
  | .UserDefined name =>
    match name.uniqueId.bind model.refToDef.get? with
    | some (.compositeType _) => return .tcons "Composite" []
    | some (.datatypeDefinition dt) => return .tcons dt.name.text []
    | some (.datatypeConstructor typeName _) => return .tcons typeName.text []
    | _ => do -- resolution should have already emitted a diagnostic
      modify fun s => { s with coreProgramHasSuperfluousErrors := true }
      return .tcons "Composite" []
  | .TCore s => return .tcons s []
  | .TReal => return LMonoTy.real
  | .Unknown => return .tcons "ExceptionResult" [] -- Used for $result/Success/Failure in ensures clauses
  | _ => throwTypeDiagnostic ty "cannot translate type to Core: not supported yet"
termination_by ty.val
decreasing_by all_goals (first | (cases elementType; term_by_mem) | (cases keyType; term_by_mem) | (cases valueType; term_by_mem))

def lookupType (name : Identifier) : TranslateM LMonoTy := do
  translateType ((← get).model.get name).getType

/-- Run a `TranslateM` action, returning either a hard error or the result and final state -/
def runTranslateM (s : TranslateState) (m : TranslateM α) : (Option α × TranslateState) :=
  m s

def returnNone: TranslateM α :=
  StateT.pure none

/-- Allocate a fresh unique ID. -/
private def freshId : TranslateM Nat := do
  let s ← get
  let id := s.nextId
  set { s with nextId := id + 1 }
  return id

/-- Throw a hard diagnostic error, aborting the current translation -/
def throwExprDiagnostic (d : DiagnosticModel): TranslateM Core.Expression.Expr := do
  emitDiagnostic d
  modify fun s => { s with coreProgramHasSuperfluousErrors := true }
  let id ← freshId
  return LExpr.fvar () (⟨s!"DUMMY_VAR_{id}", ()⟩) none

/-- Reorder instance call arguments to match the procedure signature.
    Heap parameterization may inject $heap as the first Laurel arg.
    When present: [$heap, target, otherArgs...] matching ($heap_in, self, otherArgs...).
    When absent:  [target, otherArgs...] matching (self, otherArgs...). -/
def instanceCallArgs (coreTarget : Core.Expression.Expr)
    (coreArgs : List Core.Expression.Expr)
    (laurelArgs : List StmtExprMd) : List Core.Expression.Expr :=
  let hasHeapArg := match laurelArgs with
    | ⟨.Identifier name, _⟩ :: _ => name.text == "$heap" || name.text == "$heap_in"
    | _ => false
  if hasHeapArg then
    match coreArgs with
    | heapArg :: rest => heapArg :: coreTarget :: rest
    | [] => [coreTarget]
  else
    coreTarget :: coreArgs

/--
Translate Laurel StmtExpr to Core Expression using the `TranslateM` monad.
Diagnostics for disallowed constructs are emitted into the monad state.

`isPureContext` should be `true` when translating function bodies or contract expressions.
In that case, disallowed constructs emit `DiagnosticModel` errors into the state.
When `false` (inside a procedure body statement), disallowed constructs throw a diagnostic
because `liftImperativeExpressions` should have already removed them.

`boundVars` tracks names bound by enclosing Forall/Exists quantifiers (innermost first).
When an Identifier matches a bound name at index `i`, it becomes `bvar i` (de Bruijn index)
instead of `fvar`.
-/

def translateExpr (expr : StmtExprMd)
    (boundVars : List Identifier := []) (isPureContext : Bool := false)
    : TranslateM Core.Expression.Expr := do
  let s ← get
  let model := s.model
  let md := expr.md
  let disallowed (md : MetaData) (msg : String) : TranslateM Core.Expression.Expr := do
    if isPureContext then
      throwExprDiagnostic $ md.toDiagnostic msg
    else
      throwExprDiagnostic $ md.toDiagnostic s!"{msg} (should have been lifted)" DiagnosticType.StrataBug

  match h: expr.val with
  | .LiteralBool b => return .const () (.boolConst b)
  | .LiteralInt i => return .const () (.intConst i)
  | .LiteralString s => return .const () (.strConst s)
  | .LiteralDecimal d => return .const () (.realConst (Strata.Decimal.toRat d))
  | .Identifier name =>
      -- First check if this name is bound by an enclosing quantifier
      match boundVars.findIdx? (· == name) with
      | some idx =>
          -- Bound variable: use de Bruijn index
          return .bvar () idx
      | none =>
        -- Handle synthetic exception-result identifiers injected by the frontend
        if name.text == "$result" then
          return .fvar () ⟨"$result", ()⟩ (some (.tcons "ExceptionResult" []))
        else if name.text == "Success" || name.text == "Failure" then
          return .op () ⟨name.text, ()⟩ none
        else
        match model.get name with
        | .field _ f =>
            return .op () ⟨f.name.text, ()⟩ none
        | .datatypeConstructor _ ctor =>
            return .op () ⟨ctor.name.text, ()⟩ none
        | .unresolved =>
            return .fvar () ⟨name.text, ()⟩ (some (← translateType AstNode.unresolved.getType))
        | astNode =>
            return .fvar () ⟨name.text, ()⟩ (some (← translateType astNode.getType))
  | .PrimitiveOp op [e] =>
    match op with
    | .Not =>
      let re ← translateExpr e boundVars isPureContext
      return .app () boolNotOp re
    | .Neg =>
      let re ← translateExpr e boundVars isPureContext
      let isReal := match (computeExprType model e).val with
        | .TReal => true | _ => false
      return .app () (if isReal then realNegOp else intNegOp) re
    | _ =>
      throwExprDiagnostic $ md.toDiagnostic s!"translateExpr: Invalid unary op: {repr op}" DiagnosticType.StrataBug
  | .PrimitiveOp op [e1, e2] =>
    let re1 ← translateExpr e1 boundVars isPureContext
    let re2 ← translateExpr e2 boundVars isPureContext
    let binOp (bop : Core.Expression.Expr) : Core.Expression.Expr :=
      LExpr.mkApp () bop [re1, re2]
    let isReal := match (computeExprType model e1).val, (computeExprType model e2).val with
      | .TReal, _ | _, .TReal => true
      | _, _ => false
    match op with
    | .Eq => return .eq () re1 re2
    | .Neq => return .app () boolNotOp (.eq () re1 re2)
    | .And => return binOp boolAndOp
    | .Or => return binOp boolOrOp
    | .AndThen => return binOp boolAndOp
    | .OrElse => return binOp boolOrOp
    | .Implies => return binOp boolImpliesOp
    | .Add => return binOp (if isReal then realAddOp else intAddOp)
    | .Sub => return binOp (if isReal then realSubOp else intSubOp)
    | .Mul => return binOp (if isReal then realMulOp else intMulOp)
    | .Div => return binOp (if isReal then realDivOp else intSafeDivOp)
    | .Mod => return binOp intSafeModOp
    | .DivT => return binOp intSafeDivTOp
    | .ModT => return binOp intSafeModTOp
    | .Lt => return binOp (if isReal then realLtOp else intLtOp)
    | .Leq => return binOp (if isReal then realLeOp else intLeOp)
    | .Gt => return binOp (if isReal then realGtOp else intGtOp)
    | .Geq => return binOp (if isReal then realGeOp else intGeOp)
    | .StrConcat => return binOp strConcatOp
    | _ =>
        throwExprDiagnostic $ md.toDiagnostic s!"Invalid binary op: {repr op}" DiagnosticType.NotYetImplemented
  | .PrimitiveOp op args =>
      throwExprDiagnostic $ md.toDiagnostic s!"PrimitiveOp {repr op} with {args.length} args is not supported" DiagnosticType.UserError
  | .IfThenElse cond thenBranch elseBranch =>
      let bcond ← translateExpr cond boundVars isPureContext
      let bthen ← translateExpr thenBranch boundVars isPureContext
      let belse ← match elseBranch with
        | none =>
            throwExprDiagnostic $ md.toDiagnostic s!"if-then without else expression" DiagnosticType.NotYetImplemented
        | some e =>
            have : sizeOf e < sizeOf expr := by
              have := WithMetadata.sizeOf_val_lt expr
              cases expr; simp_all; omega
            translateExpr e boundVars isPureContext
      return .ite () bcond bthen belse
  | .StaticCall callee args =>
      -- In a pure context, only Core functions (not procedures) are allowed
      if isPureContext && !model.isFunction callee then
        disallowed expr.md "calls to procedures are not supported in functions or contracts"
      else
        let fnOp : Core.Expression.Expr := .op () ⟨callee.text, ()⟩ none
        args.attach.foldlM (fun acc ⟨arg, _⟩ => do
          let re ← translateExpr arg boundVars isPureContext
          return .app () acc re) fnOp
  | .Block [single] _ => translateExpr single boundVars isPureContext
  | .Forall ⟨ name, ty ⟩ trigger body =>
      let coreTy ← translateType ty
      let coreBody ← translateExpr body (name :: boundVars) isPureContext
      match _: trigger with
      | some trig =>
        let coreTrig ← translateExpr trig (name :: boundVars) isPureContext
        return LExpr.allTr () name.text (some coreTy) coreTrig coreBody
      | none =>
        return LExpr.all () name.text (some coreTy) coreBody
  | .Exists ⟨ name, ty ⟩ trigger body =>
      let coreTy ← translateType ty
      let coreBody ← translateExpr body (name :: boundVars) isPureContext
      match _: trigger with
      | some trig =>
        let coreTrig ← translateExpr trig (name :: boundVars) isPureContext
        return LExpr.existTr () name.text (some coreTy) coreTrig coreBody
      | none =>
        return LExpr.exist () name.text (some coreTy) coreBody
  | .Hole _ _ =>
      -- Holes should have been eliminated before translation.
      disallowed expr.md "holes should have been eliminated before translation"
  | .ReferenceEquals e1 e2 =>
      let re1 ← translateExpr e1 boundVars isPureContext
      let re2 ← translateExpr e2 boundVars isPureContext
      return .eq () re1 re2
  | .Assign _ _ =>
      disallowed expr.md "destructive assignments are not supported in functions or contracts"
  | .While _ _ _ _ =>
      disallowed expr.md "loops are not supported in functions or contracts"
  | .Exit _ => disallowed expr.md "exit is not supported in expression position"

  | .Block (⟨ .Assert _, md⟩ :: rest) label => do
    _ ← disallowed md "asserts are not YET supported in functions or contracts"
    translateExpr ⟨ StmtExpr.Block rest label, md ⟩ boundVars isPureContext
  | .Block (⟨ .Assume _, md⟩ :: rest) label =>
    _ ← disallowed md "assumes are not YET supported in functions or contracts"
    translateExpr ⟨ StmtExpr.Block rest label, md ⟩ boundVars isPureContext
  | .Block (⟨ .LocalVariable name ty (some initializer), md⟩ :: rest) label => do
      let valueExpr ← translateExpr  initializer boundVars isPureContext
      let bodyExpr ← translateExpr ⟨ StmtExpr.Block rest label, md ⟩ (name :: boundVars) isPureContext
      disallowed md "local variables in functions are not YET supported"
      -- This doesn't work because of a limitation in Core.
      -- let coreMonoType := translateType ty
      -- return .app () (.abs () (some coreMonoType) bodyExpr) valueExpr
  | .Block (⟨ .LocalVariable name ty none, md⟩ :: rest) label =>
    disallowed md "local variables in functions must have initializers"
  | .Block (⟨ .IfThenElse cond thenBranch (some elseBranch), md⟩ :: rest) label =>
    disallowed md "if-then-else only supported as the last statement in a block"

  | .IsType _ _ =>
      throwExprDiagnostic $ md.toDiagnostic "IsType should have been lowered" DiagnosticType.StrataBug
  | .New _ => throwExprDiagnostic $ md.toDiagnostic s!"New should have been eliminated by typeHierarchyTransform" DiagnosticType.StrataBug
  | .FieldSelect target fieldId =>
      -- Field selects should have been eliminated by heap parameterization
      -- If we see one here, it's an error in the pipeline
      throwExprDiagnostic $ md.toDiagnostic s!"FieldSelect should have been eliminated by heap parameterization: {Std.ToFormat.format target}#{fieldId.text}" DiagnosticType.StrataBug
  | .Block _ _ =>
      throwExprDiagnostic $ md.toDiagnostic "block expression should have been lowered in a separate pass" DiagnosticType.StrataBug
  | .LocalVariable _ _ _ =>
      throwExprDiagnostic $ md.toDiagnostic "local variable expression should be lowered in a separate pass" DiagnosticType.StrataBug
  | .Return _ => disallowed expr.md "return expression should be lowered in a separate pass"

  | .AsType target _ => throwExprDiagnostic $ md.toDiagnostic "AsType expression translation" DiagnosticType.NotYetImplemented
  | .Assigned _ => throwExprDiagnostic $ md.toDiagnostic "assigned expression translation" DiagnosticType.NotYetImplemented
  | .Old value => throwExprDiagnostic $ md.toDiagnostic "old expression translation" DiagnosticType.NotYetImplemented
  | .Fresh _ => throwExprDiagnostic $ md.toDiagnostic "fresh expression translation" DiagnosticType.NotYetImplemented
  | .Assert _ => throwExprDiagnostic $ md.toDiagnostic "assert expression translation" DiagnosticType.NotYetImplemented
  | .Assume _ => throwExprDiagnostic $ md.toDiagnostic "assume expression translation" DiagnosticType.NotYetImplemented
  | .ProveBy value _ => throwExprDiagnostic $ md.toDiagnostic "proveBy expression translation" DiagnosticType.NotYetImplemented
  | .ContractOf _ _ => throwExprDiagnostic $ md.toDiagnostic "contractOf expression translation" DiagnosticType.NotYetImplemented
  | .Abstract => throwExprDiagnostic $ md.toDiagnostic "abstract expression translation" DiagnosticType.NotYetImplemented
  | .All => throwExprDiagnostic $ md.toDiagnostic "all expression translation" DiagnosticType.NotYetImplemented
  | .InstanceCall target callee args =>
      match model.get callee with
      | .instanceProcedure typeName proc =>
        if proc.isFunctional then
          let fnOp : Core.Expression.Expr := .op () ⟨callee.text, ()⟩ none
          let coreTarget ← translateExpr target boundVars isPureContext
          let coreArgs ← (args.attach).mapM (fun ⟨arg, _⟩ => translateExpr arg boundVars isPureContext)
          let allArgs := instanceCallArgs coreTarget coreArgs args
          allArgs.foldlM (fun acc arg => pure (.app () acc arg)) fnOp
        else
          -- Non-functional instance calls must be lifted to statement position
          -- by LiftImperativeExpressions before reaching translateExpr.
          throwExprDiagnostic $ md.toDiagnostic "instance call expression: non-functional callee in expression position (should have been lifted)" DiagnosticType.NotYetImplemented
      | _ => throwExprDiagnostic $ md.toDiagnostic "instance call expression: callee not resolved as instance procedure" DiagnosticType.NotYetImplemented
  | .PureFieldUpdate _ _ _ => throwExprDiagnostic $ md.toDiagnostic "pure field update expression translation" DiagnosticType.NotYetImplemented
  | .This => throwExprDiagnostic $ md.toDiagnostic "this expression translation" DiagnosticType.NotYetImplemented
  | .TryCatch _ _ _ => disallowed expr.md "try-catch is not supported in expression position"
  | .Throw _ => disallowed expr.md "throw is not supported in expression position"
  termination_by expr
  decreasing_by
    all_goals (have := WithMetadata.sizeOf_val_lt expr; term_by_mem)

def getNameFromMd (md : Imperative.MetaData Core.Expression): String :=
  let fileRange := (Imperative.getFileRange md).getD (dbg_trace "BUG: metadata without a filerange"; default)
  s!"({fileRange.range.start})"

def defaultExprForType (ty : HighTypeMd) : TranslateM Core.Expression.Expr := do
  match ty.val with
  | .TInt => return .const () (.intConst 0)
  | .TBool => return .const () (.boolConst false)
  | .TString => return .const () (.strConst "")
  | _ =>
    -- For types without a natural default (arrays, composites, etc.),
    -- use a fresh free variable. This is only used when the value is
    -- immediately overwritten by a procedure call.
    let coreTy ← translateType ty
    return .fvar () (⟨"$default", ()⟩) (some coreTy)

/--
Translate an expression in statement position into a `var $unused_N := expr` init.
Preserves the expression so it is not silently dropped from the Core output.
-/
private def exprAsUnusedInit (expr : StmtExprMd) (md : Imperative.MetaData Core.Expression)
    : TranslateM (List Core.Statement) := do
  let coreExpr ← translateExpr expr
  let id ← freshId
  let ident : Core.CoreIdent := ⟨s!"$unused_{id}", ()⟩
  let tyVarName := s!"$__ty_unused_{id}"
  let coreType := LTy.forAll [tyVarName] (.ftvar tyVarName)
  return [Core.Statement.init ident coreType (.det coreExpr) md]

/-- Build a Core.Statement.call with `$result` appended to the LHS.
    Every non-functional call needs `$result` in the LHS because
    `translateProcedure` adds it to every procedure's outputs. -/
def mkCallWithResult (lhs : List Core.CoreIdent) (callee : String)
    (args : List Core.Expression.Expr) (md : Imperative.MetaData Core.Expression) : TranslateM (List Core.Statement) := do
  let resultIdent : Core.CoreIdent := ⟨"$result", ()⟩
  let exceptionTarget := (← get).exceptionTarget
  let callStmt := Core.Statement.call (lhs ++ [resultIdent]) callee args md
  let isFailure : Core.Expression.Expr :=
    .app () (.op () ⟨"ExceptionResult..isFailure", ()⟩ none) (.fvar () resultIdent none)
  let exitStmt : Core.Statement := Imperative.Stmt.exit (some exceptionTarget) md
  let propagate : Core.Statement := Imperative.Stmt.ite (.det isFailure) [exitStmt] [] md
  return [callStmt, propagate]

/--
Translate Laurel StmtExpr to Core Statements using the `TranslateM` monad.
Diagnostics are emitted into the monad state.
-/
def translateStmt (outputParams : List Parameter) (stmt : StmtExprMd)
    : TranslateM (List Core.Statement) := do
  let s ← get
  let model := s.model
  let md := stmt.md
  match _h : stmt.val with
  | .Assert cond =>
      -- Assert/assume bodies must be pure expressions (no assignments, loops, or procedure calls)
      let coreExpr ← translateExpr cond [] (isPureContext := true)
      return [Core.Statement.assert ("assert" ++ getNameFromMd md) coreExpr md]
  | .Assume cond =>
      let coreExpr ← translateExpr cond [] (isPureContext := true)
      return [Core.Statement.assume ("assume" ++ getNameFromMd md) coreExpr md]
  | .Block stmts label =>
      let innerStmts ← stmts.flatMapM (fun s => translateStmt outputParams s)
      match label with
      | some l => return [Imperative.Stmt.block l innerStmts md]
      | none   => return innerStmts
  | .LocalVariable id ty initializer =>
      let coreMonoType ← translateType ty
      let coreType := LTy.forAll [] coreMonoType
      let ident := ⟨id.text, ()⟩
      match initializer with
      | some (⟨ .StaticCall callee args, callMd⟩) =>
          -- Check if this is a function or a procedure call
          if model.isFunction callee then
            -- Translate as expression (function application)
            let coreExpr ← translateExpr (⟨ .StaticCall callee args, callMd ⟩)
            return [Core.Statement.init ident coreType (.det coreExpr) md]
          else
            -- Translate as: var name; call name := callee(args)
            let coreArgs ← args.mapM (fun a => translateExpr a)
            let defaultExpr ← defaultExprForType ty
            let initStmt := Core.Statement.init ident coreType (.det defaultExpr) md
            let callStmts ← mkCallWithResult [ident] callee.text coreArgs md
            return [initStmt] ++ callStmts
      | some (⟨ .InstanceCall callTarget callCallee callArgs, callMd⟩) =>
          match model.get callCallee with
          | .instanceProcedure typeName proc =>
            if proc.isFunctional then
              let coreExpr ← translateExpr (⟨ .InstanceCall callTarget callCallee callArgs, callMd ⟩)
              return [Core.Statement.init ident coreType (.det coreExpr) md]
            else
              let coreTarget ← translateExpr callTarget
              let coreArgs ← callArgs.mapM (fun a => translateExpr a)
              let defaultExpr ← defaultExprForType ty
              let initStmt := Core.Statement.init ident coreType (.det defaultExpr) md
              let allArgs := instanceCallArgs coreTarget coreArgs callArgs
              let callStmts ← mkCallWithResult [ident] callCallee.text allArgs callMd
              return [initStmt] ++ callStmts
          | _ =>
            let initStmt := Core.Statement.init ident coreType .nondet md
            return [initStmt]
      | some (⟨ .Hole _ _, _⟩) =>
          -- Hole initializer: treat as havoc (init without value)
          return [Core.Statement.init ident coreType .nondet md]
      | some initExpr =>
          let coreExpr ← translateExpr initExpr
          return [Core.Statement.init ident coreType (.det coreExpr) md]
      | none =>
          return [Core.Statement.init ident coreType .nondet md]
  | .Assign targets value =>
      match targets with
      | [⟨ .Identifier targetId, _ ⟩] =>
          let ident := ⟨targetId.text, ()⟩
          -- Check if RHS is a procedure call (not a function)
          match value.val with
          | .StaticCall callee args =>
              if model.isFunction callee then
                -- Functions are translated as expressions
                let coreExpr ← translateExpr value
                return [Core.Statement.set ident coreExpr md]
              else
                -- Procedure calls need to be translated as call statements
                let coreArgs ← args.mapM (fun a => translateExpr a)
                -- Synthesize throwaway LHS variables for any outputs beyond the
                -- assigned target (e.g. void-returns-Any adds an extra output).
                let outputs := match model.get callee with
                  | .staticProcedure proc => proc.outputs
                  | .instanceProcedure _ proc => proc.outputs
                  | _ => []
                let mut inits : List Core.Statement := []
                let mut lhs : List Core.CoreIdent := [ident]
                for out in outputs.drop 1 do
                  let id ← freshId
                  let unusedIdent : Core.CoreIdent := ⟨s!"$unused_{id}", ()⟩
                  let coreType := LTy.forAll [] (← translateType out.type)
                  inits := inits ++ [Core.Statement.init unusedIdent coreType .nondet md]
                  lhs := lhs ++ [unusedIdent]
                let callStmts ← mkCallWithResult lhs callee.text coreArgs md
                return inits ++ callStmts
          | .InstanceCall callTarget callCallee callArgs =>
              match model.get callCallee with
              | .instanceProcedure typeName proc =>
                let coreTarget ← translateExpr callTarget
                let coreArgs ← callArgs.mapM (fun a => translateExpr a)
                let mut inits : List Core.Statement := []
                let mut lhs : List Core.CoreIdent := [ident]
                for out in proc.outputs.drop 1 do
                  let id ← freshId
                  let unusedIdent : Core.CoreIdent := ⟨s!"$unused_{id}", ()⟩
                  let coreType := LTy.forAll [] (← translateType out.type)
                  inits := inits ++ [Core.Statement.init unusedIdent coreType .nondet md]
                  lhs := lhs ++ [unusedIdent]
                let allArgs := instanceCallArgs coreTarget coreArgs callArgs
                let callStmts ← mkCallWithResult lhs callCallee.text allArgs md
                return inits ++ callStmts
              | _ => return [Core.Statement.havoc ident md]
          | _ =>
              let coreExpr ← translateExpr value
              return [Core.Statement.set ident coreExpr md]
      | _ =>
          -- Parallel assignment: (var1, var2, ...) := expr
          -- Example use is heap-modifying procedure calls: (result, heap) := f(heap, args)
          match value.val with
          | .StaticCall callee args =>
              let coreArgs ← args.mapM (fun a => translateExpr a)
              let lhsIdents := targets.filterMap fun t =>
                match t.val with
                | .Identifier name => some (⟨name.text, ()⟩)
                | _ => none
              mkCallWithResult lhsIdents callee.text coreArgs value.md
          | .InstanceCall callTarget callCallee callArgs =>
              match model.get callCallee with
              | .instanceProcedure typeName _ =>
                let coreTarget ← translateExpr callTarget
                let coreArgs ← callArgs.mapM (fun a => translateExpr a)
                let lhsIdents := targets.filterMap fun t =>
                  match t.val with
                  | .Identifier name => some (⟨name.text, ()⟩)
                  | _ => none
                let allArgs := instanceCallArgs coreTarget coreArgs callArgs
                mkCallWithResult lhsIdents callCallee.text allArgs value.md
              | _ =>
                let havocStmts := targets.filterMap fun t =>
                  match t.val with
                  | .Identifier name => some (Core.Statement.havoc ⟨name.text, ()⟩ md)
                  | _ => none
                return havocStmts
          | _ =>
              emitDiagnostic $ md.toDiagnostic "Assignments with multiple target but without a RHS call should not be constructed"
              returnNone
  | .IfThenElse cond thenBranch elseBranch =>
      let bcond ← translateExpr cond
      let bthen ← translateStmt outputParams thenBranch
      let belse ← match elseBranch with
                  | some e => translateStmt outputParams e
                  | none => pure []
      return [Imperative.Stmt.ite (.det bcond) bthen belse md]
  | .StaticCall callee args =>
      -- Check if this is a function or procedure
      if model.isFunction callee then
        -- Function call in statement position: preserve as unused init
        exprAsUnusedInit stmt md
      else
        let coreArgs ← args.mapM (fun a => translateExpr a)
        -- Synthesize throwaway LHS variables so Core arity checking
        -- passes (lhs.length == outputs.length).
        let outputs := match model.get callee with
          | .staticProcedure proc => proc.outputs
          | .instanceProcedure _ proc => proc.outputs
          | _ => []
        let mut inits : List Core.Statement := []
        let mut lhs : List Core.CoreIdent := []
        for out in outputs do
          let id ← freshId
          let ident : Core.CoreIdent := ⟨s!"$unused_{id}", ()⟩
          let coreType := LTy.forAll [] (← translateType out.type)
          inits := inits ++ [Core.Statement.init ident coreType .nondet md]
          lhs := lhs ++ [ident]
        let callStmts ← mkCallWithResult lhs callee.text coreArgs md
        return inits ++ callStmts
  | .InstanceCall target callee args =>
      match model.get callee with
      | .instanceProcedure typeName proc =>
        let coreTarget ← translateExpr target
        let coreArgs ← args.mapM (fun a => translateExpr a)
        let mut inits : List Core.Statement := []
        let mut lhs : List Core.CoreIdent := []
        for out in proc.outputs do
          let id ← freshId
          let ident : Core.CoreIdent := ⟨s!"$unused_{id}", ()⟩
          let coreType := LTy.forAll [] (← translateType out.type)
          inits := inits ++ [Core.Statement.init ident coreType .nondet md]
          lhs := lhs ++ [ident]
        let allArgs := instanceCallArgs coreTarget coreArgs args
        let callStmts ← mkCallWithResult lhs callee.text allArgs md
        return inits ++ callStmts
      | _ =>
        emitDiagnostic $ md.toDiagnostic "instance call: callee not resolved as instance procedure" DiagnosticType.NotYetImplemented
        return []
  | .Return valueOpt =>
      match valueOpt, outputParams.head? with
      | some value, some outParam =>
          let ident := ⟨outParam.name.text, ()⟩
          let coreExpr ← translateExpr value
          let assignStmt := Core.Statement.set ident coreExpr md
          return [assignStmt, .exit (some "$body") md]
      | none, _ =>
          return [.exit (some "$body") md]
      | some _, none =>
          emitDiagnostic $ md.toDiagnostic "Return statement with value but procedure has no output parameters"
          return [.exit (some "$body") md]
  | .While cond invariants decreasesExpr body =>
      let condExpr ← translateExpr cond
      let invExprs ← invariants.mapM (translateExpr)
      let decreasingExprCore ← decreasesExpr.mapM (translateExpr)
      let bodyStmts ← translateStmt outputParams body
      return [Imperative.Stmt.loop (.det condExpr) decreasingExprCore invExprs bodyStmts md]
  | .Exit target =>
      return [Imperative.Stmt.exit (some target) md]
  | .Throw _exception =>
      -- Throw translates to: $result := Failure(); exit <exceptionTarget>
      let target := (← get).exceptionTarget
      let resultIdent : Core.CoreIdent := ⟨"$result", ()⟩
      let failureCtor : Core.Expression.Expr := .op () ⟨"Failure", ()⟩ none
      let setResult := Core.Statement.set resultIdent failureCtor md
      let exitTarget := Imperative.Stmt.exit (some target) md
      return [setResult, exitTarget]
  | .TryCatch body catches finally_ =>
      let id ← freshId
      let tryLabel := s!"$try_end_{id}"
      let handlersLabel := s!"$handlers_{id}"
      let resultIdent : Core.CoreIdent := ⟨"$result", ()⟩
      let isFailureCheck : Core.Expression.Expr :=
        .app () (.op () ⟨"ExceptionResult..isFailure", ()⟩ none) (.fvar () resultIdent none)
      let successCtor : Core.Expression.Expr := .op () ⟨"Success", ()⟩ none
      -- Translate try body with exception target set to handlers label
      let savedTarget := (← get).exceptionTarget
      modify fun s => { s with exceptionTarget := handlersLabel }
      let bodyStmts ← translateStmt outputParams body
      modify fun s => { s with exceptionTarget := savedTarget }
      let exitTry := Imperative.Stmt.exit (some tryLabel) md
      let handlersBlock := Imperative.Stmt.block handlersLabel (bodyStmts ++ [exitTry]) md
      -- Catch dispatch
      let catchStmts ← catches.attach.flatMapM fun ⟨c, _hc⟩ => do
        have : sizeOf c.body < sizeOf stmt := by
          have := WithMetadata.sizeOf_val_lt stmt
          have : sizeOf c < sizeOf catches := List.sizeOf_lt_of_mem _hc
          cases c; cases stmt; simp_all; omega
        let handlerBody ← translateStmt outputParams c.body
        let resetResult := Core.Statement.set resultIdent successCtor md
        let catchBlock := Imperative.Stmt.ite
          (.det isFailureCheck)
          (resetResult :: handlerBody ++ [Imperative.Stmt.exit (some tryLabel) md])
          []
          md
        pure [catchBlock]
      let tryBlock := Imperative.Stmt.block tryLabel ([handlersBlock] ++ catchStmts) md
      let finallyStmts ← match finally_ with
        | some f => translateStmt outputParams f
        | none => pure []
      return [tryBlock] ++ finallyStmts
  | _ =>
      -- Expression in statement position: preserve as an unused variable init
      exprAsUnusedInit stmt md
  termination_by sizeOf stmt
  decreasing_by
    all_goals first
      | (have hlt := WithMetadata.sizeOf_val_lt stmt; cases stmt; term_by_mem)
      | (have := WithMetadata.sizeOf_val_lt stmt
         have : sizeOf ‹CatchClause› < sizeOf catches := List.sizeOf_lt_of_mem ‹_ ∈ catches›
         cases ‹CatchClause›; cases stmt; simp_all; omega)

/--
Translate a list of checks (preconditions or postconditions) to Core checks.
Each check gets a label like `"requires"` or `"requires_0"`, `"requires_1"`, etc.
-/
def translateChecks (checks : List StmtExprMd) (labelBase : String)
    : TranslateM (ListMap Core.CoreLabel Core.Procedure.Check) :=
  checks.mapIdxM (fun i check => do
    let label := if checks.length == 1 then labelBase else s!"{labelBase}_{i}"
    let checkExpr ← translateExpr check [] (isPureContext := true)
    let c : Core.Procedure.Check := { expr := checkExpr, md := check.md }
    return (label, c))

/--
Translate Laurel Parameter to Core Signature entry
-/
def translateParameterToCore (param : Parameter) : TranslateM (Core.CoreIdent × LMonoTy) := do
  let ident := ⟨param.name.text, ()⟩
  let ty ← translateType param.type
  return (ident, ty)

/--
Translate Laurel Procedure to Core Procedure using `TranslateM`.
Diagnostics from disallowed constructs in preconditions, postconditions, and body
are emitted into the monad state.
-/
def translateProcedure (proc : Procedure) : TranslateM Core.Procedure := do
  let inputPairs ← proc.inputs.mapM translateParameterToCore
  let inputs := inputPairs
  let outputs ← proc.outputs.mapM translateParameterToCore
  -- Add $result output for exception propagation (every procedure can throw)
  let resultIdent : Core.CoreIdent := ⟨"$result", ()⟩
  let resultMonoTy : LMonoTy := .tcons "ExceptionResult" []
  let header : Core.Procedure.Header := {
    name := proc.name.text
    typeArgs := []
    inputs := inputs
    outputs := outputs ++ [(resultIdent, resultMonoTy)]
  }
  -- Translate preconditions
  let preconditions ← translateChecks proc.preconditions "requires"

  -- Translate postconditions for Opaque and Abstract bodies
  let postconditions : ListMap Core.CoreLabel Core.Procedure.Check ←
    match proc.body with
    | .Opaque postconds _ _ | .Abstract postconds =>
        translateChecks postconds "postcondition"
    | _ => pure []
  let modifies : List Core.Expression.Ident := []
  let bodyStmts : List Core.Statement ←
    match proc.body with
    | .Transparent bodyExpr _ => translateStmt proc.outputs bodyExpr
    | .Opaque _postconds (some impl) _ => translateStmt proc.outputs impl
    | _ =>
      -- Bodiless procedure: assume postconditions so that verification of the
      -- procedure itself passes trivially, and inlining only introduces the
      -- postconditions as assumptions (not the unsound `assume false`).
      pure (postconditions.map fun (label, check) =>
        Core.Statement.assume label check.expr mdWithUnknownLoc)
  -- Wrap body in a labeled block so early returns (exit) work correctly.
  -- Set $result to Success before the body (default: no exception).
  let successCtor : Core.Expression.Expr := .op () ⟨"Success", ()⟩ none
  let setResult := Core.Statement.set resultIdent successCtor mdWithUnknownLoc
  let body : List Core.Statement := [setResult, .block "$body" bodyStmts mdWithUnknownLoc]
  let spec : Core.Procedure.Spec := { modifies, preconditions, postconditions }
  return { header, spec, body }

def translateInvokeOnAxiom (proc : Procedure) (trigger : StmtExprMd)
    : TranslateM (Option Core.Decl) := do
  let postconds := match proc.body with
    | .Opaque postconds _ _ | .Abstract postconds => postconds
    | _ => []
  if postconds.isEmpty then return none
  -- All input param names become bound variables.
  -- buildQuants nests ∀ p1, ∀ p2, ..., ∀ pn :: body, so inside body the innermost
  -- binder (pn) is de Bruijn index 0, and the outermost (p1) is index n-1.
  -- translateExpr uses findIdx? on boundVars, so we must list params innermost-first
  -- (i.e. reversed) so that pn → 0, ..., p1 → n-1.
  let boundVars := proc.inputs.reverse.map (·.name)
  -- Translate postconditions and trigger with the full bound-var context
  let postcondExprs ← postconds.mapM (fun pc => translateExpr pc boundVars (isPureContext := true))
  let bodyExpr : Core.Expression.Expr := match postcondExprs with
    | [] => .const () (.boolConst true)
    | [e] => e
    | e :: rest => rest.foldl (fun acc x => LExpr.mkApp () boolAndOp [acc, x]) e
  let triggerExpr ← translateExpr trigger boundVars (isPureContext := true)
  -- Wrap in ∀ from outermost (first param) to innermost (last param).
  -- The trigger is placed on the innermost quantifier.
  let quantified ← buildQuants proc.inputs bodyExpr triggerExpr
  return some (.ax { name := s!"invokeOn_{proc.name.text}", e := quantified } proc.md)
where
  /-- Build `∀ p1 ... pn :: { trigger } body`. The trigger is on the innermost quantifier. -/
  buildQuants (params : List Parameter)
      (body : Core.Expression.Expr) (trigger : Core.Expression.Expr)
      : TranslateM Core.Expression.Expr := do
    match params with
    | [] => return body
    | [p] =>
      return LExpr.allTr () p.name.text (some (← translateType p.type)) trigger body
    | p :: rest => do
      let inner ← buildQuants rest body trigger
      return LExpr.all () p.name.text (some (← translateType p.type)) inner

structure LaurelTranslateOptions where
  emitResolutionErrors : Bool := true
  inlineFunctionsWhenPossible : Bool := false

/-- Generate axioms from function postconditions.
    For each postcondition like `x < y → result < 0`, produce an axiom:
      ∀ x : int, ∀ y : int, x < y → compare(x, y) < 0
    Returns a list of axioms with the same length as postconds. -/
@[expose] def generateFunctionAxioms (proc : Procedure) (postconds : List StmtExprMd)
    (outputTy : LMonoTy) : TranslateM (List Core.Expression.Expr) :=
  if postconds.isEmpty then pure []
  else do
    -- Translate postconditions with input params as bound vars; `result` becomes fvar
    let boundVars := proc.inputs.reverse.map (·.name)
    let postcondExprs ← postconds.mapM (fun pc => translateExpr pc boundVars (isPureContext := true))
    let n := proc.inputs.length
    let inputTypes ← proc.inputs.mapM (fun p => translateType p.type)
    -- Build the arrow type for the function: T1 → T2 → ... → Tn → ReturnType
    let funcTy := match inputTypes with
      | [] => outputTy
      | ity :: irest => Lambda.LMonoTy.mkArrow ity (irest ++ [outputTy])
    -- Build function application: f(bvar(n-1), ..., bvar(0))
    let mkFuncApp := List.range n |>.foldl (fun acc i =>
      LExpr.app () acc (.bvar () (n - 1 - i))) (LExpr.op () ⟨proc.name.text, ()⟩ (some funcTy))
    -- Substitute fvar("result") with the function application in each postcondition
    let resultId : Core.Expression.Ident := ⟨"result", ()⟩
    let substituted := postcondExprs.map (fun (e : Core.Expression.Expr) =>
      LExpr.substFvar (T := Core.CoreLParams) e resultId mkFuncApp)
    -- Build individual axioms, each wrapped in ∀ quantifiers with trigger
    substituted.mapM fun postExpr => do
      let trigger := mkFuncApp
      let pairs := proc.inputs.zip inputTypes
      let rec buildQuants : List (Laurel.Parameter × LMonoTy) → TranslateM Core.Expression.Expr
        | [] => pure postExpr
        | [(_, ty)] => pure (LExpr.allTr () "" (some ty) trigger postExpr)
        | (_, ty) :: rest => do
          let inner ← buildQuants rest
          pure (LExpr.all () "" (some ty) inner)
      buildQuants pairs

private theorem List.length_mapM_optionT_stateM'
    {α β σ : Type} (f : α → OptionT (StateM σ) β)
    (l : List α) (s : σ) (result : List β) (s' : σ)
    (h : l.mapM f s = (some result, s')) :
    result.length = l.length := by
  induction l generalizing s result s' with
  | nil =>
    simp only [List.mapM, pure, OptionT.pure, OptionT.mk, StateT.pure] at h
    have := Option.some.inj (Prod.mk.inj h).1; subst this; rfl
  | cons x xs ih =>
    rw [List.mapM_cons] at h
    match hfx : f x s with
    | (some b, s1) =>
      simp only [bind, OptionT.bind, OptionT.mk, StateT.bind,
        pure, OptionT.pure, StateT.pure, hfx] at h
      match hxs : List.mapM f xs s1 with
      | (some bs, s2) =>
        simp only [hxs, pure, OptionT.pure, OptionT.mk, StateT.pure] at h
        have := Option.some.inj (Prod.mk.inj h).1; subst this
        simp [ih s1 bs s2 hxs]
      | (none, s2) =>
        simp only [hxs] at h; exact absurd (Prod.mk.inj h).1 (by simp)
    | (none, s1) =>
      simp only [bind, OptionT.bind, OptionT.mk, StateT.bind, hfx] at h
      exact absurd (Prod.mk.inj h).1 (by simp)

/-- generateFunctionAxioms preserves postcondition count. -/
theorem generateFunctionAxioms_length
    (proc : Procedure) (postconds : List StmtExprMd) (outputTy : LMonoTy)
    (s s' : TranslateState) (axioms : List Core.Expression.Expr)
    (h : generateFunctionAxioms proc postconds outputTy s = (some axioms, s')) :
    axioms.length = postconds.length := by
  unfold generateFunctionAxioms at h
  by_cases hEmpty : postconds.isEmpty = true
  · simp only [hEmpty, ite_true, pure, OptionT.pure, OptionT.mk, StateT.pure] at h
    have := Option.some.inj (Prod.mk.inj h).1; subst this
    simp [List.isEmpty_iff.mp hEmpty]
  · simp only [Bool.not_eq_true] at hEmpty
    simp only [generateFunctionAxioms, hEmpty, Bool.false_eq_true, ↓reduceIte,
      pure, OptionT.pure, OptionT.mk, OptionT.bind, OptionT.lift,
      bind, StateT.bind, StateT.pure,
      liftM, monadLift, MonadLift.monadLift] at h
    generalize hPC : postconds.mapM (fun pc =>
      translateExpr pc (proc.inputs.reverse.map (·.name)) true) s = pcResult at h
    obtain ⟨pcOpt, s1⟩ := pcResult
    cases pcOpt with
    | some postcondExprs =>
      simp only [Prod.mk.injEq] at h
      simp only [StateT.bind] at h
      generalize hIT : (proc.inputs.mapM (fun p => translateType p.type) s1) = itResult at h
      obtain ⟨itOpt, s2⟩ := itResult
      cases itOpt with
      | some inputTypes =>
        simp only [bind, StateT.bind, pure, StateT.pure, Prod.fst, Prod.snd,
          OptionT.pure, OptionT.mk, OptionT.bind] at h
        have h1 := List.length_mapM_optionT_stateM'
          (fun pc => translateExpr pc (proc.inputs.reverse.map (·.name)) true)
          postconds s postcondExprs s1 hPC
        have h2 := List.length_mapM_optionT_stateM' _ (postcondExprs.map _) s2 axioms s' h
        simp [List.length_map] at h2
        omega
      | none =>
        simp only [bind, StateT.bind, pure, StateT.pure, Prod.fst, Prod.snd,
          OptionT.pure, OptionT.mk, OptionT.bind] at h
        exact absurd (Prod.mk.inj h).1 (by simp)
    | none =>
      simp only [] at h
      exact absurd (Prod.mk.inj h).1 (by simp)

/--
Translate a Laurel Procedure to a Core Function (when applicable) using `TranslateM`.
Diagnostics for disallowed constructs in the function body are emitted into the monad state.
-/
def translateProcedureToFunction (options: LaurelTranslateOptions) (isRecursive: Bool) (proc : Procedure) : TranslateM Core.Decl := do
  let inputs ← proc.inputs.mapM translateParameterToCore
  let outputTy ← match proc.outputs.head? with
    | some p => translateType p.type
    | none => pure LMonoTy.int
  -- Translate precondition to FuncPrecondition (skip trivial `true`)
  let preconditions ← proc.preconditions.mapM (fun precondition => do
    let checkExpr ← translateExpr precondition [] true
    return { expr := checkExpr, md := () })

  -- For recursive functions, infer the @[cases] parameter index: the first input
  -- whose type is a user-defined datatype (has constructors). This is the argument
  -- the partial evaluator will case-split on to unfold the recursion.
  -- TODO: Use the decreases of the function to determine where to put @[cases]
  -- First step should be to only support a decreases clause that is exactly one datatype parameter
  -- Since that's what Core supports
  let model := (← get).model
  let casesIdx : Option Nat :=
    if !isRecursive then none
    else proc.inputs.findIdx? fun p =>
      match p.type.val with
      | .UserDefined name => match model.get name with
        | .datatypeDefinition _ => true
        | _ => false
      | _ => false
  let attr : Array Strata.DL.Util.FuncAttr :=
    match casesIdx with
    | some i => #[.inlineIfConstr i]
    | none => if options.inlineFunctionsWhenPossible then #[.inline] else #[]

  let body ← match proc.body with
    | .Transparent bodyExpr _ => some <$> translateExpr bodyExpr [] (isPureContext := true)
    | .Opaque _ (some _) _ =>
      -- Opaque function: body hidden from callers, postconditions available
      -- via axioms, checked by $check procedure
      pure none
    | _ => pure none

  -- Generate axioms from function postconditions.
  -- For each postcondition like `x < y → result < 0`, produce an axiom:
  --   ∀ x : int, ∀ y : int, x < y → compare(x, y) < 0
  let postconds := match proc.body with
    | .Transparent _ posts => posts
    | .Opaque posts _ _ => posts
    | .Abstract posts => posts
    | .External => []
  let axioms ← generateFunctionAxioms proc postconds outputTy

  let f : Core.Function := {
    name := ⟨proc.name.text, ()⟩
    typeArgs := []
    inputs := inputs
    output := outputTy
    body := body
    preconditions := preconditions
    isRecursive := isRecursive
    attr := attr
    axioms := axioms
  }
  return .func f proc.md

/-- Helper: getPostconds extracts postconditions from a Body. -/
def getPostconds : Body → List StmtExprMd
  | .Transparent _ posts => posts
  | .Opaque posts _ _ => posts
  | .Abstract posts => posts
  | .External => []

/-- Bind inversion for OptionT (StateM σ): if the bind succeeds, both parts succeeded. -/
private theorem bind_inv {α β σ : Type}
    {f : OptionT (StateM σ) α} {g : α → OptionT (StateM σ) β}
    {s : σ} {r : β} {s' : σ}
    (h : (f >>= g) s = (some r, s')) :
    ∃ (x : α) (s₁ : σ), f s = (some x, s₁) ∧ g x s₁ = (some r, s') := by
  simp only [bind, OptionT.bind, OptionT.mk, StateT.bind] at h
  generalize hf : f s = fResult at h
  obtain ⟨fOpt, s₁⟩ := fResult
  cases fOpt with
  | some x => exact ⟨x, s₁, rfl, h⟩
  | none => exact absurd (Prod.mk.inj h).1 (by simp [StateT.pure])

/-- When translateProcedureToFunction succeeds, the axiom count equals the
    postcondition count. Proved inside the module block where `unfold` works. -/
theorem translateProcedureToFunction_axioms_length
    (options : LaurelTranslateOptions) (isRecursive : Bool)
    (proc : Procedure) (s s' : TranslateState) (f : Core.Function) (fmd : MetaData)
    (hSucc : translateProcedureToFunction options isRecursive proc s = (some (.func f fmd), s')) :
    f.axioms.length = (getPostconds proc.body).length := by
  unfold translateProcedureToFunction at hSucc
  obtain ⟨inputs, s1, _, hRest⟩ := bind_inv hSucc
  simp only [bind, OptionT.bind, OptionT.mk, StateT.bind, StateT.pure,
    pure, OptionT.pure, OptionT.lift, get, MonadState.get, getThe, MonadStateOf.get,
    StateT.get, liftM, monadLift, MonadLift.monadLift, Functor.map,
    Prod.fst, Prod.snd, Function.comp] at hRest
  cases hHead : proc.outputs.head? with
  | some p =>
    simp only [hHead] at hRest
    obtain ⟨outputTy, s2, _, hRest2⟩ := bind_inv hRest
    obtain ⟨preconditions, s3, _, hRest3⟩ := bind_inv hRest2
    simp only [StateT.get, StateT.bind, StateT.pure, bind, pure] at hRest3
    cases hBC : proc.body with
    | Transparent bodyExpr postconds =>
      simp only [hBC] at hRest3
      obtain ⟨body, s5, _, hRest5⟩ := bind_inv hRest3
      obtain ⟨axioms, s6, hAxioms, hRest6⟩ := bind_inv hRest5
      simp [pure, StateT.pure] at hRest6
      have hF := Core.Decl.func.inj (Option.some.inj (Prod.mk.inj hRest6).1)
      simp only [hBC] at hAxioms; rw [← hF.1]; simp only [getPostconds]
      exact generateFunctionAxioms_length proc postconds outputTy s5 s6 axioms hAxioms
    | Opaque postconds impl _ =>
      simp only [hBC] at hRest3; cases impl <;> (
        simp only [pure, StateT.pure, StateT.bind, bind] at hRest3
        obtain ⟨axioms, s6, hAxioms, hRest6⟩ := bind_inv hRest3
        simp [pure, StateT.pure] at hRest6
        have hF := Core.Decl.func.inj (Option.some.inj (Prod.mk.inj hRest6).1)
        simp only [hBC] at hAxioms; rw [← hF.1]; simp only [getPostconds]
        exact generateFunctionAxioms_length proc postconds outputTy s3 s6 axioms hAxioms)
    | Abstract postconds =>
      simp only [hBC, pure, StateT.pure, StateT.bind, bind] at hRest3
      obtain ⟨axioms, s6, hAxioms, hRest6⟩ := bind_inv hRest3
      simp [pure, StateT.pure] at hRest6
      have hF := Core.Decl.func.inj (Option.some.inj (Prod.mk.inj hRest6).1)
      simp only [hBC] at hAxioms; rw [← hF.1]; simp only [getPostconds]
      exact generateFunctionAxioms_length proc postconds outputTy s3 s6 axioms hAxioms
    | External =>
      simp only [hBC, pure, StateT.pure, StateT.bind, bind] at hRest3
      match hAx : generateFunctionAxioms proc [] outputTy s3 with
      | (some axioms, s6) =>
        rw [hAx] at hRest3; simp [StateT.pure] at hRest3
        have hF := Core.Decl.func.inj (Option.some.inj (Prod.mk.inj hRest3).1)
        rw [← hF.1]; simp only [getPostconds]
        exact generateFunctionAxioms_length proc [] outputTy s3 s6 axioms hAx
      | (none, s6) =>
        rw [hAx] at hRest3; exact absurd (Prod.mk.inj hRest3).1 (by simp)
  | none =>
    simp only [hHead, pure, StateT.pure, StateT.bind, bind] at hRest
    obtain ⟨preconditions, s3, _, hRest3⟩ := bind_inv hRest
    simp only [StateT.get, StateT.bind, StateT.pure, bind, pure] at hRest3
    cases hBC : proc.body with
    | Transparent bodyExpr postconds =>
      simp only [hBC] at hRest3
      obtain ⟨body, s5, _, hRest5⟩ := bind_inv hRest3
      obtain ⟨axioms, s6, hAxioms, hRest6⟩ := bind_inv hRest5
      simp [pure, StateT.pure] at hRest6
      have hF := Core.Decl.func.inj (Option.some.inj (Prod.mk.inj hRest6).1)
      simp only [hBC] at hAxioms; rw [← hF.1]; simp only [getPostconds]
      exact generateFunctionAxioms_length proc postconds LMonoTy.int s5 s6 axioms hAxioms
    | Opaque postconds impl _ =>
      simp only [hBC] at hRest3; cases impl <;> (
        simp only [pure, StateT.pure, StateT.bind, bind] at hRest3
        obtain ⟨axioms, s6, hAxioms, hRest6⟩ := bind_inv hRest3
        simp [pure, StateT.pure] at hRest6
        have hF := Core.Decl.func.inj (Option.some.inj (Prod.mk.inj hRest6).1)
        simp only [hBC] at hAxioms; rw [← hF.1]; simp only [getPostconds]
        exact generateFunctionAxioms_length proc postconds LMonoTy.int s3 s6 axioms hAxioms)
    | Abstract postconds =>
      simp only [hBC, pure, StateT.pure, StateT.bind, bind] at hRest3
      obtain ⟨axioms, s6, hAxioms, hRest6⟩ := bind_inv hRest3
      simp [pure, StateT.pure] at hRest6
      have hF := Core.Decl.func.inj (Option.some.inj (Prod.mk.inj hRest6).1)
      simp only [hBC] at hAxioms; rw [← hF.1]; simp only [getPostconds]
      exact generateFunctionAxioms_length proc postconds LMonoTy.int s3 s6 axioms hAxioms
    | External =>
      simp only [hBC, pure, StateT.pure, StateT.bind, bind] at hRest3
      match hAx : generateFunctionAxioms proc [] LMonoTy.int s3 with
      | (some axioms, s6) =>
        rw [hAx] at hRest3; simp [StateT.pure] at hRest3
        have hF := Core.Decl.func.inj (Option.some.inj (Prod.mk.inj hRest3).1)
        rw [← hF.1]; simp only [getPostconds]
        exact generateFunctionAxioms_length proc [] LMonoTy.int s3 s6 axioms hAx
      | (none, s6) =>
        rw [hAx] at hRest3; exact absurd (Prod.mk.inj hRest3).1 (by simp)

/--
Translate a Laurel DatatypeDefinition to an `LDatatype Unit`.
-/
def translateDatatypeDefinition (dt : DatatypeDefinition)
    : TranslateM (Lambda.LDatatype Unit) := do
  let constrs ← dt.constructors.mapM fun c => do
    let args ← c.args.mapM fun ⟨ n, ty ⟩ => do
      return (⟨n.text, ()⟩, ← translateType ty)
    return { name := ⟨c.name.text, ()⟩
             args := args
             testerName := s!"{dt.name}..is{c.name}" : Lambda.LConstr Unit }
  -- Zero-constructor datatypes (e.g. TypeTag with no composite types) get a synthetic
  -- unit constructor so the type is valid and can be referenced by other datatypes.
  let constrs := if constrs.isEmpty then
      [{ name := ⟨s!"Mk{dt.name.text}", ()⟩, args := [] }]
    else constrs
  return {
    name := dt.name.text
    typeArgs := dt.typeArgs.map (fun id => id.text)
    constrs := constrs
    constrs_ne := by simp [constrs]; grind
    : Lambda.LDatatype Unit
  }

abbrev TranslateResult := (Option Core.Program) × (List DiagnosticModel)

/-- Like `translate` but also returns the lowered Laurel program (after all
    Laurel-to-Laurel passes, before the final translation to Core). -/
abbrev TranslateResultWithLaurel := (Option Core.Program) × (List DiagnosticModel) × Program

/--
Qualify instance procedure names with their owner composite type.
`compareTo` on Position becomes `Position~>compareTo`.
Must run before the first `resolve` call so that the resolution pass
registers each instance procedure under its unique qualified name.
See `docs/design/cross-type-resolution/decisions.md` D4.
-/
def qualifyInstanceProcNames (program : Program) : Program :=
  { program with types := program.types.map fun td =>
    match td with
    | .Composite ct =>
      .Composite { ct with instanceProcedures :=
        ct.instanceProcedures.map fun proc =>
          { proc with name := { proc.name with
            text := instanceProcCoreName ct.name.text proc.name.text } } }
    | other => other }

/--
Translate Laurel Program to Core Program, also returning the lowered Laurel program.
-/
def translateWithLaurel (options: LaurelTranslateOptions) (program : Program): TranslateResultWithLaurel :=
  let program := { program with
    staticProcedures := coreDefinitionsForLaurel.staticProcedures ++ program.staticProcedures
    types := coreDefinitionsForLaurel.types ++ program.types
  }

  -- Qualify instance procedure names before resolution so that
  -- each type's methods have unique scope entries (no shadowing).
  let program := qualifyInstanceProcNames program

  -- dbg_trace "=== Initial Laurel program ==="
  -- dbg_trace (toString (Std.Format.pretty (Std.ToFormat.format program)))
  -- dbg_trace "================================="
  let result := resolve program
  let resolutionErrors: List DiagnosticModel := if options.emitResolutionErrors then result.errors.toList else []
  let (program, model) := (result.program, result.model)
  let diamondErrors := validateDiamondFieldAccesses model program

  let (program, nonCompositeDiags) := filterNonCompositeModifies model program

  let program := heapParameterization model program
  let result := resolve program (some model)
  let (program, model) := (result.program, result.model)

  let program := typeHierarchyTransform model program
  let result := resolve program (some model)
  let (program, model) := (result.program, result.model)
  let (program, modifiesDiags) := modifiesClausesTransform model program
  let result := resolve program (some model)
  let (program, model) := (result.program, result.model)
  let result := resolve program (some model)
  let (program, model) := (result.program, result.model)
  let program := inferHoleTypes model program
  let program := eliminateHoles program
  let program := desugarShortCircuit model program
  let program := liftExpressionAssignments model program
  let program := eliminateReturnsInExpressionTransform program
  let result := resolve program (some model)
  let (program, model) := (result.program, result.model)

  let (program, constrainedTypeDiags) := constrainedTypeElim model program
  let result := resolve program (some model)
  let (program, model) := (result.program, result.model)

  let (program, funcPostcondDiags) := functionPostcondCheck program
  let result := resolve program (some model)
  let (program, model) := (result.program, result.model)

  let initState : TranslateState := {model := model }
  let (coreProgramOption, translateState) := runTranslateM initState (translateLaurelToCore options program)
  let allDiagnostics := resolutionErrors ++ diamondErrors ++ nonCompositeDiags ++ modifiesDiags ++ constrainedTypeDiags ++ funcPostcondDiags ++ translateState.diagnostics
  let coreProgramOption := if translateState.coreProgramHasSuperfluousErrors then none else coreProgramOption
  (coreProgramOption, allDiagnostics, program)
  where

  /--
  Translate Laurel datatype definitions to Core declarations.
  Datatypes are grouped by mutual references (SCC) so mutually recursive
  datatypes share a single `.data` declaration.
  -/
  translateTypes (program : Program) : TranslateM (List Core.Decl) := do
    -- Translate datatype definitions to Core declarations.
    let laurelDatatypes := program.types.filterMap fun td => match td with
      | .Datatype dt => some dt
      | _ => none
    let ldatatypes ← laurelDatatypes.mapM translateDatatypeDefinition
    let groups := groupDatatypes laurelDatatypes ldatatypes
    return groups.map fun group => Core.Decl.type (.data group) mdWithUnknownLoc

  /-- Generate equality axioms connecting Factory read functions to Box constructors.
      For each (readName, constrName) pair where the constructor exists in the program's
      Box datatype, generates: ∀ v: int. readName(constrName(v)) == v
      These axioms let the prover chain through the heap round-trip for constrained types.
      See design/constrained-types-in-heap/decisions.md D4. -/
  mkReadFuncAxioms (program : Program) : List Core.Decl :=
    let boxConstrs := program.types.foldl (fun acc td => match td with
      | .Datatype dt => if dt.name.text == "Box" then
          dt.constructors.map (·.name.text)
        else acc
      | _ => acc) ([] : List String)
    [("readInt32", "BoxInt"), ("readInt16", "BoxInt"), ("readInt8", "BoxInt")].filterMap
      fun (readName, constrName) =>
        if boxConstrs.contains constrName then
          let boxTy := LMonoTy.tcons "Box" []
          let readOp : Core.Expression.Expr := .op () ⟨readName, ()⟩ (some (.arrow boxTy .int))
          let constrOp : Core.Expression.Expr := .op () ⟨constrName, ()⟩ (some (.arrow .int boxTy))
          let v : Core.Expression.Expr := .bvar () 0
          let body : Core.Expression.Expr := .eq () (.app () readOp (.app () constrOp v)) v
          let axiomExpr : Core.Expression.Expr := .all () "v" (some LMonoTy.int) body
          some (Core.Decl.ax { name := readName ++ "_eq", e := axiomExpr } .empty)
        else none

  translateLaurelToCore (options: LaurelTranslateOptions) (program : Program): TranslateM Core.Program := do

    let sccDecls := computeSccDecls program

    let orderedDecls ← sccDecls.flatMapM (fun (procs, isRecursive) => do
      -- For each SCC, determine if it is purely functional or contains procedures.
      -- Procedures can't call functions (only functions can call functions), so an SCC
      -- either contains only functional procedures or only non-functional procedures.
      let isFuncSCC := procs.all (·.isFunctional)
      if isFuncSCC then
        let funcs ← procs.mapM (translateProcedureToFunction options isRecursive)
        if isRecursive then
          -- Wrap all recursive functions (single self-recursive or mutual) in recFuncBlock.
          let coreFuncs := funcs.filterMap (fun d => match d with
            | .func f _ => some f
            | _ => none)
          return [Core.Decl.recFuncBlock coreFuncs mdWithUnknownLoc]
        else
          return funcs
      else
        procs.flatMapM fun proc => do
          let axiomDecls : List Core.Decl ← match proc.invokeOn with
            | none => pure []
            | some trigger => do
              let axDecl? ← translateInvokeOnAxiom proc trigger
              pure axDecl?.toList
          let procDecl ← translateProcedure proc
          return [Core.Decl.proc procDecl proc.md] ++ axiomDecls
    )

    -- Translate Laurel constants to Core function declarations (0-ary functions)
    let constantDecls ← program.constants.mapM fun c => do
      let coreTy ← translateType c.type
      let body ← c.initializer.mapM (translateExpr ·)
      return Core.Decl.func {
        name := ⟨c.name.text, ()⟩
        typeArgs := []
        inputs := []
        output := coreTy
        body := body
      } mdWithUnknownLoc

    -- Instance procedures are now included in computeSccDecls and come through
    -- orderedDecls, so they go through the same functional/non-functional routing.

    -- Translate Laurel datatype definitions to Core declarations.
    let groupedDatatypeDecls ← translateTypes program
    -- ExceptionResult datatype for exception propagation
    let exceptionResultDecl : Core.Decl := Core.Decl.type (.data [{
      name := "ExceptionResult"
      typeArgs := []
      constrs := [
        { name := ⟨"Success", ()⟩, args := [], testerName := "ExceptionResult..isSuccess" },
        { name := ⟨"Failure", ()⟩, args := [], testerName := "ExceptionResult..isFailure" }
      ]
      constrs_ne := rfl
    }]) mdWithUnknownLoc
    let program := {
      decls := [exceptionResultDecl] ++ groupedDatatypeDecls ++ mkReadFuncAxioms program ++ constantDecls ++ orderedDecls
    }

    -- dbg_trace "=== Generated Strata Core Program ==="
    -- dbg_trace (toString (Std.Format.pretty (Strata.Core.formatProgram program) 100))
    -- dbg_trace "================================="
    pure program


/--
Translate Laurel Program to Core Program
-/
def translate (options: LaurelTranslateOptions) (program : Program): TranslateResult :=
  let (core, diags, _) := translateWithLaurel options program
  (core, diags)

/--
Verify a Laurel program using an SMT solver
-/
def verifyToVcResults (program : Program)
    (options : VerifyOptions := .default)
    : IO (Option VCResults × List DiagnosticModel) := do
  let (coreProgramOption, translateDiags) := translate {} program

  match coreProgramOption with
  | some coreProgram =>
    -- Enable removeIrrelevantAxioms to avoid polluting simple assertions with heap axioms
    let options := { options with removeIrrelevantAxioms := .Precise }
    let runner tempDir :=
      EIO.toIO (fun f => IO.Error.userError (toString f))
          (Core.verify coreProgram tempDir .none options)
    let ioResult ← match options.vcDirectory with
      | .none => IO.FS.withTempDir runner
      | .some p => IO.FS.createDirAll ⟨p.toString⟩; runner ⟨p.toString⟩
    return (some ioResult, translateDiags)
  | none => return (none, translateDiags)

def verifyToDiagnostics (files: Map Strata.Uri Lean.FileMap) (program : Program)
    (options : VerifyOptions := .default): IO (Array Diagnostic) := do
  let results <- verifyToVcResults program options
  let phases := Core.coreAbstractedPhases
  let translationDiags := results.snd.map (fun dm => dm.toDiagnostic files)
  let vcDiags := match results.fst with
  | some vcResults => vcResults.toList.filterMap (fun (vcr: VCResult) => vcr.toDiagnostic files phases)
  | none => []
  return (translationDiags ++ vcDiags).toArray

def verifyToDiagnosticModels (program : Program) (options : VerifyOptions := .default) : IO (Array DiagnosticModel) := do
  let results <- verifyToVcResults program options
  let phases := Core.coreAbstractedPhases
  let vcDiags := match results.fst with
  | none => []
  | some vcResults => vcResults.toList.filterMap (fun (vcr: VCResult) => toDiagnosticModel vcr phases)
  return (results.snd ++ vcDiags).toArray

end -- public section
end Laurel
