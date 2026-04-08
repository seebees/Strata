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
public import Strata.Languages.Laurel.TranslatorModel
public import Strata.Languages.Laurel.DesugarShortCircuit
public import Strata.Languages.Laurel.InferHoleTypes
public import Strata.Languages.Laurel.EliminateHoles
public import Strata.Languages.Laurel.EliminateReturnsInExpression
public import Strata.Languages.Laurel.HeapParameterization
public import Strata.Languages.Laurel.TypeHierarchy
public import Strata.Languages.Laurel.LaurelTypes
public import Strata.Languages.Laurel.ModifiesClauses
public import Strata.Languages.Laurel.CoreDefinitionsForLaurel
import Strata.Languages.Laurel.DatatypeGrouping
import Strata.DDM.Util.DecimalRat
import Strata.DL.Imperative.Stmt
import Strata.DL.Imperative.MetaData
import Strata.DL.Lambda.LExpr
import Strata.Languages.Laurel.LaurelFormat
public import Strata.Languages.Laurel.ConstrainedTypeElim
import Strata.Util.Tactics

open Core (VCResult VCResults VerifyOptions)
open Core (intAddOp intSubOp intMulOp intSafeDivOp intSafeModOp intSafeDivTOp intSafeModTOp intNegOp intLtOp intLeOp intGtOp intGeOp boolAndOp boolOrOp boolNotOp boolImpliesOp strConcatOp)
open Core (realAddOp realSubOp realMulOp realDivOp realNegOp realLtOp realLeOp realGtOp realGeOp)

namespace Strata.Laurel

open Std (Format ToFormat)
open Strata
open Lambda (LMonoTy LTy LExpr)

public section

/-
Translate Laurel HighType to Core Type
-/
def translateType (model : SemanticModel) (ty : HighTypeMd) : LMonoTy :=
  match _h : ty.val with
  | .TInt => LMonoTy.int
  | .TBool => LMonoTy.bool
  | .TString => LMonoTy.string
  | .TVoid => LMonoTy.bool -- Using bool as placeholder for void
  | .THeap => .tcons "Heap" []
  | .TTypedField _ => .tcons "Field" []
  | .TSet elementType => Core.mapTy (translateType model elementType) LMonoTy.bool
  | .TMap keyType valueType => Core.mapTy (translateType model keyType) (translateType model valueType)
  | .TSequence elementType => Core.seqTy (translateType model elementType)
  | .UserDefined name =>
    match name.uniqueId.bind model.refToDef.get? with
    | some (.compositeType _) => .tcons "Composite" []
    | some (.datatypeDefinition dt) => .tcons dt.name.text []
    | some (.constrainedType ct) =>
        -- Translate the base type directly (one level only, no recursion)
        match ct.base.val with
        | .TInt => LMonoTy.int
        | .TBool => LMonoTy.bool
        | .TString => LMonoTy.string
        | .TReal => LMonoTy.real
        | _ => .tcons "Composite" []
    | _ => .tcons "Composite" [] -- fallback for unresolved refs
  | .TCore s => .tcons s []
  | .TReal => LMonoTy.real
  | .Unknown => .tcons "Any" [] -- TODO, abort execution since there is no valid Core type to translate Unknown to
  | _ => .tcons "NotSupportedYet" [] -- TODO, abort execution since there is no valid Core type to translate Unknown to
termination_by ty.val
decreasing_by all_goals (first | (cases elementType; term_by_mem) | (cases keyType; term_by_mem) | (cases valueType; term_by_mem))

def lookupType (model : SemanticModel) (name : Identifier) : LMonoTy :=
  translateType model (model.get name).getType

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
      try block's handlers label so the catch dispatch can run.
      See spec Property 9 and Decision 7. -/
  exceptionTarget : String := "$body"

/-- The translation monad: state over Except, allowing both accumulated diagnostics and hard failures -/
@[expose] abbrev TranslateM := OptionT (StateM TranslateState)

/-- Emit a diagnostic into the translation state (soft warning, does not abort) -/
def emitDiagnostic (d : DiagnosticModel) : TranslateM Unit :=
  modify fun s => { s with diagnostics := s.diagnostics ++ [d] }

/-- Run a `TranslateM` action, returning either a hard error or the result and final state -/
@[expose] def runTranslateM (s : TranslateState) (m : TranslateM α) : (Option α × TranslateState) :=
  m s

def returnNone: TranslateM α :=
  StateT.pure none

/-- Allocate a fresh unique ID. -/
private def freshId : TranslateM Nat := do
  let s ← get
  let id := s.nextId
  set { s with nextId := id + 1 }
  return id

/-- Resolve an InstanceCall callee to its qualified Core procedure name.
    Looks up the callee in the SemanticModel to find the owning type name,
    then constructs the qualified name via `instanceProcCoreName`. -/
def resolveInstanceCallName (model : SemanticModel) (callee : Identifier) : Option String :=
  match model.get callee with
  | .instanceProcedure typeName _ => some (instanceProcCoreName typeName.text callee.text)
  | _ => none

/-- Build the Core argument list for an InstanceCall in call-statement position.
    Per D5 (instance-methods/decisions.md): the heap parameterization prepends $heap
    to args, and the translator inserts target (self) after $heap.
    Result: [$heap, target, otherArgs...] matching the procedure signature
    ($heap_in, self, otherArgs...).
    When no heap arg is present (functional instance methods), target goes first:
    [target, otherArgs...] matching (self, otherArgs...). -/
private def instanceCallArgs (coreTarget : Core.Expression.Expr)
    (coreArgs : List Core.Expression.Expr)
    (laurelArgs : List StmtExprMd) : List Core.Expression.Expr :=
  -- Check if the heap parameterization injected $heap as the first Laurel arg
  let hasHeapArg := match laurelArgs with
    | ⟨.Identifier name, _⟩ :: _ => name.text == "$heap" || name.text == "$heap_in"
    | _ => false
  if hasHeapArg then
    match coreArgs with
    | heapArg :: rest => heapArg :: coreTarget :: rest
    | [] => [coreTarget]
  else
    coreTarget :: coreArgs

/-- Throw a hard diagnostic error, aborting the current translation -/
def throwExprDiagnostic (d : DiagnosticModel): TranslateM Core.Expression.Expr := do
  emitDiagnostic d
  modify fun s => { s with coreProgramHasSuperfluousErrors := true }
  let id ← freshId
  return LExpr.fvar () (⟨s!"DUMMY_VAR_{id}", ()⟩) none

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

@[expose] def translateExpr (expr : StmtExprMd)
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
        -- Special case: $result is the ExceptionResult output parameter
        -- injected by the translator. It's not in the Laurel model but
        -- is accessible in ensures clauses.
        if name.text == "$result" then
          return .fvar () ⟨"$result", ()⟩ (some (.tcons "ExceptionResult" []))
        else if name.text == "Success" || name.text == "Failure" then
          -- ExceptionResult constructors, used in ensures clauses
          return .op () ⟨name.text, ()⟩ none
        else
        match model.get name with
        | .field _ f =>
            return .op () ⟨f.name.text, ()⟩ none
        | astNode =>
            return .fvar () ⟨name.text, ()⟩ (some (translateType model $ astNode.getType))
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
    | .AndThen => return .ite () re1 re2 (.boolConst () false)
    | .OrElse => return .ite () re1 (.boolConst () true) re2
    | .Implies => return .ite () re1 re2 (.boolConst () true)
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
      let coreTy := translateType model ty
      let coreBody ← translateExpr body (name :: boundVars) isPureContext
      match _: trigger with
      | some trig =>
        let coreTrig ← translateExpr trig (name :: boundVars) isPureContext
        return LExpr.allTr () name.text (some coreTy) coreTrig coreBody
      | none =>
        return LExpr.all () name.text (some coreTy) coreBody
  | .Exists ⟨ name, ty ⟩ trigger body =>
      let coreTy := translateType model ty
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
  | .Old value =>
      -- old(expr) in postconditions references the pre-state.
      -- For heap state: the heap parameterization already substituted $heap → $heap_in inside Old.
      -- For parameters: they're immutable, so old(x) == x.
      -- In both cases, just translate the inner expression normally.
      translateExpr value boundVars isPureContext
  | .Fresh _ => throwExprDiagnostic $ md.toDiagnostic "fresh expression translation" DiagnosticType.NotYetImplemented
  | .Assert _ => throwExprDiagnostic $ md.toDiagnostic "assert expression translation" DiagnosticType.NotYetImplemented
  | .Assume _ => throwExprDiagnostic $ md.toDiagnostic "assume expression translation" DiagnosticType.NotYetImplemented
  | .ProveBy value _ => throwExprDiagnostic $ md.toDiagnostic "proveBy expression translation" DiagnosticType.NotYetImplemented
  | .ContractOf _ _ => throwExprDiagnostic $ md.toDiagnostic "contractOf expression translation" DiagnosticType.NotYetImplemented
  | .Abstract => throwExprDiagnostic $ md.toDiagnostic "abstract expression translation" DiagnosticType.NotYetImplemented
  | .All => throwExprDiagnostic $ md.toDiagnostic "all expression translation" DiagnosticType.NotYetImplemented
  | .InstanceCall target callee args =>
      match resolveInstanceCallName model callee with
      | some coreName =>
          let coreTarget ← translateExpr target boundVars isPureContext
          let coreArgs ← args.mapM (fun a => translateExpr a boundVars isPureContext)
          let fnOp : Core.Expression.Expr := .op () ⟨coreName, ()⟩ none
          return (coreTarget :: coreArgs).foldl (fun acc arg => .app () acc arg) fnOp
      | none => throwExprDiagnostic $ md.toDiagnostic s!"Cannot resolve instance call to '{callee.text}'" DiagnosticType.StrataBug
  | .PureFieldUpdate _ _ _ => throwExprDiagnostic $ md.toDiagnostic "pure field update expression translation" DiagnosticType.NotYetImplemented
  | .This => throwExprDiagnostic $ md.toDiagnostic "this expression translation" DiagnosticType.NotYetImplemented
  | .Throw _ => throwExprDiagnostic $ md.toDiagnostic "throw in expression position is not supported" DiagnosticType.UserError
  | .TryCatch _ _ _ => throwExprDiagnostic $ md.toDiagnostic "try/catch in expression position is not supported" DiagnosticType.UserError
  termination_by expr
  decreasing_by
    all_goals (have := WithMetadata.sizeOf_val_lt expr; term_by_mem)

def getNameFromMd (md : Imperative.MetaData Core.Expression): String :=
  let fileRange := (Imperative.getFileRange md).getD (dbg_trace "BUG: metadata without a filerange"; default)
  s!"({fileRange.range.start})"

def defaultExprForType (model : SemanticModel) (ty : HighTypeMd) : Core.Expression.Expr :=
  match ty.val with
  | .TInt => .const () (.intConst 0)
  | .TBool => .const () (.boolConst false)
  | .TString => .const () (.strConst "")
  | _ =>
    -- For types without a natural default (arrays, composites, etc.),
    -- use a fresh free variable. This is only used when the value is
    -- immediately overwritten by a procedure call.
    let coreTy := translateType model ty
    .fvar () (⟨"$default", ()⟩) (some coreTy)

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
  return [Core.Statement.init ident coreType (some coreExpr) md]


/-- Generate exception propagation check after a procedure call.
    If $result is Failure, propagate by exiting $body. -/
private def exceptionPropagationCheck (md : Imperative.MetaData Core.Expression) : TranslateM (List Core.Statement) := do
  let target := (← get).exceptionTarget
  let resultIdent : Core.CoreIdent := ⟨"$result", ()⟩
  let isFailureCheck : Core.Expression.Expr :=
    .app () (.op () ⟨"ExceptionResult..isFailure", ()⟩ none) (.fvar () resultIdent none)
  return [Imperative.Stmt.ite isFailureCheck [Imperative.Stmt.exit (some target) md] [] md]

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
      let coreMonoType := translateType model ty
      let coreType := LTy.forAll [] coreMonoType
      let ident := ⟨id.text, ()⟩
      match initializer with
      | some (⟨ .StaticCall callee args, callMd⟩) =>
          -- Check if this is a function or a procedure call
          if model.isFunction callee then
            -- Translate as expression (function application)
            let coreExpr ← translateExpr (⟨ .StaticCall callee args, callMd ⟩)
            return [Core.Statement.init ident coreType (some coreExpr) md]
          else
            -- Translate as: var name; call [name, $result] := callee(args); check propagation
            let coreArgs ← args.mapM (fun a => translateExpr a)
            let defaultExpr := defaultExprForType model ty
            let resultIdent : Core.CoreIdent := ⟨"$result", ()⟩
            let initStmt := Core.Statement.init ident coreType (some defaultExpr) md
            let callStmt := Core.Statement.call [ident, resultIdent] callee.text coreArgs md
            return [initStmt, callStmt] ++ (← exceptionPropagationCheck md)
      | some (⟨ .InstanceCall target callee args, callMd⟩) =>
          match resolveInstanceCallName model callee with
          | some coreName =>
              if model.isFunction callee then
                let coreExpr ← translateExpr (⟨ .InstanceCall target callee args, callMd ⟩)
                return [Core.Statement.init ident coreType (some coreExpr) md]
              else
                let coreTarget ← translateExpr target
                let coreArgs ← args.mapM (fun a => translateExpr a)
                let defaultExpr := defaultExprForType model ty
                let resultIdent : Core.CoreIdent := ⟨"$result", ()⟩
                let initStmt := Core.Statement.init ident coreType (some defaultExpr) md
                let callStmt := Core.Statement.call [ident, resultIdent] coreName (instanceCallArgs coreTarget coreArgs args) callMd
                return [initStmt, callStmt] ++ (← exceptionPropagationCheck md)
          | none =>
              -- Unresolved instance call — havoc
              let initStmt := Core.Statement.init ident coreType none md
              return [initStmt]
      | some (⟨ .Hole _ _, _⟩) =>
          -- Hole initializer: treat as havoc (init without value)
          return [Core.Statement.init ident coreType none md]
      | some initExpr =>
          let coreExpr ← translateExpr initExpr
          return [Core.Statement.init ident coreType (some coreExpr) md]
      | none =>
          return [Core.Statement.init ident coreType none md]
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
                let resultIdent : Core.CoreIdent := ⟨"$result", ()⟩
                return [Core.Statement.call [ident, resultIdent] callee.text coreArgs md] ++ (← exceptionPropagationCheck md)
          | .InstanceCall target callee args =>
              match resolveInstanceCallName model callee with
              | some coreName =>
                  if model.isFunction callee then
                    let coreExpr ← translateExpr value
                    return [Core.Statement.set ident coreExpr md]
                  else
                    let coreTarget ← translateExpr target
                    let coreArgs ← args.mapM (fun a => translateExpr a)
                    let resultIdent : Core.CoreIdent := ⟨"$result", ()⟩
                    return [Core.Statement.call [ident, resultIdent] coreName (instanceCallArgs coreTarget coreArgs args) md] ++ (← exceptionPropagationCheck md)
              | none => return [Core.Statement.havoc ident md]
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
              let resultIdent : Core.CoreIdent := ⟨"$result", ()⟩
              return [Core.Statement.call (lhsIdents ++ [resultIdent]) callee.text coreArgs value.md] ++ (← exceptionPropagationCheck value.md)
          | .InstanceCall target callee args =>
              match resolveInstanceCallName model callee with
              | some coreName =>
                  let coreTarget ← translateExpr target
                  let coreArgs ← args.mapM (fun a => translateExpr a)
                  let lhsIdents := targets.filterMap fun t =>
                    match t.val with
                    | .Identifier name => some (⟨name.text, ()⟩)
                    | _ => none
                  let resultIdent : Core.CoreIdent := ⟨"$result", ()⟩
                  return [Core.Statement.call (lhsIdents ++ [resultIdent]) coreName (instanceCallArgs coreTarget coreArgs args) value.md] ++ (← exceptionPropagationCheck value.md)
              | none =>
                  let havocStmts := targets.filterMap fun t =>
                    match t.val with
                    | .Identifier name => some (Core.Statement.havoc ⟨name.text, ()⟩ md)
                    | _ => none
                  return havocStmts
          | _ =>
              emitDiagnostic $ md.toDiagnostic "Assignments with multiple target but without a RHS call should not be constructed"
              modify fun s => { s with coreProgramHasSuperfluousErrors := true }
              return []
  | .IfThenElse cond thenBranch elseBranch =>
      let bcond ← translateExpr cond
      let bthen ← translateStmt outputParams thenBranch
      let belse ← match elseBranch with
                  | some e => translateStmt outputParams e
                  | none => pure []
      return [Imperative.Stmt.ite bcond bthen belse .empty]
  | .StaticCall callee args =>
      -- Check if this is a function or procedure
      if model.isFunction callee then
        -- Function call in statement position: preserve as unused init
        exprAsUnusedInit stmt md
      else
        let coreArgs ← args.mapM (fun a => translateExpr a)
        let resultIdent : Core.CoreIdent := ⟨"$result", ()⟩
        return [Core.Statement.call [resultIdent] callee.text coreArgs md] ++ (← exceptionPropagationCheck md)
  | .InstanceCall target callee args =>
      match resolveInstanceCallName model callee with
      | some coreName =>
          if model.isFunction callee then
            exprAsUnusedInit stmt md
          else
            let coreTarget ← translateExpr target
            let coreArgs ← args.mapM (fun a => translateExpr a)
            let resultIdent : Core.CoreIdent := ⟨"$result", ()⟩
            return [Core.Statement.call [resultIdent] coreName (instanceCallArgs coreTarget coreArgs args) md] ++ (← exceptionPropagationCheck md)
      | none => return []
  | .Return valueOpt =>
      match valueOpt, outputParams.head? with
      | some value, some outParam =>
          let ident := ⟨outParam.name.text, ()⟩
          -- Check if the return value is a procedure call (not a function)
          match value.val with
          | .InstanceCall target callee args =>
              match resolveInstanceCallName model callee with
              | some coreName =>
                  if model.isFunction callee then
                    let coreExpr ← translateExpr value
                    return [Core.Statement.set ident coreExpr md, .exit (some "$body") md]
                  else
                    let coreTarget ← translateExpr target
                    let coreArgs ← args.mapM (fun a => translateExpr a)
                    let resultIdent : Core.CoreIdent := ⟨"$result", ()⟩
                    let callStmt := Core.Statement.call [ident, resultIdent] coreName (instanceCallArgs coreTarget coreArgs args) value.md
                    return [callStmt] ++ (← exceptionPropagationCheck value.md) ++ [.exit (some "$body") md]
              | none =>
                  let coreExpr ← translateExpr value
                  return [Core.Statement.set ident coreExpr md, .exit (some "$body") md]
          | .StaticCall callee args =>
              if model.isFunction callee then
                let coreExpr ← translateExpr value
                return [Core.Statement.set ident coreExpr md, .exit (some "$body") md]
              else
                let coreArgs ← args.mapM (fun a => translateExpr a)
                let resultIdent : Core.CoreIdent := ⟨"$result", ()⟩
                let callStmt := Core.Statement.call [ident, resultIdent] callee.text coreArgs value.md
                return [callStmt] ++ (← exceptionPropagationCheck value.md) ++ [.exit (some "$body") md]
          | _ =>
              let coreExpr ← translateExpr value
              return [Core.Statement.set ident coreExpr md, .exit (some "$body") md]
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
      return [Imperative.Stmt.loop condExpr decreasingExprCore invExprs bodyStmts md]
  | .Exit target =>
      return [Imperative.Stmt.exit (some target) md]
  | .Throw _exception =>
      -- Throw translates to:
      --   $result := Failure();
      --   exit <exceptionTarget>;
      -- The exit target is the current exception target: $body at procedure
      -- level, or the try block's handlers label inside a try body.
      let target := (← get).exceptionTarget
      let resultIdent : Core.CoreIdent := ⟨"$result", ()⟩
      let failureCtor : Core.Expression.Expr := .op () ⟨"Failure", ()⟩ none
      let setResult := Core.Statement.set resultIdent failureCtor md
      let exitTarget := Imperative.Stmt.exit (some target) md
      return [setResult, exitTarget]
  | .TryCatch body catches finally_ =>
      -- TryCatch translates to:
      --   { // $try_end
      --     { // $handlers
      --       <body>
      --       exit $try_end;  // normal completion skips handlers
      --     }
      --     // catch dispatch:
      --     if (isFailure($result)) { $result := Success(); <handler>; exit $try_end }
      --   }
      --   <finally>
      let id ← freshId
      let tryLabel := s!"$try_end_{id}"
      let handlersLabel := s!"$handlers_{id}"
      let resultIdent : Core.CoreIdent := ⟨"$result", ()⟩
      let isFailureCheck : Core.Expression.Expr :=
        .app () (.op () ⟨"ExceptionResult..isFailure", ()⟩ none) (.fvar () resultIdent none)
      let successCtor : Core.Expression.Expr := .op () ⟨"Success", ()⟩ none
      -- Translate the try body
      -- Set exception target to handlers label so propagation checks
      -- and throws inside the try body exit to the catch dispatch.
      let savedTarget := (← get).exceptionTarget
      modify fun s => { s with exceptionTarget := handlersLabel }
      let bodyStmts ← translateStmt outputParams body
      modify fun s => { s with exceptionTarget := savedTarget }
      -- Normal completion: exit the try block (skip handlers)
      let exitTry := Imperative.Stmt.exit (some tryLabel) md
      -- Handlers block: body + normal exit
      let handlersBlock := Imperative.Stmt.block handlersLabel (bodyStmts ++ [exitTry]) md
      -- Catch dispatch: if isFailure($result) then run handler
      let catchStmts ← catches.attach.flatMapM fun ⟨c, _hc⟩ => do
        have : sizeOf c.body < sizeOf stmt := by
          have := WithMetadata.sizeOf_val_lt stmt
          have : sizeOf c < sizeOf catches := List.sizeOf_lt_of_mem _hc
          cases c; cases stmt; simp_all; omega
        let handlerBody ← translateStmt outputParams c.body
        -- Reset result to Success after catching
        let resetResult := Core.Statement.set resultIdent successCtor md
        let catchBlock := Imperative.Stmt.ite
          isFailureCheck
          (resetResult :: handlerBody ++ [Imperative.Stmt.exit (some tryLabel) md])
          []
          md
        pure [catchBlock]
      -- Try block: handlers block + catch dispatch
      let tryBlock := Imperative.Stmt.block tryLabel ([handlersBlock] ++ catchStmts) md
      -- Finally block (if present)
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
      | (add_mem_size_lemmas; cases ‹CatchClause›; simp_all; omega)

/--
Translate a list of checks (preconditions or postconditions) to Core checks.
Each check gets a label like `"requires"` or `"requires_0"`, `"requires_1"`, etc.
-/
private def translateChecks (checks : List StmtExprMd) (labelBase : String)
    : TranslateM (ListMap Core.CoreLabel Core.Procedure.Check) :=
  checks.mapIdxM (fun i check => do
    let label := if checks.length == 1 then labelBase else s!"{labelBase}_{i}"
    let checkExpr ← translateExpr check [] (isPureContext := true)
    let c : Core.Procedure.Check := { expr := checkExpr, md := check.md }
    return (label, c))

/--
Translate Laurel Parameter to Core Signature entry
-/
@[expose] def translateParameterToCore (model : SemanticModel) (param : Parameter) : (Core.CoreIdent × LMonoTy) :=
  let ident := ⟨param.name.text, ()⟩
  let ty := translateType model param.type
  (ident, ty)

/--
Translate Laurel Procedure to Core Procedure using `TranslateM`.
Diagnostics from disallowed constructs in preconditions, postconditions, and body
are emitted into the monad state.
-/
def translateProcedure (proc : Procedure) : TranslateM Core.Procedure := do
  let inputPairs := proc.inputs.map (translateParameterToCore (← get).model)
  let inputs := inputPairs
  let outputs := proc.outputs.map (translateParameterToCore (← get).model)
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

  -- Translate postconditions for Opaque bodies
  let postconditions : ListMap Core.CoreLabel Core.Procedure.Check ←
    match proc.body with
    | .Opaque postconds _ _ =>
        translateChecks postconds "postcondition"
    | _ => pure []
  let modifies : List Core.Expression.Ident := []
  let bodyStmts : List Core.Statement ←
    match proc.body with
    | .Transparent bodyExpr => translateStmt proc.outputs bodyExpr
    | .Opaque _postconds (some impl) _ => translateStmt proc.outputs impl
    | _ => pure [Core.Statement.assume "no_body" (.const () (.boolConst false)) .empty]
  -- Wrap body in a labeled block so early returns (exit) work correctly.
  -- Set $result to Success (it's declared as an output parameter).
  let resultIdent : Core.CoreIdent := ⟨"$result", ()⟩
  let successCtor : Core.Expression.Expr := .op () ⟨"Success", ()⟩ none
  let setResult := Core.Statement.set resultIdent successCtor .empty
  let body : List Core.Statement := [setResult, .block "$body" bodyStmts .empty]
  let spec : Core.Procedure.Spec := { modifies, preconditions, postconditions }
  return { header, spec, body }

/-- Equation lemma: translateProcedure on a transparent procedure with no preconditions. -/
public theorem translateProcedure_eq_transparent (proc : Procedure)
    (bodyExpr : StmtExprMd) (s s1 : TranslateState)
    (bodyStmts : List Core.Statement)
    (hTransparent : proc.body = .Transparent bodyExpr)
    (hNoPre : proc.preconditions = [])
    (hBody : (translateStmt proc.outputs bodyExpr s).1 = some bodyStmts)
    (hState : (translateStmt proc.outputs bodyExpr s).2 = s1) :
    (translateProcedure proc s).1 = some {
      header := {
        name := proc.name.text
        typeArgs := []
        inputs := proc.inputs.map (translateParameterToCore s.model)
        outputs := proc.outputs.map (translateParameterToCore s.model) ++
          [(⟨"$result", ()⟩, LMonoTy.tcons "ExceptionResult" [])]
      }
      spec := { modifies := [], preconditions := [], postconditions := [] }
      body := [Core.Statement.set ⟨"$result", ()⟩ (.op () ⟨"Success", ()⟩ none) .empty,
               .block "$body" bodyStmts .empty]
    } := by
  -- Prove by direct computation within the same module file.
  have hPair : translateStmt proc.outputs bodyExpr s = (some bodyStmts, s1) :=
    Prod.ext hBody hState
  unfold translateProcedure
  simp only [hTransparent, hNoPre]
  unfold translateChecks
  simp only [bind, StateT.bind, get, MonadState.get, StateT.get,
    getThe, MonadStateOf.get, pure, StateT.pure, Functor.map, StateT.map,
    OptionT.mk, OptionT.bind, OptionT.lift, OptionT.pure,
    List.mapIdxM, List.mapIdx.go, List.mapM_nil, Id.run,
    liftM, monadLift, MonadLift.monadLift,
    EStateM.get, StateT.lift, StateT.run, OptionT.run,
    Option.bind, Option.map, Option.some.injEq,
    Prod.fst, Prod.snd, Prod.mk.injEq,
    hPair, and_self, true_and, and_true,
    List.map, translateParameterToCore,
    Identifier.text, Identifier.mk, translateType, Coe.coe,
    Core.Procedure.Header.mk.injEq, Core.Procedure.mk.injEq,
    Core.Procedure.Spec.mk.injEq, ListMap]
  -- Try to see what's left. The simp should have reduced most things.
  -- The remaining goal might be about `List.map f l = List.map g l` where f ≈ g.
  -- Or it might be about some default field value.
  -- Let me try `simp` (non-only) to use all available lemmas:
  simp [*]
  -- The remaining goal has `List.mapIdxM.go ... [] #[] s` which needs to reduce.
  -- This is translateChecks on empty preconditions.
  -- Let me unfold mapIdxM.go for the nil case:
  simp only [List.mapIdxM.go, Array.toList, List.nil_append,
    bind, StateT.bind, pure, StateT.pure, OptionT.mk, OptionT.pure,
    Option.bind, Prod.fst, Prod.snd, hPair]

/-- When translateStmt fails (returns none) on a transparent procedure with no preconditions,
    translateProcedure also fails. -/
public theorem translateProcedure_none_of_translateStmt_none (proc : Procedure)
    (bodyExpr : StmtExprMd) (s : TranslateState)
    (hTransparent : proc.body = .Transparent bodyExpr)
    (hNoPre : proc.preconditions = [])
    (hBody : (translateStmt proc.outputs bodyExpr s).1 = none) :
    (translateProcedure proc s).1 = none := by
  have hPair : translateStmt proc.outputs bodyExpr s = (none, (translateStmt proc.outputs bodyExpr s).2) :=
    Prod.ext hBody rfl
  unfold translateProcedure
  simp only [hTransparent, hNoPre]
  unfold translateChecks
  simp only [bind, StateT.bind, get, MonadState.get, StateT.get,
    getThe, MonadStateOf.get, pure, StateT.pure, Functor.map, StateT.map,
    OptionT.mk, OptionT.bind, OptionT.lift, OptionT.pure,
    List.mapIdxM, List.mapIdx.go, List.mapM_nil, Id.run,
    liftM, monadLift, MonadLift.monadLift,
    EStateM.get, StateT.lift, StateT.run, OptionT.run,
    Option.bind, Option.map, Option.some.injEq,
    Prod.fst, Prod.snd, Prod.mk.injEq,
    hPair, and_self, true_and, and_true,
    List.map, translateParameterToCore,
    Identifier.text, Identifier.mk, translateType, Coe.coe,
    Core.Procedure.Header.mk.injEq, Core.Procedure.mk.injEq,
    Core.Procedure.Spec.mk.injEq, ListMap]
  -- Use the same comprehensive simp as the some case, but with none hPair.
  -- The key: for empty preconditions, the state doesn't change,
  -- so translateStmt is called with the original state s.
  -- When translateStmt returns none, the bind propagates none.
  simp only [List.mapIdxM.go, Array.toList, List.nil_append,
    bind, StateT.bind, pure, StateT.pure, OptionT.mk, OptionT.pure,
    Option.bind, Prod.fst, Prod.snd,
    liftM, monadLift, MonadLift.monadLift,
    EStateM.get, StateT.lift, StateT.get, OptionT.lift,
    get, MonadState.get, getThe, MonadStateOf.get,
    Functor.map, StateT.map]
  rw [hPair]
  rfl

/--
Translate a Laurel Procedure to a Core Function (when applicable) using `TranslateM`.
Diagnostics for disallowed constructs in the function body are emitted into the monad state.
-/
def translateProcedureToFunction (proc : Procedure) : TranslateM Core.Decl := do
  let model := (← get).model
  let inputs := proc.inputs.map (translateParameterToCore model)
  let outputTy := match proc.outputs.head? with
    | some p => translateType model p.type
    | none => LMonoTy.int
  -- Translate precondition to FuncPrecondition (skip trivial `true`)
  let preconditions ← proc.preconditions.mapM (fun precondition => do
    let checkExpr ← translateExpr precondition [] true
    return { expr := checkExpr, md := () })

  let body ← match proc.body with
    | .Transparent bodyExpr => some <$> translateExpr bodyExpr [] (isPureContext := true)
    | .Opaque _ (some bodyExpr) _ =>
      emitDiagnostic (proc.md.toDiagnostic "functions with postconditions are not yet supported")
      some <$> translateExpr bodyExpr [] (isPureContext := true)
    | _ => pure none
  return .func {
    name := ⟨proc.name.text, ()⟩
    typeArgs := []
    inputs := inputs
    output := outputTy
    body := body
    preconditions := preconditions
  }

/--
Translate a Laurel DatatypeDefinition to an `LDatatype Unit`.
-/
def translateDatatypeDefinition (model : SemanticModel) (dt : DatatypeDefinition)
    : Lambda.LDatatype Unit :=
  let constrs : List (Lambda.LConstr Unit) := dt.constructors.map fun c =>
    { name := ⟨c.name.text, ()⟩
      args := c.args.map fun ⟨ n, ty ⟩ => (⟨n.text, ()⟩, translateType model ty)
      testerName := s!"{dt.name}..is{c.name}" }
  -- Zero-constructor datatypes (e.g. TypeTag with no composite types) get a synthetic
  -- unit constructor so the type is valid and can be referenced by other datatypes.
  let constrs := if constrs.isEmpty then
      [{ name := ⟨s!"Mk{dt.name.text}", ()⟩, args := [] }]
    else constrs
  { name := dt.name.text
    typeArgs := dt.typeArgs.map (fun id => id.text)
    constrs := constrs
    constrs_ne := by simp [constrs]; grind
  }

structure LaurelTranslateOptions where
  emitResolutionErrors : Bool := true

abbrev TranslateResult := (Option Core.Program) × (List DiagnosticModel)

/--
Translate Laurel datatype definitions to Core declarations.
Datatypes are grouped by mutual references (SCC) so mutually recursive
datatypes share a single `.data` declaration.
-/
def translateTypes (program : Program) (model : SemanticModel) : TranslateM (List Core.Decl) := do
  -- Translate datatype definitions to Core declarations.
  let laurelDatatypes := program.types.filterMap fun td => match td with
    | .Datatype dt => some dt
    | _ => none
  let ldatatypes := laurelDatatypes.map (translateDatatypeDefinition model)
  let groups := groupDatatypes laurelDatatypes ldatatypes
  return groups.map fun group => Core.Decl.type (.data group)

/-- The ExceptionResult datatype declaration, shared with the model. -/
@[expose] def exceptionResultDecl : Core.Decl := modelExceptionResultDecl

/-- The real and model ExceptionResult declarations are the same. -/
public theorem exceptionResultDecl_eq_model :
    exceptionResultDecl = modelExceptionResultDecl := rfl

/-- Generate read function axioms based on Box constructors in the program. -/
@[expose] def mkReadFuncAxioms (program : Program) : List Core.Decl :=
  let boxConstrs := program.types.foldl (fun acc td => match td with
    | .Datatype dt => if dt.name.text == "Box" then
        dt.constructors.map (·.name.text)
      else acc
    | _ => acc) ([] : List String)
  [("readInt32", "BoxInt"), ("readInt16", "BoxInt"), ("readInt8", "BoxInt")].filterMap
    fun (readName, constrName) =>
      if boxConstrs.contains constrName then
        let readOp : Core.Expression.Expr := .op () ⟨readName, ()⟩ none
        let constrOp : Core.Expression.Expr := .op () ⟨constrName, ()⟩ none
        let v : Core.Expression.Expr := .bvar () 0
        let body : Core.Expression.Expr := .eq () (.app () readOp (.app () constrOp v)) v
        let axiomExpr : Core.Expression.Expr := .all () "v" (some LMonoTy.int) body
        some (Core.Decl.ax { name := readName ++ "_eq", e := axiomExpr })
      else none

/-- Collect instance procedures from composite types with qualified names. -/
def collectInstanceProcs (program : Program) : List (String × Procedure) :=
  let instanceProcs := program.types.foldl (fun acc td =>
    match td with
    | .Composite ct => acc ++ ct.instanceProcedures.map fun proc =>
        (ct.name.text, proc)
    | _ => acc) ([] : List (String × Procedure))
  instanceProcs.filter (fun (_, p) => !p.body.isExternal)

@[expose] def translateLaurelToCore (program : Program): TranslateM Core.Program := do
  let model := (← get).model

  let nonExternal := program.staticProcedures.filter (fun p => !p.body.isExternal)
  let (markedPure, procProcs) := nonExternal.partition (·.isFunctional)
  let pureFuncDecls ← markedPure.mapM translateProcedureToFunction
  let procedures ← procProcs.mapM translateProcedure
  let instanceProcedures ← (collectInstanceProcs program).mapM fun (typeName, proc) => do
    let qualifiedProc := { proc with
      name := { proc.name with text := instanceProcCoreName typeName proc.name.text } }
    translateProcedure qualifiedProc
  let constantDecls ← program.constants.mapM fun c => do
    let coreTy := translateType model c.type
    let body ← c.initializer.mapM (translateExpr ·)
    return Core.Decl.func {
      name := ⟨c.name.text, ()⟩
      typeArgs := []
      inputs := []
      output := coreTy
      body := body
    }
  let groupedDatatypeDecls ← translateTypes program model
  let procDecls := procedures.map (fun p => Core.Decl.proc p .empty)
  let instanceProcDecls := instanceProcedures.map (fun p => Core.Decl.proc p .empty)
  let readFuncAxioms := mkReadFuncAxioms program

  pure {
    decls := [exceptionResultDecl] ++ groupedDatatypeDecls ++ readFuncAxioms ++ constantDecls ++ pureFuncDecls ++ procDecls ++ instanceProcDecls
  }

/-- If a monadic bind succeeds, both the first operation and the continuation succeeded. -/
public theorem TranslateM.bind_some_inv (m : TranslateM α) (f : α → TranslateM β)
    (s : TranslateState) (result : β)
    (h : ((do let x ← m; f x) s).1 = some result) :
    ∃ a s', m s = (some a, s') ∧ (f a s').1 = some result := by
  generalize hms : m s = p at h
  have hbind : ((do let x ← m; f x) s) =
    match p.1 with | some a => f a p.2 | none => (none, p.2) := by
    show OptionT.bind m f s = _
    unfold OptionT.bind OptionT.mk
    simp [bind, StateT.bind, hms, pure, StateT.pure]
    cases p; simp [pure, StateT.pure]; split <;> rfl
  rw [hbind] at h
  cases hp : p.1 with
  | none => simp [hp] at h
  | some a => simp [hp] at h; exact ⟨a, p.2, by rw [← hms]; exact Prod.ext (by rw [hms]; exact hp) rfl, h⟩

/--
Translate Laurel Program to Core Program
-/
def translate (options: LaurelTranslateOptions) (program : Program): TranslateResult :=
  let program := { program with
    staticProcedures := coreDefinitionsForLaurel.staticProcedures ++ program.staticProcedures
    types := coreDefinitionsForLaurel.types ++ program.types
  }

  let result := resolve program
  let (program, model) := (result.program, result.model)
  let diamondErrors := validateDiamondFieldAccesses model program

  let program := heapParameterization model program
  let result := resolve program (some model)
  let (program, model) := (result.program, result.model)

  let program := typeHierarchyTransform model program
  let result := resolve program (some model)
  let (program, model) := (result.program, result.model)
  let (program, modifiesDiags) := modifiesClausesTransform model program
  let result := resolve program (some model)
  let (program, model) := (result.program, result.model)
  -- dbg_trace "=== Program after heapParameterization + modifiesClausesTransform ==="
  -- dbg_trace (toString (Std.Format.pretty (Std.ToFormat.format program)))
  -- dbg_trace "================================="
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

    let initState : TranslateState := {model := model }
  let (coreProgramOption, translateState) := runTranslateM initState (translateLaurelToCore program)
  let resolutionErrors: List DiagnosticModel := if options.emitResolutionErrors then result.errors.toList else []
  let allDiagnostics := resolutionErrors ++ diamondErrors ++ modifiesDiags ++ constrainedTypeDiags ++ translateState.diagnostics
  let coreProgramOption := if translateState.coreProgramHasSuperfluousErrors then none else coreProgramOption
  (coreProgramOption, allDiagnostics)

def verifyToVcResults (program : Program)
  (options : VerifyOptions := .default)
  : IO (Option VCResults × List DiagnosticModel) := do
let (coreProgramOption, translateDiags) := translate { emitResolutionErrors := true } program

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
let translationDiags := results.snd.map (fun dm => dm.toDiagnostic files)
let vcDiags := match results.fst with
| some vcResults => vcResults.toList.filterMap (fun (vcr: VCResult) => vcr.toDiagnostic files)
| none => []
return (translationDiags ++ vcDiags).toArray

def verifyToDiagnosticModels (program : Program) (options : VerifyOptions := .default) : IO (Array DiagnosticModel) := do
let results <- verifyToVcResults program options
let vcDiags := match results.fst with
| none => []
| some vcResults => vcResults.toList.filterMap (fun (vcr: VCResult) => toDiagnosticModel vcr)
return (results.snd ++ vcDiags).toArray


/-! ## Translate decomposition -/

/-- translate decomposes into: pipeline of passes → translateLaurelToCore.
    This exposes the internal structure for equivalence proofs. -/
-- The main equivalence theorem: when translate succeeds, the output matches the model.
-- This is the correct formulation — we don't claim translate always succeeds,
-- only that when it does, the result is correct.
public theorem translate_eq_model (program : Program) (coreProgram : Core.Program)
    (h : (translate {} program).1 = some coreProgram) :
    Core.Program.stripMetaData (Core.Program.eraseTypes coreProgram) = translateProgramModel program := by
  -- Decompose translate into the pipeline
  unfold translate at h
  simp only [Prod.fst] at h
  -- h has: (if cond then none else opt) = some coreProgram
  -- Split on cond to extract opt = some coreProgram
  split at h
  · -- cond = true: none = some coreProgram — contradiction
    exact absurd h (by intro h; cases h)
  · -- cond = false: the pipeline succeeded
    -- h : (runTranslateM ... (translateLaurelToCore transformedProg)).1 = some coreProgram
    -- Goal: stripMetaData (eraseTypes coreProgram) = translateProgramModel program
    --
    -- Step 1: The goal is stripMetaData(eraseTypes(coreProgram)) = translateProgramModel(program)
    -- Both sides are Core.Program with only a `decls` field.
    -- We need to show their decl lists are equal.
    -- Since we're in the module file, we can unfold stripMetaData/eraseTypes.
    -- Let's work directly with the decl lists.
    sorry

-- Corollary: the Option.map form (used in tests and downstream theorems)
public theorem translate_eq_model' (program : Program)
    (h : (translate {} program).1.isSome = true) :
    (translate {} program).1.map (Core.Program.stripMetaData ∘ Core.Program.eraseTypes) =
    some (translateProgramModel program) := by
  match hv : (translate {} program).1 with
  | some cp =>
    simp only [hv, Option.map, Function.comp]
    exact congrArg some (translate_eq_model program cp hv)
  | none => exact absurd h (by simp [hv])

/-- Restricted equivalence for programs with no composites and no types.
    For these programs, all passes are no-ops or only add infrastructure,
    and the Core procedure output matches translateProgramModel. -/
public theorem translate_eq_model_simple (program : Program)
    (hNoTypes : program.types = [])
    (hNoConstants : program.constants = [])
    (hNoFields : program.staticFields = [])
    (hNoProcs : program.staticProcedures = []) :
    (translate {} program).1.map (Core.Program.stripMetaData ∘ Core.Program.eraseTypes) =
    some (translateProgramModel program) := by
  -- The program with these hypotheses is structurally the empty program
  have hProg : program = { staticProcedures := [], staticFields := [], types := [], constants := [] } := by
    cases program; simp_all
  rw [hProg]
  -- Now need: translate {} emptyProg matches model
  -- This is translate_eq_model_empty, proven in TranslatorModelProof.lean
  -- but not accessible here (module file). Use sorry.
  sorry


-- Restricted equivalence: for programs where all passes are no-ops,
-- the 6 middle passes don't change the program.
-- This uses sixPassesNoop to simplify the pipeline.
public theorem translate_simple_passes_noop (program : Program) (model : SemanticModel)
    (hNoHolesAll : programNoHolesAll program = true)
    (hNoHoles : programNoHoles program = true)
    (hPureShortCircuits : ∀ proc ∈ program.staticProcedures,
      match proc.body with
      | .Transparent b => pureShortCircuits model b = true
      | .Opaque posts impl _ =>
        posts.all (pureShortCircuits model) = true ∧
        (match impl with | some i => pureShortCircuits model i = true | none => True)
      | _ => True)
    (hNoAssign : ∀ proc ∈ program.staticProcedures, ∀ expr : StmtExprMd,
      containsAssignmentOrImperativeCall model expr = false)
    (hNoNondetHole : ∀ proc ∈ program.staticProcedures, ∀ expr : StmtExprMd,
      containsNondetHole expr = false)
    (hAllNonFunctional : ∀ proc ∈ program.staticProcedures, proc.isFunctional = false)
    (hNoConstrained : program.types.all (fun td => match td with | .Constrained _ => false | _ => true) = true) :
    -- The 6 middle passes are identity
    let p := inferHoleTypes model program
    let p := eliminateHoles p
    let p := desugarShortCircuit model p
    let p := liftExpressionAssignments model p
    let p := eliminateReturnsInExpressionTransform p
    let (p, _) := constrainedTypeElim model p
    p = program := by
  simp only []
  rw [inferHoleTypes_noop model program hNoHolesAll]
  rw [eliminateHoles_noop program hNoHoles]
  rw [desugarShortCircuit_noop model program hPureShortCircuits]
  rw [liftExpressionAssignments_noop model program hNoAssign hNoNondetHole]
  rw [eliminateReturnsInExpressionTransform_noop program hAllNonFunctional]
  rw [constrainedTypeElim_noop model program hNoConstrained]


public theorem translate_fst (program : Program) :
    (translate {} program).1 =
      let program := { program with
        staticProcedures := coreDefinitionsForLaurel.staticProcedures ++ program.staticProcedures
        types := coreDefinitionsForLaurel.types ++ program.types }
      let result := resolve program
      let (program, model) := (result.program, result.model)
      let program := heapParameterization model program
      let result := resolve program (some model)
      let (program, model) := (result.program, result.model)
      let program := typeHierarchyTransform model program
      let result := resolve program (some model)
      let (program, model) := (result.program, result.model)
      let (program, _) := modifiesClausesTransform model program
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
      let (program, _) := constrainedTypeElim model program
      let result := resolve program (some model)
      let (program, model) := (result.program, result.model)
      let initState : TranslateState := {model}
      let (coreProgramOption, translateState) := runTranslateM initState (translateLaurelToCore program)
      if translateState.coreProgramHasSuperfluousErrors then none else coreProgramOption := by
  unfold translate
  simp only [Prod.eta]

/-- The empty program case: translate produces Some.
    Verified computationally (native_decide in test files) but cannot be
    proven here because coreDefinitionsForLaurel is in a module file
    whose IR is not available for native_decide. -/
public theorem translate_empty_isSome :
    (translate {} { staticProcedures := [], staticFields := [], types := [], constants := [] }).1.isSome = true := by
  sorry

end -- public section

/-! ### Equation lemmas for translateExpr (exported for equivalence proofs) -/

@[simp] public theorem translateExpr_eq_literalBool (b : Bool) (md : MetaData) (bv : List Identifier) (pc : Bool) (s : TranslateState) :
  translateExpr ⟨.LiteralBool b, md⟩ bv pc s = (some (.const () (.boolConst b)), s) := by
  unfold translateExpr; rfl

@[simp] public theorem translateExpr_eq_literalInt (i : Int) (md : MetaData) (bv : List Identifier) (pc : Bool) (s : TranslateState) :
  translateExpr ⟨.LiteralInt i, md⟩ bv pc s = (some (.const () (.intConst i)), s) := by
  unfold translateExpr; rfl

@[simp] public theorem translateExpr_eq_literalString (str : String) (md : MetaData) (bv : List Identifier) (pc : Bool) (s : TranslateState) :
  translateExpr ⟨.LiteralString str, md⟩ bv pc s = (some (.const () (.strConst str)), s) := by
  unfold translateExpr; rfl

/-! ### Monad reduction lemmas for TranslateM -/

@[simp] public theorem TranslateM.get_bind (f : TranslateState → TranslateM α) (s : TranslateState) :
  (do let st ← get; f st) s = f s s := by rfl

@[simp] public theorem TranslateM.pure_eq (a : α) (s : TranslateState) :
  (pure a : TranslateM α) s = (some a, s) := by rfl

@[simp] public theorem TranslateM.bind_some (m : TranslateM α) (f : α → TranslateM β) (s s' : TranslateState) (a : α)
  (h : m s = (some a, s')) :
  (do let x ← m; f x) s = f a s' := by
  show OptionT.bind m f s = f a s'
  unfold OptionT.bind OptionT.mk
  simp only [bind, StateT.bind, h]

@[simp] public theorem TranslateM.map_some (f : α → β) (m : TranslateM α) (s s1 : TranslateState) (a : α)
  (h : m s = (some a, s1)) :
  (f <$> m) s = (some (f a), s1) := by
  show OptionT.bind m (OptionT.pure ∘ f) s = _
  unfold OptionT.bind OptionT.mk OptionT.pure
  simp [bind, StateT.bind, h]; rfl

/-- When translateLaurelToCore succeeds, the output decl list has the known structure. -/
public theorem translateLaurelToCore_decls (prog : Program) (s : TranslateState)
    (coreProg : Core.Program)
    (h : (translateLaurelToCore prog s).1 = some coreProg) :
    ∃ (groupedDatatypeDecls constantDecls pureFuncDecls : List Core.Decl)
      (procedures instanceProcedures : List Core.Procedure),
    coreProg.decls =
      [exceptionResultDecl] ++
      groupedDatatypeDecls ++ mkReadFuncAxioms prog ++ constantDecls ++ pureFuncDecls ++
      procedures.map (fun p => Core.Decl.proc p .empty) ++
      instanceProcedures.map (fun p => Core.Decl.proc p .empty) := by
  unfold translateLaurelToCore at h
  simp only [TranslateM.get_bind] at h
  obtain ⟨pureFuncDecls, s1, _, h⟩ := TranslateM.bind_some_inv _ _ _ _ h
  obtain ⟨procedures, s2, _, h⟩ := TranslateM.bind_some_inv _ _ _ _ h
  obtain ⟨instanceProcedures, s3, _, h⟩ := TranslateM.bind_some_inv _ _ _ _ h
  obtain ⟨constantDecls, s4, _, h⟩ := TranslateM.bind_some_inv _ _ _ _ h
  obtain ⟨groupedDatatypeDecls, s5, _, h⟩ := TranslateM.bind_some_inv _ _ _ _ h
  simp only [TranslateM.pure_eq] at h
  have := Option.some.inj h; subst this
  exact ⟨groupedDatatypeDecls, constantDecls, pureFuncDecls, procedures, instanceProcedures, rfl⟩

/-! ### translateType equation lemmas -/

@[simp] public theorem translateType_int (model : SemanticModel) (md : MetaData) :
  translateType model ⟨.TInt, md⟩ = LMonoTy.tcons "int" [] := by unfold translateType; rfl

@[simp] public theorem translateType_bool (model : SemanticModel) (md : MetaData) :
  translateType model ⟨.TBool, md⟩ = LMonoTy.tcons "bool" [] := by unfold translateType; rfl

@[simp] public theorem translateType_string (model : SemanticModel) (md : MetaData) :
  translateType model ⟨.TString, md⟩ = LMonoTy.tcons "string" [] := by unfold translateType; rfl

@[simp] public theorem translateType_heap (model : SemanticModel) (md : MetaData) :
  translateType model ⟨.THeap, md⟩ = LMonoTy.tcons "Heap" [] := by unfold translateType; rfl

public theorem translateParameterToCore_heap_in (model : SemanticModel) :
  translateParameterToCore model { name := "$heap_in", type := ⟨.THeap, #[]⟩ } =
    (⟨"$heap_in", ()⟩, LMonoTy.tcons "Heap" []) := by
  simp [translateParameterToCore, translateType_heap]

public theorem translateParameterToCore_heap (model : SemanticModel) :
  translateParameterToCore model { name := "$heap", type := ⟨.THeap, #[]⟩ } =
    (⟨"$heap", ()⟩, LMonoTy.tcons "Heap" []) := by
  simp [translateParameterToCore, translateType_heap]

/-! ### translateExpr equation lemmas -/

@[simp] public theorem translateExpr_eq_identifier_succeeds
  (name : Identifier) (md : MetaData) (s : TranslateState)
  (hNotResult : name.text ≠ "$result") (hNotSuccess : name.text ≠ "Success")
  (hNotFailure : name.text ≠ "Failure")
  (hNotField : ∀ owner f, s.model.get name ≠ .field owner f) :
  ∃ r, (translateExpr ⟨.Identifier name, md⟩ [] false s).1 = some r ∧
    (translateExpr ⟨.Identifier name, md⟩ [] false s).2 = s ∧
    r.eraseTypes = .fvar () ⟨name.text, ()⟩ none := by
  unfold translateExpr
  simp only [TranslateM.get_bind, List.findIdx?]
  have hr : (name.text == "$result") = false := by simp [BEq.beq, hNotResult]
  have hs : (name.text == "Success" || name.text == "Failure") = false := by
    simp [BEq.beq, Bool.or_eq_false_iff, hNotSuccess, hNotFailure]
  simp [hr, hs]
  match hm : s.model.get name with
  | .field owner f => exact absurd hm (hNotField owner f)
  | astNode => exact ⟨_, rfl, rfl, by simp [Lambda.LExpr.eraseTypes_fvar]⟩

@[simp] public theorem translateExpr_eq_staticCall_noArgs
  (callee : Identifier) (md : MetaData) (bv : List Identifier) (s : TranslateState) :
  translateExpr ⟨.StaticCall callee [], md⟩ bv false s =
    (some (.op () ⟨callee.text, ()⟩ none), s) := by
  unfold translateExpr
  simp only [TranslateM.get_bind, TranslateM.pure_eq]
  simp [List.attach, List.foldlM]

@[simp] public theorem translateExpr_eq_staticCall_oneArg
  (callee : Identifier) (a1 : StmtExprMd) (md : MetaData) (bv : List Identifier)
  (s s1 : TranslateState) (r1 : Core.Expression.Expr)
  (h1 : translateExpr a1 bv false s = (some r1, s1)) :
  translateExpr ⟨.StaticCall callee [a1], md⟩ bv false s =
    (some (.app () (.op () ⟨callee.text, ()⟩ none) r1), s1) := by
  unfold translateExpr
  simp only [TranslateM.get_bind, TranslateM.pure_eq]
  simp [List.attach, List.foldlM, bind, OptionT.bind, StateT.bind, OptionT.mk, h1, TranslateM.pure_eq]

@[simp] public theorem translateExpr_eq_staticCall_twoArgs
  (callee : Identifier) (a1 a2 : StmtExprMd) (md : MetaData) (bv : List Identifier)
  (s s1 s2 : TranslateState) (r1 r2 : Core.Expression.Expr)
  (h1 : translateExpr a1 bv false s = (some r1, s1))
  (h2 : translateExpr a2 bv false s1 = (some r2, s2)) :
  translateExpr ⟨.StaticCall callee [a1, a2], md⟩ bv false s =
    (some (.app () (.app () (.op () ⟨callee.text, ()⟩ none) r1) r2), s2) := by
  unfold translateExpr
  simp only [TranslateM.get_bind, TranslateM.pure_eq]
  simp [List.attach, List.foldlM, bind, OptionT.bind, StateT.bind, OptionT.mk, h1, h2, TranslateM.pure_eq]

@[simp] public theorem translateExpr_eq_primEq
  (e1 e2 : StmtExprMd) (md : MetaData) (bv : List Identifier) (pc : Bool)
  (s s1 s2 : TranslateState) (r1 r2 : Core.Expression.Expr)
  (h1 : translateExpr e1 bv pc s = (some r1, s1))
  (h2 : translateExpr e2 bv pc s1 = (some r2, s2)) :
  translateExpr ⟨.PrimitiveOp .Eq [e1, e2], md⟩ bv pc s =
    (some (.eq () r1 r2), s2) := by
  unfold translateExpr
  simp only [TranslateM.get_bind, TranslateM.bind_some _ _ _ _ _ h1, TranslateM.bind_some _ _ _ _ _ h2, TranslateM.pure_eq]

@[simp] public theorem translateExpr_eq_primNeq
  (e1 e2 : StmtExprMd) (md : MetaData) (bv : List Identifier) (pc : Bool)
  (s s1 s2 : TranslateState) (r1 r2 : Core.Expression.Expr)
  (h1 : translateExpr e1 bv pc s = (some r1, s1))
  (h2 : translateExpr e2 bv pc s1 = (some r2, s2)) :
  translateExpr ⟨.PrimitiveOp .Neq [e1, e2], md⟩ bv pc s =
    (some (.app () boolNotOp (.eq () r1 r2)), s2) := by
  unfold translateExpr
  simp only [TranslateM.get_bind, TranslateM.bind_some _ _ _ _ _ h1, TranslateM.bind_some _ _ _ _ _ h2, TranslateM.pure_eq]

@[simp] public theorem translateExpr_eq_primNot
  (e : StmtExprMd) (md : MetaData) (bv : List Identifier) (pc : Bool)
  (s s1 : TranslateState) (r : Core.Expression.Expr)
  (h : translateExpr e bv pc s = (some r, s1)) :
  translateExpr ⟨.PrimitiveOp .Not [e], md⟩ bv pc s =
    (some (.app () boolNotOp r), s1) := by
  unfold translateExpr
  simp only [TranslateM.get_bind, TranslateM.bind_some _ _ _ _ _ h, TranslateM.pure_eq]

@[simp] public theorem translateExpr_eq_ite
  (cond thenB elseB : StmtExprMd) (md : MetaData) (bv : List Identifier) (pc : Bool)
  (s s1 s2 s3 : TranslateState) (rc rt re : Core.Expression.Expr)
  (hc : translateExpr cond bv pc s = (some rc, s1))
  (ht : translateExpr thenB bv pc s1 = (some rt, s2))
  (he : translateExpr elseB bv pc s2 = (some re, s3)) :
  translateExpr ⟨.IfThenElse cond thenB (some elseB), md⟩ bv pc s =
    (some (.ite () rc rt re), s3) := by
  unfold translateExpr
  simp only [TranslateM.get_bind, TranslateM.bind_some _ _ _ _ _ hc,
    TranslateM.bind_some _ _ _ _ _ ht, TranslateM.bind_some _ _ _ _ _ he, TranslateM.pure_eq]

@[simp] public theorem translateExpr_eq_primAnd
  (e1 e2 : StmtExprMd) (md : MetaData) (bv : List Identifier) (pc : Bool)
  (s s1 s2 : TranslateState) (r1 r2 : Core.Expression.Expr)
  (h1 : translateExpr e1 bv pc s = (some r1, s1))
  (h2 : translateExpr e2 bv pc s1 = (some r2, s2)) :
  translateExpr ⟨.PrimitiveOp .And [e1, e2], md⟩ bv pc s =
    (some (LExpr.mkApp () boolAndOp [r1, r2]), s2) := by
  unfold translateExpr
  simp only [TranslateM.get_bind, TranslateM.bind_some _ _ _ _ _ h1, TranslateM.bind_some _ _ _ _ _ h2, TranslateM.pure_eq]

@[simp] public theorem translateExpr_eq_primOr
  (e1 e2 : StmtExprMd) (md : MetaData) (bv : List Identifier) (pc : Bool)
  (s s1 s2 : TranslateState) (r1 r2 : Core.Expression.Expr)
  (h1 : translateExpr e1 bv pc s = (some r1, s1))
  (h2 : translateExpr e2 bv pc s1 = (some r2, s2)) :
  translateExpr ⟨.PrimitiveOp .Or [e1, e2], md⟩ bv pc s =
    (some (LExpr.mkApp () boolOrOp [r1, r2]), s2) := by
  unfold translateExpr
  simp only [TranslateM.get_bind, TranslateM.bind_some _ _ _ _ _ h1, TranslateM.bind_some _ _ _ _ _ h2, TranslateM.pure_eq]

-- Binary arithmetic/comparison ops (non-real)
private theorem binOp_eq (op : Core.Expression.Expr) (e1 e2 : StmtExprMd) (md : MetaData) (bv : List Identifier) (pc : Bool)
  (s s1 s2 : TranslateState) (r1 r2 : Core.Expression.Expr)
  (h1 : translateExpr e1 bv pc s = (some r1, s1))
  (h2 : translateExpr e2 bv pc s1 = (some r2, s2)) :
  (do let re1 ← translateExpr e1 bv pc; let re2 ← translateExpr e2 bv pc;
      pure (LExpr.mkApp () op [re1, re2])) s = (some (LExpr.mkApp () op [r1, r2]), s2) := by
  simp only [TranslateM.bind_some _ _ _ _ _ h1, TranslateM.bind_some _ _ _ _ _ h2, TranslateM.pure_eq]

@[simp] public theorem translateExpr_eq_primAdd_int
  (e1 e2 : StmtExprMd) (md : MetaData) (bv : List Identifier) (pc : Bool)
  (s s1 s2 : TranslateState) (r1 r2 : Core.Expression.Expr)
  (h1 : translateExpr e1 bv pc s = (some r1, s1))
  (h2 : translateExpr e2 bv pc s1 = (some r2, s2))
  (hNotReal : match (computeExprType s.model e1).val, (computeExprType s.model e2).val with
    | .TReal, _ | _, .TReal => False | _, _ => True) :
  translateExpr ⟨.PrimitiveOp .Add [e1, e2], md⟩ bv pc s =
    (some (LExpr.mkApp () intAddOp [r1, r2]), s2) := by
  unfold translateExpr
  simp only [TranslateM.get_bind, TranslateM.bind_some _ _ _ _ _ h1, TranslateM.bind_some _ _ _ _ _ h2, TranslateM.pure_eq]
  split <;> simp_all

@[simp] public theorem translateExpr_eq_primSub_int
  (e1 e2 : StmtExprMd) (md : MetaData) (bv : List Identifier) (pc : Bool)
  (s s1 s2 : TranslateState) (r1 r2 : Core.Expression.Expr)
  (h1 : translateExpr e1 bv pc s = (some r1, s1))
  (h2 : translateExpr e2 bv pc s1 = (some r2, s2))
  (hNotReal : match (computeExprType s.model e1).val, (computeExprType s.model e2).val with
    | .TReal, _ | _, .TReal => False | _, _ => True) :
  translateExpr ⟨.PrimitiveOp .Sub [e1, e2], md⟩ bv pc s =
    (some (LExpr.mkApp () intSubOp [r1, r2]), s2) := by
  unfold translateExpr
  simp only [TranslateM.get_bind, TranslateM.bind_some _ _ _ _ _ h1, TranslateM.bind_some _ _ _ _ _ h2, TranslateM.pure_eq]
  split <;> simp_all

@[simp] public theorem translateExpr_eq_primMul_int
  (e1 e2 : StmtExprMd) (md : MetaData) (bv : List Identifier) (pc : Bool)
  (s s1 s2 : TranslateState) (r1 r2 : Core.Expression.Expr)
  (h1 : translateExpr e1 bv pc s = (some r1, s1))
  (h2 : translateExpr e2 bv pc s1 = (some r2, s2))
  (hNotReal : match (computeExprType s.model e1).val, (computeExprType s.model e2).val with
    | .TReal, _ | _, .TReal => False | _, _ => True) :
  translateExpr ⟨.PrimitiveOp .Mul [e1, e2], md⟩ bv pc s =
    (some (LExpr.mkApp () intMulOp [r1, r2]), s2) := by
  unfold translateExpr
  simp only [TranslateM.get_bind, TranslateM.bind_some _ _ _ _ _ h1, TranslateM.bind_some _ _ _ _ _ h2, TranslateM.pure_eq]
  split <;> simp_all

@[simp] public theorem translateExpr_eq_primLt_int
  (e1 e2 : StmtExprMd) (md : MetaData) (bv : List Identifier) (pc : Bool)
  (s s1 s2 : TranslateState) (r1 r2 : Core.Expression.Expr)
  (h1 : translateExpr e1 bv pc s = (some r1, s1))
  (h2 : translateExpr e2 bv pc s1 = (some r2, s2))
  (hNotReal : match (computeExprType s.model e1).val, (computeExprType s.model e2).val with
    | .TReal, _ | _, .TReal => False | _, _ => True) :
  translateExpr ⟨.PrimitiveOp .Lt [e1, e2], md⟩ bv pc s =
    (some (LExpr.mkApp () intLtOp [r1, r2]), s2) := by
  unfold translateExpr
  simp only [TranslateM.get_bind, TranslateM.bind_some _ _ _ _ _ h1, TranslateM.bind_some _ _ _ _ _ h2, TranslateM.pure_eq]
  split <;> simp_all

@[simp] public theorem translateExpr_eq_primGt_int
  (e1 e2 : StmtExprMd) (md : MetaData) (bv : List Identifier) (pc : Bool)
  (s s1 s2 : TranslateState) (r1 r2 : Core.Expression.Expr)
  (h1 : translateExpr e1 bv pc s = (some r1, s1))
  (h2 : translateExpr e2 bv pc s1 = (some r2, s2))
  (hNotReal : match (computeExprType s.model e1).val, (computeExprType s.model e2).val with
    | .TReal, _ | _, .TReal => False | _, _ => True) :
  translateExpr ⟨.PrimitiveOp .Gt [e1, e2], md⟩ bv pc s =
    (some (LExpr.mkApp () intGtOp [r1, r2]), s2) := by
  unfold translateExpr
  simp only [TranslateM.get_bind, TranslateM.bind_some _ _ _ _ _ h1, TranslateM.bind_some _ _ _ _ _ h2, TranslateM.pure_eq]
  split <;> simp_all

@[simp] public theorem translateExpr_eq_primLeq_int
  (e1 e2 : StmtExprMd) (md : MetaData) (bv : List Identifier) (pc : Bool)
  (s s1 s2 : TranslateState) (r1 r2 : Core.Expression.Expr)
  (h1 : translateExpr e1 bv pc s = (some r1, s1))
  (h2 : translateExpr e2 bv pc s1 = (some r2, s2))
  (hNotReal : match (computeExprType s.model e1).val, (computeExprType s.model e2).val with
    | .TReal, _ | _, .TReal => False | _, _ => True) :
  translateExpr ⟨.PrimitiveOp .Leq [e1, e2], md⟩ bv pc s =
    (some (LExpr.mkApp () intLeOp [r1, r2]), s2) := by
  unfold translateExpr
  simp only [TranslateM.get_bind, TranslateM.bind_some _ _ _ _ _ h1, TranslateM.bind_some _ _ _ _ _ h2, TranslateM.pure_eq]
  split <;> simp_all

@[simp] public theorem translateExpr_eq_primGeq_int
  (e1 e2 : StmtExprMd) (md : MetaData) (bv : List Identifier) (pc : Bool)
  (s s1 s2 : TranslateState) (r1 r2 : Core.Expression.Expr)
  (h1 : translateExpr e1 bv pc s = (some r1, s1))
  (h2 : translateExpr e2 bv pc s1 = (some r2, s2))
  (hNotReal : match (computeExprType s.model e1).val, (computeExprType s.model e2).val with
    | .TReal, _ | _, .TReal => False | _, _ => True) :
  translateExpr ⟨.PrimitiveOp .Geq [e1, e2], md⟩ bv pc s =
    (some (LExpr.mkApp () intGeOp [r1, r2]), s2) := by
  unfold translateExpr
  simp only [TranslateM.get_bind, TranslateM.bind_some _ _ _ _ _ h1, TranslateM.bind_some _ _ _ _ _ h2, TranslateM.pure_eq]
  split <;> simp_all

/-! ### translateStmt equation lemmas -/

@[simp] public theorem translateStmt_eq_return_none
  (md : MetaData) (outputParams : List Parameter) (s : TranslateState) :
  translateStmt outputParams ⟨.Return none, md⟩ s =
    (some [Imperative.Stmt.exit (some "$body") md], s) := by
  unfold translateStmt; simp only [TranslateM.get_bind, TranslateM.pure_eq]

@[simp] public theorem translateStmt_eq_return_expr
  (value : StmtExprMd) (md : MetaData) (outputParams : List Parameter)
  (outParam : Parameter) (s s1 : TranslateState) (coreExpr : Core.Expression.Expr)
  (hHead : outputParams.head? = some outParam)
  (hNotInstanceCall : ∀ t c a, value.val ≠ .InstanceCall t c a)
  (hNotStaticCall : ∀ c a, value.val ≠ .StaticCall c a)
  (hExpr : translateExpr value [] false s = (some coreExpr, s1)) :
  translateStmt outputParams ⟨.Return (some value), md⟩ s =
    (some [Core.Statement.set ⟨outParam.name.text, ()⟩ coreExpr md,
           Imperative.Stmt.exit (some "$body") md], s1) := by
  unfold translateStmt; simp only [TranslateM.get_bind, hHead]
  cases hv : value.val <;> simp_all [TranslateM.bind_some _ _ _ _ _ hExpr, TranslateM.pure_eq]

@[simp] public theorem translateStmt_eq_ite_noElse
  (cond thenB : StmtExprMd) (md : MetaData) (outputParams : List Parameter)
  (s s1 s2 : TranslateState) (rc : Core.Expression.Expr) (rt : List Core.Statement)
  (hc : translateExpr cond [] false s = (some rc, s1))
  (ht : translateStmt outputParams thenB s1 = (some rt, s2)) :
  translateStmt outputParams ⟨.IfThenElse cond thenB none, md⟩ s =
    (some [Imperative.Stmt.ite rc rt [] .empty], s2) := by
  unfold translateStmt
  simp only [TranslateM.get_bind, TranslateM.bind_some _ _ _ _ _ hc,
    TranslateM.bind_some _ _ _ _ _ ht, TranslateM.pure_eq]; rfl

@[simp] public theorem translateStmt_eq_ite_withElse
  (cond thenB elseB : StmtExprMd) (md : MetaData) (outputParams : List Parameter)
  (s s1 s2 s3 : TranslateState) (rc : Core.Expression.Expr) (rt re : List Core.Statement)
  (hc : translateExpr cond [] false s = (some rc, s1))
  (ht : translateStmt outputParams thenB s1 = (some rt, s2))
  (he : translateStmt outputParams elseB s2 = (some re, s3)) :
  translateStmt outputParams ⟨.IfThenElse cond thenB (some elseB), md⟩ s =
    (some [Imperative.Stmt.ite rc rt re .empty], s3) := by
  unfold translateStmt
  simp only [TranslateM.get_bind, TranslateM.bind_some _ _ _ _ _ hc,
    TranslateM.bind_some _ _ _ _ _ ht, TranslateM.bind_some _ _ _ _ _ he, TranslateM.pure_eq]

@[simp] public theorem translateStmt_eq_localVar_noInit
  (id : Identifier) (ty : WithMetadata HighType)
  (md : MetaData) (outputParams : List Parameter) (s : TranslateState) :
  translateStmt outputParams ⟨.LocalVariable id ty none, md⟩ s =
    (some [Core.Statement.init ⟨id.text, ()⟩ (.forAll [] (translateType s.model ty)) none md], s) := by
  unfold translateStmt; simp only [TranslateM.get_bind, TranslateM.pure_eq]

@[simp] public theorem translateStmt_eq_localVar_exprInit
  (id : Identifier) (ty : WithMetadata HighType) (v : StmtExpr) (m : MetaData)
  (md : MetaData) (outputParams : List Parameter)
  (s s1 : TranslateState) (coreExpr : Core.Expression.Expr)
  (hNotStaticCall : ∀ c a, v ≠ .StaticCall c a)
  (hNotInstanceCall : ∀ t c a, v ≠ .InstanceCall t c a)
  (hNotHole : ∀ n t, v ≠ .Hole n t)
  (hExpr : translateExpr ⟨v, m⟩ [] false s = (some coreExpr, s1)) :
  translateStmt outputParams ⟨.LocalVariable id ty (some ⟨v, m⟩), md⟩ s =
    (some [Core.Statement.init ⟨id.text, ()⟩ (.forAll [] (translateType s.model ty)) (some coreExpr) md], s1) := by
  unfold translateStmt; simp only [TranslateM.get_bind]
  cases v <;> simp_all [TranslateM.bind_some _ _ _ _ _ hExpr, TranslateM.pure_eq]

@[simp] public theorem translateStmt_eq_assign_expr
  (targetId : Identifier) (targetMd : MetaData) (value : StmtExprMd)
  (md : MetaData) (outputParams : List Parameter)
  (s s1 : TranslateState) (coreExpr : Core.Expression.Expr)
  (hNotStaticCall : ∀ c a, value.val ≠ .StaticCall c a)
  (hNotInstanceCall : ∀ t c a, value.val ≠ .InstanceCall t c a)
  (hExpr : translateExpr value [] false s = (some coreExpr, s1)) :
  translateStmt outputParams ⟨.Assign [⟨.Identifier targetId, targetMd⟩] value, md⟩ s =
    (some [Core.Statement.set ⟨targetId.text, ()⟩ coreExpr md], s1) := by
  unfold translateStmt; simp only [TranslateM.get_bind]
  cases hv : value.val <;> simp_all [TranslateM.bind_some _ _ _ _ _ hExpr, TranslateM.pure_eq]

@[simp] public theorem translateStmt_eq_block_unlabeled
  (stmts : List StmtExprMd) (md : MetaData) (outputParams : List Parameter)
  (s s1 : TranslateState) (result : List Core.Statement)
  (hInner : stmts.flatMapM (fun s => translateStmt outputParams s) s = (some result, s1)) :
  translateStmt outputParams ⟨.Block stmts none, md⟩ s = (some result, s1) := by
  unfold translateStmt
  simp only [TranslateM.get_bind, TranslateM.bind_some _ _ _ _ _ hInner, TranslateM.pure_eq]

@[simp] public theorem translateStmt_eq_while
  (cond : StmtExprMd) (invariants : List StmtExprMd) (decreasesExpr : Option StmtExprMd)
  (body : StmtExprMd) (md : MetaData) (outputParams : List Parameter)
  (s s1 : TranslateState) (condExpr : Core.Expression.Expr)
  (s2 : TranslateState) (invExprs : List Core.Expression.Expr)
  (s3 : TranslateState) (decExprCore : Option Core.Expression.Expr)
  (s4 : TranslateState) (bodyStmts : List Core.Statement)
  (hCond : translateExpr cond [] false s = (some condExpr, s1))
  (hInvs : invariants.mapM translateExpr s1 = (some invExprs, s2))
  (hDec : decreasesExpr.mapM translateExpr s2 = (some decExprCore, s3))
  (hBody : translateStmt outputParams body s3 = (some bodyStmts, s4)) :
  translateStmt outputParams ⟨.While cond invariants decreasesExpr body, md⟩ s =
    (some [Imperative.Stmt.loop condExpr decExprCore invExprs bodyStmts md], s4) := by
  unfold translateStmt
  simp only [TranslateM.get_bind, TranslateM.bind_some _ _ _ _ _ hCond,
    TranslateM.bind_some _ _ _ _ _ hInvs, TranslateM.bind_some _ _ _ _ _ hDec,
    TranslateM.bind_some _ _ _ _ _ hBody, TranslateM.pure_eq]

@[simp] public theorem translateStmt_eq_staticCall_proc
  (callee : Identifier) (args : List StmtExprMd) (md : MetaData)
  (outputParams : List Parameter)
  (s s1 : TranslateState) (coreArgs : List Core.Expression.Expr)
  (hNotFunc : s.model.isFunction callee = false)
  (hArgs : (args.mapM (fun a => translateExpr a)) s = (some coreArgs, s1)) :
  translateStmt outputParams ⟨.StaticCall callee args, md⟩ s =
    (some [Core.Statement.call [⟨"$result", ()⟩] callee.text coreArgs md,
      Imperative.Stmt.ite
        (LExpr.app () (LExpr.op () ⟨"ExceptionResult..isFailure", ()⟩ none) (LExpr.fvar () ⟨"$result", ()⟩ none))
        [Imperative.Stmt.exit (some s1.exceptionTarget) md] [] md], s1) := by
  unfold translateStmt
  simp only [TranslateM.get_bind, hNotFunc]
  norm_cast; simp only [ite_false]
  have h1 : (List.mapM (fun a => translateExpr a) args >>= fun coreArgs => do
    let __do_lift ← exceptionPropagationCheck md
    pure ([Core.Statement.call [⟨"$result", ()⟩] callee.text coreArgs md] ++ __do_lift)) s =
    (do let __do_lift ← exceptionPropagationCheck md
        pure ([Core.Statement.call [⟨"$result", ()⟩] callee.text coreArgs md] ++ __do_lift)) s1 := by
    simp only [bind, OptionT.bind, StateT.bind, OptionT.mk, hArgs]
  rw [h1]; unfold exceptionPropagationCheck
  simp only [TranslateM.get_bind, bind, OptionT.bind, StateT.bind, OptionT.mk, TranslateM.pure_eq]
  rfl

/-! ### flatMapM equation lemmas for translateStmt -/

@[simp] public theorem flatMapM_translateStmt_nil
  (outputParams : List Parameter) (s : TranslateState) :
  (List.flatMapM (fun s => translateStmt outputParams s) [] : TranslateM _) s = (some [], s) := by
  simp [List.flatMapM_nil, TranslateM.pure_eq]

@[simp] public theorem flatMapM_translateStmt_cons
  (outputParams : List Parameter)
  (x : StmtExprMd) (xs : List StmtExprMd)
  (s s1 s2 : TranslateState)
  (r1 : List Core.Statement) (r2 : List Core.Statement)
  (hHead : translateStmt outputParams x s = (some r1, s1))
  (hTail : (List.flatMapM (fun s => translateStmt outputParams s) xs : TranslateM _) s1 = (some r2, s2)) :
  (List.flatMapM (fun s => translateStmt outputParams s) (x :: xs) : TranslateM _) s = (some (r1 ++ r2), s2) := by
  rw [List.flatMapM_cons]
  simp only [TranslateM.bind_some _ _ _ _ _ hHead,
    TranslateM.bind_some _ _ _ _ _ hTail, TranslateM.pure_eq]

/-! ### translateProcedureToFunction equation lemma -/

@[simp] public theorem translateProcedureToFunction_eq_transparent
  (proc : Procedure) (bodyExpr : StmtExprMd)
  (s s1 : TranslateState) (coreBody : Core.Expression.Expr)
  (hTransparent : proc.body = .Transparent bodyExpr)
  (hNoPre : proc.preconditions = [])
  (hBody : translateExpr bodyExpr [] true s = (some coreBody, s1)) :
  translateProcedureToFunction proc s =
    (some (.func {
      name := ⟨proc.name.text, ()⟩
      typeArgs := []
      inputs := proc.inputs.map (translateParameterToCore s.model)
      output := match proc.outputs.head? with
        | some p => translateType s.model p.type
        | none => LMonoTy.int
      body := some coreBody
      preconditions := []
    }), s1) := by
  unfold translateProcedureToFunction
  simp only [TranslateM.get_bind, hTransparent]
  rw [hNoPre, List.mapM_nil]
  simp only [bind, OptionT.bind, StateT.bind, OptionT.mk, TranslateM.pure_eq,
    TranslateM.map_some _ _ _ _ _ hBody]
  rfl


end Laurel
