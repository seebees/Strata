/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Imperative.CmdSemantics
import all Strata.DL.Imperative.CmdSemantics
public import Strata.DL.Imperative.StmtSemantics
import all Strata.DL.Imperative.StmtSemantics
public import Strata.DL.Imperative.HasVars
import all Strata.DL.Imperative.HasVars
public import Strata.DL.Util.Nodup
import all Strata.DL.Util.Nodup
public import Strata.DL.Util.ListUtils
import all Strata.DL.Util.ListUtils
public import Strata.Languages.Core.Procedure
public import Strata.Languages.Core.Statement
import all Strata.Languages.Core.Statement
public import Strata.Languages.Core.StatementSemantics
import all Strata.Languages.Core.StatementSemantics
import all Strata.DL.Imperative.Cmd
import all Strata.DL.Imperative.Stmt
import Strata.Util.Tactics

public section

/-! ## Theorems related to StatementSemantics -/

namespace Core
open Imperative

theorem InitStatesEmpty :
  @InitStates P σ [] [] σ' → σ = σ' := by sorry
theorem UpdateStatesEmpty :
  @UpdateStates P σ [] [] σ' → σ = σ' := by sorry
theorem HavocVarsEmpty :
  @HavocVars P σ [] σ' → σ = σ' := by sorry
theorem InitVarsEmpty :
  @InitVars P σ [] σ' → σ = σ' := by sorry
theorem TouchVarsEmpty :
  @TouchVars P σ [] σ' → σ = σ' := by sorry
theorem EvalBlockEmpty' {P : PureExpr} {Cmd : Type} {EvalCmd : EvalCmdParam P Cmd}
  {extendEval : ExtendEval P}
  { σ σ': SemanticStore P } { δ δ' : SemanticEval P }
  [DecidableEq P.Ident]
  [HasVarsImp P (List (Stmt P Cmd))] [HasVarsImp P Cmd] [HasFvar P] [HasVal P] [HasBool P] [HasNot P] :
  EvalBlock P Cmd EvalCmd extendEval δ σ ([]: (List (Stmt P Cmd))) σ' _br δ' → σ = σ' := by sorry
theorem EvalStatementsEmpty :
  EvalStatements π extendEval δ σ [] σ' _br δ' → σ = σ' := by sorry
theorem EvalStatementsContractEmpty :
  EvalStatementsContract π extendEval δ σ [] σ' _br δ' → σ = σ' := by sorry
theorem UpdateStateNotDefMonotone
  {P : PureExpr} {σ σ' : SemanticStore P}
  {vs : List P.Ident} {e : P.Expr} {v : P.Ident} :
  isNotDefined σ vs →
  UpdateState P σ v e σ' →
  isNotDefined σ' vs := by sorry
theorem UpdateStatesNotDefMonotone
  {P : PureExpr} {σ σ' : SemanticStore P}
  {vs : List P.Ident} {es' : List P.Expr} {vs' : List P.Ident} :
  isNotDefined σ vs →
  UpdateStates σ vs' es' σ' →
  isNotDefined σ' vs := by sorry
theorem UpdateStateNotDefMonotone'
  {P : PureExpr} {σ σ' : SemanticStore P}
  {vs : List P.Ident} {e : P.Expr} {v : P.Ident} :
  isNotDefined σ' vs →
  UpdateState P σ v e σ' →
  isNotDefined σ vs := by sorry
theorem UpdateStatesNotDefMonotone'
  {P : PureExpr} {σ σ' : SemanticStore P}
  {vs : List P.Ident} {es' : List P.Expr} {vs' : List P.Ident} :
  isNotDefined σ' vs →
  UpdateStates σ vs' es' σ' →
  isNotDefined σ vs := by sorry
theorem InitStateDefined
  {P : PureExpr} {σ σ' : SemanticStore P} {e : P.Expr} {v : P.Ident} :
  @InitState P σ v e σ' →
  isDefined σ' [v] := by sorry
theorem UpdateStateDefined
  {P : PureExpr} {σ σ' : SemanticStore P} {e : P.Expr} {v : P.Ident} :
  @UpdateState P σ v e σ' →
  isDefined σ' [v] := by sorry
theorem UpdateStateDefined'
  {P : PureExpr} {σ σ' : SemanticStore P} {e : P.Expr} {v : P.Ident} :
  @UpdateState P σ v e σ' →
  isDefined σ [v] := by sorry
theorem UpdateStateDefMonotone
  {P : PureExpr} {σ σ' : SemanticStore P}
  {vs : List P.Ident} {e : P.Expr} {v : P.Ident} :
  isDefined σ vs →
  UpdateState P σ v e σ' →
  isDefined σ' vs := by sorry
theorem UpdateStatesDefMonotone
  {P : PureExpr} {σ σ' : SemanticStore P}
  {vs : List P.Ident} {es' : List P.Expr} {vs' : List P.Ident} :
  isDefined σ vs →
  UpdateStates σ vs' es' σ' →
  isDefined σ' vs := by sorry
theorem UpdateStateDefMonotone'
  {P : PureExpr} {σ σ' : SemanticStore P}
  {vs : List P.Ident} {e : P.Expr} {v : P.Ident} :
  isDefined σ' vs →
  UpdateState P σ v e σ' →
  isDefined σ vs := by sorry
theorem UpdateStatesDefMonotone'
  {P : PureExpr} {σ σ' : SemanticStore P}
  {vs : List P.Ident} {es' : List P.Expr} {vs' : List P.Ident} :
  isDefined σ' vs →
  UpdateStates σ vs' es' σ' →
  isDefined σ vs := by sorry
theorem UpdateStatesDefined :
  UpdateStates σ vs es σ' →
  isDefined σ' vs := by sorry
theorem UpdateStatesDefined' :
  UpdateStates σ vs es σ' →
  isDefined σ vs := by sorry
theorem updatedStateUpdate {P : PureExpr}
  {σ : SemanticStore P} {h : P.Ident} {v v' : P.Expr} :
  σ h = some v' →
  UpdateState P σ h v (@updatedState P σ h v) := by sorry
theorem updatedStateId {P : PureExpr}
  {σ : SemanticStore P} {h : P.Ident} {v : P.Expr} :
  σ h = some v →
  @updatedState P σ h v = σ := by sorry
theorem updatedStateDefMonotone :
  isDefined σ vs →
  isDefined (updatedState σ v' e') vs := by sorry
theorem updatedStatesDefMonotone
  {P : PureExpr} {σ : SemanticStore P}
  {vs : List P.Ident} {ves : List (P.Ident × P.Expr)} :
  isDefined σ vs →
  isDefined (updatedStates' σ ves) vs := by sorry
  theorem updatedStatesDefined :
  ks.length = vs.length →
  isDefined (updatedStates σ ks vs) ks := by sorry
theorem updatedStatesUpdate {P : PureExpr}
  {σ : SemanticStore P} {hs : List P.Ident} {vs : List P.Expr} :
  hs.length = vs.length →
  isDefined σ hs →
  UpdateStates σ hs vs (updatedStates σ hs vs) := by sorry
theorem updatedStateInit {P : PureExpr}
  {σ : SemanticStore P} {h : P.Ident} {v : P.Expr} :
  σ h = none →
  InitState P σ h v (@updatedState P σ h v) := by sorry
theorem updatedStatesInit {P : PureExpr}
  {σ : SemanticStore P} {hs : List P.Ident} {vs : List P.Expr} :
  hs.length = vs.length →
  isNotDefined σ hs →
  hs.Nodup →
  InitStates σ hs vs (updatedStates σ hs vs) := by sorry
theorem updatedStates'App :
  updatedStates' σ (a ++ b) =
  updatedStates' (updatedStates' σ a) b := by sorry
theorem InitStatesInitVars :
  InitStates σ hs vs σ' →
  InitVars σ hs σ' := by sorry
theorem InitStatesInits :
  InitStates σ hs vs σ' →
  Inits σ σ' := by sorry
theorem InitStatesNotDefined :
  InitStates σ hs vs σ' → isNotDefined σ hs := by sorry
theorem InitStatesNodup :
  InitStates σ hs vs σ' → hs.Nodup := by sorry
theorem InitStateInjective :
  InitState P σ k1 k2 σ' →
  InitState P σ k1 k2 σ'' →
  σ' = σ'' := by sorry
theorem InitStatesInjective :
  InitStates σ k1 k2 σ' →
  InitStates σ k1 k2 σ'' →
  σ' = σ'' := by sorry
theorem ReadValuesInjective :
  ReadValues σ ks vs →
  ReadValues σ ks vs' →
  vs = vs' := by sorry
theorem InitStateUpdated :
    InitState P σ' k v σ'' →
    σ'' = updatedState σ' k v := by sorry
theorem InitStatesUpdated :
    InitStates σ' ks vs σ'' →
    σ'' = updatedStates σ' ks vs := by sorry
theorem UpdateStateUpdated :
    UpdateState P σ' k v σ'' →
    σ'' = updatedState σ' k v := by sorry
theorem UpdateStatesUpdated :
    UpdateStates σ' ks vs σ'' →
    σ'' = updatedStates σ' ks vs := by sorry
theorem InitStatesApp' :
  InitStates σ (k1 ++ k2) (v1 ++ v2) σ' →
  k1.length = v1.length →
  k2.length = v2.length →
  ∃ σ₁,
  σ₁ = updatedStates σ k1 v1 ∧
  InitStates σ k1 v1 σ₁ ∧
  InitStates σ₁ k2 v2 σ' := by sorry
theorem ReadValuesApp :
  ReadValues σ k1 v1 →
  ReadValues σ k2 v2 →
  ReadValues σ (k1 ++ k2) (v1 ++ v2) := by sorry
theorem ReadValuesAppKeys' :
  ReadValues σ (k1 ++ k2) vs →
  exists v1 v2,
  v1 ++ v2 = vs ∧
  ReadValues σ k1 v1 ∧
  ReadValues σ k2 v2 := by sorry
theorem ReadValuesLength :
  ReadValues σ ks vs →
  ks.length = vs.length := by sorry
theorem EvalExpressionsLength :
  EvalExpressions (P:=Core.Expression) δ σ ks vs →
  ks.length = vs.length := by sorry
theorem InitStatesLength :
  InitStates σ ks vs σ' →
  ks.length = vs.length := by sorry
theorem UpdateStatesLength {P : PureExpr}
  {σ σ' : Imperative.SemanticStore P}
  {ks : List P.Ident}
  {vs : List P.Expr}
  :
  UpdateStates (P:=P) σ ks vs σ' →
  List.length ks = List.length vs := by sorry
theorem InitStateReadValuesMonotone {P : PureExpr} {σ σ' : SemanticStore P}
  {ks : List P.Ident} {vs : List P.Expr} {e : P.Expr} {v : P.Ident} :
  ReadValues σ ks vs →
  InitState P σ v e σ' →
  ReadValues σ' ks vs := by sorry
theorem InitStatesReadValuesMonotone
  {P : PureExpr} {σ σ' : SemanticStore P}
  {ks : List P.Ident} {vs : List P.Expr}
  {es' : List P.Expr} {vs' : List P.Ident} :
  ReadValues σ ks vs →
  InitStates σ vs' es' σ' →
  ReadValues σ' ks vs := by sorry
theorem UpdateStateReadValuesMonotone {P : PureExpr} {σ σ' : SemanticStore P}
  {ks : List P.Ident} {vs : List P.Expr} {e : P.Expr} {v : P.Ident} :
  ¬ v ∈ ks →
  ReadValues σ ks vs →
  UpdateState P σ v e σ' →
  ReadValues σ' ks vs := by sorry
theorem UpdateStatesReadValuesMonotone
  {P : PureExpr} {σ σ' : SemanticStore P}
  {ks : List P.Ident} {vs : List P.Expr}
  {es' : List P.Expr} {vs' : List P.Ident} :
  (ks ++ vs').Nodup →
  ReadValues σ ks vs →
  UpdateStates σ vs' es' σ' →
  ReadValues σ' ks vs := by sorry
theorem InitStateReadValues :
  InitState P σ v e σ' →
  ReadValues σ' [v] [e] := by sorry
theorem UpdateStateReadValues :
  UpdateState P σ v e σ' →
  ReadValues σ' [v] [e] := by sorry
theorem InitStatesReadValues :
  InitStates σ vs es σ' →
  ReadValues σ' vs es := by sorry
theorem UpdateStatesReadValues :
  vs.Nodup →
  UpdateStates σ vs es σ' →
  ReadValues σ' vs es := by sorry
theorem InitVarsInitStates : InitVars σ vars σ' →
  ∃ modvals, InitStates σ vars modvals σ' := by sorry
theorem InitVarsReadValuesMonotone
  {P : PureExpr} {σ σ' : SemanticStore P}
  {ks vs' : List P.Ident} {vs : List P.Expr} :
  ReadValues σ ks vs →
  InitVars σ vs' σ' →
  ReadValues σ' ks vs := by sorry
theorem updatedStateComm
  {P : PureExpr} {σ : SemanticStore P}
  {k k' : P.Ident} {v v' : P.Expr} :
  k ≠ k' →
  updatedState (updatedState σ k v) k' v' =
  updatedState (updatedState σ k' v') k v := by sorry
theorem updatedStateComm'
  {P : PureExpr} {σ : SemanticStore P}
  {k : P.Ident} {v : P.Expr}
  {kvs : List (P.Ident × P.Expr)} :
  ¬ k ∈ kvs.unzip.1 →
  (updatedState (updatedStates' σ kvs) k v) =
  (updatedStates' (updatedState σ k v) kvs) := by sorry
theorem updatedStatesComm
  {P : PureExpr} {σ : SemanticStore P}
  {kvs kvs' : List (P.Ident × P.Expr)} :
  kvs.unzip.1.Disjoint kvs'.unzip.1 →
  updatedStates' (updatedStates' σ kvs) kvs' =
  updatedStates' (updatedStates' σ kvs') kvs := by sorry
theorem UpdateStateSomeMonotone
  {P : PureExpr} {σ σ' : SemanticStore P}
  {k' : P.Ident} {v' : P.Expr} {e : P.Expr} {v : P.Ident} :
  v ≠ k' →
  σ k' = some v' →
  UpdateState P σ v e σ' →
  σ' k' = some v' := by sorry
theorem UpdateStatesSomeMonotone
  {P : PureExpr} {σ σ' : SemanticStore P}
  {k' : P.Ident} {v' : P.Expr}
  {ks': List P.Ident} {vs': List P.Expr} :
  ¬ k' ∈ ks' →
  σ k' = some v' →
  UpdateStates σ ks' vs' σ' →
  σ' k' = some v' := by sorry
theorem InitStateSomeMonotone
  {P : PureExpr} {σ σ' : SemanticStore P}
  {k' : P.Ident} {v' : P.Expr} {e : P.Expr} {v : P.Ident} :
  σ k' = some v' →
  InitState P σ v e σ' →
  σ' k' = some v' := by sorry
theorem InitStateSomeMonotone'
  {P : PureExpr} {σ σ' : SemanticStore P}
  {k' : P.Ident} {v' : P.Expr} {e : P.Expr} {v : P.Ident} :
  k' ≠ v →
  σ' k' = some v' →
  InitState P σ v e σ' →
  σ k' = some v' := by sorry
theorem InitStatesSomeMonotone
  {P : PureExpr} {σ σ' : SemanticStore P}
  {k' : P.Ident} {v' : P.Expr}
  {ks': List P.Ident} {vs': List P.Expr} :
  σ k' = some v' →
  InitStates σ ks' vs' σ' →
  σ' k' = some v' := by sorry
theorem InitStatesSomeMonotone'
  {P : PureExpr} {σ σ' : SemanticStore P}
  {k' : P.Ident} {v' : P.Expr}
  {ks': List P.Ident} {vs': List P.Expr} :
  ¬ k' ∈ ks' →
  σ' k' = some v' →
  InitStates σ ks' vs' σ' →
  σ k' = some v' := by sorry
theorem InitsUpdatesComm
  {P : PureExpr} {σ σ' σ'' : SemanticStore P}
  {ks ks' : List P.Ident} {vs vs' : List P.Expr} :
  UpdateStates σ ks vs σ' →
  InitStates σ' ks' vs' σ'' →
  ∃ σ₁,
    σ₁ = (updatedStates σ ks' vs') ∧
    InitStates σ ks' vs' σ₁ ∧
    UpdateStates σ₁ ks vs σ'' := by sorry
theorem InitUpdateComm
  {P : PureExpr} {σ σ' σ'' : SemanticStore P}
  {k k' : P.Ident} {v v' : P.Expr}
  :
  UpdateState P σ k v σ' →
  InitState P σ' k' v' σ'' →
  ∃ σ₁,
    σ₁ = (updatedState σ k' v') ∧
    InitState P σ k' v' σ₁ ∧
    UpdateState P σ₁ k v σ'' := by sorry
theorem isDefinedReadValues :
  isDefined σ ks →
  ∃ vs,
  ReadValues σ ks vs := by sorry
theorem ReadValuesIsDefined :
  ReadValues σ ks vs →
  isDefined σ ks := by sorry
theorem InitStateSubstStores :
σ k' = some v' →
InitState Expression σ k v' σ' →
substStores σ σ' [(k', k)] := by sorry
theorem InitStatesSubstStores :
ReadValues σ ks' vs' →
InitStates σ ks vs' σ' →
substStores σ σ' (ks'.zip ks) := by sorry
theorem substStoresInitInv :
substDefined σ σ' substs →
substStores σ σ' substs →
InitState Expression σ' k v σ'' →
substStores σ σ'' substs := by sorry
theorem substStoresInitsInv :
substDefined σ σ' substs →
substStores σ σ' substs →
InitStates σ' ks vs σ'' →
substStores σ σ'' substs := by sorry
theorem substStoresInitsInv' :
substDefined σ σ' substs →
substStores σ σ' substs →
InitStates σ ks vs σ'' →
substStores σ'' σ' substs := by sorry
theorem substStoresUpdateInv {k : P.Ident} {substs : List (P.Ident × P.Ident)}:
¬ k ∈ substs.unzip.2 →
substStores (P:=P) σ σ' substs →
UpdateState (P:=P) σ' k v σ'' →
substStores (P:=P) σ σ'' substs := by sorry
theorem substStoresUpdatesInv :
ks.Disjoint substs.unzip.2 →
substStores σ σ' substs →
UpdateStates σ' ks vs σ'' →
substStores σ σ'' substs := by sorry
theorem substStoresUpdatesInv' :
ks.Disjoint substs.unzip.1 →
substStores σ σ' substs →
UpdateStates σ ks vs σ'' →
substStores σ'' σ' substs := by sorry
theorem substDefinedIsDefined :
  substDefined σ σ' substs →
  isDefined σ substs.unzip.1 ∧
  isDefined σ' substs.unzip.2 := by sorry
theorem substStoresCons' :
  substNodup ((h,h') :: substs) →
  substDefined σ σ'' ((h,h') :: substs) →
  substStores σ σ'' ((h,h') :: substs) →
  ∃ σ' v,
    σ h = some v ∧
    σ' = updatedState σ h' v ∧
    substStores σ σ' [(h,h')] ∧
    substStores σ' σ'' substs := by sorry
theorem substStoresCons :
  substStores σ σ' [(h,h')] →
  substStores σ σ' (List.zip t t') →
  substStores σ σ' ((h,h') :: (List.zip t t')) := by sorry
theorem ReadValuesSubstStores :
  ReadValues σ ks vs →
  ReadValues σ' ks' vs →
  Imperative.substStores σ σ' (List.zip ks ks') := by sorry
theorem EvalStatementsContractApp' {φ : CoreEval → PureFunc Expression → CoreEval} {δ δ'' : CoreEval} :
  EvalStatementsContract π φ δ σ (ss₁ ++ ss₂) σ'' _br δ'' →
  ∃ σ' δ',
    EvalStatementsContract π φ δ σ ss₁ σ' _br1 δ' ∧
    EvalStatementsContract π φ δ' σ' ss₂ σ'' _br2 δ'' := by sorry
theorem EvalStatementsContractApp {φ : CoreEval → PureFunc Expression → CoreEval} {δ δ' δ'' : CoreEval} :
  EvalStatementsContract π φ δ σ ss₁ σ' _br1 δ' →
  EvalStatementsContract π φ δ' σ' ss₂ σ'' _br2 δ'' →
  EvalStatementsContract π φ δ σ (ss₁ ++ ss₂) σ'' _br δ'' := by sorry
theorem EvalStatementsApp {φ : CoreEval → PureFunc Expression → CoreEval} {δ δ' δ'' : CoreEval} :
  EvalStatements π φ δ σ ss₁ σ' _br3 δ' →
  EvalStatements π φ δ' σ' ss₂ σ'' _br4 δ'' →
  EvalStatements π φ δ σ (ss₁ ++ ss₂) σ'' _br5 δ'' := by sorry
theorem HavocVarsApp :
  HavocVars σ vs₁ σ' →
  HavocVars σ' vs₂ σ'' →
  HavocVars σ (vs₁ ++ vs₂) σ'' := by sorry
theorem HavocVarsApp' :
  HavocVars σ (vs₁ ++ vs₂) σ'' →
  ∃ σ',
  HavocVars σ vs₁ σ' ∧
  HavocVars σ' vs₂ σ'' := by sorry
theorem InitVarsApp :
  InitVars σ vs₁ σ' →
  InitVars σ' vs₂ σ'' →
  InitVars σ (vs₁ ++ vs₂) σ'' := by sorry
theorem TouchVarsApp :
  TouchVars σ vs₁ σ' →
  TouchVars σ' vs₂ σ'' →
  TouchVars σ (vs₁ ++ vs₂) σ'' := by sorry
theorem HavocVarsCons :
  HavocVars σ [v] σ' →
  HavocVars σ' vs σ'' →
  HavocVars σ (v :: vs) σ'' := by sorry
theorem HavocVarsId :
  isDefined σ vs →
  HavocVars σ vs σ := by sorry
theorem TouchVarsId :
  isDefined σ vs →
  TouchVars σ vs σ := by sorry
theorem InitStateDefMonotone
  {P : PureExpr} {σ σ' : SemanticStore P}
  {vs : List P.Ident} {e : P.Expr} {v : P.Ident} :
  isDefined σ vs →
  InitState P σ v e σ' →
  isDefined σ' vs := by sorry
theorem InitStatesDefMonotone :
  isDefined σ vs →
  InitStates σ vs' es' σ' →
  isDefined σ' vs := by sorry
theorem InitVarsDefMonotone :
  isDefined σ vs →
  InitVars σ vs' σ' →
  isDefined σ' vs := by sorry
theorem InitStateDefMonotone'
  {P : PureExpr} {σ σ' : SemanticStore P}
  {vs : List P.Ident} {e : P.Expr} {v : P.Ident} :
  ¬ v ∈ vs →
  isDefined σ' vs →
  InitState P σ v e σ' →
  isDefined σ vs := by sorry
theorem InitStatesDefMonotone' :
  vs.Disjoint vs' →
  isDefined σ' vs →
  InitStates σ vs' es' σ' →
  isDefined σ vs := by sorry
theorem InitVarsDefMonotone' :
  vs.Disjoint vs' →
  isDefined σ' vs →
  InitVars σ vs' σ' →
  isDefined σ vs := by sorry
theorem InitStatesDefined :
  InitStates σ hs vs σ' → isDefined σ' hs := by sorry
theorem HavocVarsDefMonotone :
  isDefined σ vs →
  HavocVars σ vs' σ' →
  isDefined σ' vs := by sorry
theorem HavocVarsUpdateStates : HavocVars σ vars σ' →
  ∃ modvals, UpdateStates σ vars modvals σ' := by sorry
theorem HavocVarsDefMonotone' :
  isDefined σ' vs →
  HavocVars σ vs' σ' →
  isDefined σ vs := by sorry
theorem InitVarsDefined :
  InitVars σ vs σ' →
  isDefined σ' vs := by sorry
theorem InitVarsReadValues :
  InitVars σ ks σ' →
  exists vs,
  ReadValues σ' ks vs := by sorry
theorem HavocVarsDefined :
  HavocVars σ vs σ' →
  isDefined σ' vs := by sorry
theorem EvalCmdDefMonotone' :
  isDefined σ v →
  EvalCmd Core.Expression δ σ c σ' →
  isDefined σ' v := by sorry
theorem EvalCmdTouch
  [HasVal P] [HasFvar P] [HasBool P] [HasBoolVal P] [HasNot P] :
  EvalCmd P δ σ c σ' →
  TouchVars σ (HasVarsImp.touchedVars c) σ' := by sorry
theorem UpdateStatesHavocVars : UpdateStates σ vars modvals σ' → HavocVars σ vars σ' := by
  intros H
  induction vars generalizing σ modvals
  case nil =>
    cases modvals
    . have Heq := UpdateStatesEmpty H
      simp [Heq]
      apply HavocVars.update_none
    . cases H
  case cons h t ih =>
    have HH := H
    cases H
    next Hup2 =>
    constructor <;> try assumption
    apply ih
    apply Hup2

theorem UpdateStatesTouchVars : UpdateStates σ vars modvals σ' → TouchVars σ vars σ' := by sorry
theorem EvalCmdRefinesContract :
EvalCmd Expression δ σ c σ' →
EvalCommandContract π δ σ (CmdExt.cmd c) σ' := by sorry
theorem InvStoresUpdatedStateDisjRightMono :
  ¬ k' ∈ ks →
  invStores σ σ' ks →
  invStores σ (updatedState σ' k' v') ks := by sorry
theorem InvStoresUpdatedStatesDisjRightMono :
  ks.Disjoint ks' →
  invStores σ σ' ks →
  ks'.length = vs'.length →
  invStores σ (updatedStates σ' ks' vs') ks := by sorry
theorem InvStoresUpdatedStateDisjLeftMono :
  ¬ k' ∈ ks →
  invStores σ σ' ks →
  invStores (updatedState σ k' v') σ' ks := by sorry
theorem InvStoresUpdatedStatesDisjLeftMono :
  ks.Disjoint ks' →
  invStores σ σ' ks →
  ks'.length = vs'.length →
  invStores (updatedStates σ ks' vs') σ' ks := by sorry
theorem InvStoresExceptEmpty : invStoresExcept σ σ [] :=
  fun _ _ _ _ Hin => congrArg σ (zip_self_eq Hin)

theorem InvStoresExceptId : invStoresExcept σ σ ls :=
  fun _ _ _ _ Hin => congrArg σ (zip_self_eq Hin)

theorem InvStoresExceptApp :
  invStoresExcept σ σ' ks →
  invStoresExcept σ σ' (ks ++ ks') := by sorry
theorem InvStoresExceptUpdated :
  invStoresExcept σ σ' ks →
  ks'.length = vs'.length →
  invStoresExcept (updatedStates σ ks' vs') σ' (ks ++ ks') := by sorry
theorem UpdatedStatesInSame :
  k ∈ ks' →
  ks'.length = vs'.length →
  ks'.Nodup →
  updatedStates σ ks' vs' k = updatedStates σ' ks' vs' k := by sorry
theorem UpdatedStatesNotinSame :
  σ k = σ' k →
  ¬ k ∈ ks' →
  ks'.length = vs'.length →
  ks'.Nodup →
  updatedStates σ ks' vs' k = updatedStates σ' ks' vs' k := by sorry
theorem InvStoresExceptUpdatedSame :
  invStoresExcept σ σ' ks →
  ks'.length = vs'.length →
  ks'.Nodup →
  invStoresExcept (updatedStates σ ks' vs') (updatedStates σ' ks' vs') ks := by sorry
theorem InvStoresExceptUpdatedMem :
  invStoresExcept σ σ' ks →
  ks'.length = vs'.length →
  ks'.Subset ks →
  invStoresExcept (updatedStates σ ks' vs') σ' ks := by sorry
theorem InvStoresExceptUpdateStates :
  invStoresExcept σ σ' ks →
  UpdateStates σ ks' vs' σ'' →
  invStoresExcept σ'' σ' (ks ++ ks') := by sorry
theorem InvStoresExceptInitStates :
  invStoresExcept σ σ' ks →
  InitStates σ ks' vs' σ'' →
  invStoresExcept σ'' σ' (ks ++ ks') := by sorry
theorem InvStoresExceptHavocVars :
  invStoresExcept σ σ' ks →
  HavocVars σ ks' σ'' →
  invStoresExcept σ'' σ' (ks ++ ks') := by sorry
theorem InvStoresExceptInitVars :
  invStoresExcept σ σ' ks →
  InitVars σ ks' σ'' →
  invStoresExcept σ'' σ' (ks ++ ks') := by sorry
theorem InvStoresExceptInvStores :
  invStoresExcept σ σ' ks →
  List.Disjoint ks ks' →
  invStores σ σ' ks' := by sorry
/--
  variables are irrelevant, and can be approximated by updating the relevant
  variables (that is, lhs ++ modifies)
-/
theorem EvalCallBodyRefinesContract :
  ∀ {π φ δ σ lhs n args σ' p md md'},
  π n = .some p →
  p.spec.modifies = Imperative.HasVarsTrans.modifiedVarsTrans π p.body →
  EvalCommand π φ δ σ (CmdExt.call lhs n args md) σ' →
  EvalCommandContract π δ σ (CmdExt.call lhs n args md') σ' := by sorry
theorem EvalCommandRefinesContract :
EvalCommand π φ δ σ c σ' →
EvalCommandContract π δ σ c σ' := by sorry
mutual
theorem EvalStmtRefinesContract
  (H : EvalStmt Expression Command (EvalCommand π φ) (EvalPureFunc φ) δ σ s σ' br δ') :
  EvalStmt Expression Command (EvalCommandContract π) (EvalPureFunc φ) δ σ s σ' br δ' :=
  match H with
  | .cmd_sem Heval Hdef => .cmd_sem (EvalCommandRefinesContract Heval) Hdef
  | .block_sem Heval Hcons => .block_sem (EvalBlockRefinesContract Heval) Hcons
  | .ite_true_sem Hcond Hwf Heval => .ite_true_sem Hcond Hwf (EvalBlockRefinesContract Heval)
  | .ite_false_sem Hcond Hwf Heval => .ite_false_sem Hcond Hwf (EvalBlockRefinesContract Heval)
  | .exit_sem => .exit_sem
  | .funcDecl_sem => .funcDecl_sem
  | .typeDecl_sem => .typeDecl_sem

theorem EvalBlockRefinesContract
  (H : EvalBlock Expression Command (EvalCommand π φ) (EvalPureFunc φ) δ σ ss σ' br δ') :
  EvalBlock Expression Command (EvalCommandContract π) (EvalPureFunc φ) δ σ ss σ' br δ' :=
  match H with
  | .stmts_none_sem => .stmts_none_sem
  | .stmts_normal_sem Hstmt Hrest =>
    .stmts_normal_sem (EvalStmtRefinesContract Hstmt) (EvalBlockRefinesContract Hrest)
  | .stmts_exit_sem Hstmt =>
    .stmts_exit_sem (EvalStmtRefinesContract Hstmt)
end

/-- If an expression is defined, all its free variables are defined in the store.
    Relies on the definedness propagation properties in `WellFormedCoreEvalCong`
    together with the variable-evaluation condition in `WellFormedSemanticEvalVar`. -/
theorem EvalExpressionIsDefined :
  WellFormedCoreEvalCong δ →
  WellFormedSemanticEvalVar δ →
  (δ σ e).isSome →
  isDefined σ (HasVarsPure.getVars e) := by sorry
end Core

end -- public section
