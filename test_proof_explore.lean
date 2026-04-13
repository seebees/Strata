/-
  Proof using bind inversion for OptionT (StateM σ).
-/
import Strata.Languages.Laurel.LaurelToCoreTranslator

open Strata.Laurel
open Lambda (LMonoTy)

namespace ProofExplore

def getPostconds' : Body → List StmtExprMd
  | .Transparent _ posts => posts
  | .Opaque posts _ _ => posts
  | .Abstract posts => posts
  | .External => []

/-- Bind inversion for OptionT (StateM σ). -/
theorem bind_inv {α β σ : Type}
    {f : OptionT (StateM σ) α} {g : α → OptionT (StateM σ) β}
    {s : σ} {r : β} {s' : σ}
    (h : (f >>= g) s = (some r, s')) :
    ∃ (x : α) (s₁ : σ), f s = (some x, s₁) ∧ g x s₁ = (some r, s') := by
  simp only [bind, OptionT.bind, OptionT.mk, StateT.bind, StateT.pure] at h
  generalize hf : f s = fResult at h
  obtain ⟨fOpt, s₁⟩ := fResult
  cases fOpt with
  | some x => exact ⟨x, s₁, rfl, h⟩
  | none => exact absurd (Prod.mk.inj h).1 (by simp)

-- Test: use bind_inv on translateProcedureToFunction
-- After eq_def, the first bind is: mapM inputs >>= (fun inputs => ...)
-- After that, the continuation has a `have __do_jp` (join point) and a match.
-- We need to handle this by simplifying the have/match.

set_option pp.all false in
set_option maxHeartbeats 800000 in
theorem test_axioms_length
    (options : LaurelTranslateOptions) (isRecursive : Bool)
    (proc : Procedure) (s s' : TranslateState) (f : Core.Function) (fmd : MetaData)
    (hSucc : translateProcedureToFunction options isRecursive proc s = (some (.func f fmd), s')) :
    f.axioms.length = (getPostconds' proc.body).length := by
  rw [translateProcedureToFunction.eq_def] at hSucc
  -- Step 1: extract inputs
  obtain ⟨inputs, s1, hInputs, hRest⟩ := bind_inv hSucc
  -- hRest has: (have __do_jp := fun outputTy => ...; match proc.outputs.head? with ...) s1 = ...
  -- Simplify the have/match
  simp only [bind, OptionT.bind, OptionT.mk, StateT.bind, StateT.pure,
    pure, OptionT.pure, OptionT.lift, get, MonadState.get, getThe, MonadStateOf.get,
    StateT.get, liftM, monadLift, MonadLift.monadLift, Functor.map,
    Prod.fst, Prod.snd, Function.comp] at hRest
  -- After simp, hRest should be a match on proc.outputs.head? applied to s1
  -- Case split on proc.outputs.head?
  cases hHead : proc.outputs.head? with
  | some p =>
    simp only [hHead] at hRest
    -- hRest : (translateType p.type >>= ...) s1 = ...
    -- Step 2: extract outputTy
    obtain ⟨outputTy, s2, hOutputTy, hRest2⟩ := bind_inv hRest
    -- Step 3: extract preconditions
    obtain ⟨preconditions, s3, hPreconditions, hRest3⟩ := bind_inv hRest2
    -- hRest3 has: (StateT.get.bind ...).bind ... which is the `get` operation
    -- Simplify the get operation
    simp only [StateT.get, StateT.bind, StateT.pure, bind, OptionT.bind, OptionT.mk,
      Prod.fst, Prod.snd, pure, OptionT.pure] at hRest3
    -- After simp, hRest3 should have the model/casesIdx/attr let-bindings
    -- followed by the body match and generateFunctionAxioms
    -- Step 4: body — case split on proc.body
    -- The `have` bindings (model, casesIdx, attr) are pure, so they should be inlined by simp
    -- hRest3 now has: match proc.body with | Transparent => ... | Opaque => ... | _ => ...
    -- Case split on proc.body
    cases hBodyCase : proc.body with
    | Transparent bodyExpr postconds =>
      simp only [hBodyCase] at hRest3
      -- hRest3 : (translateExpr bodyExpr >>= ...).bind ... s3 = ...
      -- The body computation is: some <$> translateExpr bodyExpr [] true
      -- which is a bind. Extract body.
      obtain ⟨body, s5, hBody, hRest5⟩ := bind_inv hRest3
      -- Step 6: extract axioms
      obtain ⟨axioms, s6, hAxioms, hRest6⟩ := bind_inv hRest5
      -- hRest6 : pure (.func { ..., axioms := axioms } proc.md) s6 = (some (.func f fmd), s')
      simp [pure, OptionT.pure, OptionT.mk, StateT.pure] at hRest6
      have hDecl := Option.some.inj (Prod.mk.inj hRest6).1
      have hF := Core.Decl.func.inj hDecl
      -- hAxioms : generateFunctionAxioms proc (match proc.body with ...) outputTy s5 = (some axioms, s6)
      -- The match on proc.body in hAxioms should reduce to postconds since hBodyCase : proc.body = Transparent ...
      simp only [hBodyCase] at hAxioms
      -- Now hAxioms : generateFunctionAxioms proc postconds outputTy s5 = (some axioms, s6)
      -- f.axioms = axioms (from hF)
      rw [← hF.1]
      simp only [getPostconds', hBodyCase]
      exact generateFunctionAxioms_length proc postconds outputTy s5 s6 axioms hAxioms
    | Opaque postconds impl modif =>
      simp only [hBodyCase] at hRest3
      -- For Opaque with impl: body = none (pure none)
      -- For Opaque without impl: body = none (pure none)
      cases impl with
      | some implExpr =>
        simp only [pure, OptionT.pure, OptionT.mk, StateT.pure, StateT.bind, bind,
          OptionT.bind, Prod.fst, Prod.snd] at hRest3
        -- body = none, so the bind for body is trivial
        obtain ⟨axioms, s6, hAxioms, hRest6⟩ := bind_inv hRest3
        simp [pure, OptionT.pure, OptionT.mk, StateT.pure] at hRest6
        have hDecl := Option.some.inj (Prod.mk.inj hRest6).1
        have hF := Core.Decl.func.inj hDecl
        simp only [hBodyCase] at hAxioms
        rw [← hF.1]; simp only [getPostconds', hBodyCase]
        exact generateFunctionAxioms_length proc postconds outputTy s3 s6 axioms hAxioms
      | none =>
        simp only [pure, OptionT.pure, OptionT.mk, StateT.pure, StateT.bind, bind,
          OptionT.bind, Prod.fst, Prod.snd] at hRest3
        obtain ⟨axioms, s6, hAxioms, hRest6⟩ := bind_inv hRest3
        simp [pure, OptionT.pure, OptionT.mk, StateT.pure] at hRest6
        have hDecl := Option.some.inj (Prod.mk.inj hRest6).1
        have hF := Core.Decl.func.inj hDecl
        simp only [hBodyCase] at hAxioms
        rw [← hF.1]; simp only [getPostconds', hBodyCase]
        exact generateFunctionAxioms_length proc postconds outputTy s3 s6 axioms hAxioms
    | Abstract postconds =>
      -- Abstract falls through to the catch-all: pure none
      -- After simp [hBodyCase], hRest3 should be a bind
      simp only [hBodyCase, pure, OptionT.pure, OptionT.mk, StateT.pure, StateT.bind, bind,
        OptionT.bind, Prod.fst, Prod.snd, OptionT.lift, liftM, monadLift, MonadLift.monadLift] at hRest3
      obtain ⟨axioms, s6, hAxioms, hRest6⟩ := bind_inv hRest3
      simp [pure, OptionT.pure, OptionT.mk, StateT.pure] at hRest6
      have hDecl := Option.some.inj (Prod.mk.inj hRest6).1
      have hF := Core.Decl.func.inj hDecl
      simp only [hBodyCase] at hAxioms
      rw [← hF.1]; simp only [getPostconds', hBodyCase]
      exact generateFunctionAxioms_length proc postconds outputTy s3 s6 axioms hAxioms
    | External =>
      simp only [hBodyCase, pure, OptionT.pure, OptionT.mk, StateT.pure, StateT.bind, bind,
        OptionT.bind, Prod.fst, Prod.snd, OptionT.lift, liftM, monadLift, MonadLift.monadLift] at hRest3
      -- hRest3 is already a match on generateFunctionAxioms result
      match hAx : generateFunctionAxioms proc [] outputTy s3 with
      | (some axioms, s6) =>
        rw [hAx] at hRest3
        simp [pure, OptionT.pure, OptionT.mk, StateT.pure] at hRest3
        have hDecl := Option.some.inj (Prod.mk.inj hRest3).1
        have hF := Core.Decl.func.inj hDecl
        rw [← hF.1]; simp only [getPostconds', hBodyCase]
        exact generateFunctionAxioms_length proc [] outputTy s3 s6 axioms hAx
      | (none, s6) =>
        rw [hAx] at hRest3
        exact absurd (Prod.mk.inj hRest3).1 (by simp)
  | none =>
    simp only [hHead, pure, OptionT.pure, OptionT.mk, StateT.pure, StateT.bind, bind,
      OptionT.bind, Prod.fst, Prod.snd, OptionT.lift, liftM, monadLift, MonadLift.monadLift] at hRest
    obtain ⟨preconditions, s3, hPC, hRest3⟩ := bind_inv hRest
    simp only [StateT.get, StateT.bind, StateT.pure, bind, OptionT.bind, OptionT.mk,
      Prod.fst, Prod.snd, pure, OptionT.pure] at hRest3
    cases hBodyCase : proc.body with
    | Transparent bodyExpr postconds =>
      simp only [hBodyCase] at hRest3
      obtain ⟨body, s5, hBody, hRest5⟩ := bind_inv hRest3
      obtain ⟨axioms, s6, hAxioms, hRest6⟩ := bind_inv hRest5
      simp [pure, OptionT.pure, OptionT.mk, StateT.pure] at hRest6
      have hF := Core.Decl.func.inj (Option.some.inj (Prod.mk.inj hRest6).1)
      simp only [hBodyCase] at hAxioms
      rw [← hF.1]; simp only [getPostconds', hBodyCase]
      exact generateFunctionAxioms_length proc postconds LMonoTy.int s5 s6 axioms hAxioms
    | Opaque postconds impl modif =>
      simp only [hBodyCase] at hRest3
      cases impl with
      | some _ =>
        simp only [pure, OptionT.pure, OptionT.mk, StateT.pure, StateT.bind, bind,
          OptionT.bind, Prod.fst, Prod.snd] at hRest3
        obtain ⟨axioms, s6, hAxioms, hRest6⟩ := bind_inv hRest3
        simp [pure, OptionT.pure, OptionT.mk, StateT.pure] at hRest6
        have hF := Core.Decl.func.inj (Option.some.inj (Prod.mk.inj hRest6).1)
        simp only [hBodyCase] at hAxioms
        rw [← hF.1]; simp only [getPostconds', hBodyCase]
        exact generateFunctionAxioms_length proc postconds LMonoTy.int s3 s6 axioms hAxioms
      | none =>
        simp only [pure, OptionT.pure, OptionT.mk, StateT.pure, StateT.bind, bind,
          OptionT.bind, Prod.fst, Prod.snd] at hRest3
        obtain ⟨axioms, s6, hAxioms, hRest6⟩ := bind_inv hRest3
        simp [pure, OptionT.pure, OptionT.mk, StateT.pure] at hRest6
        have hF := Core.Decl.func.inj (Option.some.inj (Prod.mk.inj hRest6).1)
        simp only [hBodyCase] at hAxioms
        rw [← hF.1]; simp only [getPostconds', hBodyCase]
        exact generateFunctionAxioms_length proc postconds LMonoTy.int s3 s6 axioms hAxioms
    | Abstract postconds =>
      simp only [hBodyCase, pure, OptionT.pure, OptionT.mk, StateT.pure, StateT.bind, bind,
        OptionT.bind, Prod.fst, Prod.snd, OptionT.lift, liftM, monadLift, MonadLift.monadLift] at hRest3
      obtain ⟨axioms, s6, hAxioms, hRest6⟩ := bind_inv hRest3
      simp [pure, OptionT.pure, OptionT.mk, StateT.pure] at hRest6
      have hF := Core.Decl.func.inj (Option.some.inj (Prod.mk.inj hRest6).1)
      simp only [hBodyCase] at hAxioms
      rw [← hF.1]; simp only [getPostconds', hBodyCase]
      exact generateFunctionAxioms_length proc postconds LMonoTy.int s3 s6 axioms hAxioms
    | External =>
      simp only [hBodyCase, pure, OptionT.pure, OptionT.mk, StateT.pure, StateT.bind, bind,
        OptionT.bind, Prod.fst, Prod.snd, OptionT.lift, liftM, monadLift, MonadLift.monadLift] at hRest3
      match hAx : generateFunctionAxioms proc [] LMonoTy.int s3 with
      | (some axioms, s6) =>
        rw [hAx] at hRest3; simp [StateT.pure] at hRest3
        have hF := Core.Decl.func.inj (Option.some.inj (Prod.mk.inj hRest3).1)
        rw [← hF.1]; simp only [getPostconds', hBodyCase]
        exact generateFunctionAxioms_length proc [] LMonoTy.int s3 s6 axioms hAx
      | (none, s6) =>
        rw [hAx] at hRest3; exact absurd (Prod.mk.inj hRest3).1 (by simp)

end ProofExplore
