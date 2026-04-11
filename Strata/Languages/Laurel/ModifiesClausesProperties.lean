/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Laurel.ModifiesClauses

/-!
# P-Frame-1: Modifies Clause Transformation Properties

Properties of the ModifiesClauses Laurel→Laurel pass (D21).
-/

namespace Strata.Laurel

/-! ## Identity properties: when the pass is a no-op -/

/-- transformModifiesClauses on External body is identity. -/
public theorem transformModifiesClauses_external (model : SemanticModel) (proc : Procedure)
    (hBody : proc.body = .External) :
    transformModifiesClauses model proc = .ok proc := by
  simp only [transformModifiesClauses]; rw [hBody]

/-- transformModifiesClauses on Transparent body is identity. -/
public theorem transformModifiesClauses_transparent (model : SemanticModel) (proc : Procedure)
    (bodyExpr : StmtExprMd) (postconds : List StmtExprMd)
    (hBody : proc.body = .Transparent bodyExpr postconds) :
    transformModifiesClauses model proc = .ok proc := by
  simp only [transformModifiesClauses]; rw [hBody]

/-- transformModifiesClauses on Abstract body is identity. -/
public theorem transformModifiesClauses_abstract (model : SemanticModel) (proc : Procedure)
    (postconds : List StmtExprMd)
    (hBody : proc.body = .Abstract postconds) :
    transformModifiesClauses model proc = .ok proc := by
  simp only [transformModifiesClauses]; rw [hBody]

/-- transformModifiesClauses on Opaque body without $heap output is identity. -/
public theorem transformModifiesClauses_opaque_noHeap (model : SemanticModel) (proc : Procedure)
    (postconds : List StmtExprMd) (impl : Option StmtExprMd) (modifies : List StmtExprMd)
    (hBody : proc.body = .Opaque postconds impl modifies)
    (hNoHeap : hasHeapOut proc = false) :
    transformModifiesClauses model proc = .ok proc := by
  simp only [transformModifiesClauses]; rw [hBody]; simp [hNoHeap]

/-! ## Structural properties: what changes when the pass fires -/

/-- transformModifiesClauses always succeeds (never returns .error). -/
public theorem transformModifiesClauses_always_ok (model : SemanticModel) (proc : Procedure) :
    ∃ proc', transformModifiesClauses model proc = .ok proc' := by
  simp only [transformModifiesClauses]
  cases proc.body with
  | External => exact ⟨proc, rfl⟩
  | Transparent _ _ => exact ⟨proc, rfl⟩
  | Abstract _ => exact ⟨proc, rfl⟩
  | Opaque postconds impl modifies =>
    cases hHeap : hasHeapOut proc with
    | false => exact ⟨proc, by simp [hHeap]⟩
    | true =>
      simp only [hHeap, ite_true]
      cases buildModifiesEnsures proc model modifies "$heap_in" "$heap" with
      | none => exact ⟨_, rfl⟩
      | some _ => exact ⟨_, rfl⟩

/-- transformModifiesClauses preserves procedure name. -/
public theorem transformModifiesClauses_preserves_name (model : SemanticModel) (proc proc' : Procedure)
    (h : transformModifiesClauses model proc = .ok proc') :
    proc'.name = proc.name := by
  simp only [transformModifiesClauses] at h
  cases hBody : proc.body with
  | External => rw [hBody] at h; simp at h; rw [← h]
  | Transparent _ _ => rw [hBody] at h; simp at h; rw [← h]
  | Abstract _ => rw [hBody] at h; simp at h; rw [← h]
  | Opaque postconds impl modifies =>
    rw [hBody] at h
    cases hHeap : hasHeapOut proc with
    | false => simp [hHeap] at h; rw [← h]
    | true =>
      simp only [hHeap, ite_true] at h
      cases buildModifiesEnsures proc model modifies "$heap_in" "$heap" with
      | none => simp at h; rw [← h]
      | some _ => simp at h; rw [← h]

/-- transformModifiesClauses preserves procedure inputs. -/
public theorem transformModifiesClauses_preserves_inputs (model : SemanticModel) (proc proc' : Procedure)
    (h : transformModifiesClauses model proc = .ok proc') :
    proc'.inputs = proc.inputs := by
  simp only [transformModifiesClauses] at h
  cases hBody : proc.body with
  | External => rw [hBody] at h; simp at h; rw [← h]
  | Transparent _ _ => rw [hBody] at h; simp at h; rw [← h]
  | Abstract _ => rw [hBody] at h; simp at h; rw [← h]
  | Opaque postconds impl modifies =>
    rw [hBody] at h
    cases hHeap : hasHeapOut proc with
    | false => simp [hHeap] at h; rw [← h]
    | true =>
      simp only [hHeap, ite_true] at h
      cases buildModifiesEnsures proc model modifies "$heap_in" "$heap" with
      | none => simp at h; rw [← h]
      | some _ => simp at h; rw [← h]

/-- transformModifiesClauses preserves procedure outputs. -/
public theorem transformModifiesClauses_preserves_outputs (model : SemanticModel) (proc proc' : Procedure)
    (h : transformModifiesClauses model proc = .ok proc') :
    proc'.outputs = proc.outputs := by
  simp only [transformModifiesClauses] at h
  cases hBody : proc.body with
  | External => rw [hBody] at h; simp at h; rw [← h]
  | Transparent _ _ => rw [hBody] at h; simp at h; rw [← h]
  | Abstract _ => rw [hBody] at h; simp at h; rw [← h]
  | Opaque postconds impl modifies =>
    rw [hBody] at h
    cases hHeap : hasHeapOut proc with
    | false => simp [hHeap] at h; rw [← h]
    | true =>
      simp only [hHeap, ite_true] at h
      cases buildModifiesEnsures proc model modifies "$heap_in" "$heap" with
      | none => simp at h; rw [← h]
      | some _ => simp at h; rw [← h]

/-- When the pass fires (Opaque + $heap + frame condition exists),
    postconditions are extended with the frame condition. -/
public theorem transformModifiesClauses_appends_frame (model : SemanticModel) (proc : Procedure)
    (postconds : List StmtExprMd) (impl : Option StmtExprMd) (modifies : List StmtExprMd)
    (frame : StmtExprMd)
    (hBody : proc.body = .Opaque postconds impl modifies)
    (hHeap : hasHeapOut proc = true)
    (hFrame : buildModifiesEnsures proc model modifies "$heap_in" "$heap" = some frame) :
    transformModifiesClauses model proc =
      .ok { proc with body := .Opaque (postconds ++ [frame]) impl [] } := by
  simp only [transformModifiesClauses]; rw [hBody]; simp [hHeap, hFrame]

/-- When the pass fires but buildModifiesEnsures returns none,
    postconditions are unchanged and modifies is cleared. -/
public theorem transformModifiesClauses_no_frame (model : SemanticModel) (proc : Procedure)
    (postconds : List StmtExprMd) (impl : Option StmtExprMd) (modifies : List StmtExprMd)
    (hBody : proc.body = .Opaque postconds impl modifies)
    (hHeap : hasHeapOut proc = true)
    (hNoFrame : buildModifiesEnsures proc model modifies "$heap_in" "$heap" = none) :
    transformModifiesClauses model proc =
      .ok { proc with body := .Opaque postconds impl [] } := by
  simp only [transformModifiesClauses]; rw [hBody]; simp [hHeap, hNoFrame]

/-- When the pass fires, modifies list is always cleared to []. -/
public theorem transformModifiesClauses_clears_modifies (model : SemanticModel) (proc : Procedure)
    (postconds : List StmtExprMd) (impl : Option StmtExprMd) (modifies : List StmtExprMd)
    (hBody : proc.body = .Opaque postconds impl modifies)
    (hHeap : hasHeapOut proc = true)
    (proc' : Procedure)
    (hOk : transformModifiesClauses model proc = .ok proc') :
    ∃ postconds', proc'.body = .Opaque postconds' impl [] := by
  simp only [transformModifiesClauses] at hOk; rw [hBody] at hOk
  simp only [hHeap, ite_true] at hOk
  cases hF : buildModifiesEnsures proc model modifies "$heap_in" "$heap" with
  | none => rw [hF] at hOk; simp at hOk; subst hOk; exact ⟨postconds, rfl⟩
  | some frame => rw [hF] at hOk; simp at hOk; subst hOk; exact ⟨postconds ++ [frame], rfl⟩

/-! ## conjoinAll properties -/

/-- conjoinAll on singleton list is identity. -/
public theorem conjoinAll_singleton (e : StmtExprMd) :
    conjoinAll [e] = e := by
  simp [conjoinAll]

/-- conjoinAll on empty list is LiteralBool true. -/
public theorem conjoinAll_nil :
    conjoinAll [] = mkMd (.LiteralBool true) := by
  simp [conjoinAll]

end Strata.Laurel
