/-
  Copyright Strata Contributors
  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

import Strata.Languages.Laurel.TranslatorModel
import Strata.Languages.Laurel.TranslatorModelProperties
import Strata.Languages.Laurel.LaurelToCoreTranslator

/-!
# Translator Equivalence

Structural theorems about `translateProgramModel` that build toward
proving `translate program = translateProgramModel program`.

## Strategy

Phase 1: Prove structural properties of the model's component functions.
Phase 2: Prove pass no-op lemmas for programs with no composites.
Phase 3: Prove `translateLaurelToCore = translateProgramModel` for simple programs.
-/

namespace Strata.Laurel

/-! ## Phase 1: Component function properties -/

/-- Every static non-external non-functional procedure has its name
    in expectedProcedureNames. -/
theorem static_proc_in_expected (program : Program)
  (proc : Procedure)
  (hMem : proc ∈ nonExternalStaticProcs program)
  (hNotFunc : proc.isFunctional = false) :
  proc.name.text ∈ expectedProcedureNames program := by
  unfold expectedProcedureNames
  have hneg : (!proc.isFunctional) = true := by rw [hNotFunc]; rfl
  have hFilter : proc ∈ (nonExternalStaticProcs program).filter (!·.isFunctional) :=
    List.mem_filter.mpr ⟨hMem, hneg⟩
  have hMap : proc.name.text ∈ ((nonExternalStaticProcs program).filter (!·.isFunctional)).map (·.name.text) :=
    List.mem_map.mpr ⟨proc, hFilter, rfl⟩
  simp_all [List.mem_append]

/-- Every static non-external functional procedure has its name
    in expectedFunctionNames. -/
theorem static_func_in_expected (program : Program)
  (proc : Procedure)
  (hMem : proc ∈ nonExternalStaticProcs program)
  (hFunc : proc.isFunctional = true) :
  proc.name.text ∈ expectedFunctionNames program := by
  unfold expectedFunctionNames
  have hFilter : proc ∈ (nonExternalStaticProcs program).filter (·.isFunctional) :=
    List.mem_filter.mpr ⟨hMem, hFunc⟩
  have hMap : proc.name.text ∈ ((nonExternalStaticProcs program).filter (·.isFunctional)).map (·.name.text) :=
    List.mem_map.mpr ⟨proc, hFilter, rfl⟩
  simp_all [List.mem_append]

/-! ## Phase 2: No-composite simplification lemmas -/

/-- Programs with no composites have empty allComposites. -/
theorem no_composites_means_empty (program : Program)
  (h : program.types.all (fun td => match td with | .Composite _ => false | _ => true) = true) :
  allComposites program = [] := by
  unfold allComposites
  rw [List.filterMap_eq_nil_iff]
  intro td htd
  have := List.all_eq_true.mp h td htd
  cases td <;> simp_all

/-- If allComposites is empty, nonExternalInstanceProcs is empty. -/
theorem no_composites_no_instance_procs (program : Program)
  (h : allComposites program = []) :
  nonExternalInstanceProcs program = [] := by
  unfold nonExternalInstanceProcs
  simp [h]

/-- If allComposites is empty, allFields is empty. -/
theorem no_composites_no_fields (program : Program)
  (h : allComposites program = []) :
  allFields program = [] := by
  unfold allFields
  simp [h]

/-- If allComposites is empty, no read axioms are generated. -/
theorem no_composites_no_axioms (program : Program)
  (h : allComposites program = []) :
  expectedAxiomNames program = [] := by
  unfold expectedAxiomNames
  have hFields := no_composites_no_fields program h
  -- allFields is empty, so hasIntField is false
  -- The `any` on an empty list returns false
  simp [allFields, h]

/-- For no-composite programs, expectedProcedureNames has no instance proc names. -/
theorem no_composites_proc_names_no_instance (program : Program)
  (h : allComposites program = []) :
  let instanceProcs := nonExternalInstanceProcs program
  let instanceProcNames := (instanceProcs.filter (!·.2.isFunctional)).map
    fun (typeName, proc) => qualifiedName typeName proc.name.text
  instanceProcNames = [] := by
  have hNoInst := no_composites_no_instance_procs program h
  simp [hNoInst]

/-- For no-composite programs, expectedFunctionNames has no instance func names
    and no ancestor function names. -/
theorem no_composites_func_names_no_instance (program : Program)
  (h : allComposites program = []) :
  let instanceFuncs := nonExternalInstanceProcs program
  let instanceFuncNames := (instanceFuncs.filter (·.2.isFunctional)).map
    fun (typeName, proc) => qualifiedName typeName proc.name.text
  instanceFuncNames = [] := by
  have hNoInst := no_composites_no_instance_procs program h
  simp [hNoInst]

/-- For no-composite programs, there are no ancestor functions. -/
theorem no_composites_no_ancestor_names (program : Program)
  (h : allComposites program = []) :
  (allComposites program).map (fun ct => "ancestorsFor" ++ ct.name.text) = [] := by
  simp [h]

/-! ## Phase 2b: Heap analysis properties -/

/-- FieldSelect reads the heap. -/
theorem fieldSelect_reads_heap (target : WithMetadata StmtExpr) (field : Identifier) :
  directlyReadsHeap (.FieldSelect target field) = true :=
  directlyReadsHeap_eq_fieldSelect target field

/-- New writes the heap. -/
theorem new_writes_heap (name : Identifier) :
  directlyWritesHeap (.New name) = true :=
  directlyWritesHeap_eq_new name

/-- Literals don't read the heap. -/
theorem literal_no_read (b : Bool) : directlyReadsHeap (.LiteralBool b) = false :=
  directlyReadsHeap_eq_literalBool b

/-- Literals don't write the heap. -/
theorem literal_no_write (b : Bool) : directlyWritesHeap (.LiteralBool b) = false :=
  directlyWritesHeap_eq_literalBool b

/-- Identifiers don't read the heap. -/
theorem identifier_no_read (n : Identifier) : directlyReadsHeap (.Identifier n) = false :=
  directlyReadsHeap_eq_identifier n

/-- Identifiers don't write the heap. -/
theorem identifier_no_write (n : Identifier) : directlyWritesHeap (.Identifier n) = false :=
  directlyWritesHeap_eq_identifier n

/-! ## Phase 2c: Expression translation equation lemmas -/

theorem expr_model_bool (b : Bool) :
  translateExprModel (.LiteralBool b) = .const () (.boolConst b) :=
  translateExprModel_eq_literalBool b

theorem expr_model_int (i : Int) :
  translateExprModel (.LiteralInt i) = .const () (.intConst i) :=
  translateExprModel_eq_literalInt i

theorem expr_model_string (s : String) :
  translateExprModel (.LiteralString s) = .const () (.strConst s) :=
  translateExprModel_eq_literalString s

theorem expr_model_identifier (name : Identifier) :
  translateExprModel (.Identifier name) = .fvar () ⟨name.text, ()⟩ none :=
  translateExprModel_eq_identifier name

/-! ## Phase 3 foundation: Statement translation equation lemmas -/

theorem stmt_model_return_none (isFunction : String → Bool) (outputParams : List String) :
  translateStmtModel isFunction outputParams (.Return none) =
    [Imperative.Stmt.exit (some "$body") .empty] :=
  translateStmtModel_eq_return_none isFunction outputParams

theorem stmt_model_local_no_init
  (isFunction : String → Bool) (outputParams : List String)
  (id : Identifier) (ty : WithMetadata HighType) :
  translateStmtModel isFunction outputParams (.LocalVariable id ty none) =
    [Core.Statement.init ⟨id.text, ()⟩ (.forAll [] (.tcons "int" [])) none .empty] :=
  translateStmtModel_eq_local_no_init isFunction outputParams id ty

/-! ## Phase 3: Real equivalence proofs

These theorems prove that the model's translation functions produce
the same output as the real translator's functions for specific cases.

The real translator uses `TranslateM` (= `OptionT (StateM TranslateState)`).
For leaf expressions, `translateExpr` returns `pure expr` without touching
the state, so we can extract the result and compare it to the model. -/

/-- For literal bool, the real translator succeeds and produces the same
    expression as the model. This is the first proven connection between
    the model and the real translator. -/
theorem model_matches_real_literalBool (b : Bool) (s : TranslateState) :
  (translateExpr ⟨.LiteralBool b, .empty⟩ [] false s).1 = some (translateExprModel (.LiteralBool b)) := by
  rw [translateExpr_eq_literalBool, translateExprModel_eq_literalBool]

theorem model_matches_real_literalInt (i : Int) (s : TranslateState) :
  (translateExpr ⟨.LiteralInt i, .empty⟩ [] false s).1 = some (translateExprModel (.LiteralInt i)) := by
  rw [translateExpr_eq_literalInt, translateExprModel_eq_literalInt]

theorem model_matches_real_literalString (str : String) (s : TranslateState) :
  (translateExpr ⟨.LiteralString str, .empty⟩ [] false s).1 = some (translateExprModel (.LiteralString str)) := by
  rw [translateExpr_eq_literalString, translateExprModel_eq_literalString]

/-- The real translator preserves state for literal bool. -/
theorem translateExpr_literalBool_preserves_state (b : Bool) (s : TranslateState) :
  (translateExpr ⟨.LiteralBool b, .empty⟩ [] false s).2 = s := by
  rw [translateExpr_eq_literalBool]

/-- The real translator preserves state for literal int. -/
theorem translateExpr_literalInt_preserves_state (i : Int) (s : TranslateState) :
  (translateExpr ⟨.LiteralInt i, .empty⟩ [] false s).2 = s := by
  rw [translateExpr_eq_literalInt]

/-- The real translator preserves state for literal string. -/
theorem translateExpr_literalString_preserves_state (str : String) (s : TranslateState) :
  (translateExpr ⟨.LiteralString str, .empty⟩ [] false s).2 = s := by
  rw [translateExpr_eq_literalString]

/-- The real translator always succeeds for literal bool. -/
theorem translateExpr_literalBool_succeeds (b : Bool) (s : TranslateState) :
  (translateExpr ⟨.LiteralBool b, .empty⟩ [] false s).1.isSome = true := by
  rw [translateExpr_eq_literalBool]; rfl

/-- The real translator always succeeds for literal int. -/
theorem translateExpr_literalInt_succeeds (i : Int) (s : TranslateState) :
  (translateExpr ⟨.LiteralInt i, .empty⟩ [] false s).1.isSome = true := by
  rw [translateExpr_eq_literalInt]; rfl

/-- The real translator always succeeds for literal string. -/
theorem translateExpr_literalString_succeeds (str : String) (s : TranslateState) :
  (translateExpr ⟨.LiteralString str, .empty⟩ [] false s).1.isSome = true := by
  rw [translateExpr_eq_literalString]; rfl

/-! ## Equivalence summary

We have proven that for literal expressions (Bool, Int, String):
1. The real translator succeeds (returns `some`)
2. The real translator preserves state (no side effects)
3. The real translator produces the same Core expression as the model

These are the base cases for an inductive proof that
`translateExprModel expr = (translateExpr expr s).1.get!`
for all supported expressions. The inductive step requires
equation lemmas for compound cases (PrimitiveOp, IfThenElse, etc.)
which are blocked on monadic bind reduction in OptionT (StateM S).

The path forward: add a general lemma in LaurelToCoreTranslator.lean
that factors out the `do` preamble (get/model/md/disallowed), enabling
compound case equation lemmas.
-/

end Strata.Laurel
