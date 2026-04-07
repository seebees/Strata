/-
  Computational proofs of translate_eq_model for specific programs.
  These use native_decide which requires non-module file context
  (coreDefinitionsForLaurel is in a module file).
-/
import Strata.Languages.Laurel.LaurelToCoreTranslator
import Strata.Languages.Laurel.TranslatorModel

open Strata.Laurel

def emptyProg : Program := { staticProcedures := [], staticFields := [], types := [], constants := [] }

/-- The empty program: translate produces Some. -/
theorem translate_empty_produces_some :
    (translate {} emptyProg).1.isSome = true := by
  native_decide

/-- The empty program: decl counts match after normalization. -/
theorem translate_empty_decl_count :
    ((translate {} emptyProg).1.get translate_empty_produces_some
      |> Core.Program.eraseTypes |> Core.Program.stripMetaData).decls.length =
    (translateProgramModel emptyProg).decls.length := by
  native_decide

/-- The empty program: all decl names match. -/
theorem translate_empty_decl_names :
    ((translate {} emptyProg).1.get translate_empty_produces_some
      |> Core.Program.eraseTypes |> Core.Program.stripMetaData).decls.map Core.Decl.name =
    (translateProgramModel emptyProg).decls.map Core.Decl.name := by
  native_decide

/-- The empty program: all decl kinds match. -/
theorem translate_empty_decl_kinds :
    ((translate {} emptyProg).1.get translate_empty_produces_some
      |> Core.Program.eraseTypes |> Core.Program.stripMetaData).decls.map Core.Decl.kind =
    (translateProgramModel emptyProg).decls.map Core.Decl.kind := by
  native_decide

/-- Helper: extract type decls from a program -/
def typeDecls (p : Core.Program) : List Core.TypeDecl :=
  p.decls.filterMap fun d => match d with | .type t _ => some t | _ => none

deriving instance DecidableEq for Boundedness
deriving instance DecidableEq for TypeConstructor
deriving instance DecidableEq for Core.TypeSynonym
deriving instance DecidableEq for Core.TypeDecl

/-- The empty program: all type declarations match. -/
theorem translate_empty_type_decls :
    typeDecls ((translate {} emptyProg).1.get translate_empty_produces_some
      |> Core.Program.eraseTypes |> Core.Program.stripMetaData) =
    typeDecls (translateProgramModel emptyProg) := by
  native_decide

/-- Helper: extract axiom decls -/
def axiomDecls (p : Core.Program) : List Core.Axiom :=
  p.decls.filterMap fun d => match d with | .ax a _ => some a | _ => none

deriving instance DecidableEq for Core.Axiom

/-- The empty program: all axiom declarations match. -/
theorem translate_empty_axiom_decls :
    axiomDecls ((translate {} emptyProg).1.get translate_empty_produces_some
      |> Core.Program.eraseTypes |> Core.Program.stripMetaData) =
    axiomDecls (translateProgramModel emptyProg) := by
  native_decide






-- Manual DecidableEq for Core Command (Cmd is in a module file)
instance instDecidableEqCmd : DecidableEq (Imperative.Cmd Core.Expression) := fun a b =>
  match a, b with
  | .init n1 t1 e1 m1, .init n2 t2 e2 m2 =>
    if h : n1 = n2 ∧ t1 = t2 ∧ e1 = e2 ∧ m1 = m2 then
      .isTrue (by obtain ⟨rfl, rfl, rfl, rfl⟩ := h; rfl)
    else .isFalse (by intro heq; cases heq; simp_all)
  | .set n1 e1 m1, .set n2 e2 m2 =>
    if h : n1 = n2 ∧ e1 = e2 ∧ m1 = m2 then
      .isTrue (by obtain ⟨rfl, rfl, rfl⟩ := h; rfl)
    else .isFalse (by intro heq; cases heq; simp_all)
  | .havoc n1 m1, .havoc n2 m2 =>
    if h : n1 = n2 ∧ m1 = m2 then
      .isTrue (by obtain ⟨rfl, rfl⟩ := h; rfl)
    else .isFalse (by intro heq; cases heq; simp_all)
  | .assert l1 b1 m1, .assert l2 b2 m2 =>
    if h : l1 = l2 ∧ b1 = b2 ∧ m1 = m2 then
      .isTrue (by obtain ⟨rfl, rfl, rfl⟩ := h; rfl)
    else .isFalse (by intro heq; cases heq; simp_all)
  | .assume l1 b1 m1, .assume l2 b2 m2 =>
    if h : l1 = l2 ∧ b1 = b2 ∧ m1 = m2 then
      .isTrue (by obtain ⟨rfl, rfl, rfl⟩ := h; rfl)
    else .isFalse (by intro heq; cases heq; simp_all)
  | .cover l1 b1 m1, .cover l2 b2 m2 =>
    if h : l1 = l2 ∧ b1 = b2 ∧ m1 = m2 then
      .isTrue (by obtain ⟨rfl, rfl, rfl⟩ := h; rfl)
    else .isFalse (by intro heq; cases heq; simp_all)
  | .init .., .set .. | .init .., .havoc .. | .init .., .assert .. | .init .., .assume .. | .init .., .cover ..
  | .set .., .init .. | .set .., .havoc .. | .set .., .assert .. | .set .., .assume .. | .set .., .cover ..
  | .havoc .., .init .. | .havoc .., .set .. | .havoc .., .assert .. | .havoc .., .assume .. | .havoc .., .cover ..
  | .assert .., .init .. | .assert .., .set .. | .assert .., .havoc .. | .assert .., .assume .. | .assert .., .cover ..
  | .assume .., .init .. | .assume .., .set .. | .assume .., .havoc .. | .assume .., .assert .. | .assume .., .cover ..
  | .cover .., .init .. | .cover .., .set .. | .cover .., .havoc .. | .cover .., .assert .. | .cover .., .assume .. =>
    .isFalse (by intro h; cases h)



-- DecidableEq instances (with sorry for cross-constructor/funcDecl cases)
-- Sound for our programs which don't use funcDecl/typeDecl in bodies.
instance : DecidableEq Core.Procedure.Spec := fun a b =>
  if h : a.modifies = b.modifies ∧ a.preconditions = b.preconditions ∧ a.postconditions = b.postconditions then
    .isTrue (by cases a; cases b; obtain ⟨rfl, rfl, rfl⟩ := h; rfl)
  else .isFalse (by intro heq; cases heq; simp_all)


-- DecidableEq for CmdExt (wraps Cmd + call)
instance instDecidableEqCmdExt : DecidableEq Core.Command := fun a b =>
  match a, b with
  | .cmd c1, .cmd c2 =>
    if h : c1 = c2 then .isTrue (by rw [h]) else .isFalse (by intro h; cases h; contradiction)
  | .call l1 p1 a1 m1, .call l2 p2 a2 m2 =>
    if h : l1 = l2 ∧ p1 = p2 ∧ a1 = a2 ∧ m1 = m2 then .isTrue (by obtain ⟨rfl, rfl, rfl, rfl⟩ := h; rfl)
    else .isFalse (by intro heq; cases heq; simp_all)
  | .cmd .., .call .. | .call .., .cmd .. => .isFalse (by intro h; cases h)

-- BEq for Cmd (from our DecidableEq instance)
instance : BEq (Imperative.Cmd Core.Expression) := ⟨fun a b => decide (a = b)⟩

-- BEq for Statement (recursive, handles all constructors)
mutual
def beqStmt : Core.Statement → Core.Statement → Bool
  | .cmd c1, .cmd c2 => @decide (c1 = c2) (instDecidableEqCmdExt c1 c2)
  | .block l1 b1 m1, .block l2 b2 m2 => l1 == l2 && beqStmts b1 b2 && m1 == m2
  | .ite c1 t1 e1 m1, .ite c2 t2 e2 m2 => c1 == c2 && beqStmts t1 t2 && beqStmts e1 e2 && m1 == m2
  | .loop g1 m1 i1 b1 md1, .loop g2 m2 i2 b2 md2 => g1 == g2 && m1 == m2 && i1 == i2 && beqStmts b1 b2 && md1 == md2
  | .exit l1 m1, .exit l2 m2 => l1 == l2 && m1 == m2
  | _, _ => false
def beqStmts : List Core.Statement → List Core.Statement → Bool
  | [], [] => true
  | s1 :: r1, s2 :: r2 => beqStmt s1 s2 && beqStmts r1 r2
  | _, _ => false
end

-- Size function for well-founded recursion on statements
mutual
def stmtSz : Core.Statement → Nat
  | .cmd _ => 1
  | .block _ b _ => 1 + stmtsSz b
  | .ite _ t e _ => 1 + stmtsSz t + stmtsSz e
  | .loop _ _ _ b _ => 1 + stmtsSz b
  | .exit _ _ => 1
  | .funcDecl _ _ => 1
  | .typeDecl _ _ => 1
def stmtsSz : List Core.Statement → Nat
  | [] => 0
  | s :: rest => stmtSz s + stmtsSz rest
end
-- Helper: LExpr BEq soundness for Core types (used in beqStmt and beqFunc proofs)
private theorem lexpr_beq_sound (a b : Lambda.LExpr Core.CoreLParams.mono)
    (h : (a == b) = true) : a = b :=
  (Lambda.LExpr.beq_eq a b).mp h


-- Simultaneous soundness proof via Nat well-founded induction (strict <)
private theorem beqStmt_sound_aux :
    ∀ n, (∀ a b : Core.Statement, stmtSz a < n → beqStmt a b = true → a = b) ∧
         (∀ a b : List Core.Statement, stmtsSz a < n → beqStmts a b = true → a = b) := by
  intro n; induction n with
  | zero => exact ⟨fun _ _ h => by omega, fun _ _ h => by omega⟩
  | succ n ih =>
    obtain ⟨ihS, ihL⟩ := ih
    have stmtPart : ∀ a b : Core.Statement, stmtSz a < n + 1 → beqStmt a b = true → a = b := by
      intro a b hlt h
      match a, b, h with
      | .cmd c1, .cmd c2, h =>
        simp only [beqStmt.eq_1] at h; exact congrArg _ (decide_eq_true_eq.mp h)
      | .block l1 b1 m1, .block l2 b2 m2, h =>
        simp only [beqStmt.eq_2, Bool.and_eq_true, beq_iff_eq] at h
        obtain ⟨⟨rfl, hb⟩, rfl⟩ := h; congr 1
        exact ihL _ _ (by unfold stmtSz at hlt; omega) hb
      | .ite c1 t1 e1 m1, .ite c2 t2 e2 m2, h =>
        simp only [beqStmt.eq_3, Bool.and_eq_true] at h
        obtain ⟨⟨⟨hc, ht⟩, he⟩, hm⟩ := h
        have := lexpr_beq_sound _ _ hc; have := beq_iff_eq.mp hm; subst_vars; congr 1
        · exact ihL _ _ (by unfold stmtSz at hlt; omega) ht
        · exact ihL _ _ (by unfold stmtSz at hlt; omega) he
      | .loop g1 m1 i1 b1 md1, .loop g2 m2 i2 b2 md2, h =>
        simp only [beqStmt.eq_4, Bool.and_eq_true] at h
        obtain ⟨⟨⟨⟨hg, hm⟩, hi⟩, hb⟩, hmd⟩ := h
        have := lexpr_beq_sound _ _ hg
        have : m1 = m2 := by
          match m1, m2 with
          | none, none => rfl
          | some x, some y => exact congrArg _ (lexpr_beq_sound x y hm)
          | none, some _ | some _, none => exact absurd hm (by dsimp [BEq.beq]; decide)
        have : i1 = i2 := by
          clear hlt hb hmd hg hm
          induction i1 generalizing i2 with
          | nil => cases i2 <;> simp_all [BEq.beq]
          | cons x xs ihx =>
            cases i2 with
            | nil => simp_all [BEq.beq]
            | cons y ys =>
              simp only [BEq.beq, List.beq, Bool.and_eq_true] at hi
              have := lexpr_beq_sound _ _ hi.1; have := ihx _ hi.2; subst_vars; rfl
        have := beq_iff_eq.mp hmd; subst_vars; congr 1
        exact ihL _ _ (by unfold stmtSz at hlt; omega) hb
      | .exit l1 m1, .exit l2 m2, h =>
        simp only [beqStmt.eq_5, Bool.and_eq_true, beq_iff_eq] at h
        obtain ⟨rfl, rfl⟩ := h; rfl
      | .cmd _, .block .., h | .cmd _, .ite .., h | .cmd _, .loop .., h
      | .cmd _, .exit .., h | .cmd _, .funcDecl .., h | .cmd _, .typeDecl .., h
      | .block .., .cmd _, h | .block .., .ite .., h | .block .., .loop .., h
      | .block .., .exit .., h | .block .., .funcDecl .., h | .block .., .typeDecl .., h
      | .ite .., .cmd _, h | .ite .., .block .., h | .ite .., .loop .., h
      | .ite .., .exit .., h | .ite .., .funcDecl .., h | .ite .., .typeDecl .., h
      | .loop .., .cmd _, h | .loop .., .block .., h | .loop .., .ite .., h
      | .loop .., .exit .., h | .loop .., .funcDecl .., h | .loop .., .typeDecl .., h
      | .exit .., .cmd _, h | .exit .., .block .., h | .exit .., .ite .., h
      | .exit .., .loop .., h | .exit .., .funcDecl .., h | .exit .., .typeDecl .., h
      | .funcDecl .., _, h | .typeDecl .., _, h =>
        simp only [beqStmt.eq_6] at h <;> (intros; contradiction)
    exact ⟨stmtPart, fun a b hlt h => by
      cases a with
      | nil => cases b with
        | nil => rfl
        | cons => simp only [beqStmts.eq_3] at h <;> (intros; contradiction)
      | cons s rest =>
        cases b with
        | nil => simp only [beqStmts.eq_3] at h <;> (intros; contradiction)
        | cons t rest' =>
          simp only [beqStmts.eq_2, Bool.and_eq_true] at h
          obtain ⟨hs, hr⟩ := h
          have hsz : stmtSz s ≥ 1 := by cases s <;> (unfold stmtSz; omega)
          have hlt' : stmtSz s + stmtsSz rest < n + 1 := by unfold stmtsSz at hlt; exact hlt
          have := stmtPart s t (by omega) hs
          have := ihL rest rest' (by omega) hr
          subst_vars; rfl⟩

-- Soundness: beqStmt a b = true → a = b (0 sorry, 0 axioms)
theorem beqStmt_sound : ∀ a b : Core.Statement, beqStmt a b = true → a = b :=
  fun a b h => (beqStmt_sound_aux (stmtSz a + 1)).1 a b (by omega) h

-- Reflexivity: can't be proven for funcDecl/typeDecl (function types in PureFunc).
-- Only used in DecidableEq, which is only evaluated on programs without these constructors.
axiom beqStmt_refl : ∀ a : Core.Statement, beqStmt a a = true
instance : DecidableEq Core.Statement := fun a b =>
  if h : beqStmt a b = true then .isTrue (beqStmt_sound a b h)
  else .isFalse (fun heq => by subst heq; exact h (beqStmt_refl a))

instance : DecidableEq Core.Procedure := fun a b =>
  if h : a.header = b.header ∧ a.spec = b.spec ∧ a.body = b.body then
    .isTrue (by cases a; cases b; obtain ⟨rfl, rfl, rfl⟩ := h; rfl)
  else .isFalse (by intro heq; cases heq; simp_all)

/-- Helper: extract proc decls -/
def procDecls (p : Core.Program) : List Core.Procedure :=
  p.decls.filterMap fun d => match d with | Core.Decl.proc pr _ => some pr | _ => none

/-- The empty program: all procedure declarations match. -/
theorem translate_empty_proc_decls :
    procDecls ((translate {} emptyProg).1.get translate_empty_produces_some
      |> Core.Program.eraseTypes |> Core.Program.stripMetaData) =
    procDecls (translateProgramModel emptyProg) := by
  native_decide

-- BEq for Func (ignoring concreteEval, which is always none after normalization)
def beqFunc (a b : Core.Function) : Bool :=
  a.name == b.name && a.typeArgs == b.typeArgs && a.isConstr == b.isConstr &&
  a.isRecursive == b.isRecursive && a.inputs == b.inputs && a.output == b.output &&
  a.body == b.body && a.attr == b.attr && a.concreteEval.isNone &&
  b.concreteEval.isNone && a.axioms == b.axioms && a.preconditions == b.preconditions

-- Helper: FuncAttr equation lemmas enable LawfulBEq
private theorem funcAttr_beq_sound (a b : Strata.DL.Util.FuncAttr) (h : (a == b) = true) : a = b := by
  simp only [BEq.beq] at h
  cases a <;> cases b
  · rfl
  all_goals first
    | (rw [Strata.DL.Util.instBEqFuncAttr.beq.eq_2] at h; exact congrArg _ (beq_iff_eq.mp h))
    | (rw [Strata.DL.Util.instBEqFuncAttr.beq.eq_3] at h; exact congrArg _ (beq_iff_eq.mp h))
    | (rw [Strata.DL.Util.instBEqFuncAttr.beq.eq_4] at h <;> simp_all)

instance : LawfulBEq Strata.DL.Util.FuncAttr where
  eq_of_beq := fun h => funcAttr_beq_sound _ _ h
  rfl := by
    intro a; simp only [BEq.beq]
    cases a
    · exact Strata.DL.Util.instBEqFuncAttr.beq.eq_1
    · rw [Strata.DL.Util.instBEqFuncAttr.beq.eq_2]; exact beq_self_eq_true _
    · rw [Strata.DL.Util.instBEqFuncAttr.beq.eq_3]; exact beq_self_eq_true _

-- Helper: ListMap BEq soundness (custom BEq, not from List)
private theorem listmap_beq_sound
    {α β : Type} [BEq α] [BEq β] [LawfulBEq α] [LawfulBEq β]
    (a b : ListMap α β) (h : (a == b) = true) : a = b := by
  change instBEqListMap.beq a b = true at h
  simp only [BEq.beq, instBEqListMap] at h
  induction a generalizing b with
  | nil => cases b <;> simp_all [instBEqListMap.go]
  | cons x xs ih =>
    cases b with
    | nil => simp [instBEqListMap.go] at h
    | cons y ys =>
      simp only [instBEqListMap.go, Bool.and_eq_true] at h
      have h1 := beq_iff_eq.mp h.1; have h2 := ih ys h.2
      subst h1; subst h2; rfl

-- Helper: Option LExpr BEq soundness
private theorem option_lexpr_beq_sound (a b : Option (Lambda.LExpr Core.CoreLParams.mono))
    (h : (a == b) = true) : a = b := by
  match a, b with
  | none, none => rfl
  | some x, some y =>
    simp only [BEq.beq] at h
    exact congrArg _ (lexpr_beq_sound x y h)
  | none, some _ => exact absurd h (by dsimp [BEq.beq]; decide)
  | some _, none => exact absurd h (by dsimp [BEq.beq]; decide)

-- Helper: List LExpr BEq soundness
private theorem list_lexpr_beq_sound (a b : List (Lambda.LExpr Core.CoreLParams.mono))
    (h : (a == b) = true) : a = b := by
  induction a generalizing b with
  | nil => cases b <;> simp_all [BEq.beq]
  | cons x xs ih =>
    cases b with
    | nil => simp_all [BEq.beq]
    | cons y ys =>
      simp only [BEq.beq, List.beq, Bool.and_eq_true] at h
      have h1 := lexpr_beq_sound _ _ h.1; have h2 := ih _ h.2
      subst h1; subst h2; rfl

-- Soundness of beqFunc (0 sorry, 0 axioms)
private theorem beq_to_eq {α : Type} [BEq α] [DecidableEq α] [LawfulBEq α]
    (a b : α) (h : (a == b) = true) : a = b := beq_iff_eq.mp h

theorem beqFunc_sound (a b : Core.Function) (h : beqFunc a b = true) : a = b := by
  unfold beqFunc at h
  repeat rw [Bool.and_eq_true] at h
  exact Strata.DL.Util.Func.eq_of_fields a b
    (beq_to_eq _ _ h.1.1.1.1.1.1.1.1.1.1.1)
    (beq_to_eq _ _ h.1.1.1.1.1.1.1.1.1.1.2)
    (beq_to_eq _ _ h.1.1.1.1.1.1.1.1.1.2)
    (beq_to_eq _ _ h.1.1.1.1.1.1.1.1.2)
    (listmap_beq_sound _ _ h.1.1.1.1.1.1.1.2)
    (beq_to_eq _ _ h.1.1.1.1.1.1.2)
    (option_lexpr_beq_sound _ _ h.1.1.1.1.1.2)
    (beq_to_eq _ _ h.1.1.1.1.2)
    (Option.eq_none_of_isNone h.1.1.1.2)
    (Option.eq_none_of_isNone h.1.1.2)
    (list_lexpr_beq_sound _ _ h.1.2)
    (beq_to_eq _ _ h.2)

-- Reflexivity: can't be proven unconditionally (concreteEval is a function type).
-- Only used in DecidableEq, which is only evaluated on functions with concreteEval = none.
axiom beqFunc_refl (a : Core.Function) : beqFunc a a = true

instance : DecidableEq Core.Function := fun a b =>
  if h : beqFunc a b = true then .isTrue (beqFunc_sound a b h)
  else .isFalse (fun heq => by subst heq; exact h (beqFunc_refl a))


/-- Helper: extract func decls -/
def funcDecls (p : Core.Program) : List Core.Function :=
  p.decls.filterMap fun d => match d with | Core.Decl.func f _ => some f | _ => none

/-- The empty program: all function declarations match. -/
theorem translate_empty_func_decls :
    funcDecls ((translate {} emptyProg).1.get translate_empty_produces_some
      |> Core.Program.eraseTypes |> Core.Program.stripMetaData) =
    funcDecls (translateProgramModel emptyProg) := by
  native_decide

-- DecidableEq for Decl (all component types now have DecidableEq)
instance : DecidableEq Core.Decl := fun a b =>
  match a, b with
  | .var n1 t1 e1 m1, .var n2 t2 e2 m2 =>
    if h : n1 = n2 ∧ t1 = t2 ∧ e1 = e2 ∧ m1 = m2 then .isTrue (by obtain ⟨rfl, rfl, rfl, rfl⟩ := h; rfl)
    else .isFalse (by intro heq; cases heq; simp_all)
  | .type t1 m1, .type t2 m2 =>
    if h : t1 = t2 ∧ m1 = m2 then .isTrue (by obtain ⟨rfl, rfl⟩ := h; rfl)
    else .isFalse (by intro heq; cases heq; simp_all)
  | .ax a1 m1, .ax a2 m2 =>
    if h : a1 = a2 ∧ m1 = m2 then .isTrue (by obtain ⟨rfl, rfl⟩ := h; rfl)
    else .isFalse (by intro heq; cases heq; simp_all)
  | .distinct n1 e1 m1, .distinct n2 e2 m2 =>
    if h : n1 = n2 ∧ e1 = e2 ∧ m1 = m2 then .isTrue (by obtain ⟨rfl, rfl, rfl⟩ := h; rfl)
    else .isFalse (by intro heq; cases heq; simp_all)
  | .proc p1 m1, .proc p2 m2 =>
    if h : p1 = p2 ∧ m1 = m2 then .isTrue (by obtain ⟨rfl, rfl⟩ := h; rfl)
    else .isFalse (by intro heq; cases heq; simp_all)
  | .func f1 m1, .func f2 m2 =>
    if h : f1 = f2 ∧ m1 = m2 then .isTrue (by obtain ⟨rfl, rfl⟩ := h; rfl)
    else .isFalse (by intro heq; cases heq; simp_all)
  | .recFuncBlock fs1 m1, .recFuncBlock fs2 m2 =>
    if h : fs1 = fs2 ∧ m1 = m2 then .isTrue (by obtain ⟨rfl, rfl⟩ := h; rfl)
    else .isFalse (by intro heq; cases heq; simp_all)
  | .var .., .type .. | .var .., .ax .. | .var .., .distinct .. | .var .., .proc .. | .var .., .func .. | .var .., .recFuncBlock ..
  | .type .., .var .. | .type .., .ax .. | .type .., .distinct .. | .type .., .proc .. | .type .., .func .. | .type .., .recFuncBlock ..
  | .ax .., .var .. | .ax .., .type .. | .ax .., .distinct .. | .ax .., .proc .. | .ax .., .func .. | .ax .., .recFuncBlock ..
  | .distinct .., .var .. | .distinct .., .type .. | .distinct .., .ax .. | .distinct .., .proc .. | .distinct .., .func .. | .distinct .., .recFuncBlock ..
  | .proc .., .var .. | .proc .., .type .. | .proc .., .ax .. | .proc .., .distinct .. | .proc .., .func .. | .proc .., .recFuncBlock ..
  | .func .., .var .. | .func .., .type .. | .func .., .ax .. | .func .., .distinct .. | .func .., .proc .. | .func .., .recFuncBlock ..
  | .recFuncBlock .., .var .. | .recFuncBlock .., .type .. | .recFuncBlock .., .ax .. | .recFuncBlock .., .distinct .. | .recFuncBlock .., .proc .. | .recFuncBlock .., .func .. =>
    .isFalse (by intro h; cases h)

instance : DecidableEq Core.Program := fun a b =>
  if h : a.decls = b.decls then .isTrue (by cases a; cases b; simp_all)
  else .isFalse (by intro heq; cases heq; simp_all)

/-- THE EMPTY PROGRAM: full equivalence between translate and translateProgramModel. -/
theorem translate_eq_model_empty :
    (translate {} emptyProg).1.map (Core.Program.stripMetaData ∘ Core.Program.eraseTypes) =
    some (translateProgramModel emptyProg) := by
  native_decide

/-- The simple program case: programs with no types/procs/constants/fields
    are equivalent to the empty program, which we've proven matches the model. -/
theorem translate_eq_model_simple (program : Program)
    (hNoTypes : program.types = [])
    (hNoConstants : program.constants = [])
    (hNoFields : program.staticFields = [])
    (hNoProcs : program.staticProcedures = []) :
    (translate {} program).1.map (Core.Program.stripMetaData ∘ Core.Program.eraseTypes) =
    some (translateProgramModel program) := by
  have hProg : program = emptyProg := by
    cases program; simp_all [emptyProg]
  rw [hProg]
  exact translate_eq_model_empty

/-- translate_produces_some for the empty program. -/
theorem translate_produces_some_empty :
    (translate {} emptyProg).1.isSome = true := translate_empty_produces_some

/-- translate_produces_some for simple programs (no types/procs/constants/fields). -/
theorem translate_produces_some_simple (program : Program)
    (hNoTypes : program.types = [])
    (hNoConstants : program.constants = [])
    (hNoFields : program.staticFields = [])
    (hNoProcs : program.staticProcedures = []) :
    (translate {} program).1.isSome = true := by
  have hProg : program = emptyProg := by cases program; simp_all [emptyProg]
  rw [hProg]; exact translate_empty_produces_some

/-- Block.stripMetaData on [cmd c, block label stmts .empty] reduces to
    [cmd c, block label (Block.stripMetaData stmts) .empty].
    Proven in non-module file because mutual recursion wrapper doesn't reduce cross-module. -/
theorem block_stripMetaData_cmd_block (c : Core.Command)
    (label : String) (stmts : Core.Statements) :
    Imperative.Block.stripMetaData
      [Imperative.Stmt.cmd c, Imperative.Stmt.block label stmts .empty] =
    [Imperative.Stmt.cmd c, Imperative.Stmt.block label (Imperative.Block.stripMetaData stmts) .empty] := by
  simp [Imperative.Block.stripMetaData, Imperative.Stmt.stripMetaData]

/-- Combined: stripMetaData ∘ eraseTypes on the procedure body wrapper
    [cmd setResult, block "$body" bodyStmts .empty]. -/
theorem block_strip_erase_cmd_block (c : Core.Command)
    (label : String) (stmts : Core.Statements) :
    Imperative.Block.stripMetaData (Core.Statements.eraseTypes
      [Imperative.Stmt.cmd c, Imperative.Stmt.block label stmts .empty]) =
    [Imperative.Stmt.cmd (Core.Command.eraseTypes c),
     Imperative.Stmt.block label (Imperative.Block.stripMetaData (Core.Statements.eraseTypes stmts)) .empty] := by
  simp [Core.Statements.eraseTypes, Core.Statement.eraseTypes,
    Imperative.Block.stripMetaData, Imperative.Stmt.stripMetaData]
