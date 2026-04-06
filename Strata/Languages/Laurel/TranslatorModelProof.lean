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



