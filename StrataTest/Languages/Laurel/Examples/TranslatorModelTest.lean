/-
  Differential test: compare translator model's expected declaration
  names against the real translate function's output.
-/

import StrataTest.Util.TestDiagnostics
import StrataTest.Languages.Laurel.TestExamples
import Strata.Languages.Laurel.TranslatorModel
import Strata.Languages.Laurel.LaurelToCoreTranslator
import Strata.Languages.Laurel.CoreDefinitionsForLaurel

open Strata
open Strata.Laurel
open Strata.Core
open Strata.Elab (parseStrataProgramFromDialect)

/-- Extract all declaration names from a Core program -/
def coreDeclNames (program : Core.Program) : List String :=
  program.decls.flatMap fun d => (d.names.map (·.name))

/-- Parse a Laurel program string into a Laurel Program -/
def parseLaurelString (name : String) (input : String) : IO Laurel.Program := do
  let offsetInput := String.join (List.replicate 14 "\n") ++ input
  let inputContext := Parser.stringInputContext name offsetInput
  let dialects := Strata.Elab.LoadedDialects.ofDialects! #[initDialect, Laurel]
  let strataProgram ← parseStrataProgramFromDialect dialects Laurel.name inputContext
  let transResult := Laurel.TransM.run (Strata.Uri.file name) (Laurel.parseProgram strataProgram)
  match transResult with
  | .error errs => throw (IO.userError s!"Parse errors: {errs}")
  | .ok program => pure program

/-- Run real translate and return Core decl names -/
def translateNames (name : String) (input : String) : IO (List String) := do
  let program ← parseLaurelString name input
  let (coreOpt, _) := Laurel.translate {} program
  match coreOpt with
  | some core => pure (coreDeclNames core)
  | none => throw (IO.userError s!"Translation failed")

/-- Get model's expected names -/
def modelNames (name : String) (input : String) : IO (List String) := do
  let program ← parseLaurelString name input
  let withDefs := { program with
    staticProcedures := coreDefinitionsForLaurel.staticProcedures ++ program.staticProcedures
    types := coreDefinitionsForLaurel.types ++ program.types
  }
  pure (expectedDeclNames withDefs)

def compareNames (testName : String) (input : String) : IO Unit := do
  let actual ← translateNames testName input
  let expected ← modelNames testName input
  let missing := expected.filter (fun n => !actual.contains n)
  let extra := actual.filter (fun n => !expected.contains n)
  if missing.isEmpty && extra.isEmpty then
    IO.println s!"{testName}: ✅ ({actual.length} decls)"
  else
    if !missing.isEmpty then
      IO.println s!"{testName}: ❌ model expects, translate missing: {missing}"
    if !extra.isEmpty then
      IO.println s!"{testName}: ❌ translate has, model missing: {extra}"

def simpleComposite := "
composite Box {
  var value: int
}
"

def compositeWithProc := "
composite Counter {
  var count: int
  procedure increment(self: Counter)
    modifies self
  {
    self#count := self#count + 1
  };
}
"

def staticProc := "
procedure add(x: int, y: int): int {
  return x + y
};
"

/-- Extract input parameter names from a Core procedure declaration -/
def coreProcInputNames (d : Core.Decl) : List String :=
  match d with
  | .proc p _ => p.header.inputs.map (·.1.name)
  | _ => []

/-- Extract output parameter names from a Core procedure declaration -/
def coreProcOutputNames (d : Core.Decl) : List String :=
  match d with
  | .proc p _ => p.header.outputs.map (·.1.name)
  | _ => []

/-- Check structural properties of Core declarations -/
def checkStructure (testName : String) (input : String) : IO Unit := do
  let program ← parseLaurelString testName input
  let (coreOpt, _) := Laurel.translate {} program
  match coreOpt with
  | none => IO.println s!"{testName}: ❌ Translation failed"
  | some core =>
    let mut ok := true
    -- Check: every instance procedure has $heap_in in inputs and $heap in outputs
    let withDefs := { program with
      staticProcedures := coreDefinitionsForLaurel.staticProcedures ++ program.staticProcedures
      types := coreDefinitionsForLaurel.types ++ program.types
    }
    let instanceNames := (nonExternalInstanceProcs withDefs).map fun (t, p) =>
      qualifiedName t p.name.text
    for decl in core.decls do
      let name := decl.name.name
      if instanceNames.contains name then
        let inputs := coreProcInputNames decl
        let outputs := coreProcOutputNames decl
        if !inputs.contains "$heap_in" then
          IO.println s!"{testName}: ❌ {name} missing $heap_in in inputs: {inputs}"
          ok := false
        if !inputs.contains "self" then
          IO.println s!"{testName}: ❌ {name} missing self in inputs: {inputs}"
          ok := false
        if !outputs.contains "$heap" then
          IO.println s!"{testName}: ❌ {name} missing $heap in outputs: {outputs}"
          ok := false
        if !outputs.contains "$result" then
          IO.println s!"{testName}: ❌ {name} missing $result in outputs: {outputs}"
          ok := false
    if ok then
      IO.println s!"{testName} structure: ✅"

#eval do
  compareNames "SimpleComposite" simpleComposite
  compareNames "CompositeWithProc" compositeWithProc
  compareNames "StaticProc" staticProc
  compareNames "TwoComposites" "
composite A {
  var x: int
}
composite B {
  var y: bool
}
"
  compareNames "FunctionAndProc" "
composite Box {
  var value: int
  function getValue(self: Box): int {
    self#value
  };
  procedure setValue(self: Box, v: int)
    modifies self
  {
    self#value := v
  };
}
"
  compareNames "StaticFunction" "
function double(x: int): int {
  x + x
};
"
  compareNames "ProcWithPostcondition" "
composite Counter {
  var count: int
  procedure increment(self: Counter)
    ensures self#count == old(self#count) + 1
    modifies self
  {
    self#count := self#count + 1
  };
}
"
  compareNames "MultipleInstanceProcs" "
composite Stack {
  var size: int
  procedure push(self: Stack)
    modifies self
  {
    self#size := self#size + 1
  };
  procedure pop(self: Stack)
    modifies self
  {
    self#size := self#size - 1
  };
}
"
  -- Structural checks
  checkStructure "CompositeWithProc" compositeWithProc
  checkStructure "MultipleInstanceProcs" "
composite Stack {
  var size: int
  procedure push(self: Stack)
    modifies self
  {
    self#size := self#size + 1
  };
  procedure pop(self: Stack)
    modifies self
  {
    self#size := self#size - 1
  };
}
"
  -- Name consistency: referenced names ⊆ declared names
  IO.println ""
  IO.println "=== P1: Name consistency (referenced ⊆ declared) ==="
  for (name, input) in [
    ("CompositeWithProc", compositeWithProc),
    ("StaticProc", staticProc),
    ("FieldReadWrite", "
composite Box {
  var value: int
  procedure setValue(self: Box, v: int)
    modifies self
  {
    self#value := v
  };
  procedure getValue(self: Box): int {
    return self#value
  };
}
"),
    ("NewObject", "
composite Obj {
  var x: int
}
procedure create(): Obj {
  var o: Obj := new Obj;
  return o
};
"),
    ("StaticCallsStatic", "
procedure helper(x: int): int {
  return x + 1
};
procedure caller(x: int): int {
  var y: int := helper(x);
  return y
};
"),
    ("InstanceCallsInstance", "
composite Counter {
  var count: int
  procedure increment(self: Counter)
    modifies self
  {
    self#count := self#count + 1
  };
  procedure addTwo(self: Counter)
    modifies self
  {
    self~>increment();
    self~>increment()
  };
}
"),
    ("IfElse", "
procedure abs(x: int): int {
  if (x < 0) {
    return 0 - x
  } else {
    return x
  }
};
"),
    ("WhileLoop", "
procedure sum(n: int): int
  requires n >= 0
{
  var i: int := 0;
  var s: int := 0;
  while (i < n)
    invariant i >= 0
  {
    s := s + i;
    i := i + 1
  };
  return s
};
")
  ] do
    let program ← parseLaurelString name input
    let withDefs := { program with
      staticProcedures := coreDefinitionsForLaurel.staticProcedures ++ program.staticProcedures
      types := coreDefinitionsForLaurel.types ++ program.types
    }
    let refs := allReferencedNames withDefs
    let decls := expectedDeclNames withDefs
    let missing := refs.filter (fun n => !decls.contains n)
    if missing.isEmpty then
      IO.println s!"{name}: ✅ all {refs.length} referenced names declared"
    else
      IO.println s!"{name}: ❌ referenced but not declared: {missing}"
