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

  -- P4: Signature checks
  IO.println ""
  IO.println "=== P4: Heap threading (signature checks) ==="
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
")
  ] do
    let program ← parseLaurelString name input
    let (coreOpt, _) := Laurel.translate {} program
    match coreOpt with
    | none => IO.println s!"{name}: ❌ Translation failed"
    | some core =>
      let withDefs := { program with
        staticProcedures := coreDefinitionsForLaurel.staticProcedures ++ program.staticProcedures
        types := coreDefinitionsForLaurel.types ++ program.types
      }
      let instanceNames := (nonExternalInstanceProcs withDefs).map fun (t, p) =>
        qualifiedName t (p : Procedure).name.text
      let mut ok := true
      for decl in core.decls do
        let declName := decl.name.name
        if instanceNames.contains declName then
          let inputs := coreProcInputNames decl
          let outputs := coreProcOutputNames decl
          if inputs.contains "$heap_in" && !outputs.contains "$heap" then
            IO.println s!"{name}: ❌ {declName} has $heap_in but no $heap output"
            ok := false
          if !outputs.contains "$result" then
            IO.println s!"{name}: ❌ {declName} missing $result output"
            ok := false
          if !inputs.contains "self" then
            IO.println s!"{name}: ❌ {declName} missing self input"
            ok := false
      if ok then
        IO.println s!"{name}: ✅ all signatures correct"

  -- P4 heap analysis: model vs real translator
  IO.println ""
  IO.println "=== P4: Heap analysis (model vs real) ==="
  for (name, input) in [
    ("NoHeap", "
procedure add(x: int, y: int): int {
  return x + y
};
"),
    ("FieldRead", "
composite Box {
  var value: int
  procedure getValue(self: Box): int {
    return self#value
  };
}
"),
    ("FieldWrite", "
composite Box {
  var value: int
  procedure setValue(self: Box, v: int)
    modifies self
  {
    self#value := v
  };
}
"),
    ("NewObject", "
composite Box {
  var value: int
}
procedure makeBox(): Box {
  return new Box
};
"),
    ("TransitiveRead", "
composite Box {
  var value: int
  procedure getValue(self: Box): int {
    return self#value
  };
  procedure getValuePlusOne(self: Box): int {
    return self~>getValue() + 1
  };
}
"),
    ("OpaqueModifies", "
composite Counter {
  var count: int
  procedure increment(self: Counter)
    ensures self#count == old(self#count) + 1
    modifies self
  {
    self#count := self#count + 1
  };
}
"),
    ("OpaqueNoModifies", "
procedure pureCompute(x: int): int
  ensures $result == x + 1
{
  return x + 1
};
"),
    ("OpaqueFieldInPostcond", "
composite Box {
  var value: int
  procedure getValue(self: Box): int
    ensures $result == self#value
  {
    return self#value
  };
}
"),
    ("ExternalProc", "
procedure readField(heap: Heap, obj: Composite, field: Field): Box
  external;
")
  ] do
    let program ← parseLaurelString name input
    let allProcs := program.staticProcedures ++
      (program.types.flatMap fun (t : TypeDefinition) => match t with
        | .Composite c => c.instanceProcedures
        | _ => [])
    -- Real translator's analysis
    let realReaders := computeReadsHeap allProcs
    let realWriters := computeWritesHeap allProcs
    -- Model's analysis (uses procReadsHeapDirectly/procWritesHeapDirectly)
    let modelReaders := allProcs.filter fun (p : Procedure) => procReadsHeapDirectly p
    let modelReaderNames := modelReaders.map fun (p : Procedure) => p.name.text
    -- Compare: model's direct readers should be subset of real readers
    let mut ok := true
    for n in modelReaderNames do
      if !realReaders.any (·.text == n) then
        IO.println s!"{name}: ❌ model says {n} reads heap, real disagrees"
        ok := false
    -- Check real readers that model misses (transitive)
    let transitiveOnly := realReaders.filter fun (r : Identifier) =>
      !modelReaderNames.contains r.text
    if !transitiveOnly.isEmpty then
      IO.println s!"{name}: ℹ️  transitive-only readers: {transitiveOnly.map fun (r : Identifier) => r.text}"
    -- Check writers
    let modelWriters := allProcs.filter fun (p : Procedure) => procWritesHeapDirectly p
    let modelWriterNames := modelWriters.map fun (p : Procedure) => p.name.text
    for n in modelWriterNames do
      if !realWriters.any (·.text == n) && !realReaders.any (·.text == n) then
        IO.println s!"{name}: ❌ model says {n} writes heap, real disagrees"
        ok := false
    if ok then
      IO.println s!"{name}: ✅ heap analysis consistent"

  -- P4: Transitive heap closure (model vs real)
  IO.println ""
  IO.println "=== P4: Transitive heap closure (model vs real) ==="
  for (name, input) in [
    ("DirectOnly", "
composite Box {
  var value: int
  procedure getValue(self: Box): int {
    return self#value
  };
}
"),
    ("OneHop", "
composite Box {
  var value: int
  procedure getValue(self: Box): int {
    return self#value
  };
  procedure getValuePlusOne(self: Box): int {
    return self~>getValue() + 1
  };
}
"),
    ("TwoHops", "
composite Box {
  var value: int
  procedure getValue(self: Box): int {
    return self#value
  };
  procedure getValuePlusOne(self: Box): int {
    return self~>getValue() + 1
  };
  procedure getValuePlusTwo(self: Box): int {
    return self~>getValuePlusOne() + 1
  };
}
"),
    ("WriteChain", "
composite Box {
  var value: int
  procedure setValue(self: Box, v: int)
    modifies self
  {
    self#value := v
  };
  procedure reset(self: Box)
    modifies self
  {
    self~>setValue(0)
  };
}
")
  ] do
    let program ← parseLaurelString name input
    let allProcs := program.staticProcedures ++
      (program.types.flatMap fun (t : TypeDefinition) => match t with
        | .Composite c => c.instanceProcedures
        | _ => [])
    -- Real translator
    let realReaders := (computeReadsHeap allProcs).map fun (r : Identifier) => r.text
    let realWriters := (computeWritesHeap allProcs).map fun (r : Identifier) => r.text
    -- Model's transitive analysis
    let modelReaders := transitiveHeapReaders allProcs
    let modelWriters := transitiveHeapWriters allProcs
    let mut ok := true
    -- Check: model readers ⊆ real readers
    for n in modelReaders do
      if !realReaders.contains n then
        IO.println s!"{name}: ❌ model transitive reader {n} not in real"
        ok := false
    -- Check: real readers ⊆ model readers
    for n in realReaders do
      if !modelReaders.contains n then
        IO.println s!"{name}: ❌ real reader {n} not in model transitive"
        ok := false
    -- Check writers
    for n in modelWriters do
      if !realWriters.contains n then
        IO.println s!"{name}: ❌ model transitive writer {n} not in real"
        ok := false
    for n in realWriters do
      if !modelWriters.contains n then
        IO.println s!"{name}: ❌ real writer {n} not in model transitive"
        ok := false
    if ok then
      IO.println s!"{name}: ✅ transitive closure matches (readers={modelReaders}, writers={modelWriters})"

  -- Body translation patterns
  IO.println ""
  IO.println "=== Body translation patterns ==="
  for (name, input) in [
    ("ReturnExpr", "
procedure add(x: int, y: int): int {
  return x + y
};
"),
    ("ReturnFieldRead", "
composite Box {
  var value: int
  procedure getValue(self: Box): int {
    return self#value
  };
}
"),
    ("AssignField", "
composite Box {
  var value: int
  procedure setValue(self: Box, v: int)
    modifies self
  {
    self#value := v
  };
}
"),
    ("IfElseReturn", "
procedure max(a: int, b: int): int {
  if (a > b) { return a } else { return b }
};
"),
    ("LocalVarInit", "
procedure compute(x: int): int {
  var y: int := x + 1;
  return y
};
"),
    ("ProcCallInReturn", "
procedure identity(x: int): int {
  return x
};
procedure callIt(x: int): int {
  return identity(x)
};
")
  ] do
    let program ← parseLaurelString name input
    let (coreOpt, _) := Laurel.translate {} program
    match coreOpt with
    | none => IO.println s!"{name}: ❌ Translation failed"
    | some core =>
      -- For each non-external proc, compare pattern's referenced names against Core
      let allProcs := program.staticProcedures ++
        (program.types.flatMap fun (t : TypeDefinition) => match t with
          | .Composite c => c.instanceProcedures
          | _ => [])
      let funcNames := allProcs.filter (fun (p : Procedure) => p.isFunctional) |>.map (fun (p : Procedure) => p.name.text)
      let isFunc := fun n => funcNames.contains n
      let mut ok := true
      for proc in allProcs do
        match proc.body with
        | .Transparent body =>
          let pattern := predictPattern isFunc body.val
          let patternRefs := pattern.referencedNames
          -- Collect parameter + local variable names
          let paramNames := proc.inputs.map (fun (p : Parameter) => p.name.text) ++
                           proc.outputs.map (fun (p : Parameter) => p.name.text)
          let localNames := patternRefs.filter fun r =>
            -- Names that appear as initVar targets are local declarations
            match pattern with
            | .block children => children.any fun c => match c with
              | .initVar n _ => n == r
              | _ => false
            | _ => false
          let knownNames := paramNames ++ localNames
          let coreNames := coreDeclNames core
          for r in patternRefs do
            if !knownNames.contains r && !coreNames.contains r &&
               r != "$result" && !r.startsWith "$" then
              IO.println s!"{name}/{proc.name.text}: ❌ pattern ref '{r}' not in Core decls, params, or locals"
              ok := false
        | _ => pure ()
      if ok then
        IO.println s!"{name}: ✅ pattern references consistent"

  -- P2: Type consistency
  IO.println ""
  IO.println "=== P2: Type consistency ==="
  for (name, input) in [
    ("IntParams", "
procedure add(x: int, y: int): int {
  return x + y
};
"),
    ("BoolParam", "
procedure negate(b: bool): bool {
  return !b
};
"),
    ("MixedTypes", "
procedure test(x: int, b: bool, s: string): int {
  return x
};
"),
    ("CompositeParam", "
composite Box {
  var value: int
  procedure getValue(self: Box): int {
    return self#value
  };
}
"),
    ("VoidReturn", "
procedure doNothing() {
};
")
  ] do
    let program ← parseLaurelString name input
    let (coreOpt, _) := Laurel.translate {} program
    match coreOpt with
    | none => IO.println s!"{name}: ❌ Translation failed"
    | some core =>
      let allProcs := program.staticProcedures ++
        (program.types.flatMap fun (t : TypeDefinition) => match t with
          | .Composite c => c.instanceProcedures
          | _ => [])
      let mut ok := true
      for proc in allProcs do
        -- Check input parameter types
        for param in proc.inputs do
          let modelType := coreTypeName param.type.val
          -- Find the corresponding Core decl and check its input type
          -- (simplified: just verify model type is a valid Core type)
          if modelType == "Composite" then
            match param.type.val with
            | .TInt | .TBool | .TString | .TReal =>
              IO.println s!"{name}/{proc.name.text}: ❌ param {param.name.text} mapped to Composite instead of primitive"
              ok := false
            | _ => pure ()
        for param in proc.outputs do
          let modelType := coreTypeName param.type.val
          if modelType == "Composite" then
            match param.type.val with
            | .TInt | .TBool | .TString | .TReal =>
              IO.println s!"{name}/{proc.name.text}: ❌ output {param.name.text} mapped to Composite instead of primitive"
              ok := false
            | _ => pure ()
      if ok then
        IO.println s!"{name}: ✅ type mapping consistent"

  -- P3: No duplicate declaration names
  IO.println ""
  IO.println "=== P3: No duplicate declarations ==="
  for (name, input) in [
    ("SimpleComposite", simpleComposite),
    ("CompositeWithProc", compositeWithProc),
    ("StaticProc", staticProc),
    ("FuncAndProc", "
procedure myProc(x: int) {
};
function myFunc(x: int): int {
  return x
};
"),
    ("TwoComposites", "
composite A {
  var x: int
  procedure getX(self: A): int {
    return self#x
  };
}
composite B {
  var y: int
  procedure getY(self: B): int {
    return self#y
  };
}
")
  ] do
    let program ← parseLaurelString name input
    let withDefs := { program with
      staticProcedures := coreDefinitionsForLaurel.staticProcedures ++ program.staticProcedures
      types := coreDefinitionsForLaurel.types ++ program.types
    }
    let names := expectedDeclNames withDefs
    let duplicates := names.filter fun n => names.count n > 1
    -- Also check real translator
    let (coreOpt, _) := Laurel.translate {} program
    let realDups := match coreOpt with
      | some core =>
        let realNames := coreDeclNames core
        realNames.filter fun n => realNames.count n > 1
      | none => []
    if duplicates.isEmpty then
      IO.println s!"{name}: ✅ no duplicate names ({names.length} decls)"
    else if !realDups.isEmpty then
      let unique_dups := duplicates.eraseDups
      IO.println s!"{name}: ⚠️  model duplicates: {unique_dups.take 3} (real also has duplicates)"
    else
      let unique_dups := duplicates.eraseDups
      IO.println s!"{name}: ❌ model duplicates: {unique_dups.take 3} (real has none)"

  -- translateModel: declaration name order
  IO.println ""
  IO.println "=== translateModel: decl names vs real ==="
  for (name, input) in [
    ("SimpleComposite", simpleComposite),
    ("CompositeWithProc", compositeWithProc),
    ("StaticProc", staticProc)
  ] do
    let program ← parseLaurelString name input
    let modelNames := modelDeclNames program
    let (coreOpt, _) := Laurel.translate {} program
    match coreOpt with
    | none => IO.println s!"{name}: ❌ Translation failed"
    | some core =>
      let realNames := coreDeclNames core
      let missing := modelNames.filter (fun n => !realNames.contains n)
      let extra := realNames.filter (fun n => !modelNames.contains n)
      if missing.isEmpty && extra.isEmpty then
        IO.println s!"{name}: ✅ names match ({modelNames.length} decls)"
      else
        if !missing.isEmpty then
          IO.println s!"{name}: ❌ model has, real missing: {missing.take 5}"
        if !extra.isEmpty then
          IO.println s!"{name}: ❌ real has, model missing: {extra.take 5}"

  -- translateModel: declaration kinds
  IO.println ""
  IO.println "=== translateModel: decl kinds vs real ==="
  for (name, input) in [
    ("SimpleComposite", simpleComposite),
    ("CompositeWithProc", compositeWithProc),
    ("StaticProc", staticProc)
  ] do
    let program ← parseLaurelString name input
    let modelClassified := classifyDecls program
    let (coreOpt, _) := Laurel.translate {} program
    match coreOpt with
    | none => IO.println s!"{name}: ❌ Translation failed"
    | some core =>
      let mut ok := true
      for decl in core.decls do
        let declName := decl.name.name
        let realKind : DeclClass := match decl with
          | .type _ _ => .datatype
          | .ax _ _ => .axiomDecl
          | .proc _ _ => .procedure
          | .func _ _ => .function
          | _ => .constant
        -- Look up in model
        let mut found := false
        for (mn, mk) in modelClassified do
          if mn == declName && mk != realKind then
            IO.println s!"{name}: ❌ {declName} kind mismatch: model={repr mk} real={repr realKind}"
            ok := false
            found := true
          else if mn == declName then
            found := true
        pure ()
      if ok then
        IO.println s!"{name}: ✅ all decl kinds match"

  -- translateModel: procedure headers (inputs/outputs)
  IO.println ""
  IO.println "=== translateModel: procedure headers vs real ==="
  for (name, input) in [
    ("StaticProcNoHeap", "
procedure add(x: int, y: int): int {
  return x + y
};
"),
    ("FieldReadProc", "
composite Box {
  var value: int
  procedure getValue(self: Box): int {
    return self#value
  };
}
"),
    ("FieldWriteProc", "
composite Box {
  var value: int
  procedure setValue(self: Box, v: int)
    modifies self
  {
    self#value := v
  };
}
")
  ] do
    let program ← parseLaurelString name input
    let (coreOpt, _) := Laurel.translate {} program
    match coreOpt with
    | none => IO.println s!"{name}: ❌ Translation failed"
    | some core =>
      let mut ok := true
      -- Check each Core procedure's inputs/outputs against model
      for decl in core.decls do
        match decl with
        | .proc p _ =>
          let coreInputNames := coreProcInputNames decl
          let coreOutputNames := coreProcOutputNames decl
          -- Check $result is always last output
          match coreOutputNames.getLast? with
          | some n =>
            if n != "$result" then
              IO.println s!"{name}/{p.header.name.name}: ❌ last output is '{n}', expected '$result'"
              ok := false
          | none =>
            IO.println s!"{name}/{p.header.name.name}: ❌ no outputs"
            ok := false
          let hasHeapIn := coreInputNames.any (· == "$heap_in")
          let hasHeapOut := coreOutputNames.any (· == "$heap")
          if hasHeapIn && !hasHeapOut then
            IO.println s!"{name}/{p.header.name.name}: ❌ has $heap_in but no $heap output"
            ok := false
        | _ => pure ()
      if ok then
        IO.println s!"{name}: ✅ all procedure headers correct"

  -- translateModel: detailed parameter comparison
  IO.println ""
  IO.println "=== translateModel: parameter names vs model ==="
  for (name, input) in [
    ("StaticProcNoHeap", "
procedure add(x: int, y: int): int {
  return x + y
};
"),
    ("FieldWriteProc", "
composite Box {
  var value: int
  procedure setValue(self: Box, v: int)
    modifies self
  {
    self#value := v
  };
}
")
  ] do
    let program ← parseLaurelString name input
    let (coreOpt, _) := Laurel.translate {} program
    match coreOpt with
    | none => IO.println s!"{name}: ❌ Translation failed"
    | some core =>
      let allProcs := program.staticProcedures ++
        (program.types.flatMap fun (t : TypeDefinition) => match t with
          | .Composite c => c.instanceProcedures
          | _ => [])
      let mut ok := true
      for proc in allProcs do
        -- Find the corresponding Core decl
        let coreName := if allProcs.length == program.staticProcedures.length then proc.name.text
          else proc.name.text  -- simplified: works for single-composite cases
        for decl in core.decls do
          if decl.name.name.endsWith proc.name.text then
            let realInputs := coreProcInputNames decl
            let realOutputs := coreProcOutputNames decl
            -- Model prediction
            let isInstance := !program.types.isEmpty && proc.inputs.any (fun (p : Parameter) => p.name.text == "self")
            let accessesHeap := realInputs.contains "$heap_in"
            let modelInputs := (expectedInputs proc isInstance accessesHeap).map Prod.fst
            let modelOutputs := (expectedOutputs proc accessesHeap).map Prod.fst
            -- Compare input names
            for mi in modelInputs do
              if !realInputs.contains mi then
                IO.println s!"{name}/{proc.name.text}: ❌ model input '{mi}' not in real inputs {realInputs}"
                ok := false
            -- Compare output names
            for mo in modelOutputs do
              if !realOutputs.contains mo then
                IO.println s!"{name}/{proc.name.text}: ❌ model output '{mo}' not in real outputs {realOutputs}"
                ok := false
      if ok then
        IO.println s!"{name}: ✅ parameter names match model"

  -- translateModel: body structure
  IO.println ""
  IO.println "=== translateModel: body structure ==="

  -- Helper: extract call targets from Core statements
  let rec extractCalls (stmts : Core.Statements) : List String :=
    stmts.flatMap fun (s : Core.Statement) => match s with
      | .cmd (Core.CmdExt.call _ pname _ _) => [pname]
      | .ite _ thenB elseB _ => extractCalls thenB ++ extractCalls elseB
      | .block _ body _ => extractCalls body
      | _ => []

  let rec hasExceptionPropagation (stmts : Core.Statements) : Bool :=
    stmts.any fun (s : Core.Statement) => match s with
      | .cmd (Core.CmdExt.cmd (Imperative.Cmd.assume _ _ _)) => true
      | .ite _ _ _ _ => true
      | .block _ body _ => hasExceptionPropagation body
      | _ => false

  for (name, input, procName, expectedCalls) in [
    ("ReturnExpr", "
procedure add(x: int, y: int): int {
  return x + y
};
", "add", ([] : List String)),
    ("ProcCall", "
procedure identity(x: int): int {
  return x
};
procedure callIt(x: int): int {
  var y: int := identity(x);
  return y
};
", "callIt", ["identity"])
  ] do
    let program ← parseLaurelString name input
    let (coreOpt, _) := Laurel.translate {} program
    match coreOpt with
    | none => IO.println s!"{name}: ❌ Translation failed"
    | some core =>
      let mut ok := true
      for decl in core.decls do
        match decl with
        | .proc p _ =>
          if p.header.name.name == procName then
            let callTargets := extractCalls p.body
            for ec in expectedCalls do
              if !callTargets.contains ec then
                IO.println s!"{name}/{procName}: ❌ expected call to '{ec}' not found in {callTargets}"
                ok := false
            if !callTargets.isEmpty && !hasExceptionPropagation p.body then
              IO.println s!"{name}/{procName}: ❌ has calls but no exception propagation"
              ok := false
        | _ => pure ()
      if ok then
        IO.println s!"{name}: ✅ body structure correct (calls={expectedCalls})"

  -- Expression translation model
  IO.println ""
  IO.println "=== Expression translation model ==="
  -- Test: for simple expressions, check that the model produces
  -- the same top-level structure as the real translator
  for (name, input, procName) in [
    ("LiteralReturn", "
procedure getTrue(): bool {
  return true
};
", "getTrue"),
    ("AddReturn", "
procedure add(x: int, y: int): int {
  return x + y
};
", "add"),
    ("Comparison", "
procedure isPositive(x: int): bool {
  return x > 0
};
", "isPositive")
  ] do
    let program ← parseLaurelString name input
    let (coreOpt, _) := Laurel.translate {} program
    match coreOpt with
    | none => IO.println s!"{name}: ❌ Translation failed"
    | some core =>
      let mut ok := true
      -- Find the proc body and check the model's expression matches structurally
      for proc in program.staticProcedures do
        if proc.name.text == procName then
          match proc.body with
          | .Transparent body =>
            match body.val with
            | .Return (some v) =>
              let modelExpr := translateExprModel v.val
              -- Check: model expression has the right top-level constructor
              let modelStr := toString modelExpr
              if modelStr.length == 0 then
                IO.println s!"{name}: ❌ model produced empty expression"
                ok := false
            | _ => pure ()
          | _ => pure ()
      if ok then
        IO.println s!"{name}: ✅ expression model produces output"

  -- Expression translation: deep comparison
  IO.println ""
  IO.println "=== Expression model: deep comparison ==="
  for (name, input, procName) in [
    ("LitTrue", "
function getTrue(): bool {
  true
};
", "getTrue"),
    ("LitInt", "
function getFive(): int {
  5
};
", "getFive"),
    ("AddExpr", "
function add(x: int, y: int): int {
  x + y
};
", "add")
  ] do
    let program ← parseLaurelString name input
    let (coreOpt, _) := Laurel.translate {} program
    match coreOpt with
    | none => IO.println s!"{name}: ❌ Translation failed"
    | some core =>
      -- Find the Core function and get its body expression
      let mut ok := true
      for decl in core.decls do
        match decl with
        | .func f _ =>
          if f.name.name == procName then
            match f.body with
            | some realExpr =>
              for proc in program.staticProcedures do
                if proc.name.text == procName then
                  match proc.body with
                  | .Transparent body =>
                    let modelExpr := translateExprModel body.val
                    -- Compare after erasing types
                    let realErased := toString (realExpr.eraseTypes)
                    let modelErased := toString (modelExpr.eraseTypes)
                    if realErased == modelErased then
                      IO.println s!"{name}: ✅ expressions match (erased types)"
                    else
                      IO.println s!"{name}: ❌ mismatch (erased types)"
                      IO.println s!"  real:  {realErased.take 80}"
                      IO.println s!"  model: {modelErased.take 80}"
                      ok := false
                  | _ => pure ()
            | none => pure ()
        | _ => pure ()
      pure ()

  -- More deep expression comparisons
  for (name, input, procName) in [
    ("BoolNot", "
function negate(b: bool): bool {
  !b
};
", "negate"),
    ("Comparison", "
function isPos(x: int): bool {
  x > 0
};
", "isPos"),
    ("IfThenElse", "
function max(a: int, b: int): int {
  if (a > b) a else b
};
", "max"),
    ("FuncCall", "
function identity(x: int): int {
  x
};
function callId(x: int): int {
  identity(x)
};
", "callId"),
    ("Equality", "
function isZero(x: int): bool {
  x == 0
};
", "isZero")
  ] do
    let program ← parseLaurelString name input
    let (coreOpt, _) := Laurel.translate {} program
    match coreOpt with
    | none => IO.println s!"{name}: ❌ Translation failed"
    | some core =>
      for decl in core.decls do
        match decl with
        | .func f _ =>
          if f.name.name == procName then
            match f.body with
            | some realExpr =>
              for proc in program.staticProcedures do
                if proc.name.text == procName then
                  match proc.body with
                  | .Transparent body =>
                    let modelExpr := translateExprModel body.val
                    let realErased := toString (realExpr.eraseTypes)
                    let modelErased := toString (modelExpr.eraseTypes)
                    if realErased == modelErased then
                      IO.println s!"{name}: ✅ match"
                    else
                      IO.println s!"{name}: ❌ mismatch"
                      IO.println s!"  real:  {realErased.take 100}"
                      IO.println s!"  model: {modelErased.take 100}"
                  | _ => pure ()
            | none => pure ()
        | _ => pure ()

  -- Statement translation: deep comparison
  IO.println ""
  IO.println "=== Statement model: deep comparison ==="
  for (name, input, procName) in [
    ("SimpleReturn", "
procedure add(x: int, y: int): int {
  return x + y
};
", "add"),
    ("LocalVar", "
procedure compute(x: int): int {
  var y: int := x + 1;
  return y
};
", "compute")
  ] do
    let program ← parseLaurelString name input
    let (coreOpt, _) := Laurel.translate {} program
    match coreOpt with
    | none => IO.println s!"{name}: ❌ Translation failed"
    | some core =>
      for decl in core.decls do
        match decl with
        | .proc p _ =>
          if p.header.name.name == procName then
            -- Get model output
            for proc in program.staticProcedures do
              if proc.name.text == procName then
                let funcNames := program.staticProcedures.filter (fun (p : Procedure) => p.isFunctional)
                  |>.map (fun (p : Procedure) => p.name.text)
                let isFunc := fun n => funcNames.contains n
                let outParams := proc.outputs.map (fun (p : Parameter) => p.name.text)
                match proc.body with
                | .Transparent body =>
                  let modelStmts := translateStmtModel isFunc outParams body.val
                  let realBody := p.body
                  let realInner := match realBody with
                    | [_, Imperative.Stmt.block _ inner _] => inner
                    | _ => realBody
                  if modelStmts.length == realInner.length then
                    IO.println s!"{name}: ✅ statement count matches ({modelStmts.length} inner stmts)"
                  else
                    IO.println s!"{name}: ❌ count mismatch: model={modelStmts.length} real={realInner.length}"
                | _ => pure ()
        | _ => pure ()

  -- Full translateProgramModel comparison
  IO.println ""
  IO.println "=== translateProgramModel vs real ==="
  for (name, input) in [
    ("SimpleProc", "
procedure add(x: int, y: int): int {
  return x + y
};
")
  ] do
    let program ← parseLaurelString name input
    let modelProgram := translateProgramModel program
    let (coreOpt, _) := Laurel.translate {} program
    match coreOpt with
    | none => IO.println s!"{name}: ❌ Translation failed"
    | some core =>
      -- Compare procedure declarations
      let modelProcs := modelProgram.decls.filterMap fun (d : Core.Decl) => match d with
        | .proc p _ => some p.header.name.name | _ => none
      let realProcs := core.decls.filterMap fun (d : Core.Decl) => match d with
        | .proc p _ => some p.header.name.name | _ => none
      let mut ok := true
      -- Check model procs are in real
      for mp in modelProcs do
        if !realProcs.contains mp then
          IO.println s!"{name}: ❌ model proc '{mp}' not in real"
          ok := false
      -- Check real procs are in model
      for rp in realProcs do
        if !modelProcs.contains rp then
          IO.println s!"{name}: ℹ️  real proc '{rp}' not in model (expected — builtins)"
      -- Compare body structure for matching procs
      for modelDecl in modelProgram.decls do
        match modelDecl with
        | .proc mp _ =>
          for realDecl in core.decls do
            match realDecl with
            | .proc rp _ =>
              if mp.header.name.name == rp.header.name.name then
                if mp.body.length == rp.body.length then
                  IO.println s!"{name}/{mp.header.name.name}: ✅ body length matches ({mp.body.length})"
                else
                  IO.println s!"{name}/{mp.header.name.name}: ❌ body length: model={mp.body.length} real={rp.body.length}"
                  ok := false
            | _ => pure ()
        | _ => pure ()
      if ok then
        IO.println s!"{name}: ✅ program model matches"

  -- Comprehensive translateProgramModel test
  IO.println ""
  IO.println "=== translateProgramModel: comprehensive ==="
  for (name, input) in [
    ("SimpleProc", staticProc),
    ("CompositeWithProc", compositeWithProc),
    ("TwoProcs", "
procedure add(x: int, y: int): int {
  return x + y
};
procedure negate(b: bool): bool {
  return !b
};
")
  ] do
    let program ← parseLaurelString name input
    let modelProgram := translateProgramModel program
    let (coreOpt, _) := Laurel.translate {} program
    match coreOpt with
    | none => IO.println s!"{name}: ❌ Translation failed"
    | some core =>
      let mut ok := true
      -- Check every model decl name is in real
      for (md : Core.Decl) in modelProgram.decls do
        if !core.decls.any (fun (rd : Core.Decl) => rd.name.name == md.name.name) then
          IO.println s!"{name}: ❌ model decl '{md.name.name}' not in real"
          ok := false
      -- Check every real decl name is in model
      for (rd : Core.Decl) in core.decls do
        if !modelProgram.decls.any (fun (md : Core.Decl) => md.name.name == rd.name.name) then
          IO.println s!"{name}: ❌ real decl '{rd.name.name}' not in model"
          ok := false
      -- Check decl count
      if modelProgram.decls.length != core.decls.length then
        IO.println s!"{name}: ❌ count: model={modelProgram.decls.length} real={core.decls.length}"
        ok := false
      if ok then
        IO.println s!"{name}: ✅ all {modelProgram.decls.length} decls match"
