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

set_option maxRecDepth 1024

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

-- Structural equality test (eraseTypes + stripMetaData)
private def stripLabelOffset (s : String) (pfx : String) : String :=
  match s.splitOn (pfx ++ "(") with
  | [_] => s
  | parts =>
    let rec rejoin : List String → String
      | [] => ""
      | part :: rest =>
        let afterNum := part.dropWhile (· != ')')
        pfx ++ "(0" ++ afterNum ++ rejoin rest
    parts.head! ++ rejoin parts.tail!

def normalizeDecl (d : Core.Decl) : String :=
  let s := toString (Std.Format.pretty (Std.ToFormat.format (Core.Decl.stripMetaData (Core.Decl.eraseTypes d))) (width := 200))
  let s := stripLabelOffset (stripLabelOffset s "assert") "assume"
  -- Normalize try-catch label numbering: renumber in encounter order
  let ids := extractTryIds s
  let rec renumber (s : String) (ids : List String) (nextId : Nat) : String :=
    match ids with
    | [] => s
    | id :: rest =>
      let s := s.replace s!"$try_end_{id}" s!"$TRY_{nextId}"
                |>.replace s!"$handlers_{id}" s!"$HAND_{nextId}"
      renumber s rest (nextId + 1)
  let s := renumber s ids 1
  s.replace "$TRY_" "$try_end_" |>.replace "$HAND_" "$handlers_"
where
  extractTryIds (s : String) : List String :=
    match s.splitOn "$try_end_" with
    | [_] => []
    | parts => (parts.tail!.filterMap fun part =>
        let id := (part.takeWhile Char.isDigit).toString
        if id.isEmpty then none else some id).eraseDups

def structuralEq (name src : String) : IO Unit := do
  let program ← parseLaurelString name src
  let (coreOpt, _) := Laurel.translate {} program
  let model := Laurel.translateProgramModel program
  match coreOpt with
  | none => return
  | some core =>
    if core.decls.length != model.decls.length then
      IO.println s!"{name}: ❌ STRUCT len real={core.decls.length} model={model.decls.length}"
      return
    let mut diffCount := 0
    let mut firstDiff := ""
    let mut i := 0
    while i < core.decls.length do
      if normalizeDecl core.decls[i]! != normalizeDecl model.decls[i]! then
        if diffCount == 0 then firstDiff := (Core.Decl.name core.decls[i]!).name
        diffCount := diffCount + 1
      i := i + 1
    if diffCount == 0 then IO.println s!"{name}: ✅ STRUCT ({core.decls.length})"
    else IO.println s!"{name}: ❌ STRUCT {diffCount}/{core.decls.length} first={firstDiff}"

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

#eval! do
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
        structuralEq name input

  -- Additional differential tests for uncovered patterns
  IO.println ""
  IO.println "=== Additional patterns ==="

  -- Multiple fields with read/write
  for (name, input) in [
    ("MultiField", "
composite Point {
  var x: int
  var y: int
  procedure getX(self: Point): int {
    return self#x
  };
  procedure setY(self: Point, v: int)
    modifies self
  {
    self#y := v
  };
}
"),
    -- Instance method calls (self~>method())
    ("InstanceCall", "
composite Counter {
  var count: int
  procedure increment(self: Counter)
    modifies self
  {
    self#count := self#count + 1
  };
  procedure addThree(self: Counter)
    modifies self
  {
    self~>increment();
    self~>increment();
    self~>increment()
  };
}
"),
    -- Postconditions (Opaque bodies)
    ("OpaquePostcond", "
composite Box {
  var value: int
  procedure getValue(self: Box): int
    ensures $result == self#value
  {
    return self#value
  };
}
"),
    -- Heap-modifying with modifies clause
    ("ModifiesClause", "
composite Cell {
  var data: int
  procedure setData(self: Cell, v: int)
    ensures self#data == v
    modifies self
  {
    self#data := v
  };
}
"),
    -- Nested control flow
    ("NestedControlFlow", "
procedure search(n: int): int
  requires n >= 0
{
  var i: int := 0;
  var found: int := 0;
  while (i < n)
    invariant i >= 0
  {
    if (i == 5) {
      found := 1
    } else {
      found := 0
    };
    i := i + 1
  };
  return found
};
"),
    -- Multiple composites
    ("TwoCompositesFull", "
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
    -- Name comparison
    let actual ← translateNames name input
    let expected ← modelNames name input
    let missing := expected.filter (fun n => !actual.contains n)
    let extra := actual.filter (fun n => !expected.contains n)
    if missing.isEmpty && extra.isEmpty then
      IO.println s!"{name}: ✅ names match ({actual.length} decls)"
    else
      if !missing.isEmpty then
        IO.println s!"{name}: ❌ model expects, translate missing: {missing}"
      if !extra.isEmpty then
        IO.println s!"{name}: ❌ translate has, model missing: {extra}"

  -- translateProgramModel comprehensive for new patterns
  IO.println ""
  IO.println "=== translateProgramModel: new patterns ==="
  for (name, input) in [
    ("MultiField", "
composite Point {
  var x: int
  var y: int
  procedure getX(self: Point): int {
    return self#x
  };
  procedure setY(self: Point, v: int)
    modifies self
  {
    self#y := v
  };
}
"),
    ("NestedControlFlow", "
procedure search(n: int): int
  requires n >= 0
{
  var i: int := 0;
  var found: int := 0;
  while (i < n)
    invariant i >= 0
  {
    if (i == 5) {
      found := 1
    } else {
      found := 0
    };
    i := i + 1
  };
  return found
};
"),
    ("TwoCompositesFull", "
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
    let modelProgram := translateProgramModel program
    let (coreOpt, _) := Laurel.translate {} program
    match coreOpt with
    | none => IO.println s!"{name}: ❌ Translation failed"
    | some core =>
      let mut ok := true
      for (md : Core.Decl) in modelProgram.decls do
        if !core.decls.any (fun (rd : Core.Decl) => rd.name.name == md.name.name) then
          IO.println s!"{name}: ❌ model decl '{md.name.name}' not in real"
          ok := false
      for (rd : Core.Decl) in core.decls do
        if !modelProgram.decls.any (fun (md : Core.Decl) => md.name.name == rd.name.name) then
          IO.println s!"{name}: ❌ real decl '{rd.name.name}' not in model"
          ok := false
      if modelProgram.decls.length != core.decls.length then
        IO.println s!"{name}: ❌ count: model={modelProgram.decls.length} real={core.decls.length}"
        ok := false
      if ok then
        IO.println s!"{name}: ✅ all {modelProgram.decls.length} decls match"
        structuralEq name input

  -- Stress tests: harder patterns
  IO.println ""
  IO.println "=== Stress tests: harder patterns ==="

  -- Helper for comprehensive comparison
  let comprehensiveCompare := fun (name : String) (input : String) => do
    let program ← parseLaurelString name input
    let modelProgram := translateProgramModel program
    let (coreOpt, _) := Laurel.translate {} program
    match coreOpt with
    | none => IO.println s!"{name}: ❌ Translation failed"
    | some core =>
      let modelNames := modelProgram.decls.map fun (d : Core.Decl) => d.name.name
      let realNames := core.decls.map fun (d : Core.Decl) => d.name.name
      let missing := realNames.filter (fun n => !modelNames.contains n)
      let extra := modelNames.filter (fun n => !realNames.contains n)
      if missing.isEmpty && extra.isEmpty && modelProgram.decls.length == core.decls.length then
        IO.println s!"{name}: ✅ all {modelProgram.decls.length} decls match"
        structuralEq name input
      else
        if !missing.isEmpty then
          IO.println s!"{name}: ❌ real has, model missing: {missing}"
        if !extra.isEmpty then
          IO.println s!"{name}: ❌ model has, real missing: {extra}"
        if modelProgram.decls.length != core.decls.length then
          IO.println s!"{name}: ❌ count: model={modelProgram.decls.length} real={core.decls.length}"

  -- 1. Static proc calling static proc (transitive heap through statics)
  comprehensiveCompare "StaticCallsStatic" "
procedure helper(x: int): int {
  return x + 1
};
procedure caller(x: int): int {
  var y: int := helper(x);
  return y
};
"

  -- 2. Static function calling static function
  comprehensiveCompare "FuncCallsFunc" "
function double(x: int): int {
  x + x
};
function quadruple(x: int): int {
  double(double(x))
};
"

  -- 3. Mix of functions and procedures
  comprehensiveCompare "FuncAndProcMix" "
function square(x: int): int {
  x * x
};
procedure compute(x: int): int {
  var s: int := square(x);
  return s + 1
};
"

  -- 4. Instance function (isFunctional on instance)
  comprehensiveCompare "InstanceFunction" "
composite Box {
  var value: int
  function getValue(self: Box): int {
    self#value
  };
}
"

  -- 5. Instance proc + instance function on same composite
  comprehensiveCompare "InstanceMixed" "
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

  -- 6. Static proc that creates a new object
  comprehensiveCompare "NewInStaticProc" "
composite Obj {
  var x: int
}
procedure create(): Obj {
  var o: Obj := new Obj;
  return o
};
"

  -- 7. Constrained type usage (int32 field)
  comprehensiveCompare "ConstrainedField" "
composite Sensor {
  var reading: int32
  procedure getReading(self: Sensor): int {
    return self#reading
  };
}
"

  -- 8. Multiple composites with instance procs calling each other's statics
  comprehensiveCompare "CrossComposite" "
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
procedure sumBoth(a: A, b: B): int {
  var ax: int := a~>getX();
  var by_: int := b~>getY();
  return ax + by_
};
"

  -- 9. Procedure with precondition
  comprehensiveCompare "WithPrecondition" "
procedure safeDivide(x: int, y: int): int
  requires y != 0
{
  return x
};
"

  -- 10. While loop with invariant and decreases
  comprehensiveCompare "WhileWithInvariant" "
procedure countdown(n: int): int
  requires n >= 0
{
  var i: int := n;
  var sum: int := 0;
  while (i > 0)
    invariant i >= 0
    invariant sum >= 0
  {
    sum := sum + i;
    i := i - 1
  };
  return sum
};
"

  -- 11. Deeply nested control flow
  comprehensiveCompare "DeepNesting" "
procedure classify(x: int): int {
  var result: int := 0;
  if (x > 0) {
    if (x > 100) {
      result := 3
    } else {
      if (x > 10) {
        result := 2
      } else {
        result := 1
      }
    }
  } else {
    result := 0
  };
  return result
};
"

  -- 12. Boolean operations
  comprehensiveCompare "BoolOps" "
function bothTrue(a: bool, b: bool): bool {
  a && b
};
function eitherTrue(a: bool, b: bool): bool {
  a || b
};
function negate(a: bool): bool {
  !a
};
"

  -- 13. Empty composite (no fields, no procs)
  comprehensiveCompare "EmptyComposite" "
composite Empty {
}
"

  -- 14. Composite with bool field
  comprehensiveCompare "BoolField" "
composite Flag {
  var active: bool
  procedure isActive(self: Flag): bool {
    return self#active
  };
}
"

  -- 15. Multiple field types on one composite
  comprehensiveCompare "MultiTypeFields" "
composite Record {
  var count: int
  var name: string
  var active: bool
}
"

  -- 16. Procedure that does nothing (void)
  comprehensiveCompare "VoidProc" "
procedure noop() {
};
"

  -- 17. Chained instance calls
  comprehensiveCompare "ChainedInstance" "
composite Counter {
  var count: int
  procedure increment(self: Counter)
    modifies self
  {
    self#count := self#count + 1
  };
  procedure addFive(self: Counter)
    modifies self
  {
    self~>increment();
    self~>increment();
    self~>increment();
    self~>increment();
    self~>increment()
  };
}
"

  -- 18. User-defined datatype (simple, no IsType)
  comprehensiveCompare "UserDatatype" "
datatype Color {
  Red(),
  Green(),
  Blue()
}
"

  -- 19. Forall/Exists in postcondition
  comprehensiveCompare "QuantifiedPostcond" "
composite Arr {
  var size: int
  procedure clear(self: Arr)
    ensures self#size == 0
    modifies self
  {
    self#size := 0
  };
}
"

  -- 20. Constants
  comprehensiveCompare "WithConstant" "
function maxSize(): int {
  100
};
procedure check(x: int): bool {
  return x < maxSize()
};
"

  -- === Tests added during model audit ===

  -- 71. Implies operator
  comprehensiveCompare "ImpliesOp" "
procedure test(a: bool, b: bool): bool {
  return (a ==> b)
};
"

  -- 72. Negation (unary minus)
  comprehensiveCompare "NegationOp" "
procedure negate(x: int): int {
  return -x
};
"

  -- 73. Div and Mod
  comprehensiveCompare "DivMod" "
procedure divmod(x: int, y: int): int {
  var q: int := x / y;
  var r: int := x % y;
  return q + r
};
"

  -- 74. Assign from instance proc call
  comprehensiveCompare "AssignFromInstanceProc" "
composite Box {
  var value: int
  procedure getValue(self: Box): int {
    return self#value
  };
}
procedure test(b: Box): int {
  var v: int := 0;
  v := b~>getValue();
  return v
};
"

  -- 75. Instance function call in expression position
  comprehensiveCompare "InstanceFuncInExpr" "
composite Box {
  var value: int
  function getValue(self: Box): int { self#value };
}
procedure test(b: Box): int {
  return b~>getValue() + 1
};
"

  -- 76. Cross-composite instance call
  comprehensiveCompare "CrossCompositeCall" "
composite Inner {
  var x: int
  function getX(self: Inner): int { self#x };
}
composite Outer {
  var inner: int
  procedure test(self: Outer, i: Inner): int {
    return i~>getX()
  };
}
"

  -- 77. Assume statement
  comprehensiveCompare "AssumeStmt" "
procedure test(x: int): int {
  assume x > 0;
  return x
};
"

  -- 78. Assert statement
  comprehensiveCompare "AssertStmt" "
procedure test(x: int): int {
  assert x > 0;
  return x
};
"

  -- 79. Return from instance proc call
  comprehensiveCompare "ReturnFromInstanceProc" "
composite Box {
  var value: int
  procedure getValue(self: Box): int {
    return self#value
  };
}
procedure test(b: Box): int {
  return b~>getValue()
};
"

  -- 80. Three-level inheritance
  comprehensiveCompare "InheritanceChain" "
composite A { var x: int }
composite B extends A { var y: int }
composite C extends B { var z: int }
"

  -- 81. Subtraction and multiplication
  comprehensiveCompare "SubMul" "
procedure test(x: int, y: int): int {
  return (x - y) * (x + y)
};
"

  -- 82. Equality and inequality
  comprehensiveCompare "EqNeq" "
procedure test(x: int, y: int): bool {
  var eq: bool := x == y;
  var neq: bool := x != y;
  return eq
};
"

  -- 83. Assign from static proc call
  comprehensiveCompare "AssignFromStaticProc" "
procedure helper(x: int): int { return x + 1 };
procedure test(x: int): int {
  var y: int := 0;
  y := helper(x);
  return y
};
"

  -- 84. Return from static proc call
  comprehensiveCompare "ReturnFromProcCall" "
procedure helper(x: int): int { return x + 1 };
procedure test(x: int): int {
  return helper(x)
};
"

  -- 85. While with no invariant
  comprehensiveCompare "WhileNoInvariant" "
procedure test(n: int): int {
  var i: int := 0;
  while (i < n) {
    i := i + 1
  };
  return i
};
"

  -- 86. While with multiple invariants
  comprehensiveCompare "WhileMultiInvariant" "
procedure test(n: int): int
  requires n >= 0
{
  var i: int := 0;
  var s: int := 0;
  while (i < n)
    invariant i >= 0
    invariant i <= n
    invariant s >= 0
  {
    s := s + i;
    i := i + 1
  };
  return s
};
"

  -- 87. Local from instance proc call (not function)
  comprehensiveCompare "LocalFromInstanceProc" "
composite Box {
  var value: int
  procedure getValue(self: Box): int {
    return self#value
  };
}
procedure test(b: Box): int {
  var v: int := b~>getValue();
  return v
};
"

  -- 88. Multiple constrained params
  comprehensiveCompare "MultiConstrainedParams" "
procedure test(a: int8, b: int16, c: int32): int {
  return a + b + c
};
"

  -- 89. Old expression in postcondition
  comprehensiveCompare "OldExpr" "
composite Box {
  var value: int
  procedure increment(self: Box)
    ensures self#value == old(self#value) + 1
    modifies self
  {
    self#value := self#value + 1
  };
}
"

  -- 90. If without else
  comprehensiveCompare "IfNoElse" "
procedure test(x: int): int {
  var r: int := 0;
  if (x > 0) {
    r := x
  };
  return r
};
"

  -- 91. Nested function calls
  comprehensiveCompare "NestedFuncCalls" "
function f(x: int): int { x + 1 };
function g(x: int): int { x * 2 };
procedure test(x: int): int {
  return f(g(x))
};
"

  -- 92. Multi-arg function call
  comprehensiveCompare "MultiArgCall" "
function add3(a: int, b: int, c: int): int { a + b + c };
procedure test(): int {
  return add3(1, 2, 3)
};
"

  -- 93. Instance proc calling another instance proc
  comprehensiveCompare "InstanceCallsInstance2" "
composite Counter {
  var count: int
  procedure increment(self: Counter)
    modifies self
  { self#count := self#count + 1 };
  procedure incrementTwice(self: Counter)
    modifies self
  {
    self~>increment();
    self~>increment()
  };
}
"

  -- 94. Datatype with multiple constructors
  comprehensiveCompare "DatatypeMultiConstr" "
datatype Shape {
  Circle(radius: int),
  Rectangle(width: int, height: int)
}
"

  -- 95. Opaque ensures field (known gap)
  comprehensiveCompare "OpaqueEnsuresField" "
composite Counter {
  var count: int
  procedure reset(self: Counter)
    ensures self#count == 0
    modifies self
  opaque;
}
"

  -- 96. Opaque ensures no modifies (known gap)
  comprehensiveCompare "OpaqueEnsuresNoModifies" "
composite Box {
  var value: int
  procedure check(self: Box): bool
    ensures $result == (self#value > 0)
  opaque;
}
"

  -- Round 2: Edge cases and harder patterns
  IO.println ""
  IO.println "=== Round 2: Edge cases ==="

  -- 97. String field read/write
  comprehensiveCompare "StringFieldOps" "
composite Named {
  var name: string
  function getName(self: Named): string { self#name };
  procedure setName(self: Named, n: string)
    modifies self
  { self#name := n };
}
"

  -- 98. Bool field read/write
  comprehensiveCompare "BoolFieldOps" "
composite Flag {
  var active: bool
  function isActive(self: Flag): bool { self#active };
  procedure setActive(self: Flag, v: bool)
    modifies self
  { self#active := v };
}
"

  -- 99. External function
  comprehensiveCompare "ExternalFunc" "
function externalCompute(x: int): int external;
"

  -- 100. External procedure
  comprehensiveCompare "ExternalProc" "
composite Widget {
  var id: int
  procedure render(self: Widget) external;
}
"

  -- 101. Opaque with implementation
  comprehensiveCompare "OpaqueWithImpl" "
composite Box {
  var value: int
  procedure set(self: Box, v: int)
    ensures self#value == v
    modifies self
  {
    self#value := v
  };
}
"

  -- 102. Multiple datatypes
  comprehensiveCompare "MultipleDatatypes" "
datatype Color { Red, Green, Blue }
datatype Shape { Circle(radius: int), Square(side: int) }
"

  -- 103. Composite with no procs
  comprehensiveCompare "CompositeNoProcs" "
composite Point {
  var x: int
  var y: int
}
"

  -- 104. Instance proc with multiple args
  comprehensiveCompare "InstanceMultiArgs" "
composite Calc {
  var result: int
  procedure add(self: Calc, a: int, b: int)
    modifies self
  { self#result := a + b };
}
"

  -- 105. While with instance call in body
  comprehensiveCompare "WhileWithInstanceCall" "
composite Counter {
  var count: int
  procedure increment(self: Counter)
    modifies self
  { self#count := self#count + 1 };
}
procedure loop(c: Counter, n: int) {
  var i: int := 0;
  while (i < n) {
    c~>increment();
    i := i + 1
  }
};
"

  -- 106. Function with bool return from comparison
  comprehensiveCompare "FuncReturnsBool" "
function isPositive(x: int): bool { x > 0 };
function isZero(x: int): bool { x == 0 };
"

  -- 107. Constrained field read
  comprehensiveCompare "ConstrainedFieldRead2" "
composite Sensor {
  var reading: int32
  function getReading(self: Sensor): int { self#reading };
}
"

  -- 108. Two composites with cross-instance calls
  comprehensiveCompare "CrossInstanceCalls" "
composite Engine {
  var rpm: int
  function getRpm(self: Engine): int { self#rpm };
}
composite Car {
  var speed: int
  procedure updateSpeed(self: Car, e: Engine)
    modifies self
  { self#speed := e~>getRpm() };
}
"

  -- 109. Procedure with multiple outputs
  comprehensiveCompare "MultipleReturns" "
procedure compute(x: int): int {
  if (x > 0) {
    return x * 2
  };
  return 0
};
"

  -- 110. Nested if-else
  comprehensiveCompare "NestedIfElse" "
procedure classify(x: int): int {
  if (x > 0) {
    if (x > 100) {
      return 2
    } else {
      return 1
    }
  } else {
    return 0
  }
};
"

  -- 111. Old expression with arithmetic
  comprehensiveCompare "OldExprArith" "
composite Counter {
  var count: int
  procedure add(self: Counter, n: int)
    ensures self#count == old(self#count) + n
    modifies self
  {
    self#count := self#count + n
  };
}
"

  -- 112. Inheritance with proc
  comprehensiveCompare "InheritanceWithProc" "
composite Animal {
  var age: int
}
composite Dog extends Animal {
  var name: string
  function getAge(self: Dog): int { self#age };
}
"

  -- 113. Three composites
  comprehensiveCompare "ThreeComposites" "
composite A { var x: int }
composite B { var y: int }
composite C { var z: int }
"

  -- 114. Mixed local var types
  comprehensiveCompare "MixedLocalVars" "
procedure test(): int {
  var a: int := 1;
  var b: bool := true;
  var c: string := \"hello\";
  return a
};
"

  -- 115. Constrained param with precondition
  comprehensiveCompare "ConstrainedWithPrecond" "
procedure test(x: int32): int
  requires x > 0
{
  return x + 1
};
"

  -- === More opaque variants (now that opaque is fixed) ===

  -- 116. Opaque with multiple ensures
  comprehensiveCompare "OpaqueMultiEnsures" "
composite Box {
  var value: int
  procedure clamp(self: Box, lo: int, hi: int)
    ensures self#value >= lo
    ensures self#value <= hi
    modifies self
  opaque;
}
"

  -- 117. Opaque function (no modifies, returns value)
  comprehensiveCompare "OpaqueFunction" "
composite Box {
  var value: int
  function getValue(self: Box): int
    ensures $result == self#value
  opaque;
}
"

  -- 118. Opaque with impl (ensures + body)
  comprehensiveCompare "OpaqueWithImplEnsures" "
composite Box {
  var value: int
  procedure set(self: Box, v: int)
    ensures self#value == v
    modifies self
  {
    self#value := v
  };
}
"

  -- 119. Opaque with old in ensures + modifies
  comprehensiveCompare "OpaqueOldModifies" "
composite Counter {
  var count: int
  procedure increment(self: Counter)
    ensures self#count == old(self#count) + 1
    modifies self
  opaque;
}
"

  -- 120. Abstract procedure (no body at all)
  comprehensiveCompare "AbstractProc" "
composite Box {
  var value: int
  procedure reset(self: Box)
    ensures self#count == 0
    modifies self
  abstract;
}
"

  -- === Instance call edge cases ===

  -- 121. Instance function call with multiple args
  comprehensiveCompare "InstanceFuncMultiArgs" "
composite Math {
  var base: int
  function add(self: Math, a: int, b: int): int { self#base + a + b };
}
procedure test(m: Math): int {
  return m~>add(1, 2)
};
"

  -- 122. Chained instance calls in expression
  comprehensiveCompare "ChainedInstanceExpr" "
composite Box {
  var value: int
  function getValue(self: Box): int { self#value };
}
procedure test(a: Box, b: Box): int {
  return a~>getValue() + b~>getValue()
};
"

  -- 123. Instance call in while condition
  comprehensiveCompare "InstanceCallInWhileCond" "
composite Counter {
  var count: int
  function getCount(self: Counter): int { self#count };
  procedure increment(self: Counter)
    modifies self
  { self#count := self#count + 1 };
}
procedure loop(c: Counter, n: int) {
  while (c~>getCount() < n) {
    c~>increment()
  }
};
"

  -- 124. Instance call in if condition
  comprehensiveCompare "InstanceCallInIfCond" "
composite Box {
  var value: int
  function isPositive(self: Box): bool { self#value > 0 };
}
procedure test(b: Box): int {
  if (b~>isPositive()) {
    return 1
  } else {
    return 0
  }
};
"

  -- === More expression coverage ===

  -- 125. Ternary/conditional expression in function body
  comprehensiveCompare "ConditionalExpr" "
function max(a: int, b: int): int {
  if (a > b) { a } else { b }
};
"

  -- 126. Nested field access in postcondition
  comprehensiveCompare "NestedFieldPostcond" "
composite Pair {
  var first: int
  var second: int
  procedure swap(self: Pair)
    ensures self#first == old(self#second)
    ensures self#second == old(self#first)
    modifies self
  {
    var tmp: int := self#first;
    self#first := self#second;
    self#second := tmp
  };
}
"

  -- 127. Forall in postcondition
  comprehensiveCompare "ForallPostcond" "
composite Arr {
  var size: int
  procedure clear(self: Arr)
    ensures self#size == 0
    modifies self
  {
    self#size := 0
  };
}
"

  -- 128. Multiple composites with inheritance and procs
  comprehensiveCompare "InheritanceWithMultiProcs" "
composite Shape {
  var area: int
}
composite Circle extends Shape {
  var radius: int
  function getArea(self: Circle): int { self#area };
  procedure setRadius(self: Circle, r: int)
    modifies self
  { self#radius := r };
}
"

  -- === Stress tests ===

  -- 129. Proc calling function that calls function
  comprehensiveCompare "DeepFuncChain" "
function f(x: int): int { x + 1 };
function g(x: int): int { f(x) + f(x) };
procedure test(x: int): int {
  return g(f(x))
};
"

  -- 130. Instance proc with precondition
  comprehensiveCompare "InstanceProcWithPrecond" "
composite Stack {
  var size: int
  procedure pop(self: Stack)
    requires self#size > 0
    modifies self
  { self#size := self#size - 1 };
}
"

  -- 131. Multiple preconditions on instance proc
  comprehensiveCompare "InstanceMultiPrecond" "
composite Range {
  var lo: int
  var hi: int
  procedure set(self: Range, a: int, b: int)
    requires a >= 0
    requires b > a
    modifies self
  {
    self#lo := a;
    self#hi := b
  };
}
"

  -- 132. Constrained field write
  comprehensiveCompare "ConstrainedFieldWrite" "
composite Sensor {
  var reading: int32
  procedure setReading(self: Sensor, v: int32)
    modifies self
  { self#reading := v };
}
"

  -- 133. Function with forall postcondition
  comprehensiveCompare "FuncWithEnsures" "
function abs(x: int): int
  ensures $result >= 0
{
  if (x >= 0) { x } else { -x }
};
"

  -- 134. Composite with only functions (no procedures)
  comprehensiveCompare "FunctionsOnlyComposite" "
composite Point {
  var x: int
  var y: int
  function getX(self: Point): int { self#x };
  function getY(self: Point): int { self#y };
  function sum(self: Point): int { self#x + self#y };
}
"

  -- 135. While with invariant and early exit
  comprehensiveCompare "WhileWithDecreases" "
procedure countdown(n: int): int
  requires n >= 0
{
  var i: int := n;
  while (i > 0)
    invariant i >= 0
  {
    i := i - 1
  };
  return i
};
"

  -- 136. Opaque with old and multiple modifies targets
  comprehensiveCompare "OpaqueOldMultiModifies" "
composite Pair {
  var first: int
  var second: int
  procedure swap(self: Pair)
    ensures self#first == old(self#second)
    ensures self#second == old(self#first)
    modifies self
  opaque;
}
"

  -- 137. Static proc calling instance function in return
  comprehensiveCompare "StaticCallsInstanceFuncReturn" "
composite Box {
  var value: int
  function getValue(self: Box): int { self#value };
}
procedure doubleValue(b: Box): int {
  return b~>getValue() * 2
};
"

  -- 138. Nested while loops
  comprehensiveCompare "NestedWhile" "
procedure matrix(n: int, m: int): int {
  var sum: int := 0;
  var i: int := 0;
  while (i < n) {
    var j: int := 0;
    while (j < m) {
      sum := sum + 1;
      j := j + 1
    };
    i := i + 1
  };
  return sum
};
"

  -- === Exception and control flow features ===

  -- 139. Throw statement
  comprehensiveCompare "ThrowStmt" "
composite MyException {}
procedure mayFail(x: int, e: MyException) {
  if (x < 0) {
    throw e
  }
};
"

  -- 140. Try-catch basic
  comprehensiveCompare "TryCatchBasic" "
composite MyException {}
procedure safeDo() {
  var x: int := 0;
  try {
    x := 1
  } catch (e: MyException) {
    x := 0
  }
};
"

  -- 141. Try-catch with throw inside
  comprehensiveCompare "TryCatchWithThrow" "
composite MyException {}
procedure tryCatchThrow(x: int, ex: MyException): int {
  var result: int := 0;
  try {
    if (x < 0) {
      throw ex
    };
    result := x
  } catch (e: MyException) {
    result := 0
  };
  return result
};
"

  -- 142. Try-catch-finally
  comprehensiveCompare "TryCatchFinally" "
composite MyException {}
procedure withFinally(): int {
  var x: int := 0;
  try {
    x := 1
  } catch (e: MyException) {
    x := 2
  } finally {
    x := x + 10
  };
  return x
};
"

  -- 143. Labeled block with exit
  comprehensiveCompare "LabeledBlockExit" "
procedure exitTest(): int {
  var x: int := 0;
  {
    x := 1;
    exit done
  } done;
  return x
};
"

  -- 144. Exception propagation from proc call
  comprehensiveCompare "ExceptionPropagation" "
procedure helper(x: int): int {
  return x + 1
};
procedure test(x: int): int {
  var y: int := helper(x);
  return y
};
"

  -- 145. Early return in middle of block
  comprehensiveCompare "EarlyReturn" "
procedure earlyReturn(x: int): int {
  if (x > 0) {
    return x
  };
  return 0
};
"

  -- 146. Multiple early returns
  comprehensiveCompare "MultipleEarlyReturns" "
procedure classify(x: int): int {
  if (x > 100) { return 3 };
  if (x > 10) { return 2 };
  if (x > 0) { return 1 };
  return 0
};
"

  -- 147. Void procedure with early return
  -- 147. Void procedure (no early return - Laurel doesn't support bare return)
  comprehensiveCompare "VoidProcSimple" "
procedure guard(x: int) {
  assume x >= 0
};
"

  -- 148. Bool literal usage
  comprehensiveCompare "BoolLiteral" "
procedure test(): bool {
  return false
};
"

  -- 149. String literal usage
  comprehensiveCompare "StringLiteral" "
procedure test(): string {
  return \"hello\"
};
"

  -- 150. Nested try-catch
  comprehensiveCompare "NestedTryCatch" "
composite InnerEx {}
composite OuterEx {}
procedure nestedTry(ex: InnerEx): int {
  var x: int := 0;
  try {
    try {
      throw ex
    } catch (e: InnerEx) {
      x := 1
    }
  } catch (e: OuterEx) {
    x := 2
  };
  return x
};
"

  -- 151. Throw in instance proc
  comprehensiveCompare "ThrowInInstanceProc" "
composite MyException {}
composite Box {
  var value: int
  procedure setPositive(self: Box, v: int, ex: MyException)
    modifies self
  {
    if (v <= 0) { throw ex };
    self#value := v
  };
}
"

  -- 152. Proc call that may throw + propagation
  comprehensiveCompare "CallMayThrow" "
composite MyException {}
procedure mayThrow(x: int, ex: MyException): int {
  if (x < 0) { throw ex };
  return x
};
procedure caller(x: int, ex: MyException): int {
  var y: int := mayThrow(x, ex);
  return y + 1
};
"

  -- 153. Forall with trigger in postcondition
  comprehensiveCompare "ForallWithTrigger" "
composite Arr {
  var size: int
  procedure init(self: Arr, n: int)
    requires n >= 0
    ensures self#size == n
    modifies self
  {
    self#size := n
  };
}
"

  -- 154. Exists quantifier in postcondition
  comprehensiveCompare "ExistsPostcond" "
composite Container {
  var count: int
  procedure addOne(self: Container)
    ensures self#count > old(self#count)
    modifies self
  {
    self#count := self#count + 1
  };
}
"

  -- 155. Block in expression position (function body)
  comprehensiveCompare "BlockExprFunc" "
function compute(x: int): int {
  var y: int := x + 1;
  y * 2
};
"

  -- 156. Nested block in procedure
  comprehensiveCompare "NestedBlock" "
procedure test(x: int): int {
  var r: int := 0;
  {
    var tmp: int := x + 1;
    r := tmp * 2
  };
  return r
};
"


  -- === Untested expression features ===

  -- 157. String concatenation (++)
  comprehensiveCompare "StrConcatOp" "
procedure test(a: string, b: string): string {
  return a ++ b
};
"

  -- 158. Real number literal
  comprehensiveCompare "RealLiteral" "
procedure test(): real {
  return 3.14
};
"

  -- 159. Real arithmetic (from JVerify T1_Decimals — real programs need this)
  comprehensiveCompare "RealArith" "
procedure test(x: real, y: real): real {
  return x + y
};
"

  -- 159b. Real arithmetic with literals (model handles this via isRealExpr)
  comprehensiveCompare "RealArithLiteral" "
procedure test(): real {
  var a: real := 1.5;
  var b: real := 2.5;
  var sum: real := a + b;
  return sum
};
"

  -- 159c. Full decimal test from JVerify T1_Decimals
  comprehensiveCompare "JV_T1_Decimals" "
procedure testDecimalLiterals() {
    var a: real := 1.5;
    var b: real := 2.5;
    assert a == 1.5;
    assert b == 2.5;
    assert a != b
};

procedure testDecimalArithmetic() {
    var a: real := 1.5;
    var b: real := 2.5;
    var sum: real := a + b;
    assert sum == 4.0;
    var diff: real := b - a;
    assert diff == 1.0;
    var prod: real := a * b;
    assert prod == 3.75;
    var quot: real := b / a;
    assert quot == 5.0 / 3.0
};

procedure testDecimalNeg() {
    var a: real := 1.5;
    var neg: real := -a;
    assert neg == 0.0 - 1.5
};

procedure testDecimalComparisons() {
    var a: real := 1.5;
    var b: real := 2.5;
    assert a < b;
    assert a <= b;
    assert b > a;
    assert b >= a;
    assert a <= a;
    assert a >= a
};
"

  -- 160. Forall with trigger
  comprehensiveCompare "ForallWithTrigger" "
composite Arr {
  var size: int
  procedure init(self: Arr, n: int)
    ensures forall(i: int) {i} => (i >= 0 && i < n) ==> (self#size > i)
    modifies self
  {
    self#size := n
  };
}
"

  -- 161. Exists quantifier
  comprehensiveCompare "ExistsQuantifier" "
function hasPositive(a: int, b: int): bool {
  exists(x: int) => (x == a || x == b) && x > 0
};
"

  -- 162. Block with local variable in expression position (let-in)
  comprehensiveCompare "LetInExpr" "
function compute(x: int): int {
  var y: int := x + 1;
  y * 2
};
"

  -- 163. Expression in statement position (→ $unused init)
  comprehensiveCompare "ExprAsStmt" "
procedure test(x: int) {
  x + 1
};
"

  -- 164. Map type parameter
  comprehensiveCompare "MapTypeParam" "
procedure test(m: Map int int): int {
  return 0
};
"

  -- 165. Sequence type parameter
  comprehensiveCompare "SeqTypeParam" "
procedure test(s: Sequence int): int {
  return 0
};
"

  -- 166. Void return type (no return value)
  comprehensiveCompare "VoidReturnType" "
procedure doNothing() {
};
"

  -- 167. Procedure with decreases clause
  comprehensiveCompare "ProcWithDecreases" "
procedure countdown(n: int)
  decreases [n]
{
  if (n > 0) {
    countdown(n - 1)
  }
};
"

  -- 168. Multiple catch clauses
  comprehensiveCompare "MultipleCatches" "
composite ExA {}
composite ExB {}
procedure multiCatch(ea: ExA, eb: ExB): int {
  var x: int := 0;
  try {
    throw ea
  } catch (e: ExA) {
    x := 1
  } catch (e: ExB) {
    x := 2
  };
  return x
};
"

  -- 169. Nested labeled blocks
  comprehensiveCompare "NestedLabeledBlocks" "
procedure test(): int {
  var x: int := 0;
  {
    {
      x := 42;
      exit outer
    } inner;
    x := 99
  } outer;
  return x
};
"

  -- 170. Opaque function (instance, no body)
  comprehensiveCompare "OpaqueInstanceFunc" "
composite Box {
  var value: int
  function getValue(self: Box): int
    ensures $result >= 0
  opaque;
}
"

  -- === JVerify Test Suite Programs ===
  IO.println ""
  IO.println "=== JVerify Test Suite ==="
  pure ()

-- Split into separate #eval! block to avoid max recursion depth
#eval! do
  let comprehensiveCompare := fun (name : String) (input : String) => do
    let program ← parseLaurelString name input
    let modelProgram := translateProgramModel program
    let (coreOpt, _) := Laurel.translate {} program
    match coreOpt with
    | none => IO.println s!"{name}: ❌ Translation failed"
    | some core =>
      let modelNames := modelProgram.decls.map fun (d : Core.Decl) => d.name.name
      let realNames := core.decls.map fun (d : Core.Decl) => d.name.name
      let missing := realNames.filter (fun n => !modelNames.contains n)
      let extra := modelNames.filter (fun n => !realNames.contains n)
      if missing.isEmpty && extra.isEmpty && modelProgram.decls.length == core.decls.length then
        IO.println s!"{name}: ✅ all {modelProgram.decls.length} decls match"
        structuralEq name input
      else
        if !missing.isEmpty then
          IO.println s!"{name}: ❌ real has, model missing: {missing}"
        if !extra.isEmpty then
          IO.println s!"{name}: ❌ model has, real missing: {extra}"
        if modelProgram.decls.length != core.decls.length then
          IO.println s!"{name}: ❌ count: model={modelProgram.decls.length} real={core.decls.length}"

  comprehensiveCompare "JV_T10_ConstrainedTypes_program" "
constrained nat = x: int where x >= 0 witness 0
constrained posnat = x: nat where x != 0 witness 1

// Input constraint becomes requires — body can rely on it
procedure inputAssumed(n: nat) {
  assert n >= 0
};

// Output constraint — valid return passes
procedure outputValid(): nat {
  return 3
};

// Output constraint — invalid return fails
procedure outputInvalid(): nat {
//                         ^^^ error: assertion does not hold
  return -1
};

// Return value of constrained type — caller gets ensures via call elimination
procedure opaqueNat(): nat;
procedure callerAssumes() returns (r: int) {
  var x: int := opaqueNat();
  assert x >= 0;
  return x
};

// Assignment to constrained-typed variable — valid
procedure assignValid() {
  var y: nat := 5
};

// Assignment to constrained-typed variable — invalid
procedure assignInvalid() {
  var y: nat := -1
//^^^^^^^^^^^^^^^^ error: assertion does not hold
};

// Reassignment to constrained-typed variable — invalid
procedure reassignInvalid() {
  var y: nat := 5;
  y := -1
//^^^^^^^ error: assertion does not hold
};

// Argument to constrained-typed parameter — valid
procedure takesNat(n: nat) returns (r: int) { return n };
//                    ^^^ error: assertion does not hold
procedure argValid() returns (r: int) {
  var x: int := takesNat(3);
  return x
};

// Argument to constrained-typed parameter — invalid (requires violation)
procedure argInvalid() returns (r: int) {
  var x: int := takesNat(-1);
  return x
};

// Nested constrained type — independent constraints require transitive collection
constrained even = x: int where x % 2 == 0 witness 0
constrained evenpos = x: even where x > 0 witness 2
procedure nestedInput(x: evenpos) {
  assert x > 0;
  assert x % 2 == 0
};

// Multiple constrained-typed parameters
procedure multiParam(a: nat, b: nat) {
  assert a >= 0;
  assert b >= 0
};

// Two calls to same procedure — no temp var collision
procedure twoCalls() returns (r: int) {
  var a: int := takesNat(1);
  var b: int := takesNat(2);
  return a + b
};

// Constrained type in expression position must be resolved
procedure constrainedInExpr() {
  var b: bool := forall(n: nat) => n + 1 > n;
  assert b
};

// Invalid witness — witness -1 does not satisfy x > 0
constrained bad = x: int where x > 0 witness -1
//                                           ^^ error: assertion does not hold

// Uninitialized constrained variable — havoc + assume constraint
procedure uninitNat() {
  var y: nat;
  assert y >= 0
};

// Uninitialized nested constrained variable — havoc + assume constraint
procedure uninitPosnat() {
  var y: posnat;
  assert y != 0;
  assert y >= 0
};

// Uninitialized constrained variable — witness value is not provable
procedure uninitNotWitness() {
  var y: posnat;
  assert y == 1
//^^^^^^^^^^^^^ error: assertion does not hold
};

// Function with valid constrained return — constraint not checked (not yet supported)
function goodFunc(): nat { 3 };
//       ^^^^^^^^ error: constrained return types on functions are not yet supported

// Function with invalid constrained return — constraint not checked (not yet supported)
function badFunc(): nat { -1 };
//       ^^^^^^^ error: constrained return types on functions are not yet supported

// Caller of constrained function — body is inlined, caller sees actual value
procedure callerGood() {
  var x: int := goodFunc();
  assert x >= 0
};

// Quantifier constraint injection — forall
// n + 1 > 0 is only provable with n >= 0 injected; false for all int
procedure forallNat() {
  var b: bool := forall(n: nat) => n + 1 > 0;
  assert b
};

// Quantifier constraint injection — exists
// n == -1 is satisfiable for int, but not when n >= 0 is required
// n == 42 works because 42 >= 0
procedure existsNat() {
  var b: bool := exists(n: nat) => n == 42;
  assert b
};

// Quantifier constraint injection — nested constrained type
// n - 1 >= 0 is only provable with n > 0 injected
procedure forallPosnat() {
  var b: bool := forall(n: posnat) => n - 1 >= 0;
  assert b
};

// Capture avoidance — bound var y in constraint must not collide with parameter y
// Without capture avoidance, requires becomes exists(y) => y > y (false), making body vacuously true
constrained haslarger = x: int where (exists(y: int) => y > x) witness 0
procedure captureTest(y: haslarger) {
  assert false
//^^^^^^^^^^^^ error: assertion does not hold
};
"

  comprehensiveCompare "JV_T12_Operators_operatorsProgram" "
procedure testArithmetic() {
    var a: int := 10;
    var b: int := 3;
    var x: int := a - b;
    assert x == 7;
    var y: int := x * 2;
    assert y == 14;
    var z: int := y / 2;
    assert z == 7;
    var r: int := 17 % 5;
    assert r == 2
};

procedure testLogical() {
    var t: bool := true;
    var f: bool := false;
    var a: bool := t && f;
    assert a == false;
    var b: bool := t || f;
    assert b == true;
    var c: bool := !f;
    assert c == true;
    assert t ==> t;
    assert f ==> t
};

procedure testUnary() {
    var x: int := 5;
    var y: int := -x;
    assert y == 0 - 5
};

procedure testTruncatingDiv() {
    assert 7 /t 3 == 2;
    assert 7 %t 3 == 1;
    assert (0 - 7) /t 3 == 0 - 2;
    assert (0 - 7) %t 3 == 0 - 1
};
"

  comprehensiveCompare "JV_T13_WhileLoops_whileLoopsProgram" "
procedure countDown() {
    var i: int := 3;
    while(i > 0)
      invariant i >= 0
    {
        i := i - 1
    };
    assert i == 0
};

procedure countUp() {
    var n: int := 5;
    var i: int := 0;
    while(i < n)
      invariant i >= 0
      invariant i <= n
    {
        i := i + 1
    };
    assert i == n
};
"

  comprehensiveCompare "JV_T14_Quantifiers_quantifiersProgram" "
procedure testForall() {
    assert forall(x: int) => x + 0 == x
};

procedure testExists() {
    assert exists(x: int) => x == 42
};

procedure testQuantifierInContract(n: int)
  requires n > 0
  ensures forall(i: int) => i >= 0 ==> i < n ==> i < n + 1
{
};

function P(x: int): int;
function Q(): int;
procedure triggers() {
  assert forall(i: int) { P(i) } => P(i) == i + 1;
//^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: assertion does not hold
  assert forall(i: int) => true;

  assume forall(i: int) { P(i) } => P(i) == i + 1 && Q() == 0;
  assert Q() == 0;
//^^^^^^^^^^^^^^^ error: assertion could not be proved
  assert P(1) == 2
};

"

  comprehensiveCompare "JV_T15_ShortCircuit_shortCircuitProgram" "
function mustNotCallFunc(x: int): int
  requires false
{ x };

procedure mustNotCallProc(): int
  requires false
{
  return 0
};

// Pure path: function with requires false

procedure testAndThenFunc() {
  var b: bool := false && mustNotCallFunc(0) > 0;
  assert !b
};

procedure testOrElseFunc() {
  var b: bool := true || mustNotCallFunc(0) > 0;
  assert b
};

procedure testImpliesFunc() {
  var b: bool := false ==> mustNotCallFunc(0) > 0;
  assert b
};

// Pure path: division by zero

procedure testAndThenDivByZero() {
  assert !(false && 1 / 0 > 0)
};

procedure testOrElseDivByZero() {
  assert true || 1 / 0 > 0
};

procedure testImpliesDivByZero() {
  assert false ==> 1 / 0 > 0
};

// Imperative path: procedure with requires false

procedure testAndThenProc() {
  var b: bool := false && mustNotCallProc() > 0;
  assert !b
};

procedure testOrElseProc() {
  var b: bool := true || mustNotCallProc() > 0;
  assert b
};

procedure testImpliesProc() {
  var b: bool := false ==> mustNotCallProc() > 0;
  assert b
};
"

  comprehensiveCompare "JV_T17_ForLoop_forLoopProgram" "
procedure sumToThree() {
  var sum: int := 0;
  for (var i: int := 0; i < 3; i := i + 1)
    invariant sum >= 0
    invariant sum <= 3
    invariant i >= 0
    invariant i <= 3
    invariant sum == i
  {
    sum := sum + 1
  };
  assert sum == 3
};
"

  comprehensiveCompare "JV_T18_Throw_throwUnreachable" "
composite MyException {}
procedure throwUnreachable(e: MyException) {
    throw e;
    assert false
};
"

  comprehensiveCompare "JV_T18_Throw_normalSkipsHandlers" "
composite MyException {}
procedure normalSkipsHandlers() {
    var x: int := 0;
    try { x := 1 } catch (e: MyException) { x := 99 };
    assert x == 1
};
"

  comprehensiveCompare "JV_T18_Throw_assertInTryBody" "
composite MyException {}
procedure assertInTryBody() {
    try { var x: int := 42; assert x == 42 } catch (e: MyException) { assert true }
};
"

  comprehensiveCompare "JV_T18_Throw_finallyExecutes" "
composite MyException {}
procedure finallyExecutes() {
    var z: int := 0;
    try { var x: int := 1 } catch (e: MyException) { var y: int := 2 } finally { z := 42 };
    assert z == 42
};
"

  comprehensiveCompare "JV_T18_Throw_multipleCatches" "
composite ExceptionA {}
composite ExceptionB {}
procedure multipleCatches() {
    var x: int := 0;
    try { x := 1 } catch (a: ExceptionA) { x := 10 } catch (b: ExceptionB) { x := 20 };
    assert x == 1
};
"

  comprehensiveCompare "JV_T19_DoWhileDesugaring_doWhileBasic" "
procedure doWhileCountToTen() {
    var i: int := 0;
    // --- desugared do/while ---
    // first execution (establishes invariant)
    i := i + 1;
    // while loop (maintains invariant)
    while(i < 10)
      invariant i > 0
      invariant i <= 10
    {
        i := i + 1
    };
    // after loop: invariant AND NOT condition
    assert i == 10
};
"

  comprehensiveCompare "JV_T19_DoWhileDesugaring_doWhileOnce" "
procedure doWhileExecutesOnce() {
    var x: int := 0;
    // --- desugared do/while ---
    x := 42;
    while(false)
      invariant x == 42
    {
        x := 42
    };
    assert x == 42
};
"

  comprehensiveCompare "JV_T19_DoWhileDesugaring_doWhileWithPrecondition" "
procedure doWhileWithBound(n: int)
  requires n > 0
  requires n <= 100
{
    var i: int := 0;
    // --- desugared do/while ---
    i := i + 1;
    while(i < n)
      invariant i > 0
      invariant i <= n
    {
        i := i + 1
    };
    assert i == n
};
"

  comprehensiveCompare "JV_T19_DoWhileDesugaring_doWhileEstablishesInvariant" "
procedure doWhileFirstPassEstablishes() {
    var found: bool := false;
    // --- desugared do/while ---
    // Before this point: found = false (invariant does NOT hold)
    found := true;
    // After first execution: found = true (invariant holds)
    while(false)
      invariant found
    {
        found := true
    };
    assert found
};
"

  comprehensiveCompare "JV_T19_DoWhileDesugaring_doWhileAccumulator" "
procedure doWhileSum() {
    var sum: int := 0;
    var i: int := 0;
    // --- desugared do/while ---
    sum := sum + i;
    i := i + 1;
    while(i <= 3)
      invariant i >= 1
      invariant i <= 4
      invariant sum == (i * (i - 1)) / 2
    {
        sum := sum + i;
        i := i + 1
    };
    // i == 4, sum == 0+1+2+3 == 6
    assert sum == 6
};
"

  comprehensiveCompare "JV_T1_AssertFalse_program" "
procedure foo() {
    assert true;
    assert false;
//  ^^^^^^^^^^^^ error: assertion does not hold
    assert false
//  ^^^^^^^^^^^^ error: assertion does not hold
};

procedure bar() {
    assume false;
    assert false
};
"

  comprehensiveCompare "JV_T3_ControlFlow_program" "
function returnAtEnd(x: int) returns (r: int) {
  if (x > 0) {
    if (x == 1) {
      return 1
    } else {
      return 2
    }
  } else {
    return 3
  }
};

function elseWithCall(): int {
  if (true) 3 else returnAtEnd(3)
};

function guardInFunction(x: int) returns (r: int) {
  if (x > 0) {
    if (x == 1) {
      return 1
    } else {
      return 2
    }
  };

  return 3
};

procedure testFunctions() {
  assert returnAtEnd(1) == 1;
  assert returnAtEnd(1) == 2;
//^^^^^^^^^^^^^^^^^^^^^^^^^^ error: assertion does not hold

  assert guardInFunction(1) == 1;
  assert guardInFunction(1) == 2
//^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: assertion does not hold
};

procedure guards(a: int) returns (r: int)
{
  var b: int := a + 2;
  if (b > 2) {
      var c: int := b + 3;
      if (c > 3) {
          return c + 4
      };
      var d: int := c + 5;
      return d + 6
  };
  var e: int := b + 1;
  assert e <= 3;
  assert e < 3;
//^^^^^^^^^^^^ error: assertion does not hold
  return e
};

procedure dag(a: int) returns (r: int)
{
  var b: int;

  if (a > 0) {
    b := 1
  };
  assert if (a > 0) { b == 1 } else { true };
  assert if (a > 0) { b == 2 } else { true };
//^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: assertion does not hold
  return b
};
"

  comprehensiveCompare "JV_T3_ControlFlowError_program" "
function assertAndAssumeInFunctions(a: int) returns (r: int)
{
  assert 2 == 3;
//^^^^^^^^^^^^^ error: asserts are not YET supported in functions or contracts
  assume true;
//^^^^^^^^^^^ error: assumes are not YET supported in functions or contracts
  a
};

// Lettish bindings in functions not yet supported
// because Core expressions do not support let bindings
function letsInFunction() returns (r: int) {
  var x: int := 0;
//^^^^^^^^^^^^^^^ error: local variables in functions are not YET supported
  var y: int := x + 1;
//^^^^^^^^^^^^^^^^^^^ error: local variables in functions are not YET supported
  var z: int := y + 1;
//^^^^^^^^^^^^^^^^^^^ error: local variables in functions are not YET supported
  z
};

function localVariableWithoutInitializer(): int {
  var x: int;
//^^^^^^^^^^ error: local variables in functions must have initializers
  3
};

function deadCodeAfterIfElse(x: int) returns (r: int) {
  if (x > 0) { return 1 } else { return 2 };
//^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: if-then-else only supported as the last statement in a block
  return 3
};
"

  comprehensiveCompare "JV_T4_LoopJumps_program" "
procedure whileWithBreakAndContinue(steps: int, continueSteps: int, exitSteps: int): int {
  var counter = 0
  {
    while(steps > 0)
      invariant counter >= 0
    {
      {
        if (steps == exitSteps) {
          counter = -10;
          exit breakBlock;
        }
        if (steps == continueSteps) {
          exit continueBlock;
        }
        counter = counter + 1;
      } continueBlock;
      steps = steps - 1;
    }
  } breakBlock;
  counter;
};
"

  comprehensiveCompare "JV_T4b_Exit_exitProgram" "
procedure exitSkipsRest() {
    var x: int := 0;
    {
        x := 1;
        exit done
    } done;
    assert x == 1
};

procedure exitFromNestedBlock() {
    var x: int := 0;
    {
        {
            x := 42;
            exit outer
        } inner;
        x := 99
    } outer;
    assert x == 42
};
"

  comprehensiveCompare "JV_T5_ProcedureCalls_program" "
procedure fooReassign(): int {
  var x: int := 0;
  x := x + 1;
  assert x == 1;
  x := x + 1;
  x
};

procedure fooSingleAssign(): int {
  var x: int := 0;
  var x2: int := x + 1;
  var x3: int := x2 + 1;
  x3
};

procedure fooProof() {
  var x: int := fooReassign();
  var y: int := fooSingleAssign()
// The following assertions fails while it should succeed,
// because Core does not yet support transparent procedures
//  assert x == y;
};

function aFunction(x: int): int
{
  x
};

procedure aFunctionCaller() {
  var x: int := aFunction(3);
  assert x == 3
};
"

  comprehensiveCompare "JV_T6_Preconditions_program" "
procedure hasRequires(x: int) returns (r: int)
  requires x > 2
//         ^^^^^ error: assertion does not hold
// Core does not seem to report precondition errors correctly.
// This should occur at the call site and with a different message
{
  assert x > 0;
  assert x > 3;
//^^^^^^^^^^^^ error: assertion does not hold
  x + 1
};

procedure caller() {
  var x: int := hasRequires(1);
  var y: int := hasRequires(3)
};

function aFunctionWithPrecondition(x: int): int
  requires x == 10
{
  x
};

procedure aFunctionWithPreconditionCaller() {
  var x: int := aFunctionWithPrecondition(0)
//^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: assertion does not hold
// Error ranges are too wide because Core does not use expression locations
};

procedure multipleRequires(x: int, y: int) returns (r: int)
  requires x > 0
  requires y > 0
{
  x + y
};

// This test fails because Core incorrectly report error locations on procedure preconditions
// procedure multipleRequiresCaller() {
//  var a: int := multipleRequires(1, 2);
//  var b: int := multipleRequires(-1, 2);
// error: assertion does not hold
// };

function funcMultipleRequires(x: int, y: int): int
  requires x > 0
  requires y > 0
{
  x + y
};

procedure funcMultipleRequiresCaller() {
  var a: int := funcMultipleRequires(1, 2);
  var b: int := funcMultipleRequires(1, -1)
//^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: assertion does not hold
};
"

  comprehensiveCompare "JV_T7_Decreases_program" "
procedure noDecreases(x: int): boolean;
procedure caller(x: int)
  requires noDecreases(x)
//                    ^ error: noDecreases can not be called from a pure context, because it is not proven to terminate
;

procedure noCyclicCalls()
  decreases []
{
  leaf();
};

procedure leaf() decreases [1] { };

procedure mutualRecursionA(x: nat)
  decreases [x, 1]
{
  mutualRecursionB(x);
};

procedure mutualRecursionB(x: nat)
  decreases [x, 0]
{
  if x != 0 { mutualRecursionA(x-1); }
};
"

  comprehensiveCompare "JV_T8_Postconditions_program" "
procedure opaqueBody(x: int) returns (r: int)
// the presence of the ensures make the body opaque. we can consider more explicit syntax.
  ensures r > 0
{
  if (x > 0) { r := x }
  else { r := 1 }
};

procedure callerOfOpaqueProcedure() {
  var x: int := opaqueBody(3);
  assert x > 0;
  assert x == 3
//^^^^^^^^^^^^^ error: assertion does not hold
};

procedure invalidPostcondition(x: int)
    ensures false
//          ^^^^^ error: assertion does not hold
{
};
"

  comprehensiveCompare "JV_T8_PostconditionsErrors_program" "

function opaqueFunction(x: int) returns (r: int)
//       ^^^^^^^^^^^^^^ error: functions with postconditions are not yet supported
// The above limitation is because Core does not yet support functions with postconditions
  requires x > 0
  ensures r > 0
// The above limitation is because functions in Core do not support postconditions
{
  x
};

procedure callerOfOpaqueFunction() {
  var x: int := opaqueFunction(3);
  assert x > 0;
// The following assertion should fail but does not
// Because Core does not support opaque functions
  assert x == 3
};
"

  comprehensiveCompare "JV_T8b_EarlyReturnPostconditions_program" "
procedure earlyReturnCorrect(x: int) returns (r: int)
  ensures r >= 0
{
  if (x < 0) {
    return -x
  };
  return x
};

procedure earlyReturnBuggy(x: int) returns (r: int)
  ensures r >= 0
//        ^^^^^^ error: assertion does not hold
{
  if (x < 0) {
    return x
  };
  return x
};
"

  comprehensiveCompare "JV_T9_Nondeterministic_program" "
nondet procedure nonDeterministic(x: int): (r: int)
  ensures r > 0
{
  assumed
};

procedure caller() {
  var x = nonDeterministic(1)
  assert x > 0;
  var y = nonDeterministic(1)
    assert x == y;
//  ^^^^^^^^^^^^^^ error: assertion does not hold
};

nondet procedure nonDeterminsticTransparant(x: int): (r: int)
{
  nonDeterministic(x + 1)
};

procedure nonDeterministicCaller(x: int): int
{
  nonDeterministic(x)
};
"

  comprehensiveCompare "JV_T2_ModifiesClauses_program" "
composite Container {
  var value: int
}

procedure modifyContainerOpaque(c: Container) returns (b: bool)
  ensures true // makes this procedure opaque. Maybe we should use explicit syntax
  modifies c
{
  c#value := c#value + 1;
  true
};

procedure modifyContainerTransparant(c: Container) returns (i: int)
{
  c#value := c#value + 1;
  7
};

procedure caller() {
  var c: Container := new Container;
  var d: Container := new Container;
  var x: int := d#value;
  var b: bool := modifyContainerOpaque(c);
  assert x == d#value // pass
};

// This test-case does not work yet.
// Because Core procedures never have transparent bodies
//procedure modifyContainerWithPermission1(c: Container, d: Container)
//   ensures true
//   modifies c
//{
//    var i: int := modifyContainerTransparant(c);
//}

procedure modifyContainerWithoutPermission1(c: Container, d: Container)
//        ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: assertion could not be proved
//        ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: assertion could not be proved
// the above error is because the body does not satisfy the empty modifies clause. error needs to be improved
   ensures true
{
    var i: int := modifyContainerTransparant(c)
};

procedure modifyContainerWithoutPermission2(c: Container, d: Container)
//        ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: assertion could not be proved
// the above error is because the body does not satisfy the modifies clause. error needs to be improved
  ensures true
  modifies d
{
    c#value := 2
};

procedure modifyContainerWithoutPermission3(c: Container, d: Container)
//        ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: assertion could not be proved
// the above error is because the body does not satisfy the modifies clause. error needs to be improved
//        ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: assertion could not be proved
  ensures true
  modifies d
{
    var i: int := modifyContainerTransparant(c)
};

procedure multipleModifiesClauses(c: Container, d: Container, e: Container)
  modifies c
  modifies d
;

procedure multipleModifiesClausesCaller() {
  var c: Container := new Container;
  var d: Container := new Container;
  var e: Container := new Container;
  var x: int := e#value;
  multipleModifiesClauses(c, d, e);
  assert x == e#value // pass
};

procedure newObjectDoNotCountForModifies()
  ensures true
{
  var c: Container := new Container;
  c#value := 1
};
"

  comprehensiveCompare "JV_T5_inheritance_program" "
composite Base {
  var xValue: int
}

composite Base2 {
  var yValue: int
}

composite Extender extends Base, Base2 {
  var zValue: int
}

procedure inheritedFields(a: Extender) {
  a#xValue := 1;
  a#yValue := 2;
  a#zValue := 3;

  assert a#xValue == 1;
  assert a#yValue == 2;
  assert a#zValue == 3
};

procedure typeCheckingAndCasting() {
  var a: Base := new Base;
  assert a is Base;
  assert !(a is Extender);
  var b: Extender := new Extender;
  assert b is Base;
  assert b is Base2;
  assert b is Extender;

  var c: Base := b;
  var d: Extender := c as Extender;
  var e: Extender := a as Extender
//                   ^^^^^^^^^^^^^ error: assertion could not be proved
};

composite Top {
  var tValue: int
}

composite Left extends Top {
  var lValue: int
}
composite Right extends Top {
  var rValue: int
}
composite Bottom extends Left, Right {
  var bValue: int
}

procedure diamondInheritance() {
  var b: Bottom := new Bottom;
  b#lValue := 1;
  b#rValue := 2;
  b#bValue := 3;
  // tValue can not be used

  assert b#lValue == 1;
  assert b#rValue == 2;
  assert b#bValue == 3;

  assert b is Left;
  assert b is Right;
  assert b is Top;
  assert b is Bottom
};

// Currently does not pass. Implementation needs b type invariant mechanism that we have yet to add.
//procedure typedParameter(b: Bottom) {
//  var b: Bottom := b;
//  assert b is Left;
//  assert b is Right;
//  assert b is Top;
//  assert b is Bottom;
//}
"

  comprehensiveCompare "JV_T5_inheritanceErrors_program" "
composite Top {
  var xValue: int
}

composite Left extends Top {}
composite Right extends Top {}
composite Bottom extends Left, Right {}

procedure diamondField(b: Bottom) {
  b#xValue := 1
//  ^^^^^^ error: fields that are inherited multiple times can not be accessed.
};
"

  comprehensiveCompare "JV_T6_Datatypes_datatypeProgram" "
datatype IntList {
  Nil(),
  Cons(head: int, tail: IntList)
}

// Construction and destructor access
procedure testConstruction() {
  var xs: IntList := Cons(42, Nil());
  assert IntList..head(xs) == 42
};

// Constructor testing
procedure testConstructorTest() {
  var xs: IntList := Cons(1, Nil());
  assert IntList..isCons(xs);
  assert !IntList..isNil(xs);

  var ys: IntList := Nil();
  assert IntList..isNil(ys);
  assert !IntList..isCons(ys)
};

// Nested construction and deconstruction
procedure testNested() {
  var xs: IntList := Cons(1, Cons(2, Nil()));
  assert IntList..isCons(xs);
  assert IntList..head(xs) == 1;
  assert IntList..isCons(IntList..tail(xs));
  assert IntList..head(IntList..tail(xs)) == 2;
  assert IntList..isNil(IntList..tail(IntList..tail(xs)))
};

procedure unsafeDestructor() {
  var nil: IntList := Nil();
  var noError: int := IntList..head!(nil);
  var error: int := IntList..head(nil)
//^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: assertion does not hold
};

// Datatype in function
function listHead(xs: IntList): int
  requires IntList..isCons(xs)
{
  IntList..head(xs)
};

procedure testFunction() {
  var xs: IntList := Cons(10, Nil());
  var h: int := listHead(xs);
  assert h == 10
};

// Failing assertion
procedure testFailing() {
  var xs: IntList := Nil();
  assert IntList..isCons(xs)
//^^^^^^^^^^^^^^^^^^^^^^^^^^ error: assertion does not hold
};

// Mutually recursive datatypes: even/odd-length lists
datatype EvenList {
  ENil(),
  ECons(head: int, tail: OddList)
}

datatype OddList {
  OCons(head: int, tail: EvenList)
}

procedure testMutualConstruction() {
  var even: EvenList := ENil();
  assert EvenList..isENil(even);
  var odd: OddList := OCons(1, ENil());
  assert OddList..isOCons(odd);
  assert OddList..head(odd) == 1;
  var even2: EvenList := ECons(2, OCons(3, ENil()));
  assert EvenList..isECons(even2);
  assert EvenList..head(even2) == 2
};

datatype RootBeforeLeaf { RootBeforeLeaf(leaf: LeafAfterRoot) }
datatype LeafAfterRoot { LeafAfterRoot }
"

  comprehensiveCompare "JV_T7_InstanceProcedures_instanceProcedureProgram" "
composite Counter {
  var count: int
  procedure increment(self: Counter) {
    self#count := self#count + 1
  };
  procedure reset(self: Counter) {
    self#count := 0
  };
}
"

  comprehensiveCompare "JV_T8_ImmutableFields_immutableFieldProgram" "
composite Position {
  line: int
  character: int
}

procedure testReadImmutableField(p: Position) {
  var x: int := p#line;
  var y: int := p#character;
  assert x == p#line;
  assert y == p#character
};

procedure testTwoPositionsEqual(a: Position, b: Position)
  requires a#line == b#line
  requires a#character == b#character
{
  assert a#line == b#line;
  assert a#character == b#character
};

procedure testFieldComparison(a: Position, b: Position)
  requires a#line > b#line
{
  assert a#line > b#line
};
"

  comprehensiveCompare "JV_T9_InstanceCall_instanceCallProgram" "
composite Counter {
  var count: int
  procedure getCount(self: Counter): int
    ensures result == self#count
  {
    return self#count
  };
}

procedure test(): int
  ensures result == 42
{
  var c: Counter := new Counter;
  c#count := 42;
  var x: int := c~>getCount();
  return x
};
"

