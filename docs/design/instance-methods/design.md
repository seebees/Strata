# Instance Method Support: Design

**Date:** 2026-03-26

Implementation plan for instance method support in the Strata Laurel
pipeline. Each section is a file change with the specific modification
and test cases to verify it.

---

## 1. Shared Name Function

**File:** `Strata/Languages/Laurel/Laurel.lean`

Add `instanceProcCoreName` to the Laurel module where both the
translator and future proof can reference it.

```lean
def instanceProcCoreName (typeName : String) (procName : String) : String :=
  typeName ++ ".." ++ procName
```

**Tests:** None needed — exercised through downstream changes.

---

## 2. Heap Analysis: Track InstanceCall Callees

**File:** `Strata/Languages/Laurel/HeapParameterization.lean`
**Function:** `collectExpr`

Change the `InstanceCall` case from:
```lean
| .InstanceCall target _ args => collectExprMd target; for a in args do collectExprMd a
```
to:
```lean
| .InstanceCall target callee args =>
    modify fun s => { s with callees := callee :: s.callees }
    collectExprMd target; for a in args do collectExprMd a
```

Same as `StaticCall` — add callee to the callees list so the fixpoint
computation propagates heap access transitively.

**Test: Indirect heap access through instance call.**
A static procedure that only touches the heap through an instance call
(no direct field access, no `new`). Verify it gets `$heap` parameters.
```
composite Counter { var count: int }
// increment writes heap directly
procedure Counter.increment(self: Counter) { self#count := self#count + 1 };
// caller only touches heap through the instance call
procedure callIncrement(c: Counter) { c.increment() };
```
If the analysis doesn't track the callee, `callIncrement` won't get
`$heap` and the program will fail.

---

## 3. Heap Transform: Inject $heap into InstanceCall

**File:** `Strata/Languages/Laurel/HeapParameterization.lean`
**Function:** `heapTransformExpr`

Change the `InstanceCall` case from passing through unchanged to
injecting `$heap`, following the same pattern as `StaticCall`:

```
InstanceCall target callee args:
  - if callee writes heap:
      if value used:
        var fresh; (heap, fresh) := InstanceCall target callee (heap :: args); fresh
      else:
        heap := InstanceCall target callee (heap :: args)
  - else if callee reads heap:
      InstanceCall target callee (heap :: args)
  - else:
      InstanceCall target callee args
```

**Test: Instance method that reads heap.**
```
composite Box { var value: int }
procedure Box.getValue(self: Box): int { return self#value };
procedure reader(b: Box): int { return b.getValue() };
```
Verify `reader` gets `$heap` as input (reads heap transitively).

**Test: Instance method that writes heap.**
```
composite Box { var value: int }
procedure Box.setValue(self: Box, v: int) { self#value := v };
procedure writer(b: Box) { b.setValue(42) };
```
Verify `writer` gets `$heap` as input AND output.

---

## 4. Modifies Clauses: Process Instance Procedures

**File:** `Strata/Languages/Laurel/ModifiesClauses.lean`
**Function:** `modifiesClausesTransform`

Also iterate instance procedures from composites:
```lean
let types' := program.types.map fun td =>
  match td with
  | .Composite ct =>
    let (instProcs', instErrs) := ct.instanceProcedures.foldl (fun (acc, errs) proc =>
      match transformModifiesClauses model proc with
      | .ok proc' => (acc ++ [proc'], errs)
      | .error newErrs => (acc ++ [proc], errs ++ newErrs.toList)) ([], [])
    -- accumulate errors...
    .Composite { ct with instanceProcedures := instProcs' }
  | other => other
```

**Test: Instance method with modifies clause.**
```
composite Container { var value: int }
procedure Container.update(self: Container)
  ensures true
  modifies self
{ self#value := 42 };

procedure caller() {
  var c: Container := new Container;
  var d: Container := new Container;
  var x: int := d#value;
  c.update();
  assert x == d#value  // should pass — modifies only c
};
```
This is the instance method version of T2_ModifiesClauses.

---

## 5. Translator: Instance Procedure Definitions

**File:** `Strata/Languages/Laurel/LaurelToCoreTranslator.lean`
**Function:** `translateLaurelToCore`

Remove the "not yet supported" diagnostic. Collect instance procedures
from composites and translate them using `translateProcedure`, but with
the qualified name:

```lean
for td in program.types do
  if let .Composite ct := td then
    for proc in ct.instanceProcedures do
      let qualifiedProc := { proc with
        name := { proc.name with text := instanceProcCoreName ct.name.text proc.name.text } }
      let coreProc ← translateProcedure qualifiedProc
      -- add to procedures list
```

**Test: Instance procedure appears in Core output.**
```
composite Counter { var count: int }
procedure Counter.increment(self: Counter) { self#count := self#count + 1 };
```
Verify a Core procedure named `Counter..increment` exists with
inputs `($heap, self: Composite)` and output `($heap, $result)`.

---

## 6. Translator: InstanceCall at Call Sites

**File:** `Strata/Languages/Laurel/LaurelToCoreTranslator.lean`
**Functions:** `translateExpr`, `translateStmt`

Replace all `InstanceCall` havoc/error cases with actual translation.
Look up callee in SemanticModel to get the type name, construct the
qualified name via `instanceProcCoreName`, emit Core call with
`target` prepended to args.

### Expression position (functional instance method)
```lean
| .InstanceCall target callee args =>
    match model.get callee with
    | .instanceProcedure typeName _ =>
        let coreName := instanceProcCoreName typeName.text callee.text
        -- translate as function application
        let coreTarget ← translateExpr target
        let coreArgs ← args.mapM translateExpr
        return .app () ⟨coreName, ()⟩ (coreTarget :: coreArgs)
    | _ => throwExprDiagnostic ...
```

### Variable initializer (`var x := target.method(args)`)
Same pattern as StaticCall initializer but with qualified name and
target prepended to args.

### Assignment (`x := target.method(args)`)
Same pattern as StaticCall assignment.

### Statement position (`target.method(args)`)
Same pattern as StaticCall statement — call with no return value
capture (just `$result` for exception propagation).

### Multi-assignment
Same pattern as StaticCall multi-assignment.

**Test: Instance call in variable initializer.**
```
composite Box { var value: int }
procedure Box.getValue(self: Box): int
  ensures true
{ return self#value };

procedure test() {
  var b: Box := new Box;
  var x: int := b.getValue();
};
```

**Test: Instance call as statement.**
```
composite Counter { var count: int }
procedure Counter.increment(self: Counter)
  modifies self
{ self#count := self#count + 1 };

procedure test() {
  var c: Counter := new Counter;
  c.increment();
  assert c#count == 1   // should fail — we don't know initial count
};
```

**Test: Instance call with postcondition verification.**
```
composite Counter { var count: int }
procedure Counter.increment(self: Counter)
  ensures self#count == old(self#count) + 1
  modifies self
{ self#count := self#count + 1 };

procedure test(c: Counter)
  modifies c
{
  assume c#count == 0;
  c.increment();
  assert c#count == 1   // should pass via postcondition
};
```
Note: this test needs `old()` support (F3). May need to defer.

---

## 7. Consistency Proof

**File:** `Strata/Languages/Laurel/InstanceMethodProperties.lean` (new)

```lean
theorem instance_call_name_consistency
  (model : SemanticModel) (calleeId : Nat)
  (typeName : Identifier) (proc : Procedure)
  (h : model.refToDef.get? calleeId =
       some (.instanceProcedure typeName proc)) :
  instanceProcCoreName typeName.text proc.name.text
  =
  instanceProcCoreName typeName.text proc.name.text := by
  rfl
```

---

## 8. Update Existing Tests

**File:** `StrataTest/Languages/Laurel/Examples/Objects/T7_InstanceProcedures.lean`

Change from expecting "not yet supported" errors to expecting success.
The Counter example should translate and verify without errors.

---

## Edge Cases to Test

These are the scenarios most likely to reveal bugs:

**E1: Name collision with heap constants.**
An instance method named `increment` (same as the heap allocation
function). Verify the qualified name `Counter..increment` avoids
the collision.

**E2: Two types with same method name.**
```
composite A { procedure foo(self: A) { ... }; }
composite B { procedure foo(self: B) { ... }; }
```
Verify `A..foo` and `B..foo` are distinct Core procedures and calls
resolve to the correct one.

**E3: Instance method calling another instance method.**
```
composite Counter { var count: int }
procedure Counter.reset(self: Counter) { self#count := 0 };
procedure Counter.resetAndIncrement(self: Counter) {
  self.reset();
  self#count := self#count + 1
};
```
Verify the heap analysis propagates transitively and both methods
get correct `$heap` parameters.

**E4: Static procedure calling instance method.**
```
procedure test() {
  var c: Counter := new Counter;
  c.increment();
  assert c#count == 1
};
```
The most common pattern — static test harness calling instance methods.

**E5: Instance method with exception support.**
```
composite Validator { var limit: int }
procedure Validator.validate(self: Validator, x: int) {
  if (x > self#limit) { throw new IllegalArgumentException }
};
```
Verify exception propagation works with instance methods — the
`$result` output parameter and propagation check should work
identically to static procedures.

**E6: Instance method with precondition.**
```
composite Stack { var size: int }
procedure Stack.pop(self: Stack)
  requires self#size > 0
  modifies self
{ self#size := self#size - 1 };
```
Verify precondition checking works at the call site.

**E7: Multiple instance methods, one opaque.**
```
composite Buffer { var pos: int }
procedure Buffer.write(self: Buffer)
  ensures self#pos > old(self#pos)
  modifies self
;  // opaque — no body

procedure Buffer.writeTwo(self: Buffer)
  modifies self
{
  self.write();
  self.write();
};
```
Verify opaque instance methods work — caller uses postcondition
without seeing the body.

---

## Implementation Order

1. ✅ `instanceProcCoreName` in Laurel.lean
2. ✅ Heap analysis fix (collectExpr)
3. ✅ Heap transform fix (heapTransformExpr)
4. ✅ Modifies clauses fix (modifiesClausesTransform)
5. ✅ Translator: instance procedure definitions
6. ✅ Translator: InstanceCall at call sites
7. ✅ Update T7 test
8. Edge case tests — **cannot test InstanceCall from Laurel source.**
   The Laurel grammar has `instanceCall` syntax (`target..callee(args)`)
   but it doesn't work: the tokenizer consumes `target..callee` as a
   single identifier because `.` is in `strataIsIdRest`. See Decision 8.
   Instance CALLS are tested through JVerify end-to-end tests (Ion path).
9. ✅ Consistency proof (IM1)
10. ✅ Full test suite passes (516 tests, 488 build jobs)
