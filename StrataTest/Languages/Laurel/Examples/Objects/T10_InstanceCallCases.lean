/-
  Test cases for instance call resolution.
  Isolates the bug: functional instance procedures (isFunctional=true)
  go through translateProcedure instead of translateProcedureToFunction,
  producing a Core procedure with $result instead of a Core function.
-/

import StrataTest.Util.TestDiagnostics
import StrataTest.Languages.Laurel.TestExamples

open StrataTest.Util
open Strata

namespace Strata.Laurel

-- Case 1: Instance procedure calling instance procedure (no functions).
-- This should work — it's the same pattern as StrataChainedMethodCallPost.
def case1_procCallsProc := r"
composite Counter {
  var count: int
  procedure increment(self: Counter)
    modifies self
  {
    self#count := self#count + 1
  };
  procedure incrementTwice(self: Counter)
    modifies self
  {
    self~>increment();
    self~>increment()
  };
}
"

-- Case 2: Composite with a function AND a procedure.
-- The function should be translated as a Core function, not a procedure.
def case2_funcAndProc := r"
composite Box {
  var value: int
  function getValue(self: Box): int {
    return self#value
  };
  procedure setValue(self: Box, v: int)
    modifies self
  {
    self#value := v
  };
}
"

-- Case 3: Instance procedure calling an instance function.
-- This is the pattern that breaks on records (doubleSum calling sum).
def case3_procCallsFunc := r"
composite Box {
  var value: int
  function getValue(self: Box): int {
    return self#value
  };
  procedure test(self: Box): int
    ensures result == self#value
  {
    var x: int := self~>getValue();
    return x
  };
}
"

#eval do
  let r1 ← try
    testInputWithOffset "Case1" case1_procCallsProc 14 processLaurelFile
    pure "Case1_ProcCallsProc: ✅ PASS"
  catch e => pure s!"Case1_ProcCallsProc: ❌ FAIL — {toString e}"
  IO.println r1
  let r2 ← try
    testInputWithOffset "Case2" case2_funcAndProc 14 processLaurelFile
    pure "Case2_FuncAndProc: ✅ PASS"
  catch e => pure s!"Case2_FuncAndProc: ❌ FAIL — {toString e}"
  IO.println r2
  let r3 ← try
    testInputWithOffset "Case3" case3_procCallsFunc 14 processLaurelFile
    pure "Case3_ProcCallsFunc: ✅ PASS"
  catch e => pure s!"Case3_ProcCallsFunc: ❌ FAIL — {toString e}"
  IO.println r3

end Laurel
