/-
  Test: function keyword in composites.
  Validates that `function` (isFunctional=true) instance methods
  go through eliminateReturnsInExpression and heap parameterization.
-/

import StrataTest.Util.TestDiagnostics
import StrataTest.Languages.Laurel.TestExamples

open StrataTest.Util
open Strata

namespace Strata.Laurel

-- Case 1: Pure function (no heap access) — should pass
def pureFunction := "
composite Point {
  function zero(self: Point): int
  {
    return 0
  };
}
"

-- Case 2: Function with heap access, single composite — should pass
-- (validates eliminateReturnsInExpression + heap parameterization for instance functions)
def heapFunction := "
composite Point {
  var x: int
  function getX(self: Point): int
  {
    return self#x
  };
}
"

-- Case 3: Function with ensures + two composites — should pass
-- (validates heap parameterization of postconditions in Transparent bodies)
def functionWithEnsures := "
composite Point {
  var x: int
  function getX(self: Point): int
    ensures result == self#x
  {
    return self#x
  };
}

composite Line {
  var start: Point
}
"

#eval do
  let r1 ← try
    testInputWithOffset "PureFunction" pureFunction 14 processLaurelFile
    pure "Case1_PureFunction: ✅ PASS"
  catch e => pure s!"Case1_PureFunction: ❌ FAIL — {toString e}"
  IO.println r1
  let r2 ← try
    testInputWithOffset "HeapFunction" heapFunction 14 processLaurelFile
    pure "Case2_HeapFunction: ✅ PASS"
  catch e => pure s!"Case2_HeapFunction: ❌ FAIL — {toString e}"
  IO.println r2
  let r3 ← try
    testInputWithOffset "FunctionWithEnsures" functionWithEnsures 14 processLaurelFile
    pure "Case3_FunctionWithEnsures: ✅ PASS"
  catch e => pure s!"Case3_FunctionWithEnsures: ❌ FAIL — {toString e}"
  IO.println r3

end Laurel
