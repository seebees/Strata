/-
  Test: Cross-type instance calls.
  Exercises the qualified callee name resolution where one composite
  calls another composite's instance method.

  Case 1: Functional instance call in expression position (same type).
  Case 2: Non-functional instance call in statement position (same type).
  Case 3: Self-call — one instance method calls another on the same type.
-/

import StrataTest.Util.TestDiagnostics
import StrataTest.Languages.Laurel.TestExamples

open StrataTest.Util
open Strata

namespace Strata.Laurel

-- Case 1: Functional instance call in expression position.
-- Point has a pure function `sum`. A static procedure calls it.
def case1_functionalExprPos := "
composite Point {
  var x: int
  var y: int
  function sum(self: Point): int
    ensures result == self#x + self#y
  {
    return self#x + self#y
  };
}

procedure test(p: Point): int
{
  var s: int := p~>sum();
  return s
};
"

-- Case 2: Non-functional instance call in statement position.
-- Counter has a procedure `increment`. A static procedure calls it.
def case2_nonFunctionalStmtPos := "
composite Counter {
  var count: int
  procedure increment(self: Counter)
    modifies self
  {
    self#count := self#count + 1
  };
}

procedure test(c: Counter)
  modifies c
{
  c~>increment()
};
"

-- Case 3: Self-call — one instance method calls another on the same type.
def case3_selfCall := "
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

#eval do
  let r1 ← try
    testInputWithOffset "FunctionalExprPos" case1_functionalExprPos 14 processLaurelFile
    pure "Case1_FunctionalExprPos: ✅ PASS"
  catch e => pure s!"Case1_FunctionalExprPos: ❌ FAIL — {toString e}"
  IO.println r1
  let r2 ← try
    testInputWithOffset "NonFunctionalStmtPos" case2_nonFunctionalStmtPos 14 processLaurelFile
    pure "Case2_NonFunctionalStmtPos: ✅ PASS"
  catch e => pure s!"Case2_NonFunctionalStmtPos: ❌ FAIL — {toString e}"
  IO.println r2
  let r3 ← try
    testInputWithOffset "SelfCall" case3_selfCall 14 processLaurelFile
    pure "Case3_SelfCall: ✅ PASS"
  catch e => pure s!"Case3_SelfCall: ❌ FAIL — {toString e}"
  IO.println r3

end Laurel
