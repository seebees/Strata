/-
  Test cases for instance call resolution from Laurel source.
  Tests the ~> syntax and the isFunction fix for instanceProcedure.
-/

import StrataTest.Util.TestDiagnostics
import StrataTest.Languages.Laurel.TestExamples

open StrataTest.Util
open Strata

namespace Strata.Laurel

-- Case 1: Instance procedure calling instance procedure.
-- This is the core instance call pattern.
def case1_procCallsProc := "
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

-- Case 2: Instance procedure with postcondition calling another.
def case2_procCallWithPost := "
composite Counter {
  var count: int
  procedure increment(self: Counter)
    ensures self#count == old(self#count) + 1
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
"

#eval do
  let r1 ← try
    testInputWithOffset "Case1" case1_procCallsProc 14 processLaurelFile
    pure "Case1_ProcCallsProc: ✅ PASS"
  catch e => pure s!"Case1_ProcCallsProc: ❌ FAIL — {toString e}"
  IO.println r1
  let r2 ← try
    testInputWithOffset "Case2" case2_procCallWithPost 14 processLaurelFile
    pure "Case2_ProcCallWithPost: ✅ PASS"
  catch e => pure s!"Case2_ProcCallWithPost: ❌ FAIL — {toString e}"
  IO.println r2

end Laurel
