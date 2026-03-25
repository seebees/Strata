/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataTest.Util.TestDiagnostics
import StrataTest.Languages.Laurel.TestExamples

open StrataTest.Util

namespace Strata
namespace Laurel

/-- Test that throw parses and reaches the translator (which emits not-yet-implemented). -/
def throwProgram := r"
composite MyException {}

procedure throwSimple(e: MyException) {
    throw e
//  ^^^^^^^ error: throw statement translation not yet implemented
};
"

#guard_msgs(drop info, error) in
#eval testInputWithOffset "ThrowSimple" throwProgram 17 processLaurelFile

/-- Test that try/catch parses correctly by verifying the translator receives it. -/
def tryCatchProgram := r"
composite MyException {}

procedure tryCatchSimple(e: MyException) {
    try {
        var x: int := 1
    } catch (e: MyException) {
        var y: int := 2
    }
};
"

/-- Test that try/catch/finally parses correctly. -/
def tryCatchFinallyProgram := r"
composite MyException {}

procedure tryCatchFinally(e: MyException) {
    try {
        var x: int := 1
    } catch (e: MyException) {
        var y: int := 2
    } finally {
        var z: int := 3
    }
};
"

/-- Test that multiple catch clauses parse correctly. -/
def multiCatchProgram := r"
composite ExceptionA {}
composite ExceptionB {}

procedure multiCatch(e: ExceptionA) {
    try {
        var x: int := 1
    } catch (a: ExceptionA) {
        var y: int := 2
    } catch (b: ExceptionB) {
        var z: int := 3
    }
};
"

private def assertSingleDiagnostic (name : String) (prog : String) (expectedMsg : String) : IO Unit := do
  let inputContext := Strata.Parser.stringInputContext name prog
  let diagnostics ← processLaurelFile inputContext
  match diagnostics.toList with
  | [d] =>
    if !stringContains d.message expectedMsg then
      throw (IO.userError s!"{name}: expected message containing '{expectedMsg}', got '{d.message}'")
  | other =>
    throw (IO.userError s!"{name}: expected 1 diagnostic, got {other.length}")

#eval! assertSingleDiagnostic "tryCatch" tryCatchProgram "try/catch statement translation not yet implemented"
#eval! assertSingleDiagnostic "tryCatchFinally" tryCatchFinallyProgram "try/catch statement translation not yet implemented"
#eval! assertSingleDiagnostic "multiCatch" multiCatchProgram "try/catch statement translation not yet implemented"

end Laurel
