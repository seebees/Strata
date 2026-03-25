/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataTest.Util.TestDiagnostics
import StrataTest.Languages.Laurel.TestExamples

open StrataTest.Util

namespace Strata
namespace Laurel

private def assertNoDiagnostics (name : String) (prog : String) : IO Unit := do
  let inputContext := Strata.Parser.stringInputContext name prog
  let diagnostics ← processLaurelFile inputContext
  match diagnostics.toList with
  | [] => pure ()
  | ds => throw (IO.userError s!"{name}: expected 0 diagnostics, got {ds.length}: {ds.map (·.message)}")

/-- Property 4 from spec: Normal completion skips catch handlers. -/
def normalSkipsHandlers := r"
composite MyException {}
procedure normalSkipsHandlers() {
    var x: int := 0;
    try { x := 1 } catch (e: MyException) { x := 99 };
    assert x == 1
};
"

#eval! assertNoDiagnostics "normalSkipsHandlers" normalSkipsHandlers

/-- Assertion inside try body is verified. -/
def assertInTryBody := r"
composite MyException {}
procedure assertInTryBody() {
    try { var x: int := 42; assert x == 42 } catch (e: MyException) { assert true }
};
"

#eval! assertNoDiagnostics "assertInTryBody" assertInTryBody

/-- Property 6 from spec: Finally block executes. -/
def finallyExecutes := r"
composite MyException {}
procedure finallyExecutes() {
    var z: int := 0;
    try { var x: int := 1 } catch (e: MyException) { var y: int := 2 } finally { z := 42 };
    assert z == 42
};
"

#eval! assertNoDiagnostics "finallyExecutes" finallyExecutes

/-- Multiple catch clauses — normal path skips all handlers. -/
def multipleCatches := r"
composite ExceptionA {}
composite ExceptionB {}
procedure multipleCatches() {
    var x: int := 0;
    try { x := 1 } catch (a: ExceptionA) { x := 10 } catch (b: ExceptionB) { x := 20 };
    assert x == 1
};
"

#eval! assertNoDiagnostics "multipleCatches" multipleCatches

end Laurel
