/-
  Test: Range.compareTo → Position.compareTo end-to-end.
  Exercises cross-type instance calls where one composite's method
  calls another composite's method with the same name.

  This is the motivating example from cross-type-resolution/context.md.
-/

import StrataTest.Util.TestDiagnostics
import StrataTest.Languages.Laurel.TestExamples

open StrataTest.Util
open Strata

namespace Strata.Laurel

-- Case 1: Position.compareTo only (baseline).
def case1_positionOnly := "
composite Position {
  var line: int
  var character: int
  procedure compareTo(self: Position, o: Position) returns (result: int)
    modifies self
  {
    if (self#line < o#line) then { return 0 - 1 };
    if (self#line > o#line) then { return 1 };
    if (self#character < o#character) then { return 0 - 1 };
    if (self#character > o#character) then { return 1 };
    return 0
  };
}
"

-- Case 2: Range.compareTo calls Position~>compareTo (cross-type).
-- Uses the return value of the cross-type call.
def case2_rangeCallsPosition := "
composite Position {
  var line: int
  var character: int
  procedure compareTo(self: Position, o: Position) returns (result: int)
    modifies self
  {
    if (self#line < o#line) then { return 0 - 1 };
    if (self#line > o#line) then { return 1 };
    if (self#character < o#character) then { return 0 - 1 };
    if (self#character > o#character) then { return 1 };
    return 0
  };
}

composite Range {
  var start: Position
  var end: Position
  procedure compareTo(self: Range, o: Range) returns (result: int)
    modifies self
  {
    var s: Position := self#start;
    var os: Position := o#start;
    var startCmp: int := s~>compareTo(os);
    if (startCmp != 0) then { return startCmp };
    var e: Position := self#end;
    var oe: Position := o#end;
    var endCmp: int := e~>compareTo(oe);
    return endCmp
  };
}
"

-- Case 3: Static procedure calls cross-type instance method.
def case3_staticCallsCrossType := "
composite Position {
  var line: int
  var character: int
  procedure compareTo(self: Position, o: Position) returns (result: int)
    modifies self
  {
    if (self#line < o#line) then { return 0 - 1 };
    if (self#line > o#line) then { return 1 };
    return 0
  };
}

composite Range {
  var start: Position
  var end: Position
}

procedure compareStarts(a: Range, b: Range) returns (result: int)
  modifies a
{
  var s1: Position := a#start;
  var s2: Position := b#start;
  var cmp: int := s1~>compareTo(s2);
  return cmp
};
"

-- Case 4: Ternary with cross-type instance call (the Range.compareTo pattern).
-- The non-functional instance call is inside an if-then-else expression,
-- which requires LiftImperativeExpressions to detect and lift it.
def case4_ternaryWithCrossType := "
composite Position {
  var line: int
  var character: int
  procedure compareTo(self: Position, o: Position) returns (result: int)
    modifies self
  {
    if (self#line < o#line) then { return 0 - 1 };
    if (self#line > o#line) then { return 1 };
    if (self#character < o#character) then { return 0 - 1 };
    if (self#character > o#character) then { return 1 };
    return 0
  };
}

composite Range {
  var start: Position
  var end: Position
  procedure compareTo(self: Range, o: Range) returns (result: int)
    modifies self
  {
    var s: Position := self#start;
    var os: Position := o#start;
    var startCmp: int := s~>compareTo(os);
    if (startCmp != 0) then { return startCmp };
    var e: Position := self#end;
    var oe: Position := o#end;
    return e~>compareTo(oe)
  };
}
"

#eval do
  let r1 ← try
    testInputWithOffset "PositionOnly" case1_positionOnly 14 processLaurelFile
    pure "Case1_PositionOnly: ✅ PASS"
  catch e => pure s!"Case1_PositionOnly: ❌ FAIL — {toString e}"
  IO.println r1
  let r2 ← try
    testInputWithOffset "RangeCallsPosition" case2_rangeCallsPosition 14 processLaurelFile
    pure "Case2_RangeCallsPosition: ✅ PASS"
  catch e => pure s!"Case2_RangeCallsPosition: ❌ FAIL — {toString e}"
  IO.println r2
  let r3 ← try
    testInputWithOffset "StaticCallsCrossType" case3_staticCallsCrossType 14 processLaurelFile
    pure "Case3_StaticCallsCrossType: ✅ PASS"
  catch e => pure s!"Case3_StaticCallsCrossType: ❌ FAIL — {toString e}"
  IO.println r3
  let r4 ← try
    testInputWithOffset "TernaryWithCrossType" case4_ternaryWithCrossType 14 processLaurelFile
    pure "Case4_TernaryWithCrossType: ✅ PASS"
  catch e => pure s!"Case4_TernaryWithCrossType: ❌ FAIL — {toString e}"
  IO.println r4

end Laurel
