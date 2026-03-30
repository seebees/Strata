/-
  Test: val (immutable) fields on composites.
  Verifies that field reads work on immutable fields.
-/

import StrataTest.Util.TestDiagnostics
import StrataTest.Languages.Laurel.TestExamples

open StrataTest.Util
open Strata

namespace Strata.Laurel

def immutableFieldProgram := r"
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

#guard_msgs (drop info, error) in
#eval testInputWithOffset "ImmutableFields" immutableFieldProgram 14 processLaurelFile

end Laurel
