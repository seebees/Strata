/-
  Differential test: verify that Laurel programs round-trip through Ion
  faithfully at the Strata.Program level.

  These tests run at elaboration time (#eval) and block the build if
  they fail. This catches any drift between the text parser and the
  Ion serializer/deserializer.

  The round-trip property tested: fromIon(toIon(parse(text))) == parse(text)

  This does NOT prove the property for all programs (that would require
  proving 61 toIon/fromIon pairs are inverses across mutually recursive
  AST types with monadic symbol interning — not tractable). Instead,
  these are build-blocking regression tests covering every Laurel feature
  used by JVerify.
-/
import StrataTest.Languages.Laurel.TestExamples
import Strata.DDM.Ion

open Strata
open Strata.Laurel
open Strata.Elab (parseStrataProgramFromDialect)

/-- Parse Laurel source text to a Strata.Program -/
private def parseLaurelToStrata (name : String) (input : String) : IO Strata.Program := do
  let offsetInput := String.join (List.replicate 14 "\n") ++ input
  let inputContext := Parser.stringInputContext name offsetInput
  let dialects := Strata.Elab.LoadedDialects.ofDialects! #[initDialect, Laurel]
  parseStrataProgramFromDialect dialects Laurel.name inputContext

/-- Parse text, Ion round-trip, assert equality. Throws on failure. -/
def assertIonRoundTrip (name : String) (input : String) : IO Unit := do
  let original ← parseLaurelToStrata name input
  let ionBytes := original.toIon
  match Program.fromIon original.dialects original.dialect ionBytes with
  | .error msg => throw (IO.userError s!"[{name}] ❌ Ion deserialization failed: {msg}")
  | .ok roundTripped =>
    if roundTripped == original then
      IO.println s!"[{name}] ✅ PASS"
    else
      throw (IO.userError s!"[{name}] ❌ Strata.Program differs after Ion round-trip")

-- Fundamentals
#eval assertIonRoundTrip "controlFlow" r"
procedure abs(x: int) returns (result: int)
  ensures result >= 0
{
  if (x >= 0) { return x } else { return 0 - x }
};
"

#eval assertIonRoundTrip "postconditions" r"
procedure add(x: int, y: int) returns (result: int)
  ensures result == x + y
{ return x + y };
"

#eval assertIonRoundTrip "whileLoops" r"
procedure sumTo(n: int) returns (result: int)
  ensures result == n * (n + 1) / 2
{
  var i: int := 0;
  var s: int := 0;
  while (i < n) invariant s == i * (i + 1) / 2 invariant i <= n {
    i := i + 1; s := s + i
  };
  return s
};
"

#eval assertIonRoundTrip "nondeterministic" r"
procedure choose() returns (result: int)
  ensures result >= 0
  ensures result <= 100
{ var x: int; assume x >= 0; assume x <= 100; return x };
"

-- Objects: composites, fields, modifies, old()
#eval assertIonRoundTrip "mutableFields" r"
composite Counter { var count: int }
procedure increment(c: Counter) returns (result: Counter)
  ensures c#count == old(c#count) + 1
  modifies c
{ c#count := c#count + 1; return c };
"

#eval assertIonRoundTrip "modifiesClauses" r"
composite Pair { var first: int  var second: int }
procedure setFirst(p: Pair, v: int) returns (result: Pair)
  ensures p#first == v
  ensures p#second == old(p#second)
  modifies p
{ p#first := v; return p };
"

#eval assertIonRoundTrip "immutableFields" r"
composite Point { x: int  y: int }
"

-- Instance methods (CRITICAL: delimiter drift detection)
#eval assertIonRoundTrip "instanceProcedure" r"
composite Counter {
  var count: int
  procedure increment(self: Counter)
    ensures self#count == old(self#count) + 1
    modifies self
  { self#count := self#count + 1 };
}
"

#eval assertIonRoundTrip "instanceCallSyntax" r"
composite Counter {
  var count: int
  procedure getCount(self: Counter) returns (result: int)
    ensures result == self#count
  { return self#count };
  procedure incrementTwice(self: Counter) modifies self
  { self~>increment(); self~>increment() };
  procedure increment(self: Counter) modifies self
  { self#count := self#count + 1 };
}
"

-- Opaque procedures with postconditions (JVerify contract pattern)
#eval assertIonRoundTrip "opaqueWithPostconditions" r"
procedure compare(x: int, y: int) returns (result: int)
  ensures (x < y) ==> (result < 0)
  ensures (x == y) ==> (result == 0)
  ensures (x > y) ==> (result > 0)
;
"

#eval assertIonRoundTrip "opaqueWithPreconditions" r"
procedure divide(x: int, y: int) returns (result: int)
  requires y != 0
  ensures result * y == x
;
"

-- Datatypes and inheritance
#eval assertIonRoundTrip "datatypes" r"
datatype Color { Red(), Green(), Blue() }
procedure isRed(c: Color) returns (result: bool)
  ensures result == Color..isRed(c)
{ return Color..isRed(c) };
"

#eval assertIonRoundTrip "inheritance" r"
composite Base { var x: int }
composite Extender extends Base { var y: int }
"

-- Postcondition expressions (implies, old, field select, connectives)
#eval assertIonRoundTrip "postconditionExpressions" r"
composite Obj { var a: int  var b: int }
procedure swap(o: Obj)
  ensures o#a == old(o#b)
  ensures o#b == old(o#a)
  ensures (o#a > 0) ==> (old(o#b) > 0)
  modifies o
{ var tmp: int := o#a; o#a := o#b; o#b := tmp };
"

-- Position.compareTo pattern (6 postconditions)
#eval assertIonRoundTrip "multiplePostconditions" r"
composite Position { line: int  character: int }
procedure compareTo(self: Position, o: Position) returns (result: int)
  ensures (self#line == o#line && self#character == o#character) ==> (result == 0)
  ensures (result == 0) ==> (self#line == o#line && self#character == o#character)
  ensures (self#line < o#line) ==> (result < 0)
  ensures (self#line > o#line) ==> (result > 0)
  ensures (self#line == o#line && self#character < o#character) ==> (result < 0)
  ensures (self#line == o#line && self#character > o#character) ==> (result > 0)
{
  if (self#line < o#line) { return 0 - 1 };
  if (self#line > o#line) { return 1 };
  if (self#character < o#character) { return 0 - 1 };
  if (self#character > o#character) { return 1 };
  return 0
};
"
