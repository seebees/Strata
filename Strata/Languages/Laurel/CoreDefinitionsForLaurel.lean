/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DDM.Elab
public import Strata.DDM.AST
public import Strata.Languages.Laurel.Grammar.LaurelGrammar
public meta import Strata.Languages.Laurel.Grammar.LaurelGrammar
public import Strata.Languages.Laurel.Grammar.ConcreteToAbstractTreeTranslator

namespace Strata.Laurel

public section

/--
Core map operations (`select`, `update`, `const`) expressed in Laurel syntax.
These are polymorphic map primitives used by the Laurel-to-Core translator.
Since Laurel doesn't have polymorphic types, `int` is used as a placeholder type
for all parameters — the actual types are inferred during Core translation.
-/
def coreDefinitionsForLaurelDDM :=
#strata
program Laurel;

datatype Float64IsNotSupportedYet {}

// The types for these Map functions are incorrect.
// We'll fix them when Laurel supports polymorphism
function select(map: int, key: int) : int
  external;

function update(map: int, key: int, value: int) : int
  external;

function const(value: int) : int
  external;

// Sequence (array) operations with accurate Sequence types
function Sequence.length(s: Sequence int) : int
  external;

function Sequence.select(s: Sequence int, i: int) : int
  external;

function Sequence.selectInt32(s: Sequence int, i: int) : int
  external;

function Sequence.selectInt16(s: Sequence int, i: int) : int
  external;

function Sequence.selectInt8(s: Sequence int, i: int) : int
  external;

function Sequence.update(s: Sequence int, i: int, v: int) : int
  external;

function Sequence.build(i: int, v: int) : Sequence int
  external;

// Bounded integer types — mathematical facts about number ranges.
// Language compilers select from this vocabulary for their type mappings.
// See docs/design/constrained-types-in-heap/decisions.md D1.
constrained int8 = x: int where x >= -128 && x <= 127 witness 0
constrained int16 = x: int where x >= -32768 && x <= 32767 witness 0
constrained int32 = x: int where x >= -2147483648 && x <= 2147483647 witness 0
constrained int64 = x: int where x >= -9223372036854775808 && x <= 9223372036854775807 witness 0
constrained nat32 = x: int where x >= 0 && x <= 2147483647 witness 0

#end

/--
The core map operation definitions as a `Laurel.Program`, parsed at compile time.
-/
def coreDefinitionsForLaurel : Program :=
  match TransM.run none (parseProgram coreDefinitionsForLaurelDDM) with
  | .ok program => program
  | .error e => dbg_trace s!"BUG: CoreDefinitionsForLaurel parse error: {e}"; default

private def resultId (s : String) : Identifier := { text := s }

/-- Result<T> ADT for exception propagation (spec §1.1).
    `Success(value: T)` carries the return value; `Failure()` signals an exception.
    Defined programmatically because the Laurel DDM grammar doesn't support type parameters. -/
def resultDatatypeDefinition : DatatypeDefinition where
  name := resultId "Result"
  typeArgs := [resultId "T"]
  constructors := [
    { name := resultId "Success", args := [{ name := resultId "value", type := ⟨.UserDefined (resultId "T"), #[]⟩ }] },
    { name := resultId "Failure", args := [] }
  ]

/-- Core definitions for Laurel, including the Result<T> datatype. -/
def coreDefinitionsForLaurelWithResult : Program :=
  { coreDefinitionsForLaurel with
    types := coreDefinitionsForLaurel.types ++ [.Datatype resultDatatypeDefinition] }

end -- public section

end Strata.Laurel
