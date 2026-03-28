# Constrained Types in the Heap Model: Decisions

**Date:** 2026-03-28

## D1: Where do bounded integer types belong?

Java has `int` (32-bit signed), `byte` (8-bit signed), `long`
(64-bit signed). Rust has `i32`, `i8`, `i64`. JavaScript numbers
are IEEE 754 doubles. Python integers are unbounded.

Every language has its own set of bounded numeric types. The
question: where does the knowledge "this value is in range
[-2147483648, 2147483647]" live?

**Options:**

- **A. In Core.** Add axioms like `int32_range(x) => x >= -2^31 && x < 2^31`.
  Rejected: Core is language-agnostic. Python integers have no such
  bound. Putting Java's bounds in Core constrains all languages.

- **B. In CoreDefinitionsForLaurel.** Define constrained types in the
  shared Laurel definitions. Rejected for the same reason — a
  Python→Laurel backend would inherit Java-specific constraints.

- **C. In the language compiler.** The JVerify compiler defines
  `int32` as a constrained type and selects it for Java `int`.
  A Rust compiler defines the same `int32` for Rust `i32`. Python
  defines nothing. Each compiler selects from a vocabulary of
  mathematical range constraints.

- **D. Laurel provides the vocabulary, compilers select from it.**
  Laurel defines constrained types like `int8`, `int16`, `int32`,
  `int64`, `nat32` as a menu of options. These are mathematical
  facts about number ranges — not language-specific. Any compiler
  can select the ones its language needs. Laurel's constrained type
  machinery (elimination, constraint checking) handles them
  generically.

**Decision: D**

**Rationale:** The range [-2^31, 2^31-1] is a mathematical fact,
not a Java fact. Multiple languages share the same ranges. Laurel
should provide the vocabulary; compilers should select from it.
This is the same pattern used for `nat32` in the array-length
decision — the JVerify compiler selects `nat32` for array lengths,
but `nat32` itself is a language-agnostic constrained type.

Currently the constrained types (`int8`, `int16`, `int32`, `int64`,
`nat32`) are all defined by the JVerify compiler. They should be
defined in Laurel's `CoreDefinitionsForLaurel` as the vocabulary
of available bounded integer types. The JVerify compiler should
select from them rather than defining them. This is the same
architectural choice made for array lengths — Laurel provides the
option, the compiler selects it.

---

## D2: The heap must preserve constrained types

When a field is declared with a constrained type (e.g., `int32`),
storing it in the heap and reading it back should preserve the
constraint. This is basic type soundness — if you put an `int32`
in, you should get an `int32` out.

Currently this doesn't work. The heap model stores values in a Box
datatype. The Box system maps constrained types to their base types:
`int32` → `BoxInt(intVal: int)`. The constraint is lost. Reading
the field back yields unbounded `int`.

A workaround was attempted: strip constrained types from fields
before heap parameterization, converting `int32` fields to `int`.
This made the Box types consistent but deliberately discarded the
constraint information. Tests that read constrained-type fields
then fail because the prover can't prove the return value is in
range.

**The real problem:** The workaround was masking a bug in the heap
parameterization's equality handler. The equality handler assumed
all `UserDefined` types are composites and applied `Composite..ref!`
to compare them by reference. But constrained types like `int32`
are also `UserDefined`. Applying `Composite..ref!` to an `int`
value produces a type mismatch.

**The fix has two parts:**

1. Fix the equality handler to check whether a `UserDefined` type
   is actually a composite before applying `Composite..ref!`.
   (Done — added `isComposite` check.)

2. Make the Box system preserve constrained types instead of
   stripping them to base types. This requires the heap
   parameterization to carry constraint knowledge through field
   reads (see D4).

**Decision: The heap must preserve constrained types. The stripping
workaround should be removed once the heap parameterization
correctly carries constraints through field reads.**

---

## D3: Constrained type elimination should handle datatype destructors

The constrained type elimination pass currently handles procedure
boundaries: it adds `requires` for constrained-type inputs and
`ensures` for constrained-type outputs. This is how constraint
knowledge flows through procedure calls.

Datatype constructors and destructors are also a boundary. When
`BoxInt32(v)` is constructed with `v: int32`, the elimination pass
checks the constraint at the write site. But when `Box..int32Val!`
extracts the value, there's no corresponding guarantee.

This is the same pattern as procedures — the constructor is like
a procedure input (constraint checked), the destructor is like a
procedure output (constraint should be guaranteed).

Note: this applies to all datatypes, not just Box. If someone
defines `datatype Pair { MkPair(x: int32, y: int32) }`, then
`Pair..x!(p)` should carry the `int32` constraint. The fix should
be general.

**Decision: Accepted — datatype destructors are a type boundary
and should carry constraint knowledge, same as procedure outputs.**

---

## D4: Predefined Core read functions with fixed axioms

Each constrained type in Laurel is paired with a predefined Core
read function that has fixed axioms. The translator calls the
appropriate read function — it does not generate axioms.

**Options considered:**

- **Assume in constrained type elimination.** Assumes cannot
  appear in pure contexts (contracts, postconditions) or in
  functions. Field reads appear in both. Unsuitable.

- **Wrapper procedure with ensures.** Procedures cannot be called
  in pure contexts. Same problem.

- **Translator-generated axioms.** The translator would construct
  axioms dynamically. This gives the translator too much power —
  it could generate arbitrary axioms. Hard to audit.

- **Parameterized Core function (readBoundedInt with lo/hi).**
  Too flexible — the translator could pass any bounds. No way to
  verify the bounds match the constrained type without inspecting
  every call site.

- **Predefined Core read functions with fixed axioms.** One
  function per constrained type, defined in Core's Factory. Fixed
  bounds, fixed axioms, no parameters. The translator selects
  which function to call — it cannot modify the axioms.

**Decision: Predefined Core Factory read functions with fixed
axioms over an opaque type parameter, plus program-level equality
axioms connecting them to the Box system.**

### Architecture

The proof that a constrained-type field read is bounded relies on
two separate facts, proved by two separate mechanisms:

**1. Bounds (Factory axioms — fixed, auditable):**
```
function readInt32 : ∀a. a → int
  axiom: ∀ box. readInt32(box) >= -2147483648
  axiom: ∀ box. readInt32(box) <= 2147483647
```
Defined in Core's Factory alongside Sequence and Map axioms.
The bounds cannot be changed by the translator. The opaque type
parameter `a` is wired to Box by the translator.

**2. Equality (program-level axiom — generated, connects to heap):**
```
axiom readInt32_eq: ∀ v: int. readInt32(BoxInt(v)) == v
```
Generated by the translator, conditional on BoxInt existing in
the program's Box datatype. This connects the opaque Factory
function to the Box constructor so the prover can chain through
the heap round-trip.

### How the prover chains them

Consider `this.value = this.value + 1` where `value` is `int32`:

```
-- Write: wrap value in Box, store in heap
heap₂ = updateField(heap₁, self, field, BoxInt(old_value + 1))

-- Read: retrieve Box from heap, unwrap with readInt32
result = readInt32(readField(heap₂, self, field))
```

The prover chains three facts:

1. **Heap round-trip (map axiom):**
   `readField(updateField(heap, obj, fld, val), obj, fld) == val`
   → `readField(heap₂, self, field) == BoxInt(old_value + 1)`

2. **Unwrap (equality axiom):**
   `readInt32(BoxInt(v)) == v`
   → `readInt32(BoxInt(old_value + 1)) == old_value + 1`

3. **Bounds (Factory axioms):**
   `readInt32(box) >= -2147483648 ∧ readInt32(box) <= 2147483647`
   → the result is in int32 range

The map axiom handles the container (you get back the same Box
you put in). The equality axiom handles the contents (unwrapping
the Box gives back the value). The Factory axioms handle the
bounds (the value is in range). Three separate concerns.

### Soundness: why the equality axiom is safe

The mailbox analogy: you put a letter in an envelope (BoxInt),
put the envelope in a mailbox (heap field), then later open the
mailbox and open the envelope.

The heap model is purely functional. **A new Box is always
created** — there is no mutation. `updateField` creates a new
heap where the field maps to a fresh `BoxInt(43)`. The old heap
still has `BoxInt(42)`. Nothing is mutated. This means:

- `BoxInt(v)` always contains exactly `v` — no one can change
  it after construction.
- `readInt32(BoxInt(v)) == v` is a tautology about the
  constructor/destructor relationship.
- The only way to get a `BoxInt` in the heap is to construct
  one explicitly, which the constrained type elimination checks
  at the write site.

There is no backdoor. You can't mutate a Box in place. You can't
store a value without going through the constructor (which is
checked). The heap preserves whatever Box you stored (map axioms).
And `readInt32` faithfully extracts the value (equality axiom)
while also carrying the bounds (Factory axioms).

### Trust boundary

Only the translator calls these functions. The translator is the
trust boundary. The pattern is auditable:

- **Factory axioms:** Small, enumerable, fixed. Inspect once.
- **Equality axioms:** Generated, but structurally trivial
  (`readIntN(BoxInt(v)) == v`). The translator can only emit
  these for Box constructors that exist.
- **Call sites:** The heap parameterization calls `readInt32`
  only for fields typed `int32`. Verifying the translator would
  prove this pairing is correct.

### Implementation (DONE — commit a2def101)

- `Factory.lean`: `readInt32Func`, `readInt16Func`, `readInt8Func`
  with bound axioms, registered in `WFFactory`
- `HeapParameterizationConstants.lean`: External Laurel declarations
  for resolution
- `HeapParameterization.lean`: Field reads for constrained types
  use `readInt32` instead of `Box..intVal!`
- `LaurelToCoreTranslator.lean`: Equality axioms generated
  conditional on BoxInt existing in Box datatype
- Stripping workaround removed
- Results: 72 JVerify tests, 5 failures (down from 7). Fixed:
  StrataInstanceFieldRead, StrataModifiesMultiple,
  StrataModifiesField, StrataChainedFieldWrite

---

## D5: Diagnostic source ranges for generated constraint checks

When the prover can't prove a constraint — for example, a field
write where the value doesn't fit in `int32` — the diagnostic
needs to point the user to a meaningful location in their source
code.

The constraint checks are generated by Strata infrastructure (heap
parameterization, constrained type elimination), not written by the
user. But they correspond to operations the user DID write: a field
assignment, a return statement, an array write.

**The problem we encountered:** Generated constraint checks were
carrying metadata from the constrained type definition (which has
no meaningful source location) or empty metadata (which maps to
`<unknown>`). When the prover produced a diagnostic, the test
engine crashed trying to look up a source file that doesn't exist.

This is analogous to how `JArray.length` postconditions use
`SourceRange.NONE`, which maps to `1:1-1:1` — "somewhere in this
file." This works (doesn't crash) but isn't helpful for the user.

**Options:**

- **A. Use the constrained type definition's source range.**
  This is what the constrained type elimination currently does.
  But constrained types defined by the compiler have no meaningful
  source location. Produces `<unknown>` or `1:1-1:1`.

- **B. Use the procedure's source range.** The generated ensures
  clause would point to the procedure declaration. Better than
  `<unknown>` but still not specific — the user knows which method
  has a problem but not which line.

- **C. Use the operation site's source range.** The field write,
  field read, return statement, or array access that triggered the
  constraint check. This is the line the user needs to look at.
  The source range is available — the original AST node carries
  it through the heap parameterization.

**Decision: C — use the operation site's source range.**

**Rationale:** This is the same principle as any other verification
error. When a postcondition fails, the diagnostic points to the
postcondition. When a precondition fails, the diagnostic points to
the call site. When a constraint check fails, the diagnostic should
point to the operation that violates the constraint.

The user wrote `this.value = expr` — if `expr` doesn't satisfy
`int32`, the diagnostic should point to that assignment. The user
wrote `return this.value` — if the return type constraint can't be
proved, the diagnostic should point to the return statement. This
is the same as how a user-defined type's contract violation would
be reported: point to where the violation happens, not where the
type is defined.

This also fixes the `<unknown>` crash — the operation site always
has a valid source file because it came from the user's code.

**Implementation note:** The heap parameterization has access to
the metadata (`md`) of the AST node being transformed. Generated
constraint checks should use this metadata, not the constrained
type's metadata or empty metadata. The wrapper functions (D4)
should carry the calling site's metadata. Additionally, the
constrained type elimination pass should fall back to the
procedure's metadata when the parameter type metadata lacks a
valid file range — this prevents crashes from compiler-generated
types with no source location.
