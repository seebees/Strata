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

## D4: Constrained type elimination generates assumes for datatype accessor reads

When the constrained type elimination pass encounters a datatype
accessor call whose constructor argument had a constrained type,
it inserts `assume int32$constraint(value)` after the read.

For example, reading an `int32` field from the heap produces:
```
value := Box..intVal!(readField(heap, obj, field))
assume int32$constraint(value)
```

The assume is generated by the constrained type elimination pass
— the same pass that generates the `assert` at the write site and
the `int32$constraint` function itself.

**Options considered:**

- **Wrapper procedure with ensures.** Procedures cannot be called
  in pure contexts (contracts, postconditions). Field reads appear
  in postconditions. Unsuitable.

- **Wrapper function with axioms.** Functions are callable in pure
  contexts. However, the Laurel-to-Core translator does not
  currently generate axioms from Laurel functions, and Core
  function axioms are reserved for built-in mathematical properties
  (like Sequence axioms). Adding compiler-generated axioms would
  require extending the translator.

- **Bake constrained types into Core.** Make `int32` a Core-level
  type with native support. This eliminates the problem entirely
  but adds complexity to Core's type system. This is a two-way
  door — compilers don't change, only Strata internals move. We
  chose to keep Core simple for now.

- **Assume in constrained type elimination.** The elimination pass
  already handles the write side (assert at constructor). It
  generates the `int32$constraint` function. It walks every
  statement. It can also handle the read side (assume at accessor).
  The assume is justified by the constructor-side assert plus heap
  faithfulness.

**Decision: Assume in constrained type elimination.**

**Rationale:** This keeps the constraint handling in one place —
the constrained type elimination pass owns both the write-side
assert and the read-side assume. No changes to the heap
parameterization, translator, or Core. The assume is generated
mechanically by Strata infrastructure, not hand-written by
compilers.

The `int32$constraint` function exists in Core after elimination.
The assume references it. The prover uses it. This works in all
contexts — statements, contracts, postconditions — because the
assume is inserted at the statement level, not through a procedure
or function call.

### Correctness argument

The assume is sound because:
1. At write time, `assert int32$constraint(value)` is proven
2. The heap preserves the value faithfully (Core map axioms)
3. The accessor extracts the same value
4. Therefore the value satisfies the constraint

Steps 1-3 are individually sound. The connection between them is
our reasoning, encoded as a trusted assume.

### Verification gap

The constrained type elimination pass is not formally verified.
The correctness of the assume generation is trusted, not proven.
To prove it, we would need a semantics-preservation theorem for
the elimination pass — showing that the program with assumes has
the same meaning as the original program.

This is the same verification gap identified in the instance
methods Decision 2 (option B): full translator verification is
deferred as significant work. The assume pattern is small,
auditable, and mechanically generated — it's a bounded trust
surface.

If constrained types are later moved to Core (the two-way door),
the assume goes away entirely — the constraint becomes a
Core-level type guarantee.

### Testing strategy

To build confidence in the assume generation:
- JVerify tests exercise the heap round-trip for `int32` fields
  (StrataInstanceFieldRead, StrataModifiesField, etc.)
- Strata-level Laurel tests should exercise constrained types on
  datatype fields directly, without JVerify involvement
- Tests should cover multiple constrained types (`int8`, `int32`,
  `nat32`) and multiple datatype patterns (Box, user-defined)
- Tests should include pure contexts (postconditions referencing
  constrained-type field reads) to verify the assume works in
  all contexts

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
