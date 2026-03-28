# Sequence Types in Laurel: Decisions

**Date:** 2026-03-27

## Context

Core has parameterized Sequence types: `Sequence int`, `Sequence bool`,
`Sequence Composite`. These are used to model arrays, lists, and other
ordered collections. The Sequence operations (`Sequence.length`,
`Sequence.select`, `Sequence.update`, `Sequence.build`) are proven
correct in Core and work at the Core level.

Laurel has no way to express "Sequence of X" as a type. The `HighType`
enum has `TInt`, `TBool`, `UserDefined name` — but no `TSequence`.
This means language compilers targeting Laurel cannot declare variables
or fields with Sequence types.

This gap was discovered while implementing heap-based array mutation
(L1) for JVerify. The JVerify compiler needed to declare a field that
holds a Sequence, and there was no way to express that in Laurel.

### How we got here

The original array support (commit `3563680f`) worked around this gap
by adding `composite JArray {}` to `CoreDefinitionsForLaurel.lean` and
hardcoding `if name.text == "JArray" then Core.seqTy LMonoTy.int` in
the translator. This was the fastest way to make resolution succeed,
but it put Java-specific knowledge into Strata's shared infrastructure.

Subsequent commits (`d53ab55b`, `24a93705`) added more Java-specific
workarounds: `startsWith "JArray"` checks in the heap parameterization
for BoxSequence handling, and hardcoded type mappings for `JArrayBool`
and `JArrayComposite` in the translator.

The L1 implementation (heap-based array mutation) added further
Java-specific types (`JArrayData`, `JArrayBoolData`,
`JArrayCompositeData`) to `CoreDefinitionsForLaurel.lean` and more
hardcoded mappings in the translator.

### The fundamental problem

Laurel already has parameterized types for Set and Map:

```
| TSet (elementType : WithMetadata HighType)
| TMap (keyType : WithMetadata HighType) (valueType : WithMetadata HighType)
```

The translator handles these generically:

```
| .TSet elementType => Core.mapTy (translateType model elementType) LMonoTy.bool
| .TMap keyType valueType => Core.mapTy (translateType model keyType) (translateType model valueType)
```

Sequence is the only Core collection type without a corresponding
Laurel type. This forces every language compiler that needs sequences
to invent workaround names and requires the translator to have
hardcoded knowledge of those names.

### The architectural principle

From the array-support decisions doc:

> "CoreDefinitionsForLaurel is shared across all Laurel-targeting
> languages. A Python→Laurel backend would inherit this Java-specific
> constraint."

This principle was correctly applied for `nat32` (kept in JVerify
compiler, not Strata). It was violated for JArray types (put in
Strata). This decision corrects that violation.

---

## Decision 1: Add TSequence to Laurel's HighType

**Options:**

### A. Add `TSequence (elementType)` to HighType

Add a new variant to the `HighType` enum:

```
| TSequence (elementType : WithMetadata HighType)
```

Add a one-line case to the translator:

```
| .TSequence elementType => Core.seqTy (translateType model elementType)
```

Language compilers express sequence field types directly:
`TSequence(TInt)`, `TSequence(TBool)`, `TSequence(UserDefined "Composite")`.

**Pros:**
- Follows the exact pattern of TSet and TMap — already proven to work
- Language-agnostic: any compiler can use TSequence
- No hardcoded names in the translator
- No Java-specific code in Strata
- The heap parameterization can handle TSequence generically through
  a new Box variant, same as it handles TInt, TBool, etc.

**Cons:**
- Requires a small change to Laurel's grammar/AST
- Every pass that pattern-matches on HighType needs a TSequence case
  (but most are mechanical — just recurse into the element type)

### B. Naming convention (e.g., `Seq_int` → `Sequence int`)

The translator recognizes a prefix like `Seq_` and parses the element
type from the suffix.

**Pros:**
- No Laurel AST change needed

**Cons:**
- String parsing in the translator — fragile, hard to validate
- The convention is implicit — nothing in the type system enforces it
- Error messages would show `Seq_int` instead of `Sequence int`
- Every pass that handles UserDefined types would silently pass through
  `Seq_int` without understanding it's a Sequence

### C. Keep hardcoded mappings, just move them to the compiler

Move `JArrayData` definitions from `CoreDefinitionsForLaurel.lean` to
the JVerify compiler. Keep the translator mappings.

**Pros:**
- Smallest change to Strata

**Cons:**
- The translator still has Java-specific names (`JArrayData`)
- Every new language compiler needs its own set of workaround names
- The translator's hardcoded list grows with each language
- Doesn't solve the fundamental problem

### D. Use the existing `Applied` type in HighType

Laurel already has `Applied (base) (typeArguments)` for generic type
application. We could use `Applied(UserDefined("Sequence"), [TInt])`.

**Pros:**
- No new HighType variant needed
- Uses existing infrastructure

**Cons:**
- `Applied` is designed for user-defined generics (e.g., `List<Int>`),
  not for built-in Core types
- The translator would need to special-case
  `Applied(UserDefined("Sequence"), ...)` — still a string check
- `Sequence` would need to be defined somewhere as a resolvable name
- Overloads the meaning of `Applied` — it's meant for source-language
  generics, not for Laurel-to-Core type mapping

**Decision: A — Add TSequence to HighType**

**Rationale:** It follows the established pattern (TSet, TMap), is
language-agnostic, and eliminates all the workaround code. The change
is small and mechanical. Options B and C don't solve the fundamental
problem. Option D misuses an existing construct.

---

## Decision 2: Include grammar support for TSequence

`TMap` has grammar support (`Map keyType valueType` in
`LaurelGrammar.st`). `TSequence` should too, for consistency and
to enable accurate type signatures on the Sequence operations in
`CoreDefinitionsForLaurel.lean`.

Currently the Sequence operations use `int` as a placeholder type:

```
function Sequence.length(s: int) : int
  external;
```

With grammar support, they become accurate:

```
function Sequence.length(s: Sequence int) : int
  external;
```

The grammar support is ~6 lines across three files (grammar rule,
concrete-to-abstract translation, format). Deferring it would leave
the placeholder types in place and create a cleanup task to remember.

**Decision: Include grammar support now**

**Rationale:** The work is trivial (~6 lines). Doing it now means
the Sequence operation signatures in `CoreDefinitionsForLaurel.lean`
are accurate, and there's no deferred cleanup to track.

---

## Decision 3: Remove all JArray-specific code from Strata

Once TSequence exists, the following Strata code becomes unnecessary:

1. **CoreDefinitionsForLaurel.lean:** JArray/JArrayBool/JArrayComposite
   composite definitions and JArrayData/JArrayBoolData/JArrayCompositeData
   types. The JVerify compiler emits these as regular composites with
   `$data: TSequence(elementType)` fields.

2. **LaurelToCoreTranslator.lean:** All `if name.text == "JArray"`
   and `if name.text == "JArrayData"` checks. JArray composites go
   through the generic `compositeType → Composite` path. TSequence
   goes through the new `TSequence → Core.seqTy` path.

3. **HeapParameterization.lean:** All `startsWith "JArray"` checks
   in `boxDestructorName`, `boxConstructorName`, `boxConstructorDef`.
   TSequence fields get a new Box variant handled generically by
   element type, same as TInt gets BoxInt.

**Decision: Accepted**

**Rationale:** This is the direct consequence of Decision 1. Once
Laurel can express Sequence types natively, there's no reason for
Strata to have Java-specific workarounds. The JVerify compiler
becomes the sole owner of Java-specific array modeling decisions.

---

## Decision 4: BoxSequence handling in heap parameterization

When a composite field has type `TSequence elementType`, the heap
parameterization needs to box/unbox it. How?

**Options:**

### A. Single BoxSequence variant (monomorphic)

One Box constructor: `BoxSequence(sequenceVal: ???)`. But what's the
stored type? `Sequence int` and `Sequence bool` are different Core
types. A single BoxSequence can't hold both.

**Cons:** Type mismatch when different sequence element types coexist.
This is exactly the bug we hit during L1 implementation — `JArrayData`
and `JArrayBoolData` collided in a shared `BoxSequence`.

### B. Per-element-type Box variants

Generate Box constructors based on the element type:
- `TSequence(TInt)` → `BoxSequenceInt(sequenceIntVal: TSequence(TInt))`
- `TSequence(TBool)` → `BoxSequenceBool(sequenceBoolVal: TSequence(TBool))`

**Pros:**
- Each variant has the correct type
- No collisions between different element types
- Follows the pattern of BoxInt, BoxBool, BoxString

**Cons:**
- More Box constructors in the datatype
- Constructor names are derived from element types

### C. Use the generic datatype Box path

TSequence types could be treated like datatypes in the Box system,
getting `Box..{name}` constructors. But TSequence isn't a named
datatype — it's a built-in parameterized type.

**Cons:** Doesn't fit the existing datatype pattern cleanly.

**Decision: B — Per-element-type Box variants**

**Rationale:** This is the same approach used for all other Box
variants. BoxInt stores int, BoxBool stores bool, BoxSequenceInt
stores Sequence int. Each type gets its own Box constructor. The
heap parameterization already generates Box constructors dynamically
based on field types — adding TSequence to this logic is mechanical.

---

## Decision 5: Strata infrastructure fixes are kept

During the L1 implementation, two genuine Strata bugs were found
and fixed. These fixes are language-agnostic and should be kept
regardless of how the Sequence type question is resolved:

1. **HeapParameterization.lean — FieldSelect target recursion:**
   Nested field access (`obj.field1.field2`) wasn't recursing into
   the target expression. The inner FieldSelect wasn't being
   transformed to a heap read. Fixed by adding `recurse selectTarget`.

2. **Resolution.lean — targetTypeName for FieldSelect:**
   The resolution pass couldn't resolve field names on nested field
   access targets because `targetTypeName` only handled `Identifier`
   targets. Extended to handle `FieldSelect` targets.

3. **HeapParameterization.lean — Box datatype ordering:**
   The Box datatype was emitted before the types it references.
   Reordered so dependent types are defined first.

**Decision: Keep these fixes**

**Rationale:** These are bugs in Strata's generic infrastructure.
Any language with nested field access or composite fields would hit
them. They're not Java-specific.

---

## Implementation Plan

### Strata changes

1. Add `TSequence (elementType : WithMetadata HighType)` to
   `HighType` in `Laurel.lean`
2. Add grammar rule `Sequence elementType` to `LaurelGrammar.st`
3. Add concrete-to-abstract translation in
   `ConcreteToAbstractTreeTranslator.lean`
4. Add format case in `LaurelFormat.lean`
5. Add `TSequence` case to `translateType` in
   `LaurelToCoreTranslator.lean`
6. Add `TSequence` cases to Box functions in
   `HeapParameterization.lean` (per-element-type variants)
7. Add `TSequence` cases to any other passes that pattern-match
   on `HighType` (mechanical — recurse into element type)
8. Update Sequence operation signatures in
   `CoreDefinitionsForLaurel.lean` to use `Sequence int` instead
   of `int` placeholder
9. Remove JArray composites from `CoreDefinitionsForLaurel.lean`
10. Remove all JArray-specific checks from translator and heap
    parameterization
11. Keep infrastructure fixes (FieldSelect recursion, nested
    resolution, Box ordering)

### JVerify changes

12. Update JVerify compiler to emit JArray composites in
    `getPredefinedTypes()` with `$data` fields using
    `TSequence(elementType)` — via the Laurel AST, not grammar
13. Verify all Strata tests still pass
14. Verify all JVerify Strata tests still pass
