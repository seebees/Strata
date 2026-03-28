# Constrained Types in the Heap Model: Design

## Overview

The heap model stores composite field values in a Box datatype.
The Box system needs to preserve constrained types through the
store/load round-trip. Currently it doesn't — constrained types
are stripped to their base types, losing the constraint.

## Architecture

### The constrained type vocabulary

Laurel provides a vocabulary of constrained types representing
bounded integer ranges: `int8`, `int16`, `int32`, `int64`, `nat32`.
These are mathematical facts about number ranges, not language-
specific knowledge.

Each constrained type is paired with a Core read function that
carries the constraint as fixed axioms:

| Constrained type | Core read function | Axioms |
|---|---|---|
| int8 | readInt8(box) | result >= -128, result <= 127 |
| int16 | readInt16(box) | result >= -32768, result <= 32767 |
| int32 | readInt32(box) | result >= -2147483648, result <= 2147483647 |
| int64 | readInt64(box) | result >= -2^63, result <= 2^63-1 |
| nat32 | readNat32(box) | result >= 0, result <= 2147483647 |

All read functions also have the axiom `result == Box..intVal!(box)`,
tying the result to the actual heap value.

Language compilers select from this vocabulary:
- JVerify selects `int32` for Java `int`, `int8` for Java `byte`
- A Rust backend would select `int32` for `i32`, `int8` for `i8`
- A Python backend would not select any

### The heap round-trip

When a composite field has a constrained type, the value passes
through three stages:

1. **Write:** The value is boxed and stored in the heap.
   `heap := updateField(heap, obj, field, BoxInt(value))`
   The constrained type elimination checks `int32$constraint(value)`
   at this point (assert at constructor call).

2. **Storage:** The heap holds the boxed value faithfully
   (Core map axioms).

3. **Read:** The value is unboxed using the paired read function.
   `result := readInt32(readField(heap, obj, field))`
   The read function's axioms guarantee the result is in range.

### The layered architecture

No layer generates axioms. Each layer selects from what the layer
below provides:

- **Core** defines `readInt32`, `readInt8`, etc. with fixed axioms.
  These are defined in the Factory alongside map and Sequence
  axioms. The axioms are auditable and fixed.

- **Laurel** pairs each constrained type with its Core read
  function. `int32` is paired with `readInt32`. The constrained
  type elimination generates the write-side assert. The pairing
  is fixed — you can't use `readInt32` with `int8`.

- **Translator** calls the paired read function when translating
  a constrained-type field read. It does not generate axioms —
  it selects the predefined function.

- **Compilers** select which constrained types to use for their
  language's types. JVerify selects `int32` for Java `int`.

### Soundness

The read function axiom `readInt32(box) >= -2147483648` is sound
under three conditions:

1. **Heap faithfulness.** The heap preserves values exactly.
   (Core map axioms.)

2. **Constructor invariant.** BoxInt is only constructed with
   values satisfying the constraint for the field's declared type.
   (Maintained by constrained type elimination's write-side assert.)

3. **No backdoor writes.** The language cannot modify heap values
   without going through the constraint-checked write path.
   (Property of well-behaved languages: Java, Rust, etc.)

### Auditability

For any generated program, the correctness can be audited:

- **Core level:** Inspect the `readInt32` axioms — are they
  mathematically consistent with the `int32` constraint?
- **Translator output:** Inspect the Core program — is `readInt32`
  only used for `int32` fields? Are the write-side asserts present?
- **Compiler output:** Inspect the Laurel program — did the
  compiler correctly select `int32` for the language's types?

Each level is independently inspectable. The axioms are fixed and
predefined, not generated. The trust surface is the Core read
functions, which are a small, enumerable, auditable set.

### Provability

If the translator were formally verified, we could prove:
1. The translator only calls `readInt32` for fields declared as
   `int32` (correct pairing).
2. The constrained type elimination inserts asserts at all BoxInt
   constructor calls for `int32` fields (constructor invariant).
3. Combined with Core's map axioms and the read function axioms,
   the constraint is preserved through the heap round-trip.

### Interaction with existing passes

- **Heap parameterization:** No changes to Box variants. Fields
  with constrained types still use BoxInt (the base type's Box).
  The constrained type stripping workaround is removed — the
  field type stays `int32` through heap parameterization.

- **Constrained type elimination:** Continues to generate write-
  side asserts. Resolves constrained types in datatype definitions.
  No new assume or axiom generation.

- **Translator:** When translating a field read where the field
  type was a constrained type, calls the paired Core read function
  instead of the raw Box accessor. This is the only new behavior
  in the translator.

- **Core Factory:** New read functions (`readInt32`, etc.) defined
  alongside existing map and Sequence functions.

### What gets removed

1. The constrained type stripping workaround.
2. Tests no longer need explicit preconditions for field value
   ranges.

### Adding new constrained types

To add a new constrained type (e.g., `int128` for Rust):
1. Define the constrained type in Laurel's vocabulary
2. Define the paired Core read function in the Factory with
   fixed axioms
3. Language compilers can then select it

No translator changes needed — the translator already handles
the pairing generically.
