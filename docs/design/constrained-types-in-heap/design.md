# Constrained Types in the Heap Model: Design

## Overview

The heap model stores composite field values in a Box datatype.
The Box system preserves constrained types through the store/load
round-trip using two mechanisms: Factory read functions (for bounds)
and program-level equality axioms (for value identity).

## Architecture

### The constrained type vocabulary

Laurel provides a vocabulary of constrained types representing
bounded integer ranges: `int8`, `int16`, `int32`, `int64`, `nat32`.
These are mathematical facts about number ranges, not language-
specific knowledge.

Each constrained type is paired with a Core Factory read function
that carries the constraint as fixed axioms:

| Constrained type | Core read function | Factory axioms |
|---|---|---|
| int8 | readInt8(box) | result >= -128, result <= 127 |
| int16 | readInt16(box) | result >= -32768, result <= 32767 |
| int32 | readInt32(box) | result >= -2147483648, result <= 2147483647 |

These are opaque functions over a type parameter `a`. The
translator wires Box into the type parameter.

Language compilers select from this vocabulary:
- JVerify selects `int32` for Java `int`, `int8` for Java `byte`
- A Rust backend would select `int32` for `i32`, `int8` for `i8`
- A Python backend would not select any

### The two-part proof

Reading a constrained-type field from the heap requires proving
two things: the value is correct (equality) and the value is
bounded (range). These come from separate mechanisms.

**Bounds (Factory axioms — fixed, auditable):**
The Factory defines `readInt32 : ∀a. a → int` with axioms
guaranteeing the result is in [-2147483648, 2147483647]. These
axioms are fixed in Core and cannot be changed by the translator.

**Equality (program-level axiom — generated, connects to heap):**
The translator generates `∀ v: int. readInt32(BoxInt(v)) == v`
as a Core axiom, conditional on BoxInt existing in the program's
Box datatype. This connects the opaque Factory function to the
Box constructor.

### The heap round-trip

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
bounds (the value is in range).

### Soundness: why the equality axiom is safe

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

### The layered architecture

No layer generates bound axioms. Each layer selects from what
the layer below provides:

- **Core Factory** defines `readInt32`, `readInt8`, etc. with
  fixed bound axioms. These are defined alongside map and Sequence
  axioms. The axioms are auditable and fixed.

- **Translator** generates equality axioms connecting Factory
  read functions to Box constructors. These are structurally
  trivial (`readIntN(BoxInt(v)) == v`) and conditional on the
  Box constructor existing.

- **Heap parameterization** calls the paired read function when
  a constrained-type field is read. It does not generate axioms.

- **Constrained type elimination** generates write-side asserts
  at Box constructor calls. It does not generate read-side axioms.

- **Compilers** select which constrained types to use for their
  language's types. JVerify selects `int32` for Java `int`.

### Auditability

For any generated program, the correctness can be audited:

- **Core level:** Inspect the `readInt32` axioms — are they
  mathematically consistent with the `int32` constraint?
- **Program level:** Inspect the equality axioms — do they
  correctly connect read functions to Box constructors?
- **Translator output:** Inspect the Core program — is `readInt32`
  only used for `int32` fields? Are the write-side asserts present?
- **Compiler output:** Inspect the Laurel program — did the
  compiler correctly select `int32` for the language's types?

Each level is independently inspectable. The bound axioms are
fixed and predefined. The equality axioms are generated but
structurally trivial. The trust surface is small and enumerable.

### Interaction with existing passes

- **Heap parameterization:** No changes to Box variants. Fields
  with constrained types still use BoxInt (the base type's Box).
  The constrained type stripping workaround is removed — the
  field type stays `int32` through heap parameterization. The
  `isComposite` check prevents the equality handler from applying
  `Composite..ref!` to constrained types.

- **Constrained type elimination:** Continues to generate write-
  side asserts and `int32$constraint` functions. No new assume
  or axiom generation.

- **Translator:** Generates equality axioms conditional on Box
  constructors existing. No other changes.

- **Core Factory:** `readInt32`, `readInt16`, `readInt8` defined
  as opaque functions with bound axioms.

### Adding new constrained types

To add a new constrained type (e.g., `int64`):
1. Define the constrained type in Laurel's vocabulary
2. Define the paired Core Factory read function with fixed axioms
3. Add the equality axiom generation in the translator
4. Language compilers can then select it

### Implementation

Commit `a2def101` on `seebees/experimental-work`.

Files modified:
- `Factory.lean`: `readInt32Func`, `readInt16Func`, `readInt8Func`
- `HeapParameterizationConstants.lean`: External Laurel declarations
- `HeapParameterization.lean`: Field reads use `readInt32` for
  constrained types
- `LaurelToCoreTranslator.lean`: Equality axioms, stripping removed
- `ProcedureEvalTests.lean`, `ProgramTypeTests.lean`: Updated
  expected output

Results: 72 JVerify tests, 2 failures (down from 7).
Fixed: StrataInstanceFieldRead, StrataModifiesMultiple,
StrataModifiesField, StrataChainedFieldWrite, StrataArrayLength,
StrataArrayForLoop, StrataArrayLengthPost.
