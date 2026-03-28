# Constrained Types in the Heap Model: Design

## Overview

The heap model stores composite field values in a Box datatype.
The Box system needs to preserve constrained types through the
store/load round-trip. Currently it doesn't — constrained types
are stripped to their base types, losing the constraint.

## Architecture

### The constrained type vocabulary

Laurel should provide a vocabulary of constrained types representing
bounded integer ranges: `int8`, `int16`, `int32`, `int64`, `nat32`,
and potentially others. These are mathematical facts about number
ranges, not language-specific knowledge.

Language compilers select from this vocabulary:
- JVerify selects `int32` for Java `int`, `int8` for Java `byte`
- A Rust backend would select `int32` for `i32`, `int8` for `i8`
- A Python backend would not select any (Python integers are
  unbounded)

The constrained type elimination pass translates these into Core
by generating constraint-checking functions (`int32$constraint`)
and inserting checks at type boundaries.

### The heap round-trip

When a composite field has a constrained type, the value passes
through three stages:

1. **Write:** The value is boxed and stored in the heap.
   `heap := updateField(heap, obj, field, Box..int32(value))`
   The constrained type elimination checks `int32$constraint(value)`
   at this point.

2. **Storage:** The heap holds the boxed value. The Box constructor
   preserves the constrained type in its argument type.

3. **Read:** The value is unboxed from the heap.
   `result := Box..int32Val!(readField(heap, obj, field))`
   The destructor should return a value that satisfies `int32`.

Currently, stage 3 loses the constraint because the constrained
type elimination doesn't generate constraint knowledge for datatype
destructors.

### The fix

The heap parameterization generates wrapper functions for
constrained-type field reads. The wrapper calls the raw datatype
accessor and carries the constraint as a function axiom.

Core functions already have an `axioms` field — this is the
established mechanism for function properties. The Sequence
operations use axioms (e.g., `Sequence.length(Sequence.build(s, v))
== Sequence.length(s) + 1`). The wrapper functions follow the same
pattern.

Functions are pure and callable in all contexts — contracts,
postconditions, and statements. This avoids the limitation where
procedures cannot be called in pure contexts.

This is general — it applies to all datatypes, not just Box. If
a user defines `datatype Pair { MkPair(x: int32, y: int32) }`,
then reading `x` through the heap would use a wrapper function
with an axiom carrying the `int32` constraint.

### Interaction with existing passes

- **Heap parameterization:** Generates wrapper functions for
  constrained-type field reads. The wrapper calls the raw accessor
  and has axioms carrying the constraint.

- **Constrained type elimination:** The wrapper function's output
  type is the constrained type. The elimination pass resolves it
  to the base type and may add additional constraint checks at
  call sites. The axiom carries the constraint independently.

- **Modifies clause transformation:** No changes needed. The frame
  condition preserves field values for unmodified objects. If the
  value satisfies a constraint before modification, it still
  satisfies it after (since it's the same value).

- **Translator:** Functions with axioms are already supported in
  Core. The translator handles them through the existing function
  translation path. No changes needed.

### What gets removed

Once this is implemented:

1. The constrained type stripping workaround is removed from the
   translator pipeline. Fields keep their declared constrained
   types through heap parameterization.

2. Tests that currently need explicit preconditions for field
   value ranges (e.g., `precondition(this.value >= -2^31 && ...)`)
   no longer need them — the constraint is preserved automatically.

### Trust surface

The constraint on destructor results is sound because:
- The constructor checks the constraint at write time
- The Box preserves the value exactly (no transformation)
- The destructor extracts the same value that was stored

This is the same reasoning that makes procedure postconditions
sound: if the procedure body establishes the postcondition, callers
can rely on it. If the constructor establishes the constraint,
destructor callers can rely on it.
