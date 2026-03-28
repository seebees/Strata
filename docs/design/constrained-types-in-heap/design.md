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

The constrained type elimination pass handles both sides of the
heap round-trip:

- **Write side (existing):** When a value is stored in a Box
  constructor with a constrained-type argument, the pass inserts
  `assert int32$constraint(value)`. The prover must prove this.

- **Read side (new):** When a datatype accessor extracts a value
  whose constructor argument had a constrained type, the pass
  inserts `assume int32$constraint(value)`. The prover can use
  this knowledge.

The assume is justified by the write-side assert plus heap
faithfulness: the value was checked going in, the heap preserves
it, the accessor extracts the same value.

This approach keeps all constraint handling in one pass. The heap
parameterization doesn't need to know about constrained types. The
translator doesn't need to generate axioms. Core stays simple.

### Interaction with existing passes

- **Heap parameterization:** No changes needed. It generates Box
  constructors/destructors based on field types. With the stripping
  workaround removed, it uses the constrained type directly.

- **Constrained type elimination:** Extended to handle the read
  side of the heap round-trip. When it encounters a datatype
  accessor call whose constructor argument had a constrained type,
  it inserts an assume with the constraint. This is the same pass
  that generates the write-side assert and the constraint function.

- **Modifies clause transformation:** No changes needed. The frame
  condition preserves field values for unmodified objects. If the
  value satisfies a constraint before modification, it still
  satisfies it after (since it's the same value).

- **Translator:** No changes needed. The assume is a Laurel-level
  statement that translates to a Core assume. The constraint
  function is already in Core after elimination.

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
