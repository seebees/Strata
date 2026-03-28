# Constrained Types in the Heap Model: Design

## Overview

The heap model stores composite field values in a Box datatype.
The Box system needs to preserve constrained types through the
store/load round-trip. Currently it doesn't — constrained types
are stripped to their base types, losing the constraint.

## Architecture

### The constrained type vocabulary

Laurel provides a vocabulary of constrained types representing
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
   `heap := updateField(heap, obj, field, BoxInt32(value))`
   The constrained type elimination checks `int32$constraint(value)`
   at this point.

2. **Storage:** The heap holds the boxed value. The Box constructor
   preserves the constrained type in its variant name.

3. **Read:** The value is unboxed from the heap.
   `result := Box..int32Val!(readField(heap, obj, field))`
   The accessor returns the value. The constraint needs to be
   re-established.

### The layered axiom approach

The constraint is re-established through a layered axiom chain,
following the same architecture used throughout the system:

**Core provides the foundation:**
- Heap faithfulness: `select(update(m, k, v), k) == v`
- Datatype accessor correctness: `Box..int32Val!(BoxInt32(v)) == v`
- These are mathematical truths, proven or provable.

**Core provides constraint axioms on Box accessors:**
For each constrained-type Box variant, Core provides an axiom:
```
forall box. Box..isBoxInt32(box) ==> int32$constraint(Box..int32Val!(box))
```
This axiom says: if a Box value IS a BoxInt32, then the extracted
value satisfies the int32 constraint.

This axiom is NOT a standalone mathematical truth. It is sound
only under the invariant that BoxInt32 is always constructed with
values satisfying `int32$constraint`. This invariant is maintained
by the constrained type elimination pass (which inserts asserts
at constructor call sites).

**Laurel exposes constrained types that map to these axioms:**
The constrained type elimination generates BoxInt32 variants for
int32 fields, and the translator generates the corresponding Core
axioms. Laurel can only use axioms that Core provides.

**Compilers select from Laurel's vocabulary:**
JVerify declares fields as `int32`. Laurel handles the rest.

### Soundness dependencies

The axiom `Box..isBoxInt32(box) ==> int32$constraint(Box..int32Val!(box))`
is sound IF AND ONLY IF all three conditions hold:

1. **Heap faithfulness.** The heap preserves values exactly. What
   you write is what you read. This is a property of Core's map
   axioms (`select(update(m, k, v), k) == v`). Languages with
   undefined behavior on memory access (like C) may violate this.

2. **Constructor invariant.** BoxInt32 is only ever constructed
   with values satisfying `int32$constraint`. This is maintained
   by the constrained type elimination pass, which inserts
   `assert int32$constraint(value)` at every BoxInt32 constructor
   call. If the pass has a bug, or if a program constructs BoxInt32
   directly without going through the pass, the invariant breaks.

3. **No backdoor writes.** The language cannot modify heap values
   without going through the normal write path (which includes
   the constraint check). Languages with raw memory access,
   pointer aliasing, or undefined behavior may violate this.

For the languages we target (Java, Rust, JavaScript, Python),
all three conditions hold. These languages have well-behaved heaps,
all writes go through the programming language's own mechanisms,
and the constrained type elimination processes all code paths.

### Provability

If the translator and constrained type elimination pass were
formally verified, we could prove:

1. The constrained type elimination maintains the constructor
   invariant: BoxInt32 is only constructed with int32-satisfying
   values. (Property of the pass.)

2. The generated axiom is consistent with the constructor
   invariant. (Property of the translator.)

3. The axiom, combined with heap faithfulness and the constructor
   invariant, implies that accessor results satisfy the constraint.
   (Logical consequence of 1 + 2 + Core map axioms.)

This is the same verification structure as the instance method
consistency proof (Decision 2 in instance-methods/decisions.md):
a property that traces through multiple passes, provable if the
passes are verified, trusted by testing and audit until then.

### Interaction with existing passes

- **Heap parameterization:** Generates per-constrained-type Box
  variants (BoxInt32, BoxInt16, etc.) instead of mapping all
  constrained types to the base type's Box variant. The variant
  name carries the constraint identity.

- **Constrained type elimination:** Inserts asserts at BoxInt32
  constructor calls (write side). Resolves constrained types in
  datatype definitions. The constraint function `int32$constraint`
  is generated as today.

- **Translator:** Generates the Core axiom for each constrained-
  type Box accessor. The axiom is: if the Box is the right variant,
  the accessor result satisfies the constraint.

- **Modifies clause transformation:** No changes needed. The frame
  condition preserves field values for unmodified objects.

### What gets removed

Once this is implemented:

1. The constrained type stripping workaround is removed from the
   translator pipeline.

2. Tests that currently need explicit preconditions for field
   value ranges no longer need them.

### Trust surface

The trust surface is:
- The Core axiom on each constrained-type Box accessor
- The constructor invariant maintained by constrained type
  elimination
- The heap faithfulness property of Core's map model

The axiom is generated mechanically, not hand-written. It follows
a fixed pattern. It is auditable by inspecting the translator's
axiom generation code. It is provable if the translator and
constrained type elimination are formally verified.
