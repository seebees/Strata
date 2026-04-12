# Cross-Type Instance Call Resolution: Context

**Date:** 2026-04-11
**Status:** Decided — see [decisions.md](decisions.md)

## The Problem in One Sentence

When two composite types have instance procedures with the same
name, the Laurel resolution pass assigns the wrong procedure to
cross-type calls because it uses name-based global scope lookup
instead of type-directed lookup.

## Concrete Example

```java
// Position has compareTo
record Position(int line, int character) {
    int compareTo(Position o) { ... }
}

// Range has compareTo AND calls Position's compareTo
record Range(Position start, Position end) {
    int compareTo(Range o) {
        int startSign = start().compareTo(o.start());  // ← calls Position.compareTo
        return startSign == 0 ? end().compareTo(o.end()) : startSign;
    }
}
```

## Where the Information Was Lost

### Step 1: Java frontend (CORRECT)

javac knows `start()` returns `Position` and `.compareTo()` is
`Position.compareTo`. The frontend emitted only the unqualified
name:

```
InstanceCall(
    target: FieldAccess(self, "start"),
    callee: "compareTo",                   // ← unqualified
    args: [FieldAccess(other, "start")]
)
```

### Step 2: Laurel resolution (INCORRECT)

The resolution pass registered instance procedures in the global
scope, causing shadowing:

```
scope["compareTo"] = (id=3, Position's compareTo)   // registered first
scope["compareTo"] = (id=7, Range's compareTo)       // overwrites!
```

### Step 3: Translator (USED WRONG ID)

```lean
model.get callee  -- callee has id=7
-- returned: instanceProcedure "Range" rangeCompareTo
-- generated: Range~>compareTo(target, args)
-- should be: Position~>compareTo(target, args)
```

### Step 4: Core pipeline (CRASHED)

The Core call referenced `Range~>compareTo` with Position-typed
arguments. The output arity didn't match. The CallElim transform
crashed: "output length and lhs length mismatch."

## Resolution

The fix has two parts:

1. **Frontend qualifies callee names (D2).** The Java frontend
   now emits `InstanceCall(target, "Position~>compareTo", args)`.
   The `~>` separator distinguishes instance methods from
   datatype destructors (which use `..`). See Decision 9 in
   `instance-methods/decisions.md`.

2. **Definitions qualified early (D4).** Instance procedure
   definitions are qualified before the first resolution pass.
   `preRegisterTopLevel` registers `"Position~>compareTo"` and
   `"Range~>compareTo"` as separate scope entries. No shadowing.

See [decisions.md](decisions.md) for the full design: 6 decisions
covering dispatch responsibility (D1), communication mechanism
(D2), semantic verification (D3), heap analysis (D4), proof
obligations (D5), and implementation order (D6).
