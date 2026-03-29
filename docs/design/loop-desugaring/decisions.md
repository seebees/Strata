# Loop Desugaring Patterns

**Date:** 2026-03-29

Strata's Laurel language provides `While` as the only loop
primitive. Language compilers that target Laurel must desugar
other loop forms into `While`. This document records verified
desugaring patterns that any compiler can use.

## Do/While → Body + While

A `do { body } while (cond)` with `invariant(I)` desugars to:

```
body;                        // first execution establishes I
while (cond)
  invariant I
{ body };                    // maintains I
```

### Hoare logic correctness

The do/while Hoare rule:
```
{Q} body {I}    {I ∧ cond} body {I}
─────────────────────────────────────
{Q} do { body } while (cond) {I ∧ ¬cond}
```

is derived from sequential composition + the while rule:
```
{Q} body {I}    {I} while (cond) { body } {I ∧ ¬cond}
────────────────────────────────────────────────────────
{Q} body; while (cond) { body } {I ∧ ¬cond}
```

Both sequential composition and the while rule are proven in
Strata's Core.

### Key property: invariant establishment

Unlike `while`, the invariant does NOT need to hold before the
loop. The first body execution establishes it. This is correct
because do/while guarantees at least one execution.

### Verified in Strata

Five test cases verify this desugaring pattern:
`StrataTest/Languages/Laurel/Examples/Fundamentals/T19_DoWhileDesugaring.lean`

1. Multiple iterations (count to 10)
2. Single execution (while runs zero times)
3. Precondition-dependent invariant
4. Invariant false before first execution (key difference from while)
5. Accumulator with arithmetic invariant

## For Loop → Init + While

Already implemented in Strata's Laurel parser. A `for (init; cond; step) { body }`
desugars to:

```
init;
while (cond)
  invariant I
{
  body;
  step
};
```

See `ConcreteToAbstractTreeTranslator.lean` line 333.
