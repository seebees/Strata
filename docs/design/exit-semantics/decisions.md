# Exit Semantics: Design Decisions

**Date:** 2026-03-25
**Status:** Proposed

## Decision 1: BlockResult as a separate type vs encoding in store

**Context:** The formal semantics needs to represent the outcome
of evaluating a block — did it complete normally, or did an
`exit` transfer control out? Where does this information live?

### Option A: BlockResult as a new inductive type

Add a new type to the evaluation result:

```lean
inductive BlockResult where
  | normal
  | exited (label : Option String)
```

`EvalStmt` and `EvalBlock` gain a `BlockResult` parameter.

- Pro: Clean separation. The store only contains program
  variables. Exit status is control flow, not data.
- Pro: Proofs about store preservation are simpler — exit
  doesn't modify the store by definition.
- Con: Changes the signature of `EvalStmt` and `EvalBlock`,
  affecting all downstream proofs (~7 files, ~101 lines).

### Option B: Encode exit as a special store variable

Add a `$exit_label` variable to the store.

- Pro: No signature change to `EvalStmt`/`EvalBlock`.
- Con: Conflates control flow with data. Every proof about
  store values must account for the special variable.
- Con: The operational evaluator uses a separate field
  (`exitLabel`), so this would diverge from the implementation.

### Decision: Option A

The operational evaluator already uses a separate field. The
formal semantics should match. The signature change is the right
cost to pay for clean separation.

## Decision 2: Where to define BlockResult

**Context:** `BlockResult` is a new type. Where in the codebase
does it belong?

### Option A: In `DL/Imperative/StmtSemantics.lean`

Co-located with `EvalStmt`/`EvalBlock` that use it.

- Pro: Semantic concept lives with the semantics.
- Con: None significant.

### Option B: In `DL/Imperative/Stmt.lean`

Co-located with the `Stmt` type definition.

- Pro: Part of the statement abstraction.
- Con: `BlockResult` is about evaluation outcomes, not syntax.

### Decision: Option A

`BlockResult` is a semantic concept (an evaluation outcome), not
a syntactic concept. It belongs with the semantics.

## Decision 3: Loop semantics and exit

**Context:** Can `exit` occur inside a loop body? If so, what
happens to the loop?

The type checker allows `exit` inside a loop body. The loop body
is not a labeled block — it has no label to consume exits.

### Option A: Exit propagates out of the loop

If the loop body produces `exited L`, the loop terminates
immediately and propagates the exit. The loop does not continue
iterating.

- Pro: Matches the operational evaluator behavior.
- Pro: Matches Java/Python semantics (break/continue desugar
  to exit).

### Option B: Exit is not allowed inside loops

Reject programs with exit inside loop bodies.

- Pro: Simpler loop semantics.
- Con: Breaks existing programs. Break/continue use exit.

### Decision: Option A

Exit inside a loop body propagates out of the loop. The loop's
`EvalStmt` constructor must handle `BlockResult` from its body
evaluation. If the body produces `exited L`, the loop terminates
and propagates the exit.
