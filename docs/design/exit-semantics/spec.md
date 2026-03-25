# Exit Semantics: Formal Specification

**Date:** 2026-03-25
**Status:** Proposed

## 1. Context

The formal semantics (`EvalStmt`/`EvalBlock` in
`DL/Imperative/StmtSemantics.lean`) has no semantics for `exit`.
The comment reads: `-- (TODO): Define semantics of exit.`

The operational evaluator (`StatementEval.lean`) handles exit
correctly via an `exitLabel` field. The type checker
(`StatementType.lean`) enforces well-formedness constraints on
labels.

Exit and labeled blocks are used by multiple language features:
Java break/continue, Python try/except, Go defer, and the
Laurel→Core exception translation. This specification defines
the formal semantics independently of any particular use case.

## 2. Definitions

### 2.1 BlockResult

A block evaluation produces one of two outcomes:

```
inductive BlockResult where
  | normal                          -- all statements completed
  | exited (label : Option String)  -- exit is propagating
```

`exited none` means "exit the nearest enclosing block" (unlabeled
exit). `exited (some L)` means "exit the block labeled L."

### 2.2 consumeExit

A labeled block may consume a matching exit:

```
def consumeExit (blockLabel : String) : BlockResult → BlockResult
  | .normal => .normal
  | .exited .none => .normal
  | .exited (.some l) =>
      if l == blockLabel then .normal
      else .exited (.some l)
```

### 2.3 Well-formedness (from type checker)

A program is well-formed with respect to exit if:

- **WF-NoShadow**: No block label shadows an enclosing block
  label in the same nesting chain.
- **WF-LabelExists**: Every `exit L` has an enclosing block
  with label `L`.
- **WF-InsideBlock**: Every `exit` occurs inside at least one
  block.

These are enforced by the type checker and are preconditions
for the formal semantics.

## 3. Semantics

### 3.1 EvalStmt

`EvalStmt` relates an input state to an output state, a
`BlockResult`, and an output evaluation context:

```
EvalStmt : δ → σ → Stmt → σ' → BlockResult → δ' → Prop
```

Constructors:

```
| cmd_sem :
    EvalCmd δ σ c σ' →
    isDefinedOver ... →
    EvalStmt δ σ (Stmt.cmd c) σ' .normal δ

| block_sem :
    EvalBlock δ σ body σ' br δ' →
    consumeExit label br = br' →
    EvalStmt δ σ (.block label body md) σ' br' δ'

| ite_true_sem :
    δ σ cond = some tt →
    EvalBlock δ σ thenBranch σ' br δ' →
    EvalStmt δ σ (.ite cond thenBranch elseBranch md) σ' br δ'

| ite_false_sem :
    δ σ cond = some ff →
    EvalBlock δ σ elseBranch σ' br δ' →
    EvalStmt δ σ (.ite cond thenBranch elseBranch md) σ' br δ'

| exit_sem :
    EvalStmt δ σ (.exit label md) σ (.exited label) δ

| funcDecl_sem :
    EvalStmt δ σ (.funcDecl decl md) σ .normal (extendEval δ σ decl)

| typeDecl_sem :
    EvalStmt δ σ (.typeDecl tc md) σ .normal δ
```

### 3.2 EvalBlock

`EvalBlock` relates an input state to an output state, a
`BlockResult`, and an output evaluation context:

```
EvalBlock : δ → σ → List Stmt → σ' → BlockResult → δ' → Prop
```

Constructors:

```
| stmts_none_sem :
    EvalBlock δ σ [] σ .normal δ

| stmts_normal_sem :
    EvalStmt δ σ s σ' .normal δ' →
    EvalBlock δ' σ' rest σ'' br δ'' →
    EvalBlock δ σ (s :: rest) σ'' br δ''

| stmts_exit_sem :
    EvalStmt δ σ s σ' (.exited label) δ' →
    EvalBlock δ σ (s :: rest) σ' (.exited label) δ'
```

## 4. Correctness Properties

### E1: Exit Preserves Store

An `exit` statement does not modify the store or evaluation
context.

```
theorem exit_preserves_store :
  EvalStmt δ σ (.exit label md) σ' br δ' →
  σ' = σ ∧ δ' = δ ∧ br = .exited label
```

### E2: Exit Skips Remaining Statements

If a statement in a block produces an exit, subsequent
statements do not execute and do not affect the store.

```
theorem exit_skips_remaining :
  EvalBlock δ σ (s :: rest) σ' (.exited label) δ' →
  EvalStmt δ σ s σ' (.exited label) δ'
```

(The store `σ'` is determined entirely by `s`, not by `rest`.)

### E3: Matching Block Consumes Exit

A block with label L that contains an `exit (some L)` completes
normally.

```
theorem matching_block_consumes :
  EvalBlock δ σ body σ' (.exited (some L)) δ' →
  EvalStmt δ σ (.block L body md) σ' .normal δ'
```

### E4: Non-Matching Exit Propagates

A block with label L that contains an `exit (some M)` where
M ≠ L propagates the exit.

```
theorem nonmatching_exit_propagates :
  M ≠ L →
  EvalBlock δ σ body σ' (.exited (some M)) δ' →
  EvalStmt δ σ (.block L body md) σ' (.exited (some M)) δ'
```

### E5: Normal Block Completion

If a block's body completes normally, the block completes
normally.

```
theorem normal_block_completion :
  EvalBlock δ σ body σ' .normal δ' →
  EvalStmt δ σ (.block L body md) σ' .normal δ'
```

### E6: Exit Propagates Through Conditionals

If the taken branch of a conditional produces an exit, the
conditional produces the same exit.

```
theorem exit_propagates_through_ite :
  δ σ cond = some tt →
  EvalBlock δ σ thenBranch σ' (.exited label) δ' →
  EvalStmt δ σ (.ite cond thenBranch elseBranch md) σ' (.exited label) δ'
```

(Symmetric for the false branch.)

### E7: Determinism of Exit Consumption

`consumeExit` is a total function — given a block label and a
`BlockResult`, the output is uniquely determined.

```
theorem consumeExit_deterministic :
  consumeExit L br = br₁ →
  consumeExit L br = br₂ →
  br₁ = br₂
```

(This is trivially true since `consumeExit` is a function, but
stating it explicitly documents that there is no ambiguity in
which block consumes an exit.)

### E8: Uniqueness of Exit Target

In a well-formed program (WF-NoShadow), for any `exit (some L)`,
there is exactly one enclosing block with label `L` that will
consume it.

```
theorem exit_target_unique :
  WellFormed program →
  exit (some L) occurs in program →
  ∃! block, block.label = L ∧ block encloses the exit
```

This is a structural property of well-formed programs, not a
semantic property. It follows from WF-NoShadow and WF-LabelExists.

### E9: Completeness of Exit Resolution

In a well-formed program, every `exit` is eventually consumed
by some enclosing block. No exit propagates past the outermost
block of a procedure.

```
theorem exit_eventually_consumed :
  WellFormed program →
  EvalBlock δ σ procedureBody σ' br δ' →
  br = .normal
```

This states that the procedure body (which is wrapped in a
`block "$body" ...`) always completes normally — all exits are
consumed before reaching the procedure boundary.

## 5. Decisions

### Decision 1: BlockResult as a separate type vs encoding in store

**Option A**: `BlockResult` as a new inductive type (proposed above).

- Pro: Clean separation. The store only contains program
  variables. Exit status is control flow, not data.
- Pro: Proofs about store preservation are simpler — exit
  doesn't modify the store by definition.
- Con: Changes the signature of `EvalStmt` and `EvalBlock`,
  affecting all downstream proofs.

**Option B**: Encode exit as a special store variable
(e.g., `$exit_label`).

- Pro: No signature change to `EvalStmt`/`EvalBlock`.
- Con: Conflates control flow with data. Every proof about
  store values must account for the special variable.
- Con: The operational evaluator uses a separate field
  (`exitLabel`), so this would diverge from the implementation.

**Decision**: Option A. The operational evaluator already uses a
separate field. The formal semantics should match. The signature
change is the right cost to pay for clean separation.

### Decision 2: Where to define BlockResult

**Option A**: In `DL/Imperative/StmtSemantics.lean` alongside
`EvalStmt`/`EvalBlock`.

- Pro: Co-located with the semantics that use it.
- Con: The DL layer is language-independent. `BlockResult` is
  specific to imperative languages with labeled blocks.

**Option B**: In `DL/Imperative/Stmt.lean` alongside the `Stmt`
type definition.

- Pro: `BlockResult` is about statement evaluation outcomes,
  which is part of the statement abstraction.

**Decision**: Option A. `BlockResult` is a semantic concept (an
evaluation outcome), not a syntactic concept. It belongs with
the semantics.

### Decision 3: Loop semantics and exit

The current `EvalStmt` has a `loop` constructor (not shown in
detail). Can `exit` occur inside a loop body?

The type checker allows it — `exit` inside a loop exits the
loop's enclosing block, not the loop itself. The loop body is
not a labeled block.

**Decision**: Exit inside a loop body propagates out of the loop.
The loop's `EvalStmt` constructor must handle `BlockResult` from
its body evaluation. If the body produces `exited L`, the loop
terminates and propagates the exit.

## 6. Dependents

The following features depend on exit semantics being formalized:

- **Laurel exception translation** (`Throw`/`TryCatch` desugar
  to labeled blocks and exit). See
  `docs/design/laurel-exceptions/spec.md`.
- **Break/continue** in loops (desugar to exit).
- **Early return** (desugars to `exit $body`).
- **Python try/except** (uses exit + labeled blocks in
  `PythonToLaurel.lean`).

## 7. Compatibility

Adding `BlockResult` to `EvalStmt`/`EvalBlock` changes their
signatures. Affected files:

| File | Impact |
|---|---|
| `DL/Imperative/StmtSemantics.lean` | Definition change |
| `DL/Imperative/SemanticsProps.lean` | Add exit cases to existing proofs |
| `DL/Imperative/StmtSemanticsSmallStep.lean` | Add exit to small-step semantics |
| `DL/Imperative/CFGSemantics.lean` | Add exit to CFG semantics |
| `Languages/Core/StatementSemantics.lean` | Update Core instantiation |
| `Languages/Core/StatementSemanticsProps.lean` | Add exit cases to Core proofs |
| `Transform/CallElimCorrect.lean` | Add exit case to correctness proof |
| `Transform/DetToNondetCorrect.lean` | Add exit case to correctness proof |

Existing proofs that pattern-match on `EvalStmt` need a new
`exit_sem` case. Existing proofs that pattern-match on `EvalBlock`
need to handle `stmts_exit_sem`. In most cases the exit case is
vacuous (the proof context already excludes exit) or follows the
same pattern as existing cases.
