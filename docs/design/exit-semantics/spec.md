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
M ≠ L does not consume the exit. The exit passes through the
block unchanged.

This is the mechanism that makes uncaught exceptions work. In
the exception translation, a try/catch block has label `$try_end`.
The catch dispatch code checks each handler's exception type.
If none match, the exception must propagate to the caller. The
catch dispatch does NOT re-throw — instead, the original exit
(targeting `$body` or an outer handler) simply passes through
the `$try_end` block because the labels don't match.

Example in Java terms: `try { foo() } catch (IOException e) { ... }`
where `foo()` throws `NullPointerException`. The try block's
label is `$try_end`. The exit from the throw targets `$body`
(the procedure boundary). Since `$body ≠ $try_end`, the exit
propagates through the try block, skipping the catch handler
entirely.

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

Conditionals (`if/else`) are not blocks. They have no label.
They cannot consume exits. If the taken branch produces an exit,
the conditional produces the same exit — it is transparent.

This matters because throw (which desugars to exit) can occur
inside a conditional inside a try body:

```java
try {
    if (badInput) {
        throw new IllegalArgumentException();
    }
    doWork();
} catch (IllegalArgumentException e) { ... }
```

The `throw` produces an exit. The `if` must propagate that exit
so it reaches the enclosing handlers block. If the conditional
absorbed the exit, the catch handler would never run.

The same applies to any non-block statement that contains nested
evaluation: conditionals are the primary case because they
evaluate sub-blocks (the then/else branches).

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

See [decisions.md](decisions.md) for design decisions about
`BlockResult` representation, placement, and loop interaction.

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
