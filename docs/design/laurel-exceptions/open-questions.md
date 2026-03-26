# Exception Support: Open Questions

## 1. Variable name `result` collides with Laurel output parameter

**Problem:** If a user names a local variable `result`, it collides
with the Laurel output parameter that the translator uses for the
return value. Strata rejects the program with "Variable result of
type int already in context."

**Impact:** Users cannot use `result` as a variable name in any
verified method. This is a common name and will surprise people.

**Options:**
- Mangle the translator's output parameter name (e.g., `$__result`)
  to avoid collisions with user names
- Mangle user variable names that collide
- Use a namespace/scope mechanism in Core to distinguish them

**Status:** Known issue, not yet fixed. Workaround: don't name
variables `result`.

---

## 2. Cross-method non-throwing proofs

**Problem:** How does a caller prove that a callee never throws?

**Resolution:** `postconditionOnThrow(false)` works. It means
"if this method throws, false must hold" — which is impossible,
so the prover must prove the method never throws. The caller's
propagation check is then satisfied because `$result` is
constrained to `Success` by the postcondition.

No new primitive needed. `postconditionOnThrow(false)` is the
"does not throw" contract.

**Possible sugar:** A `doesNotThrow()` method could be added as
syntactic sugar for `postconditionOnThrow(false)`, but it's not
required for correctness.

---

## 3. Lambda overloads of postconditionOnReturn hit javac NPE

**Problem:** `postconditionOnReturn((int res) -> res > 0)` causes
a NullPointerException in javac's `Lower.java:2645` during the
desugaring phase. The boolean overload works fine.

**Impact:** Users must use the boolean overload for
`postconditionOnReturn` and `postconditionOnThrow`. Lambda
overloads (which reference the return value) don't work yet.

**Root cause:** Likely a javac bug with lambda desugaring in the
presence of the JVerify compiler plugin. The same NPE appears in
other JVerify tests (ArraysVerification, Lambdas, etc.).

**Status:** Known issue. Boolean overloads work as a workaround.

---

## 4. Source ranges for generated ensures clauses

**Problem:** Ensures clauses generated from `guard()`,
`postconditionOnReturn()`, and `postconditionOnThrow()` carry the
source range of the argument expression, not the enclosing method
call. This means the diagnostic points to `x <= 0` rather than
`guard(x <= 0)`.

**Impact:** Minor UX issue. The diagnostic still points to the
right area of code, just not the exact call.

**Fix:** The contract compiler could store the invocation tree
alongside the argument expression, and the Laurel compiler could
use the invocation's source range for the ensures clause.

---

## 5. Postcondition semantics with exceptions

**Problem:** `postcondition(P)` applies to ALL exit paths (normal
return and throw). This is the existing Laurel `ensures` semantics
and is unchanged. But for exception-aware code, users often want
postconditions that apply only to the success path.

**Resolution:** `postconditionOnReturn(P)` applies only to the
success path. `postconditionOnThrow(P)` applies only to the throw
path. `postcondition(P)` remains unconditional (all paths).

See Decision 9 in `jverify/design/exceptions/decisions.md`.
