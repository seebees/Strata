# Strata Laurel Exceptions: Open Questions

Issues specific to the Strata/Laurel translator and Core backend.

## 1. Variable name `result` collides with Laurel output parameter

**Problem:** If a user names a local variable `result`, it collides
with the Laurel output parameter that the translator uses for the
return value. Strata rejects the program with "Variable result of
type int already in context."

**Options:**
- Mangle the translator's output parameter name (e.g., `$__result`)
- Mangle user variable names that collide
- Use a namespace/scope mechanism in Core to distinguish them

**Status:** Known issue. Workaround: don't name variables `result`.

---

## 2. Propagation check exits procedure, not try block

**Problem:** The cross-method exception propagation check
(`if isFailure($result) { exit $body }`) always exits to `$body`
(the procedure-level label). When a method call is inside a
try/catch block, the propagation exit should go to the try block's
handler, not to the procedure body.

**Impact:** `try { throwingMethod(); } catch (E e) { ... }` does
not work as expected for cross-method exceptions.

**Fix:** The propagation check needs to be context-aware. Inside a
try block, it should exit to the try block's handler label instead
of `$body`. This requires the translator to track the current
try/catch context and pass the right label to the propagation check.

**Status:** Known limitation. Workaround: `postconditionOnThrow(false)`
on the callee prevents the propagation check from firing.
