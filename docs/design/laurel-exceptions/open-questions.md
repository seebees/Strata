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

## 2. ~~Propagation check exits procedure, not try block~~ ✅ FIXED

Fixed: the translator now tracks the current exception target label.
Inside a try body, propagation exits to the handlers label. Properties
P9-P12 proven in Lean. See Decision 7 in decisions.md.
