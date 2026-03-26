# Instance Method Support: Investigation Notes

**Date:** 2026-03-26
**Status:** Investigated, not implemented. Needs more design work.

## What We Found

### Laurel Already Has the Grammar and AST
- `InstanceCall(target, callee, args)` — call an instance method
- `FieldSelect(target, fieldName)` — read a field
- `SelfRef` — reference to `this`/`self`
- `Composite.instanceProcedures` — methods defined on a type
- Explicit `self` parameter in Laurel (like Python)

### Heap Parameterization Handles Field Access
The heap parameterization pass already transforms:
- `self#field` reads → `readField($heap, self, Field)`
- `self#field` writes → `updateField($heap, self, Field, val)`
- Adds `$heap` as input/output parameter for heap-accessing procedures

This pass works correctly for instance procedure DEFINITIONS.

### The Translator Rejects Instance Procedures
The Laurel→Core translator only processes `program.staticProcedures`.
Instance procedures on composites are rejected with "not yet supported."

### What We Tried
Promoted instance procedures from `composite.instanceProcedures` to
`program.staticProcedures` after heap parameterization, with qualified
names (e.g., `Counter..increment`).

**Result:** Instance procedure DEFINITIONS translated correctly.
Read-only methods worked. Mutating methods worked after fixing a
name collision with the heap constant `increment`.

### Why We Rolled Back

**The call side is not implemented.** `InstanceCall` nodes in callers
are NOT transformed by heap parameterization — they survive unchanged
into the translator, which rejects them ("not yet implemented").

For instance methods to work end-to-end, we need BOTH:
1. Definition: instance procedure → Core procedure (partially done)
2. Call: `InstanceCall target callee args` → `StaticCall "Type..callee" (target, args)` with heap parameter

The call transformation requires knowing the TYPE of the target
expression to determine the qualified procedure name. This type
information may not be available in the heap parameterization pass.

### The Full Work Required

#### In Strata (Laurel pipeline):
1. **Heap parameterization**: Transform `InstanceCall target callee args`
   into `StaticCall "TypeName..callee" (heap, target, args)`.
   Needs: type of `target` to determine `TypeName`.
   
2. **Promote definitions**: Move transformed instance procedures from
   composites to `staticProcedures` (the approach we tried, works).

3. **Name qualification**: Ensure the qualified name used at the call
   site matches the qualified name on the definition. Currently
   resolution gives instance procedures unqualified names.

4. **Type resolution at call sites**: The heap parameterization needs
   to know the type of the `InstanceCall` target. Options:
   - Use the resolution pass's type information
   - Add a type annotation to `InstanceCall` in the AST
   - Run a separate type inference pass before heap parameterization

#### In JVerify (Java→Laurel compiler):
5. **Emit composites**: Map Java classes to Laurel composite types
   with fields and instance procedures.

6. **Emit instance calls**: Map `obj.method(args)` to Laurel
   `InstanceCall(obj, method, args)`.

7. **Emit field access**: Map `obj.field` to Laurel
   `FieldSelect(obj, field)`.

8. **Handle `this`**: Map Java `this` to Laurel `SelfRef`.

9. **Handle constructors**: Map `new ClassName(args)` to Laurel
   `New` + constructor call.

10. **Handle inheritance**: Map Java `extends` to Laurel composite
    `extending`.

### Existing Tests
- T1_MutableFields: composites with fields (works)
- T2_ModifiesClauses: modifies on composites (works)
- T5_inheritance: composite extending (works)
- T7_InstanceProcedures: instance methods (currently expects error)

### Recommendation
This is a significant feature, not a quick fix. The Strata side
needs type information threading through the heap parameterization
pass. The JVerify side needs a substantial expansion of the Laurel
compiler. Estimate: multiple sessions of work.

Consider tackling smaller items first (enhanced for loops, old(),
break/continue) before returning to instance methods.
