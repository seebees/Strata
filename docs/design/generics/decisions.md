# Generics Support in Laurel: Decisions

**Date:** 2026-04-16

## Motivation

JVerify's builtin contracts (`IntegerContract`, `LongContract`, `OptionalContract`, `SetContract`, etc.) use Java generics. The Dafny backend handles these because JVerify skips javac's type erasure phase (phase 6, TRANSTYPES), preserving type parameters in the AST. The Laurel backend cannot compile these contracts because it has no support for type parameters.

19 of 35 builtin contract files use generics. Until the Laurel compiler can handle them, the Strata backend must skip all contract source files and hand-code the few definitions it needs (`JArray` types, `Long.compare`). This blocks `@Contract` support for Strata entirely — including user-defined contracts like `ArraysContract` for `Arrays.fill`.

The goal: add type parameter support to Laurel so that the Strata backend can compile generic contracts (and eventually generic user code) through the existing proven Laurel→Core→SMT pipeline.

---

## Decision 1: How should type parameters be represented in Laurel?

### Context

Laurel needs a way to say "this procedure/type has type parameters." The representation must:
- Carry type parameter information faithfully from the frontend to Core
- Leave room for future bounded type parameters (Java `<T extends Comparable>`, TypeScript structural bounds, etc.)
- Not bake in language-specific semantics (Laurel is language-agnostic)

### Option A: Bare identifier list

`typeArgs : List Identifier` — the same representation Core's `Procedure.Header` and `DatatypeDefinition` already use. Simple, minimal.

- Pro: Matches Core exactly. No translation needed for the type parameter list itself. Already proven to work for `DatatypeDefinition.typeArgs` in the Laurel→Core translator.
- Con: No place to attach bounds or constraints later. Adding bounds would require changing the type from `List Identifier` to something richer, touching every use site.

### Option B: TypeParameter structure

```
structure TypeParameter where
  name : Identifier
  -- Future: bound, constraints, metadata
```

A structure with just a name for now, but extensible.

- Pro: Adding bounds later is a field addition, not a type change. Call sites that only need the name use `tp.name`. The structure documents intent — "this is a type parameter, not just a string."
- Con: Slightly more ceremony than a bare identifier. The Laurel→Core translator must map `TypeParameter` to Core's `TyIdentifier` (trivial: `tp.name.text`).

### Option C: TypeParameter with bound slot

```
structure TypeParameter where
  name : Identifier
  bound : Option HighType
```

Include the bound slot now, even though it's always `None`.

- Pro: The slot exists from day one. No future structure change needed for simple type bounds.
- Con: Premature. We discussed that bounds might not be a type — they could be a predicate, a set of declarations, a nominal reference, or something we haven't designed yet. Committing to `Option HighType` now could be wrong. An `Option HighType` bound implies structural/subtype bounds, which doesn't capture nominal bounds (Java's `extends Comparable`) or predicate bounds cleanly.

### Decision: Option B

A `TypeParameter` structure with just `name` for now. This is extensible without being premature. When we design bounded type parameters, we add fields to this structure — whether that's a type bound, a predicate, a nominal reference, or a list of required declarations. We don't need to decide the shape of bounds today.

The key principle from the cross-type-resolution design: "Laurel carries the frontend's answer through faithfully." For unbounded type parameters, the answer is just the name. For bounded type parameters (future), the answer will be richer, and the structure has room for it.

---

## Decision 2: Where do type parameters go in Laurel's AST?

### Context

Java has type parameters on classes (`class Optional<T>`), methods (`static <E> Set<E> of(E e1)`), and constructors. Laurel needs to carry these through.

### Option A: Type parameters on Procedure only

Add `typeArgs` to `Procedure`. For class-level type parameters, the frontend hoists them onto each method.

- Pro: Minimal change — only one structure modified. Matches Core, where procedures have `typeArgs` but there's no class-level concept.
- Con: Loses the information that the type parameter belongs to the class, not the method. If two methods on `Optional<T>` both use `T`, the frontend must independently declare `T` on each. Inconsistent with how Java developers think about generics.

### Option B: Type parameters on both Procedure and CompositeType

Add `typeArgs` to both `Procedure` and `CompositeType`. Class-level type parameters go on the composite. Method-level type parameters go on the procedure.

- Pro: Preserves the source-level structure. The frontend can express "Optional has a type parameter T" and "this method has an additional type parameter E." The Laurel→Core translator can merge them (composite type params + method type params → Core procedure type params).
- Con: Two places to manage type parameters. The translator must handle the merging. More complex than Option A.

### Option C: Type parameters on Procedure only, with a convention for class-level params

Same as Option A, but with a naming convention: class-level type parameters are prefixed with the class name (e.g., `Optional$T`). This preserves the origin information without changing CompositeType.

- Pro: Single structure change. Origin information preserved via convention.
- Con: Conventions are fragile. Parsing the prefix to recover the class name is error-prone.

### Decision: Option A

Type parameters on `Procedure` only. The frontend hoists class-level type parameters onto each method. This matches Core's model exactly — Core has `Procedure.Header.typeArgs` and nothing else. The Laurel→Core translator doesn't need to merge anything.

The information that "T belongs to Optional, not to get()" is a Java concept. Laurel doesn't need it. What Laurel needs is: "this procedure has a type parameter T." The frontend resolves the scoping (which is language-specific) and tells Laurel the answer.

This follows the dispatch precedent: the frontend resolves, Laurel carries the answer. Java's class-level vs method-level distinction is like Java's static vs dynamic dispatch — a language concern that the frontend handles.

For CompositeType, type parameters are deferred. The immediate need (compiling contracts) doesn't require generic composite types in Laurel — the contracts define procedures with type parameters, not composite types with type parameters. If we later need generic composites (e.g., for verifying `class Optional<T> { T value; }`), we add `typeArgs` to `CompositeType` at that point.

---

## Decision 3: How do type variables resolve in the Laurel→Core translator?

### Context

When a procedure has `typeArgs = ["T"]` and a parameter has type `UserDefined "T"`, the translator needs to recognize that `T` is a type variable (not a composite type) and emit `LMonoTy.ftvar "T"` instead of `LMonoTy.tcons "Composite" []`.

### Option A: Name-based resolution (match against typeArgs list)

The translator checks if a `UserDefined` name matches any type parameter in scope. If yes, emit `ftvar`. If no, follow the existing path (composite, datatype, etc.).

This is exactly what `translateDatatypeDefinition` already does:
```lean
let typeArgNames := dt.typeArgs.map (fun id => id.text)
match ty.val with
| .UserDefined name =>
  if typeArgNames.contains name.text then pure (.ftvar name.text)
  else translateType ty
```

- Pro: Already implemented and working for datatypes. Proven pattern. No new resolution infrastructure needed.
- Con: Name-based matching is fragile if type parameter names shadow type names. E.g., if someone names a type parameter `int`, it would be treated as a type variable instead of the integer type. In practice this doesn't happen — javac would catch it.

### Option B: Distinct HighType variant for type variables

Add `HighType.TypeVar (name : Identifier)` alongside `UserDefined`. The frontend emits `TypeVar` for type parameters and `UserDefined` for concrete types. No ambiguity.

- Pro: No name-based matching needed. The translator knows unambiguously whether something is a type variable.
- Con: Requires a new HighType variant, which touches the grammar, the Ion format, the Java AST classes, every HighType match in every Laurel pass (resolution, heap parameterization, grouping, etc.), and the translator. Significant change surface.

### Option C: Resolution pass marks type variables

The existing Laurel resolution pass already resolves identifiers. Extend it to resolve type variables — when it sees `UserDefined "T"` in a procedure with `typeArgs = ["T"]`, it marks it (e.g., by setting a unique ID that the translator can check).

- Pro: Uses existing infrastructure. Resolution already handles name scoping.
- Con: The resolution pass currently operates on expressions, not types. Extending it to types is new work. The translator would need to check the resolution result, adding coupling between passes.

### Decision: Option A

Name-based resolution, matching the proven `translateDatatypeDefinition` pattern. The translator maintains a set of in-scope type parameter names and checks `UserDefined` names against it. This is simple, already working for datatypes, and sufficient.

The shadowing concern is theoretical — Java doesn't allow type parameters named `int` or `boolean`, and the Laurel type names (`int32`, `int64`, `bool`) don't collide with typical type parameter names (`T`, `K`, `V`, `E`).

If shadowing becomes a real problem, we can move to Option B at that point. The migration is mechanical: replace `UserDefined` with `TypeVar` where the name matches a type parameter.

---

## Decision 4: How does `HighType.Applied` translate to Core?

### Context

`HighType.Applied` represents a generic type application: `Applied(UserDefined("Optional"), [TInt])` means `Optional<int>`. The Laurel→Core translator currently rejects `Applied` with "cannot translate type to Core: not supported yet."

Core represents parameterized types as `LMonoTy.tcons name [args]`. For example, `Optional<int>` would be `tcons "Optional" [tcons "int32" []]`.

### Option A: Translate Applied to tcons with translated arguments

`Applied(base, args)` → `tcons(translateBase(base), args.map(translateType))`. The base must be a `UserDefined` name. The arguments are recursively translated.

- Pro: Direct mapping. Uses existing `tcons` infrastructure. The SMT encoder already handles `tcons` with arguments.
- Con: Requires that the base type is a named type (not a primitive or another Applied). In practice this is always true for Java generics.

### Option B: Erase Applied to its base type

`Applied(base, args)` → `translateType(base)`, ignoring the type arguments. This is type erasure — `Optional<int>` becomes just `Optional`.

- Pro: Simplest possible change. No new Core types needed.
- Con: Loses type information. `Optional<int>` and `Optional<String>` become the same type. The solver can't distinguish them. This creates potential unsoundness edges — a value of type `Optional<int>` could be used where `Optional<String>` is expected, and the solver wouldn't catch it.

### Decision: Option A

Translate `Applied` faithfully to `tcons` with arguments. This preserves type information through to the solver. The SMT encoder already handles parameterized `tcons` — it emits them as parameterized sorts. Type unification at call sites (`unifyTypes`) already handles matching `ftvar` against concrete types.

This follows the architectural principle: Laurel carries type information faithfully. Erasure (Option B) is the kind of information loss the architecture is designed to prevent.

---

## Decision 5: What is the proof and test strategy?

### Context

The Laurel→Core translator has partial proofs (translator properties, eq lemmas). Adding type parameters changes the translator. We need to know the translation is correct.

### Tier 1: Core-level tests (immediate)

Core already has passing tests for polymorphic functions (`choose<a>` with `typeArgs := ["a"]`) and polymorphic type aliases (`FooAlias<a>`). These prove the Core infrastructure works. We add tests that exercise the specific patterns the contracts need:

- **Polymorphic procedure with opaque body**: A procedure `get<T>(x: T): T` with no body (opaque). Verifies that the type parameter flows through to the SMT encoding and that callers can instantiate it with concrete types.
- **Polymorphic procedure with postcondition**: A procedure `identity<T>(x: T): T ensures result == x`. Verifies that postconditions can reference type-parameterized values.
- **Type instantiation at call sites**: A caller that invokes `identity<int>(42)` and asserts the result is 42. Verifies that `unifyTypes` correctly instantiates `T = int`.
- **Multiple type parameters**: A procedure `pair<K, V>(k: K, v: V)` to verify multiple type parameters work.

### Tier 2: Laurel-level tests (with implementation)

End-to-end tests that go through the full Laurel→Core→SMT pipeline:

- **Laurel program with a generic procedure**: Write a Laurel program (programmatically, since the grammar doesn't support type parameters) with a procedure that has `typeArgs`. Verify it translates to Core and verifies correctly.
- **Laurel program with Applied types**: A procedure that takes `Sequence<int>` (using `Applied`) and returns `int`. Verify the type flows through.
- **Contract-like pattern**: An opaque procedure with type parameters and postconditions, called by a concrete procedure. This is the pattern the builtin contracts use.

### Tier 3: Java integration tests (with Java→Laurel changes)

JVerify test cases that compile Java generics through the Strata backend:

- **Generic contract compilation**: Enable `useBuiltinContracts = true` on a Strata test that calls a method from a `@Contract` class (e.g., `Long.compare`, which already has a contract). Verify it compiles and verifies.
- **User-defined generic contract**: Write a simple `@Contract` with a type parameter and verify it works through Strata.
- **The Arrays.fill contract**: The motivating use case. Verify that `Arrays.fill(byte[], byte)` works through the Strata backend with the existing `ArraysContract`.

### Tier 4: Translator proofs (incremental)

The existing translator proof structure (`TranslatorEqLemmas.lean`, `TranslatorProperties.lean`) covers procedure translation. When we add `typeArgs` to Laurel's `Procedure`, the proofs need updating:

- **translateProcedure preserves typeArgs**: The Core procedure's `header.typeArgs` equals the Laurel procedure's `typeArgs` (mapped through `TypeParameter.name`).
- **translateType handles ftvar**: When a `UserDefined` name matches a type parameter, the translator emits `ftvar`, not `tcons "Composite" []`.

These are extensions of existing proofs, not new proof structures. The `translateDatatypeDefinition` path already proves the `ftvar` mapping for datatypes — the procedure path follows the same pattern.

---

## Decision 6: How do we handle bounded type parameters (deferred)?

### Context

Java has `<T extends Comparable<T>>`. TypeScript has `<T extends { name: string }>`. Rust has `<T: Clone + Send>`. Dafny has `(==)` and `(0)` characteristics. These are all constraints on what types can fill a type parameter.

### Decision: Deferred, with design space documented

Bounded type parameters are not needed for the immediate goal (compiling builtin contracts — all 19 generic contract files use unbounded type parameters). We defer the implementation but document the design space so we don't paint ourselves into a corner.

The `TypeParameter` structure (Decision 1) is extensible. When we need bounds, we add fields. The design space includes:

- **Nominal bounds** (`T extends Comparable`): T must be a subtype of a named type. Java's model. The bound is a type reference.
- **Structural bounds** (`T extends { name: string }`): T must have certain members. TypeScript's model. The bound is a shape description.
- **Predicate bounds** (`P(T) = ...`): T must satisfy an arbitrary predicate. Most general. But requires a meta-level predicate language that can talk about types, which Core doesn't have today (Core's expression language operates on values, not types).
- **Declaration bounds**: The bound is expressed as a set of procedure/field declarations that must exist for T. The frontend emits these declarations. This avoids the meta-level problem but conflates nominal and structural typing.

Each approach has trade-offs around expressiveness, soundness, and solver complexity. The key constraint: bounds must be **checked** at instantiation sites, not **assumed**. This distinguishes them from axioms — the system verifies the bound holds for the concrete type, rather than trusting the frontend's claim.

We chose `TypeParameter` as a structure (not a bare identifier) specifically to leave room for this future work. Adding a `bound` field — whatever its type turns out to be — is a field addition, not a type change.

---

## Summary of changes

### Laurel AST (`Laurel.lean`)
- Add `structure TypeParameter` with `name : Identifier`
- Add `typeArgs : List TypeParameter` to `Procedure`

### Laurel grammar (`LaurelGrammar.st`)
- No change needed for now (grammar doesn't need to parse type parameters — Java emits them programmatically via Ion, same as `Result<T>`)

### Ion format / Java AST classes
- Add `typeArgs` field to `Procedure_` and `Function` Java records
- Update `ConcreteToAbstractTreeTranslator.parseProcedure` to read `typeArgs` from Ion (with backward compatibility for existing 7-9 arg format)

### Laurel→Core translator (`LaurelToCoreTranslator.lean`)
- `translateType`: handle `UserDefined` names that match in-scope type parameters → emit `ftvar`
- `translateType`: handle `HighType.Applied` → emit `tcons` with translated arguments
- `translateProcedure`: propagate `typeArgs` to Core `Procedure.Header.typeArgs`

### Java→Laurel compiler (`JavaToLaurelCompiler.java`)
- `translateType`: handle `TypeTag.TYPEVAR` → emit `CompositeType` with the type variable name (which the Laurel translator will resolve to `ftvar`)
- Propagate type parameters from Java classes/methods to Laurel procedures
- Stop skipping contract source files (the original motivation)
- Remove hardcoded `getPredefinedTypes()`/`getPredefinedFunctions()` once contracts compile

### Translator proofs
- Update `TranslatorEqLemmas` and `TranslatorProperties` for the new `typeArgs` field on Procedure
- Add lemma: type parameter names in Laurel procedure map to `ftvar` names in Core procedure