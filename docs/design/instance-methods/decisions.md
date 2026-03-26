# Instance Method Support: Decisions

**Date:** 2026-03-26

## Decision 1: Keep InstanceCall through the Laurel pipeline

**Options:**
- A. Convert InstanceCall → StaticCall early (in heap parameterization)
- B. Keep InstanceCall through all passes, flatten in translator only

**Choice:** B

**Rationale:** Keeps the semantic distinction visible through the pipeline.
The translator is the single place where InstanceCall becomes a Core `call`.
This makes the translation more provable — the name mapping is localized
to one function in one place. If we convert early, the name construction
happens in one pass and the Core emission happens in another, making the
proof that they agree harder because it spans two passes.

## Decision 2: Prove a consistency property for name mapping

**Options:**
- A. Prove at Core level (type-checking catches mismatches)
- B. Prove at Laurel level (theorem about translator correctness)
- C. Prove via SemanticModel (name consistency between call and definition)

**Choice:** C (with A as baseline, B as future goal)

**Rationale:** Option A is free but insufficient — it can't distinguish
"correct translation" from "accidentally correct." Option B is the right
long-term answer but is research-level work we haven't attempted for any
part of the translator. Option C is achievable now: prove that the name
construction function used at the call site is the same function used at
the definition site. Combined with Core type-checking (A), this gives
reasonable confidence.

If empirical testing reveals bugs, that's the signal to invest in B.

## Decision 3: Instance procedure naming convention

The Core procedure name for an instance procedure is qualified:
`typeName ++ ".." ++ procName`. This follows the existing convention
used for datatype destructors (`Color..isRed`, `Heap..data!`).

A single pure function `instanceProcCoreName` constructs this name.
Both the definition translator and the call translator use it.
The consistency proof is that they call the same function.
