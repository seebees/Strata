/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Core.Verifier

/-!
# Polymorphic Contract Tests

Tests for the patterns needed by generic contracts (e.g., `Optional<T>.get()`,
`Set<E>.of(E e1)`). These exercise polymorphic opaque procedures with
postconditions, called at concrete types.
-/

---------------------------------------------------------------------
namespace Strata.PolymorphicOpaqueWithPostcondition
---------------------------------------------------------------------

/-- An opaque polymorphic procedure with a postcondition that the caller uses.
    Models the pattern: `T get<T>()` with `ensures result == stored_value`. -/
def opaquePostPgm : Program :=
#strata
program Core;

procedure identity<a>(x : a) returns (r : a)
spec {
  free ensures r == x;
};

procedure TestInt() returns () spec { ensures true; }
{
  var r : int;
  call r := identity(42);
  assert [result_is_42]: r == 42;
};

procedure TestBool() returns () spec { ensures true; }
{
  var r : bool;
  call r := identity(true);
  assert [result_is_true]: r == true;
};
#end

/--
info: [Strata.Core] Type checking succeeded.


VCs:
Label: identity_ensures_0
Property: assert
Obligation:
true

Label: result_is_42
Property: assert
Assumptions:
callElimAssume_identity_ensures_0_2: $__r3 == 42
Obligation:
$__r3 == 42

Label: TestInt_ensures_0
Property: assert
Assumptions:
callElimAssume_identity_ensures_0_2: $__r3 == 42
Obligation:
true

Label: result_is_true
Property: assert
Assumptions:
callElimAssume_identity_ensures_0_5: $__r5 == true
Obligation:
$__r5 == true

Label: TestBool_ensures_0
Property: assert
Assumptions:
callElimAssume_identity_ensures_0_5: $__r5 == true
Obligation:
true

---
info:
Obligation: identity_ensures_0
Property: assert
Result: ✅ pass

Obligation: result_is_42
Property: assert
Result: ✅ pass

Obligation: TestInt_ensures_0
Property: assert
Result: ✅ pass

Obligation: result_is_true
Property: assert
Result: ✅ pass

Obligation: TestBool_ensures_0
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval verify opaquePostPgm

end Strata.PolymorphicOpaqueWithPostcondition

---------------------------------------------------------------------
namespace Strata.PolymorphicMultipleTypeParams
---------------------------------------------------------------------

/-- Multiple type parameters on a single procedure.
    Models patterns like `Map<K,V>.put(K key, V value)`. -/
def multiParamPgm : Program :=
#strata
program Core;

procedure swap<A, B>(a : A, b : B) returns (ra : B, rb : A)
spec {
  free ensures ra == b;
  free ensures rb == a;
};

procedure TestSwap() returns () spec { ensures true; }
{
  var ri : int;
  var rb : bool;
  call rb, ri := swap(1, true);
  assert [bool_is_true]: rb == true;
  assert [int_is_1]: ri == 1;
};
#end

/--
info: [Strata.Core] Type checking succeeded.


VCs:
Label: swap_ensures_0
Property: assert
Obligation:
true

Label: swap_ensures_1
Property: assert
Obligation:
true

Label: bool_is_true
Property: assert
Assumptions:
callElimAssume_swap_ensures_0_4: $__rb6 == true
callElimAssume_swap_ensures_1_5: $__ri7 == 1
Obligation:
$__rb6 == true

Label: int_is_1
Property: assert
Assumptions:
callElimAssume_swap_ensures_0_4: $__rb6 == true
callElimAssume_swap_ensures_1_5: $__ri7 == 1
Obligation:
$__ri7 == 1

Label: TestSwap_ensures_0
Property: assert
Assumptions:
callElimAssume_swap_ensures_0_4: $__rb6 == true
callElimAssume_swap_ensures_1_5: $__ri7 == 1
Obligation:
true

---
info:
Obligation: swap_ensures_0
Property: assert
Result: ✅ pass

Obligation: swap_ensures_1
Property: assert
Result: ✅ pass

Obligation: bool_is_true
Property: assert
Result: ✅ pass

Obligation: int_is_1
Property: assert
Result: ✅ pass

Obligation: TestSwap_ensures_0
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval verify multiParamPgm

end Strata.PolymorphicMultipleTypeParams

---------------------------------------------------------------------
namespace Strata.PolymorphicContractPattern
---------------------------------------------------------------------

/-- The full contract pattern: an opaque polymorphic procedure with a
    postcondition involving a quantifier over the type parameter.
    Models `Arrays.fill(T[] a, T val) ensures forall i. a[i] == val`. -/
def contractPatternPgm : Program :=
#strata
program Core;

function seqlen<T>(s : Sequence T) : int;
function seqget<T>(s : Sequence T, i : int) : T;
axiom [len_nonneg]: (forall s : Sequence int :: seqlen(s) >= 0);

procedure fill<T>(a : Sequence T, val : T) returns (result : Sequence T)
spec {
  free ensures (forall i : int ::
    (0 <= i && i < seqlen(result)) ==> (seqget(result, i) == val));
  free ensures seqlen(result) == seqlen(a);
};

procedure TestFill() returns () spec { ensures true; }
{
  var a : Sequence int;
  var result : Sequence int;
  call result := fill(a, 0);
  assert [all_zero]: (forall i : int ::
    (0 <= i && i < seqlen(result)) ==> (seqget(result, i) == 0));
  assert [same_length]: seqlen(result) == seqlen(a);
};
#end

/--
info: [Strata.Core] Type checking succeeded.


VCs:
Label: fill_ensures_0
Property: assert
Assumptions:
len_nonneg: forall __q0 : (Sequence int) :: seqlen(__q0) >= 0
Obligation:
true

Label: fill_ensures_1
Property: assert
Assumptions:
len_nonneg: forall __q0 : (Sequence int) :: seqlen(__q0) >= 0
Obligation:
true

Label: all_zero
Property: assert
Assumptions:
callElimAssume_fill_ensures_0_3: forall __q0 : int :: 0 <= __q0 && __q0 < seqlen($__result5) ==> seqget($__result5, __q0) == 0
callElimAssume_fill_ensures_1_4: seqlen($__result5) == seqlen($__a3)
len_nonneg: forall __q0 : (Sequence int) :: seqlen(__q0) >= 0
Obligation:
forall __q0 : int :: 0 <= __q0 && __q0 < seqlen($__result5) ==> seqget($__result5, __q0) == 0

Label: same_length
Property: assert
Assumptions:
callElimAssume_fill_ensures_0_3: forall __q0 : int :: 0 <= __q0 && __q0 < seqlen($__result5) ==> seqget($__result5, __q0) == 0
callElimAssume_fill_ensures_1_4: seqlen($__result5) == seqlen($__a3)
len_nonneg: forall __q0 : (Sequence int) :: seqlen(__q0) >= 0
Obligation:
seqlen($__result5) == seqlen($__a3)

Label: TestFill_ensures_0
Property: assert
Assumptions:
callElimAssume_fill_ensures_0_3: forall __q0 : int :: 0 <= __q0 && __q0 < seqlen($__result5) ==> seqget($__result5, __q0) == 0
callElimAssume_fill_ensures_1_4: seqlen($__result5) == seqlen($__a3)
len_nonneg: forall __q0 : (Sequence int) :: seqlen(__q0) >= 0
Obligation:
true

---
info:
Obligation: fill_ensures_0
Property: assert
Result: ✅ pass

Obligation: fill_ensures_1
Property: assert
Result: ✅ pass

Obligation: all_zero
Property: assert
Result: ✅ pass

Obligation: same_length
Property: assert
Result: ✅ pass

Obligation: TestFill_ensures_0
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval verify contractPatternPgm

end Strata.PolymorphicContractPattern
