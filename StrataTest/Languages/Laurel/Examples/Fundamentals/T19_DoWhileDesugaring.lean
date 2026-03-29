/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataTest.Util.TestDiagnostics
import StrataTest.Languages.Laurel.TestExamples

open StrataTest.Util

namespace Strata
namespace Laurel

/-!
# Do/While Loop Desugaring Proof

A `do { body } while (cond)` with `invariant(I)` can be desugared to:

```
body;                        // first execution establishes I
while (cond)
  invariant I
{ body };                    // maintains I
```

This is sound because:
1. Sequential composition: {Q} body {I} and {I} while(cond){body} {I ∧ ¬cond}
   gives {Q} body; while(cond){body} {I ∧ ¬cond}
2. The first body execution establishes I (unlike while, where the caller must)
3. The while loop maintains I through additional iterations

These tests prove the desugaring works by encoding it directly in Laurel
and verifying with Strata's proven While rule.
-/

-- Basic do/while: count from 0 to 10.
-- do { i = i + 1 } while (i < 10)
-- Invariant: 0 < i <= 10 (established by first execution: i goes 0→1)
def doWhileBasic := r"
procedure doWhileCountToTen() {
    var i: int := 0;
    // --- desugared do/while ---
    // first execution (establishes invariant)
    i := i + 1;
    // while loop (maintains invariant)
    while(i < 10)
      invariant i > 0
      invariant i <= 10
    {
        i := i + 1
    };
    // after loop: invariant AND NOT condition
    assert i == 10
};
"

-- Do/while that executes exactly once.
-- do { x = 42 } while (false)
-- Invariant: x == 42 (established by first execution, trivially maintained)
def doWhileOnce := r"
procedure doWhileExecutesOnce() {
    var x: int := 0;
    // --- desugared do/while ---
    x := 42;
    while(false)
      invariant x == 42
    {
        x := 42
    };
    assert x == 42
};
"

-- Do/while with precondition: the invariant depends on input.
-- Given n > 0:
-- do { i = i + 1 } while (i < n)
-- Invariant: 0 < i <= n
def doWhileWithPrecondition := r"
procedure doWhileWithBound(n: int)
  requires n > 0
  requires n <= 100
{
    var i: int := 0;
    // --- desugared do/while ---
    i := i + 1;
    while(i < n)
      invariant i > 0
      invariant i <= n
    {
        i := i + 1
    };
    assert i == n
};
"

-- Do/while where the invariant is NOT true before the first execution.
-- This is the key difference from while: the caller does NOT need to
-- establish the invariant. The first body execution does.
-- Before loop: found = false. Invariant: found = true.
-- First execution sets found = true, establishing the invariant.
def doWhileEstablishesInvariant := r"
procedure doWhileFirstPassEstablishes() {
    var found: bool := false;
    // --- desugared do/while ---
    // Before this point: found = false (invariant does NOT hold)
    found := true;
    // After first execution: found = true (invariant holds)
    while(false)
      invariant found
    {
        found := true
    };
    assert found
};
"

-- Do/while with accumulator: sum digits.
-- do { sum = sum + i; i = i + 1 } while (i <= 3)
-- Invariant: sum == i*(i-1)/2 and 1 <= i <= 4
def doWhileAccumulator := r"
procedure doWhileSum() {
    var sum: int := 0;
    var i: int := 0;
    // --- desugared do/while ---
    sum := sum + i;
    i := i + 1;
    while(i <= 3)
      invariant i >= 1
      invariant i <= 4
      invariant sum == (i * (i - 1)) / 2
    {
        sum := sum + i;
        i := i + 1
    };
    // i == 4, sum == 0+1+2+3 == 6
    assert sum == 6
};
"

#guard_msgs(drop info, error) in
#eval testInputWithOffset "DoWhileBasic" doWhileBasic 36 processLaurelFile

#guard_msgs(drop info, error) in
#eval testInputWithOffset "DoWhileOnce" doWhileOnce 49 processLaurelFile

#guard_msgs(drop info, error) in
#eval testInputWithOffset "DoWhileWithPrecondition" doWhileWithPrecondition 60 processLaurelFile

#guard_msgs(drop info, error) in
#eval testInputWithOffset "DoWhileEstablishesInvariant" doWhileEstablishesInvariant 75 processLaurelFile

#guard_msgs(drop info, error) in
#eval testInputWithOffset "DoWhileAccumulator" doWhileAccumulator 89 processLaurelFile

end Laurel
end Strata
