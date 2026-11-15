# Homework: answers

Name(s):

## OpenJML

### 1. Absolute

Q: What does OpenJML complain about before you write a contract, and for which input?

OpenJML reports an `ArithmeticOperationRange` failure in `abs` at `return -n`
("int negation"). The input that triggers it is `n = Integer.MIN_VALUE`
(−2147483648): its negation is 2147483648, which does not fit in a 32-bit
`int`, so the Java operation overflows. This check is independent of the
contract: OpenJML also checks arithmetic ranges in code with no specification.

Q: Which `requires` did you need, and why? Could you avoid it by changing the `ensures`?

I used

```java
//@ requires n != Integer.MIN_VALUE;
//@ ensures \result >= 0 && (\result == n || \result == -n);
```

The `requires` is needed because the stated postcondition is impossible for
`n = Integer.MIN_VALUE`: the mathematical absolute value 2147483648 cannot be
returned as an `int`, and the code's `-n` overflows. Without the `requires`,
OpenJML cannot discharge the range check on `-n`.

Changing the `ensures` does not avoid it. One can weaken the postcondition,
e.g. `ensures n != Integer.MIN_VALUE ==> (\result >= 0 && ...)`, and the
postcondition failure disappears, but OpenJML still reports the
`ArithmeticOperationRange` failure at `return -n`, because that is a property
of the code, not of the contract. To verify the method as written, the input
must be constrained (or the code changed).

### 2. SumX

Q: Which proof obligations fail? Is the program wrong?

With the given invariant `0 <= i && i <= x`, two obligations fail:

- `Postcondition` at `return s`: the invariant says nothing about `s`, so
  `s == x * (x + 1) / 2` cannot be established.
- `ArithmeticOperationRange` at `s = s + i`: without a relation between `s`
  and `i`, `s` is unbounded, so the addition may overflow.

The program is not wrong. For `0 <= x <= 1000` the largest sum is
1000·1001/2 = 500500 and every intermediate sum is far below
`Integer.MAX_VALUE`; only the invariant is too weak. Strengthening it to
`2 * s == i * (i + 1)` (with `0 <= i && i <= x` and `decreases x - i`) makes
both obligations verify.

Q: Largest N for which `x <= N` verifies? What happens with N + 1, and why?

N = 65535. The final sum is 65535·65536/2 = 2147450880, which is at most
`Integer.MAX_VALUE` (2147483647), so every intermediate `s` fits in an `int`.

With `x <= 65536`, OpenJML reports `ArithmeticOperationRange` at `s = s + i`
("overflow in int sum") and a `LoopInvariant` failure for
`2 * s == i * (i + 1)`: at the last iteration the true sum is
65536·65537/2 = 2147516416 > `Integer.MAX_VALUE`, so the 32-bit addition wraps
and the invariant becomes false. JML specifications are evaluated with
mathematical integers, but the code's arithmetic is 32-bit `int`; verification
must show the two agree.

### 3. Max

Q: Is the remaining failure caused by your invariants or by the code? (Your hypothesis.)

I wrote

```java
//@ loop_invariant 1 <= i && i <= a.length;
//@ loop_invariant (\forall int j; 0 <= j && j < i; m >= a[j]);
//@ loop_invariant (\exists int j; 0 <= j && j < i; m == a[j]);
//@ decreases a.length - i;
```

and OpenJML then reports only one failure: the `Postcondition`
`(\forall int j; 0 <= j && j < a.length; \result >= a[j])` at `return m`.
(The `\exists` postcondition still holds, because `m` is always an examined
element, so it is some `a[j]` with `j < a.length`.)

The remaining failure is caused by the code, not by the invariants: the loop
`for (int i = 1; i < a.length - 1; i++)` stops at index `a.length - 2`, so
`a[a.length - 1]` is never examined. If the last element is the unique maximum,
`m` is smaller than it. My hypothesis: an array whose maximum appears only in
the last position, e.g. `{3, 32770}`, makes `max` return a wrong result.

### 4. BinarySearch

Q: What does OpenJML report, in which method, and for which concrete call? How large must the array be?

OpenJML reports, in `midpoint`, an `ArithmeticOperationRange` failure at
`(lo + hi) / 2` ("overflow in int sum") and consequently a `Postcondition`
failure of `ensures lo <= \result && \result <= hi`.

Concrete call: `midpoint(1073741824, 1073741824)` (both 2^30). The sum
`lo + hi = 2^31` overflows to −2147483648; division by 2 gives −1073741824,
which is smaller than `lo`, violating the postcondition.

Through `search`, the array must have at least 2^30 + 1 = 1073741825 elements
(about 1.07 billion `int`s, roughly 4 GB), so that `hi = a.length - 1 = 2^30`
and the search can reach `lo = hi = 2^30`. `search` itself verifies because it
uses only the contract of `midpoint`, which is assumed; the bug is inside
`midpoint`'s own verification.

Q: What happens without `/*@ pure @*/` on `midpoint`, and why?

`search` no longer verifies. OpenJML reports, at the call `midpoint(lo, hi)`:

- an `Assignable: \everything` failure, and
- `LoopInvariant` failures for both invariants about the array `a`.

Without `pure`, the call is treated as potentially modifying any location
(the default `assignable` clause is `\everything`), so the verifier may not
assume that `a`, `lo` and `hi` are unchanged after the call; the loop
invariants may be broken by it. `pure` states that the method has no side
effects (and is deterministic), which is what allows OpenJML to use only its
contract and assume the heap is unchanged.

## JBMC

### 5. Max, again

Q: What input did JBMC find, and what goes wrong? Was your hypothesis of exercise 3 right?

The counterexample is `a = {3, 32770}` (length 2). `Max.max` sets `m = 3`; the
loop condition `i < a.length - 1` is `1 < 1`, false, so the loop body never
runs and the method returns 3. The assertion `r >= a[1]` fails because
`3 >= 32770` is false. The last element is never examined. This confirms the
hypothesis of exercise 3. (The `found` assertion still holds, since
`r == a[0]`, which is why the independently written `\exists` postcondition is
not enough to catch this bug.)

Q: Smallest `--unwind` and `--max-nondet-array-length` that find it? Relation to the small scope hypothesis?

The smallest values are `--unwind 2` and `--max-nondet-array-length 2`
(with `--no-unwinding-assertions`). With `--unwind 1` the harness's checking
loop is cut off before it reaches the assertion for index 1; with arrays of
length at most 1 there is no second element to ignore. With `--unwind 2` and
length 2, the counterexample is found.

This is the small scope hypothesis in action: the bug appears already on the
smallest possible input (an array of length 2), so small bounds are enough to
find it. Bounds are needed mainly to make sure the search covers inputs large
enough for the bug, not to explore large sizes for their own sake.

Q: Why does `--unwind 5` with unwinding assertions fail on the fixed version? Smallest K with `--max-nondet-array-length 4`, and why not one less? What has been proved?

After fixing `max` (`i < a.length`), `./bmc MaxCheck.check --unwind 5` still
fails, but not in `Max.max`: the failed property is the unwinding assertion of
the harness's own loop
`for (int j = 0; j < a.length; j++)`. With arrays of length up to 5, JBMC
unrolls the loop 5 times (j = 0 … 4), but it still must evaluate the guard
once more (j = 5) to prove that the loop has ended; the unwinding assertion at
line 14 fails for the array of length 5.

With `--max-nondet-array-length 4`, the smallest `--unwind` that gives
VERIFICATION SUCCESSFUL is **5**. Four unrollings execute the body for
j = 0 … 3, and the fifth unrolling evaluates the final guard `j < a.length`
(j = 4) and discharges the unwinding assertion. With `--unwind 4` the final
guard cannot be evaluated, so JBMC reports the unwinding assertion as failed;
it cannot prove that the loop terminates within the bound.

What has been proved: for every `int` array `a` with
`1 <= a.length <= 4` (all element values, all lengths in that range),
`Max.max` returns a value that is `>=` every element and equal to some
element, with no index or null errors. It is a proof only within
`--max-nondet-array-length 4`; arrays of length 5 or more are not covered.

### 6. SumX

Q: Which values of `x` were checked with `--unwind 10 --no-unwinding-assertions`? Why does it fail with unwinding assertions? Which K is a proof? Sizes and times for K = 10, 100 and that K.

With `--unwind 10 --no-unwinding-assertions`, executions that need more than
10 loop iterations are discarded: after 10 unrollings JBMC assumes the loop
guard is false. So only `x = 0 … 10` are really checked; for `x >= 11` the
loop is cut off before the postcondition is reached, and those inputs are
ignored. The reported success therefore covers only small `x`.

Dropping `--no-unwinding-assertions` turns the cut-off into an assertion that
the loop has ended after 10 unrollings. For `x >= 11` this is false, so JBMC
reports the unwinding assertion at `s = s + i` as failed (the counterexample
has, for example, `x = 161`).

K = **1001** turns the result into a proof: `x <= 1000`, the body runs at most
1000 times, and unrolling 1001 times also evaluates the final guard. Measured
with unwinding assertions:

| K | SAT formula | time | result |
| --- | --- | --- | --- |
| 10 | 4638 variables, 13644 clauses | 0.00 s | fails (unwinding assertion) |
| 100 | 9587 variables, 30260 clauses | 0.02 s | fails (unwinding assertion) |
| 1000 | 66800 variables, 664961 clauses | 1.52 s | fails (needs the final guard evaluation) |
| 1001 | 66870 variables, 666136 clauses | 1.50 s | VERIFICATION SUCCESSFUL |

For comparison, with `--no-unwinding-assertions`: K = 10 gives 4635
variables / 13635 clauses and 0.00 s; K = 100 gives 9584 variables / 30251
clauses and 0.02 s. The formula grows roughly linearly with K, and the time
grows with it.

Q: What did OpenJML need from you, and what did JBMC need?

OpenJML needed a loop invariant strong enough to relate `s` and `i`
(`2 * s == i * (i + 1)`, together with `0 <= i && i <= x`) and the `decreases`
clause. With those, one proof covers every `x` with `0 <= x <= 1000`
symbolically; there is no iteration bound.

JBMC needed a harness: assume the precondition, call `sum`, assert the
postcondition. It needed no loop invariant, but it needed a large enough
unwinding bound, `--unwind 1001`, and unwinding assertions to make the result
a proof. That proof is bound-dependent: it exhaustively encodes all `x <= 1000`
in one SAT formula.

### 7. BinarySearch

Q: Why does JBMC miss the bug with the `search` harness? Could a larger bound help?

The `search` harness restricts arrays with `--max-nondet-array-length 5`, so
every array JBMC can choose has at most 5 elements. The overflow needs `lo`
and `hi` near 2^30, hence an array of more than 2^30 elements; no such array
is in the search space, so `lo + hi` never overflows in any explored
execution and the harness reports success.

A larger unwind bound alone would not help in practice: binary search needs
only about 31 iterations for a billion-element array. One would also have to
raise `--max-nondet-array-length` to more than 1073741824, i.e. model arrays of
over a billion elements, which is far beyond SAT-based BMC. This is a
small-scope failure: the bug hides behind input sizes that BMC cannot reach.

Q: What did the `midpoint` harness find?

With the original `(lo + hi) / 2`, `./bmc BinarySearchCheck.midpoint --unwind 1`
fails the assertion `lo <= mid && mid <= hi` with, for example,

```text
lo = 229638144
hi = 2068840448
mid = -998244352
```

`lo + hi = 2296478592 > Integer.MAX_VALUE`, so the sum wraps to a negative
number and division gives a `mid` smaller than `lo`. (The simpler
`midpoint(1073741824, 1073741824)` is also a counterexample: `lo + hi = 2^31`
wraps to −2^31 and `mid = -1073741824`.) After restoring the fix
`lo + (hi - lo) / 2`, the harness verifies with `--unwind 1`.

## Comparison

### 8. Comparison

| program | OpenJML: result, what you wrote | JBMC: result, bound used |
| --- | --- | --- |
| SumX | Not verified with the given invariant (Postcondition + ArithmeticOperationRange); verifies after strengthening it to `2 * s == i * (i + 1)`; `requires 0 <= x && x <= 1000`, `decreases x - i` | With the harness: success with `--unwind 10 --no-unwinding-assertions` but only x = 0…10 checked; a proof with `--unwind 1001` (unwinding assertions), all x ≤ 1000 |
| Max | Postcondition `\forall` failure remains with the best invariants because the loop misses the last element; verifies after fixing the loop bound (`i < a.length`), with invariants `1 <= i && i <= a.length`, `\forall j < i: m >= a[j]`, `\exists j < i: m == a[j]` | Found the bug with `--unwind 3 --no-unwinding-assertions` (minimum: `--unwind 2`, `--max-nondet-array-length 2`, counterexample `{3, 32770}`); after the fix, success with `--unwind 5 --max-nondet-array-length 4` (unwinding assertions), a proof for arrays of length ≤ 4 |
| BinarySearch | Found the overflow in `midpoint` (`ArithmeticOperationRange`); needs an array of ≥ 2^30 + 1 elements to trigger through `search`; removed `pure` breaks `search`'s proof; fixed with `lo + (hi - lo) / 2`; verifies | `search` harness with `--unwind 6 --max-nondet-array-length 5` misses the bug (arrays too short); the `midpoint` harness with `--unwind 1` finds it (counterexample with `lo`, `hi` around 2^30); after the fix, both harnesses report success |

Q: When would you use each tool?

Use **JBMC** when you want to find bugs early and cheaply: it needs only a
harness and a bound, gives concrete counterexamples, and is easy to automate.
It is good at off-by-one errors and for checking bounded sequences of
operations. But success only means "no bug within the bound and the chosen
input sizes", so it can miss bugs that need large arrays or many iterations.

Use **OpenJML** when you need a guarantee for all executions and all input
sizes: it requires contracts, loop invariants and `decreases` clauses, and is
more work and less automatic. It catches bugs that BMC cannot reach (such as
the `midpoint` overflow, which needs a billion-element array) and verifies
unbounded loops, but the specification work is substantial and an "error"
may mean a too-weak invariant rather than a real bug. In practice: JBMC
first for debugging, OpenJML for the final proof of the important properties.
