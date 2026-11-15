# Homework plus: answers

Name(s):

### 1. Invariants from an LLM

| method | LLM | rounds | mistakes | final invariants by |
| --- | --- | --- | --- | --- |
| count | Claude | 2 | round 1 had only the `\num_of` invariant; OpenJML timed out, round 2 added `0 <= c && c <= i` as a supporting bound | LLM (accepted by OpenJML) |
| reverse | Claude | 2 | round 1 missed the relation `i + j == a.length - 1`, the bound `i <= j + 1`, and the "middle unchanged" invariant, so the prefix/suffix invariants were not inductive and the postcondition failed | LLM (accepted by OpenJML) |
| isqrt | Claude | 1 | none | LLM (accepted by OpenJML) |
| dutchFlag | Claude | 2 | round 1 missed the invariant that all elements stay in 0..2, so the suffix-of-2s invariant could not be preserved in the `a[mid]` branch | LLM (accepted by OpenJML) |

The final invariants I used were:

```java
// count
//@ loop_invariant 0 <= i && i <= a.length;
//@ loop_invariant 0 <= c && c <= i;
//@ loop_invariant c == (\num_of int k; 0 <= k && k < i; a[k] == x);
//@ decreases a.length - i;

// reverse
//@ loop_invariant 0 <= i && i <= a.length && -1 <= j && j < a.length;
//@ loop_invariant i <= j + 1;
//@ loop_invariant i + j == a.length - 1;
//@ loop_invariant (\forall int k; 0 <= k && k < i; a[k] == \old(a[a.length - 1 - k]));
//@ loop_invariant (\forall int k; j < k && k < a.length; a[k] == \old(a[a.length - 1 - k]));
//@ loop_invariant (\forall int k; i <= k && k <= j; a[k] == \old(a[k]));
//@ decreases j - i;

// isqrt
//@ loop_invariant 0 <= r && r * r <= n;
//@ decreases n - r;

// dutchFlag
//@ loop_invariant 0 <= lo && lo <= mid && mid <= hi && hi <= a.length;
//@ loop_invariant (\forall int k; 0 <= k && k < a.length; 0 <= a[k] && a[k] <= 2);
//@ loop_invariant (\forall int k; 0 <= k && k < lo; a[k] == 0);
//@ loop_invariant (\forall int k; lo <= k && k < mid; a[k] == 1);
//@ loop_invariant (\forall int k; hi <= k && k < a.length; a[k] == 2);
//@ decreases hi - mid;
```

Q: Why is it safe to use invariants written by an LLM here, even if the LLM is often wrong?

Because the LLM only proposes; OpenJML is the judge. For every loop it checks that
the invariant is true on entry, is preserved by every iteration (including the
loop condition and the update), and is strong enough to imply the postcondition
when the loop exits. A false invariant fails the first two checks, and a true but
too-weak invariant fails the third, as happened in the first rounds above. A
wrong proposal therefore costs an extra round, not soundness: nothing is
accepted unless the proof obligations are discharged. (This assumes, of course,
that the code and the method contracts — not just the invariants — are trusted.)

### 2. The Zune bug

Q: `--unwind 31 --no-unwinding-assertions` says SUCCESSFUL. Does that mean `yearOf` is correct for every day it checked?

No. With `--no-unwinding-assertions`, a loop that is still running after 31
unrollings is cut off and its continuation is assumed away. Executions that hit
the infinite loop are therefore discarded before the postcondition is reached:
they are not checked at all, and the "SUCCESSFUL" says nothing about them. For the
days whose loop does terminate within the bound, the run only shows that the
*weak* range property (the year is in `[1980, 2010)`) holds. So the result does
not establish correctness for all days, and in particular it hides exactly the
days on which the method never returns.

Q: What does JBMC report without `--no-unwinding-assertions`? Is K too small, or is something else wrong?

JBMC reports a failed unwinding assertion at the `while` loop: after 31
unrollings the loop may not have terminated. The counterexample has `days = 1827`,
which is December 31, 1984: the loop reaches the leap year 1984 with exactly 366
days left, the condition `days > 366` is false, and the loop body makes no
progress, so it spins forever. Increasing K does not help: with `--unwind 100`
JBMC still fails, with another leap-year December 31 (`days = 3288`, which is
December 31, 1988, the same pattern in the next leap year). K is not too small —
the loop is genuinely non-terminating on those days. (`days = 1827` is December
31, 1984.)

Q: What is wrong with the loop? Which date froze the Zune?

In a leap year, the loop only subtracts 366 when `days > 366`. When `days` is
exactly 366 — the last day of a leap year — neither branch makes progress:
`isLeapYear(year)` is true and `days > 366` is false, so `days -= 366` is
skipped and the loop repeats forever. The Zune froze on **December 31, 2008**,
the last day of a leap year (day 10593 since January 1, 1980). JBMC found the
smallest instance, December 31, 1984 (day 1827).

Fix: in the leap-year branch, when `days <= 366`, break out of the loop; only
subtract a leap year when `days > 366`. (Equivalently, loop while
`days > (isLeapYear(year) ? 366 : 365)` and subtract accordingly.) With this fix
December 31 of a leap year is correctly counted in that same year.

Q: With your fix, what is the smallest K that gives VERIFICATION SUCCESSFUL with unwinding assertions? What exactly has been proved?

In this JBMC build, `yearOfInRange` alone already succeeds with **K = 22**
(K = 21 still fails the unwinding assertion). The two harnesses together,
including `yearOfIsRight`, need **K = 30**: `yearOfIsRight` also runs
`daysBefore`, whose loop takes up to 29 iterations for the years up to 2009, and
K = 29 fails while K = 30 succeeds. K = 30 therefore covers both harnesses, which
is the bound used in the README's final check.

What has been proved with K = 30 and unwinding assertions: for every
`days` with `1 <= days <= 365 * 30`, `yearOf` terminates within the bound and
returns a year in `[1980, 2010)` (`yearOfInRange`), and `yearOfIsRight` proves
that the returned year is the *right* one: `daysBefore(year) < days` and
`days` is no later than the end of `year`. Unwinding assertions guarantee that no
execution was silently cut off, so this is a complete proof for that range of
days. It is not a proof for days beyond `365 * 30` (the contract's range).

Q: A colleague changes `days > 366` to `days >= 366`. Which harness notices, and why?

Only `yearOfIsRight` notices. For `days = 366` (December 31 of the first leap
year, 1980), the changed condition subtracts 366 and advances to 1981, so
`yearOf` returns 1981 instead of 1980. `yearOfInRange` accepts this because 1981
is still in `[1980, 2010)`, but `yearOfIsRight` checks the exact year and fails:
`daysBefore(1981) = 366`, so `before < days` is `366 < 366`, false. The weak
harness checks only that the result is *some* year in range; the strong one ties
the result to the day. (And the change does stop the infinite loop, so it is a
"fix" that trades a hang for a wrong answer.)

Q (★): Why does `./esc` say OK on the original? What changes with `decreases`?

Without a `decreases` clause, OpenJML proves *partial* correctness: if the
method returns, the postcondition holds; non-termination is allowed. The
original infinite loop is therefore not a counterexample to the contract, and
`./esc plus/Zune.java` says OK. Adding `//@ decreases days;` asks for *total*
correctness. On the original code, the stalling path leaves `days` at 366, so
OpenJML reports `LoopDecreases` at the `decreases` clause. With the fixed loop it
verifies: every iteration decreases `days`, so the method terminates as well.

### 3. Range

Q: Why does `size()` not verify? Give concrete values.

`size()` returns an `int`, but the number of ints in the interval can exceed
`Integer.MAX_VALUE`. The code computes `hi - lo + 1` in 32-bit `int` arithmetic,
so it overflows, while the `ensures` compares the result with the mathematical
value `(long) hi - lo + 1`. For example, with `lo = -1646305535` and
`hi = 1073741824` (the invariant `lo <= hi` holds), the true size is
2720047360, but the `int` expression wraps to -1574919936, which cannot equal
2720047360. Even simpler: `lo = 0`, `hi = 2147483647` gives a true size of
2^31, which no `int` can return. OpenJML reports `ArithmeticOperationRange` for
the subtraction and the addition, and the `Postcondition` failure.

Q: Compare JBMC's counterexample with your answer above.

JBMC's counterexample is `lo = -1646305535`, `hi = 1073741824`, exactly the
overflow situation described above: `Range.size()` returns -1574919936 while the
harness's contract assertion requires 2720047360. The concrete numbers differ
from the simplest `lo = 0, hi = Integer.MAX_VALUE`, but the phenomenon is the
same: the mathematical size does not fit in 32 bits.

Fix (code, not contract): make `size()` return `long` and compute
`(long) hi - lo + 1`. The `long` arithmetic cannot overflow for two `int`
endpoints, and the contract is unchanged. After the fix `./esc` reports OK and
`RangeCheck.size --unwind 1` reports VERIFICATION SUCCESSFUL.

### 4. StackAr

The implementation keeps `elems` and `top` with the class invariant

```java
//@ public invariant elems != null && -1 <= top && top < elems.length;
```

`push` requires `top + 1 < elems.length` and assigns only `top` and
`elems[top + 1]`; `pop` and `peek` require `top >= 0`; `pop` assigns only `top`
and returns `\old(elems[\old(top)])`; `isEmpty`, `isFull`, `size` and `peek` are
`pure` with contracts that tie them to `top` and `elems.length`. Both
`./esc plus/StackAr.java` and
`./bmc StackArCheck.operations --unwind 5 --no-unwinding-assertions` verify.

Q: Which tool reports your bug, and how? Could a bug get past OpenJML but not JBMC, or the other way around?

I introduced a typical off-by-one bug in `isFull`:

```java
return top + 1 <= elems.length;      // always true for a legal stack
```

OpenJML reports a `Postcondition` failure in `isFull`: the result no longer
implies `top + 1 == elems.length`. JBMC reports the harness assertion
`s.isFull() == (n == capacity)` as failed, with the counterexample
`capacity = 3, n = 0`: an empty stack is reported as full. So this bug is caught
by both, at different levels: OpenJML points at the violated contract, JBMC at
the wrong observable behavior.

Yes, a bug can get past one tool and not the other. A bug in a method with no
contract (or with a too-weak contract/invariant) can pass OpenJML — the given
`StackAr` file "verified" before anything was written — while JBMC's independent
model of the operations still notices the wrong answer. Conversely, a bug that
needs a longer sequence of operations than the unwind bound, or inputs outside
the harness's scope, can pass JBMC while OpenJML (with a strong contract) proves
or finds it. For example, the `midpoint` overflow in the homework needs arrays of
about 2^30 elements, invisible to JBMC's small arrays but found by OpenJML.
Each tool is only as strong as the specification/harness you give it.

### 5. SafeLock

Q: Smallest K that finds a bug? Which sequence of events? What is wrong in the code?

The smallest K is **5** (K = 1, 2, 3 and 4 report SUCCESSFUL with
`--no-unwinding-assertions`). The sequence is

```text
wrong PIN, wrong PIN, Close, wrong PIN, correct PIN
```

The bug is in `close()`: it resets `failed = 0` even when the safe was not
OPEN. After two wrong PINs, the Close event clears the counter; the third wrong
PIN only makes `failed = 1` instead of blocking, and the following correct PIN
opens the safe. The harness counts wrong PINs in a row across Close events (Close
is neither a correct PIN nor an admin reset), so it reaches 3 and observes the
safe OPEN — the property is violated. An attacker can thus avoid the block
forever by pressing Close between attempts.

Fix: reset `failed` only when an OPEN safe is actually closed:
`if (state == State.OPEN) { state = State.LOCKED; failed = 0; }`. Closing a
locked or blocked safe must not clear the attempt counter. With this fix K = 8,
10 and 12 all report VERIFICATION SUCCESSFUL for property 1 with
`--no-unwinding-assertions`.

Q: Formula size and time for K = 8, 10, 12.

For `SafeLockCheck.neverOpensAfterTooManyWrongPins` on the fixed `SafeLock`
(with `--no-unwinding-assertions`):

| K | SAT formula | time |
| --- | --- | --- |
| 8 | 46050 variables, 68865 clauses | 0.28 s |
| 10 | 56941 variables, 87971 clauses | 0.53 s |
| 12 | 67836 variables, 107563 clauses | 1.02 s |

The formula grows roughly linearly with K, and so does the solving time.

Q: Does SUCCESSFUL with K = 12 mean the property holds for every sequence? Can unwinding assertions help?

No. With `--no-unwinding-assertions`, the event loop of the harness is unrolled
only 12 times; sequences longer than 12 events are cut off and ignored. The
result covers only sequences of at most 12 events. Unwinding assertions cannot
turn this into a proof for all sequences: the harness deliberately allows an
arbitrary number of events (`while (CProver.nondetBoolean())`), so after any
finite K the loop guard can still be true — JBMC would report the unwinding
assertion as failed rather than prove the property. They can tell you that the
bound is insufficient, but they cannot prove an unbounded property; that needs
an inductive argument (loop invariant / class invariant), not a larger bound.
The same applies to `onlyAdminUnblocks`: SUCCESSFUL at K = 12 (or 8) means no
sequence of at most 12 (or 8) events breaks it, not that every sequence does.
