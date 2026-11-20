# Bonus: answers

Name(s):

### 1. Composite

Q: Which part of the invariant breaks, after which calls? What is wrong in `update`?

I completed `checkInvariant` with all the clauses from the field comments:

```java
static void checkInvariant(Composite n) {
    for (Composite c = n.firstChild; c != null; c = c.nextSibling) {
        assert c.parent == n;                                  // each child points back to its parent
    }
    int max = n.initValue;
    for (Composite c = n.firstChild; c != null; c = c.nextSibling) {
        if (max < c.value) {
            max = c.value;
        }
    }
    assert n.value == max;                                     // value is the maximum
    assert (n.maxChild == null) == (n.value == n.initValue);   // null exactly when value == initValue
    if (n.maxChild != null) {
        assert n.maxChild.parent == n;                         // maxChild is one of the children
        assert n.maxChild.value == n.value;
    }
}
```

The clause that breaks is **"`maxChild` is one of the children"**: the ancestor's
`maxChild` ends up pointing at a **grandchild**. Everything else (parent back
pointers, `value == max`, `maxChild == null` exactly when `value == initValue`,
and `maxChild.value == value`) still holds.

The bug is in `update`, more precisely in its **recursive call**. `update(c)` is
first called by `addChild(c)` with the node that was just attached, so for the
direct parent `maxChild = c` is correct. But when the parent's value rises, the
parent calls `parent.update(c)` — it passes the same `c` further up. The
grandparent then sets `maxChild = c`, although `c` is a child of its child, not
its own child. The value it computes is right (`c.value` really is the new
maximum of its subtree), only the witness `maxChild` is wrong.

For example, with three nodes `A`, `B`, `C` and `initValue`s 0, 1, 10:

```text
A.addChild(B);          // B is a child of A
B.addChild(C);          // C is a child of B, and C.value > B.value > A.value
```

`B.update(C)` sets `B.value = 10, B.maxChild = C` correctly and then calls
`A.update(C)`; `A` sets `A.value = 10, A.maxChild = C`, but `C.parent == B`, not
`A`. JBMC finds exactly this: in its K = 4 counterexample the first call attaches
a smaller node, the second attaches a larger node, and the invariant fails at
`assert n.maxChild.parent == n` on the grandparent (`n = Composite#2`, whose
`maxChild = Composite#1` has `parent = Composite#3`).

Fix: propagate the node whose value actually rose, i.e. `this`, not the argument:

```java
private void update(Composite c) {
    if (value < c.value) {
        value = c.value;
        maxChild = c;
        if (parent != null) {
            parent.update(this);      // this node is the child of our parent
        }
    }
}
```

With this fix `./bmc CompositeCheck.addChildren --unwind 5 --no-unwinding-assertions`
reports VERIFICATION SUCCESSFUL.

Q: Why does JBMC need K = 4 to find a bug that needs two calls?

`--unwind K` applies to **every** loop, and in this JBMC `K` unwindings allow
`K - 1` iterations through the loop body (the raw log at K = 3 says
`Unwinding loop ... iteration 1`, `iteration 2`, then `Not unwinding ... iteration 3`).
The harness's first loop creates `NODES = 3` nodes, so it needs three iterations
and the guard test `i < 3` that follows them. At K = 3 the cut happens while
that guard is still true; with `--no-unwinding-assertions` the cut becomes
`assume !(i < 3)`, i.e. `assume false`, so **every path is pruned** and JBMC has
no formula to solve. K = 4 is the first bound that finishes the three-iteration
initialization loop (and the later loop over the three nodes in
`checkInvariant`); with it, two `addChild` calls fit in the event loop and the
two-call chain is reachable.

So the bug itself needs only two calls, but reaching them already costs the
bound of the three-iteration loops around them. K = 2 and K = 3 therefore report
VERIFICATION SUCCESSFUL with **no SAT formula at all**: the success is vacuous
(the same phenomenon as `--no-unwinding-assertions` in the Zune exercise).
Without `--no-unwinding-assertions`, K = 3 fails a genuine unwinding assertion
at the initialization `for` loop, which confirms that the bound is too small
rather than that the property holds.

Q: How large is the formula compared with the previous exercises? What would you need to verify `Composite` with OpenJML?

With the completed invariant and the **buggy** `update` (JBMC reports the failed
assertion, so a formula is built):

| K | SAT variables | clauses | time |
| --- | --- | --- | --- |
| 2 | — (no formula) | — | — |
| 3 | — (no formula) | — | — |
| 4 | 138 729 | 344 827 | 5.17 s |
| 5 | 197 421 | 515 800 | 7.00 s |

For comparison, the SafeLock harnesses from homework plus had about 46 000
variables / 69 000 clauses at K = 8 and 68 000 / 108 000 at K = 12. Composite is
therefore roughly three to five times larger at the same order of bound, and
grows by about 40 % in variables and 50 % in clauses per extra iteration.

The reason is the heap. The previous exercises have a few scalar inputs (or an
array); here JBMC must encode three objects with five fields each, the array of
references to them, and every possible aliasing pattern between `parent`,
`firstChild`, `nextSibling` and `maxChild`. Each dereference adds null and array
bounds checks, the harness nests four loops (initialization, the event loop, the
loop over the three nodes and the two sibling-list walks inside
`checkInvariant`), and the recursive `update` is unwound once per ancestor.
Compare the star variant below, where allowing subtrees raises K = 5 to about
246 000 variables / 638 000 clauses.

To verify `Composite` with OpenJML you would have to write the whole
specification that JBMC gets for free from the harness:

- a **class invariant** formalising all the field comments — parent links,
  `value` = maximum of `initValue` and the children's `value`s, `maxChild` null
  exactly when `value == initValue`, and otherwise a child with
  `maxChild.value == value` — plus the structural property that the nodes form a
  tree (no cycles, a single root). The last part is not local: it needs a pure
  helper that walks `parent`, or the `firstChild`/`nextSibling` lists, or a
  ghost/model field, because "is a child" / "is an ancestor" is not expressible
  as a comparison of two fields;
- **contracts for `addChild` and `update`**: preconditions (non-null, `c` is a
  root, `c != this`, `c` is not an ancestor), postconditions saying how `value`
  and `maxChild` change along the whole ancestor chain, and `assignable`
  (frame) clauses covering `this` and every ancestor — datagroups or a
  reachability expression are needed because the set of modified objects is not
  known statically;
- a **`decreases`** clause for the recursive `update` (e.g. the distance to the
  root) to prove termination, and loop invariants for the sibling-list walks;
- JML's class invariant is checked at method boundaries, so every method that
  changes the structure (including the private `update`) needs a contract that
  restores it.

Then OpenJML proves the property for **all** trees, not only for the heaps of
three nodes that JBMC explores. The hard part is exactly the specification: JBMC
only needs `assert`s in a harness, while OpenJML needs the invariant, the frame
conditions and the termination argument.

Q (★): What goes wrong when subtrees are allowed?

I dropped `c.firstChild == null` from `addChild` and from the harness's `assume`.
With the fixed `update` the **original invariant does not notice anything**: K =
4, 5 and 6 all report VERIFICATION SUCCESSFUL. That is wrong, because the harness
can now build a cycle in two calls:

```text
A.addChild(B);      // B is a child of A
B.addChild(A);      // A is a root, A != B, and A is an ancestor of B -> cycle
```

(JBMC's own K = 5 counterexample is a three-call variant — `#1.addChild(#3)`,
`#1.addChild(#2)`, `#3.addChild(#1)` — but the two-call version is already
legal.) All the local clauses still hold on the cyclic structure: every
`c.parent == n` back pointer is consistent, and the cached maxima are still the
maxima of the (now cyclic) child lists. What is missing is **tree-ness**:
`addChild` must not attach a node below one of its own descendants.

I added the missing property to `checkInvariant` as a bounded parent-chain walk
(following `parent` from `n` must reach `null`, never come back to `n`):

```java
Composite q = n;
for (int i = 0; i < NODES; i++) {
    q = q.parent;
    if (q == null) {
        break;
    }
    assert q != n;
}
```

JBMC now fails at `assert q != n` (on the three-call counterexample it finds;
the two-call cycle fails the same way). The fix is to reject an ancestor in
`addChild`, and to mirror that condition in the harness:

```java
static boolean isAncestor(Composite a, Composite n) {
    for (Composite q = n.parent; q != null; q = q.parent) {
        if (q == a) {
            return true;
        }
    }
    return false;
}
// in addChild:
if (c == this || c.parent != null || isAncestor(c, this)) {
    throw new IllegalArgumentException();
}
// in the harness:
CProver.assume(c != p && c.parent == null && !Composite.isAncestor(c, p));
```

With these changes the star variant verifies again: K = 5 gives VERIFICATION
SUCCESSFUL (109 properties, 245 977 variables / 637 509 clauses, 6.23 s). The
committed `Composite`/`CompositeCheck` are this stronger version.

### 2. SafeLock for any number of events

Q: Why does OpenJML think `failed++` may overflow?

Extended static checking is modular: at the entry of a method the only facts
OpenJML may assume about the receiver are its class invariant and the method's
precondition. The given `SafeLock` has no class invariant, so `failed` is an
unconstrained `int` field as far as the prover is concerned: it must consider a
reachable object state with `failed == Integer.MAX_VALUE`. In that state
`failed++` overflows 32-bit `int`, and OpenJML reports
`ArithmeticOperationRange: overflow in int sum` at the `failed++` line. The code
in fact blocks after three wrong attempts, but that is a fact about the *code*;
without an invariant it is not a fact about the *states* OpenJML considers.

A bound alone is not enough: with only

```java
//@ private invariant 0 <= failed && failed <= MAX_ATTEMPTS;
```

OpenJML still permits the state `state == LOCKED && failed == 3`, where
`failed++` makes 4 and breaks the bound; it then reports `InvariantExit` in
`enterPin`. The invariant must relate `failed` and `state`, e.g.

```java
//@ private invariant 0 <= failed && failed <= MAX_ATTEMPTS;
//@ private invariant (state == State.BLOCKED) <==> (failed >= MAX_ATTEMPTS);
//@ private invariant state == State.OPEN ==> failed == 0;
```

Now a non-`BLOCKED` state has `failed <= 2`, so `failed++` is at most 3 and
cannot overflow; `./esc plus/SafeLock.java` says OK with the fixed `close`.

Q: Does your invariant catch the bug of homework plus, exercise 5? What does this proof give you that JBMC did not?

Partly. Putting the exercise-5 bug back (`close` resets `failed = 0`
unconditionally, even when the safe is not OPEN) makes OpenJML fail — but with
`InvariantExit` in `close`: the method can be called on a **`BLOCKED`** safe
(`state == BLOCKED`, `failed == 3`); it leaves `state == BLOCKED` but sets
`failed = 0`, which contradicts the biconditional. So the verifier rejects the
buggy program, and it does so for every reachable state at once.

It does **not** catch the attack that JBMC found. The dangerous sequence

```text
wrong PIN, wrong PIN, Close, wrong PIN, correct PIN
```

acts while the safe is `LOCKED`: after two wrong PINs `failed == 2`; the buggy
`Close` resets it to 0 and leaves `state == LOCKED`; the next wrong PIN gives
`failed == 1`, and the correct PIN opens the safe. The resulting state
`(LOCKED, failed = 0)` satisfies the invariant — it is indistinguishable from a
freshly constructed safe. I checked this: if `close` resets `failed` only when
`state` is `OPEN` or `LOCKED` (so the BLOCKED case that OpenJML catches is
removed, but the exploit remains), `./esc` still says OK. Catching the exploit
needs a **history** property, e.g. a ghost field counting wrong PINs since the
last legitimate opening, updated on every event, with an invariant tying
`failed` to it; a class invariant over the current fields cannot see that
history because the buggy execution returns the fields to a legal initial
configuration.

What the proof gives that JBMC did not: JBMC only explored sequences of at most
K events (K = 5 finds the bug; K = 8/12 in homework plus) and only the concrete
harness property. The OpenJML invariant is inductive, so it holds after **every**
sequence of events, for any number of events, and it establishes the state
relation `0 <= failed <= 3`, `BLOCKED <-> failed >= 3`, `OPEN -> failed == 0` at
every method boundary. That is a stronger statement than any finite K, but it
proves only what the invariant says: it is not a proof of the behavioural
security property. The two tools are complementary — JBMC's harness state
(`wrongInARow`) catches the lost history with a concrete counterexample, while
OpenJML's invariant catches the state-relation violation for unbounded
executions.

The committed `plus/SafeLock.java` has the fix back in place and verifies with
this invariant.
