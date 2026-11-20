import org.cprover.CProver;

// 1. JBMC builds trees of NODES nodes by calling addChild on any pair of nodes
// allowed by its precondition, and checks the class invariant of every node after
// each call. Subtrees are allowed (bonus exercise ★); the precondition also excludes
// cycles. --unwind K bounds the number of calls (and every other loop).
//   ./bmc CompositeCheck.addChildren --unwind 5 --no-unwinding-assertions
public class CompositeCheck {

    static final int NODES = 3;

    public static void addChildren() {
        Composite[] nodes = new Composite[NODES];
        for (int i = 0; i < NODES; i++) {
            nodes[i] = new Composite(CProver.nondetInt());
        }
        while (CProver.nondetBoolean()) {
            Composite p = nodes[anyIndex()];
            Composite c = nodes[anyIndex()];
            CProver.assume(c != p && c.parent == null && !Composite.isAncestor(c, p));   // addChild's precondition
            p.addChild(c);
            for (Composite n : nodes) {
                checkInvariant(n);
            }
        }
    }

    static int anyIndex() {
        int i = CProver.nondetInt();
        CProver.assume(0 <= i && i < NODES);
        return i;
    }

    // The class invariant of Composite, from the comments on its fields.
    static void checkInvariant(Composite n) {
        for (Composite c = n.firstChild; c != null; c = c.nextSibling) {
            assert c.parent == n;                  // each child points back to its parent
        }

        // value is the maximum of initValue and the children's values
        int max = n.initValue;
        for (Composite c = n.firstChild; c != null; c = c.nextSibling) {
            if (max < c.value) {
                max = c.value;
            }
        }
        assert n.value == max;

        // maxChild is null exactly when value == initValue,
        // and otherwise it is one of the children and its value is value
        assert (n.maxChild == null) == (n.value == n.initValue);
        if (n.maxChild != null) {
            assert n.maxChild.parent == n;
            assert n.maxChild.value == n.value;
        }

        // no parent cycle: following parent must terminate at a root (bonus ★)
        Composite q = n;
        for (int i = 0; i < NODES; i++) {
            q = q.parent;
            if (q == null) {
                break;
            }
            assert q != n;
        }
    }
}
