// 1. A tree of components (the Composite pattern) that caches, in every node,
// the maximum value of its subtree.
//
// Ported from the Java version of AutoProof's composite.e (an Eiffel verification
// benchmark) used in the GAssert and SpecFuzzer experiments. Changes: the list of
// children is a linked list (firstChild, nextSibling), since JBMC does not model
// java.util collections, and the set of ancestors, which addChild did not need, is gone.
//
// The fields are package-private so that the harness can read them.
public final class Composite {

    /** The children: firstChild, firstChild.nextSibling, ... (null-terminated). */
    Composite firstChild;
    Composite nextSibling;

    /** Parent node (null for a root). */
    Composite parent;

    /** The maximum of initValue and the values of the children. */
    int value;

    /** Initial value (at node creation). */
    final int initValue;

    /** The child whose value is value, if value is greater than initValue; null otherwise. */
    Composite maxChild;

    /** Creates a single node with initial value v. */
    public Composite(int v) {
        initValue = v;
        value = v;
    }

    /** Adds c as a child: c must be a root (no parent) other than this and must not
        be an ancestor of this. Subtrees are allowed; the ancestor check is what
        keeps the structure acyclic. */
    public void addChild(Composite c) {
        if (c == null) {
            throw new IllegalArgumentException();
        }
        if (c == this || c.parent != null || isAncestor(c, this)) {
            throw new IllegalArgumentException();
        }
        c.parent = this;
        c.nextSibling = firstChild;
        firstChild = c;
        update(c);
    }

    /** Is a a proper ancestor of n (on n's parent chain)? */
    static boolean isAncestor(Composite a, Composite n) {
        for (Composite q = n.parent; q != null; q = q.parent) {
            if (q == a) {
                return true;
            }
        }
        return false;
    }

    /** Updates value of this node and its ancestors taking into account an updated child c.
        c is a direct child whose value may have risen; when this node's value rises,
        it is *this* node that must be reported to the parent, not c. */
    private void update(Composite c) {
        if (value < c.value) {
            value = c.value;
            maxChild = c;
            if (parent != null) {
                parent.update(this);
            }
        }
    }
}
