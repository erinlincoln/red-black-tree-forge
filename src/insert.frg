#lang forge "final" "jpqtay573rwx8pc6@gmail.com"

open "tree.frg"

pred insert[n : Node] {
    // Assumption: tree is a wellformed BST

    // Don't insert until done deleting
    no dbNode

    -- Don't insert until the previous insert is cleaned up
    no nextInsertNode

    -- New node is not in the current tree
    n not in treeNode

    -- New node must not be DoubleBlack
    no n.type

    -- All colors stay the same except the new node is red
    color' = (color - (n -> Color)) + n -> Red

    // Delete state stays the same
    type' = type
    nullNode' = nullNode

    // After adding, the new node is positioned correctly in the binary tree
    // Note that this models the lookup algorithm to find the correct node in one step,
    // hiding this algorithmic complexity
    next_state {
        all p: treeNode | {
            (n in p.left.children) => n.value < p.value
            (n in p.right.children) => n.value > p.value
        }
    }

    (no root) => {
        // Insertion into an empty tree
        root' = n
        no left'
        no right'
    } else {
        // Insertion into an existing tree

        // Root stays the same
        root' = root

        // Add to the correct side of the parent node
        // Data structure constraints automatically exclude the possibility
        // of adding two left relations from a given node, so we do not need
        // to check if the node already has a left/right child
        some p: treeNode | {
            {
                n.value < p.value
                left' = left + p -> n
                right' = right
            } or {
                n.value > p.value
                right' = right + p -> n
                left' = left
            }
        }
    }
}

// Guard conditions for `insertRecolor`
pred insertRecolorEnabled[n: Node] {
    -- Must be in the process of inserting
    some nextInsertNode

    // Only recolor a red Node
    n.color = Red

    // Grandparent cannot be red
    n.grandparent.color in Black

    // Parent is red or this is the root (with no parent)
    n.parent.color in Red

    // Parent's sibling is red or missing
    n.uncle.color = Red or (no n.uncle and no n.grandparent)
}

// Implements recoloring, which must be done in certain cases to preserve
// the properties of a RBT
pred insertRecolor[n: Node] {
    insertRecolorEnabled[n]

    // Recoloring does not change the tree structure
    root' = root
    left' = left
    right' = right
    type' = type
    nullNode' = nullNode

    no n.grandparent => {
        no n.parent => {
            // No grandparent or parent (i.e. root)
            color' = (color - (n -> Color)) + n -> Black
        } else {
            // No grandparent, but has a parent (i.e. second-level)
            color' = color
        }
    } else {
        (some n.parent) => (let g = n.grandparent, p = n.parent, u = n.uncle | {
            // Has a grandparent and a parent
            color' = (color - ((g + p + u) -> Color)) +
                g -> Red +
                p -> Black +
                u -> Black
        })
    }
}

// Swaps out the grandparent node with a new one
// Always constrains the root and the `prev.parent.(left + right + color)`
// properties, if `prev.parent` exists
pred replaceGrandparent[prev: Node, next: Node] {
    (prev = root) => {
        // If it is the root node, just replace that
        root' = next
    } else {
        // If it is not the root, the root stays the same
        root' = root

        prev.parent.color' = prev.parent.color

        (some prev.~left) => {
            // If it is the left node, replace the left node and leave the right untouched
            prev.parent.left' = next
            prev.parent.right' = prev.parent.right
        } else {
            // If it is the right node, replace the right node and leave the left untouched
            prev.parent.right' = next
            prev.parent.left' = prev.parent.left
        }
    }
}

// Guard conditions for insertRotate
pred insertRotateEnabled[n: Node] {
    -- Must be in the process of inserting
    some nextInsertNode

    // Only rotate at a red node
    n.color = Red

    // Only rotate if third-level or deeper
    some n.grandparent

    -- If n's parent is black, there is no fixing required, so therefore no rotation happens
    n.parent.color = Red

    -- Uncle is either missing or is Black (otherwise only recoloring is needed)
    n.uncle.color in Black
}

pred insertRotate[n : Node] {
    insertRotateEnabled[n]

    -- Since parent is red, and n is red, the coloring is violated
    -- Grandparent must always be black, since parent is red
    -- Uncle may be missing

    // Preserve deletion state
    type' = type
    nullNode' = nullNode
    
    let p = n.parent, g = n.grandparent, u = n.uncle | {
        -- Let everything except n, p, g, and g.parent stay the same
        // The exceptions will be constrained in the cases
        -- Uncle does not change in any case
        all o: Node - (n + p + g + g.parent) | {
            o.left' = o.left
            o.right' = o.right
            o.color' = o.color
        }

        -- Left Left case
        //        g          pB
        //       / \        / \
        //      p   u  =>  n   gR
        //     / \             / \
        //    n  p_r         p_r  u
        (g.left.left = n) => {
            -- Replace grandparent with parent
            replaceGrandparent[g, p]

            p.left' = n
            p.right' = g
            p.color' = Black

            g.left' = p.right
            g.right' = u
            g.color' = Red

            // n does not change
            n.left' = n.left
            n.right' = n.right
            n.color' = n.color
        }

        -- Left Right case
        //        g             nB
        //       / \          /    \
        //      p   u  =>   pR      gR
        //     / \         /  \     / \
        //   p_l  n      p_l  n_l n_r  u
        //       / \
        //     n_l n_r
        (g.left.right = n) => {
            -- Replace the grandparent with n
            replaceGrandparent[g, n]

            n.left' = p
            n.right' = g
            n.color' = Black

            p.left' = p.left
            p.right' = n.left
            p.color' = Red

            g.left' = n.right
            g.right' = u
            g.color' = Red
        }

        -- Right Right case
        //        g          pB
        //       / \        / \
        //      u   p  =>  gR  nR
        //         / \    / \
        //       p_l  n  u  p_l
        (g.right.right = n) => {
            -- Replace grandparent with parent
            replaceGrandparent[g, p]

            p.left' = g
            p.right' = n
            p.color' = Black

            g.left' = u
            g.right' = p.left
            g.color' = Red

            n.left' = n.left
            n.right' = n.right
            n.color' = n.color
        }

        -- Right Left case
        //        g                nB
        //       / \             /    \
        //      u    p    =>   gR       p
        //          / \       /  \     / \
        //         n   p_r   u  n_l  n_r p_r
        //        / \
        //      n_l n_r
        (g.right.left = n) => {
            replaceGrandparent[g, n]

            n.left' = g
            n.right' = p
            n.color' = Black

            g.left' = u
            g.right' = n.left
            g.color' = Red

            p.left' = n.right
            p.right' = p.right
            p.color' = p.color
        }
    }
}

// Get next node that is violating wellformed
// This node is used for identifying which node(s) must be rotated or
// recolored. Note that in imperative code, this node can be explictly
// tracked instead of calculated at each step.
fun nextInsertNode: lone Node {
    {root.color = Red} => root
    else { n : Node | n.parent.color = Red and n.color = Red }
}

// Initialization of a trace
pred init {
    // Start with a well-formed tree
    wellformed_rb
    // Reset the step counter
    Tree.step = 0
}

// Ending transition (i.e. do nothing)
pred terminateTransition {
    // Don't terminate until done inserting
    no nextInsertNode
    // Don't terminate until done deleting
    no dbNode

    // Preserve all state
    left' = left
    right' = right
    value' = value
    color' = color
    rootNode' = rootNode
    step' = step
    type' = type
    nullNode' = nullNode
}

// Transition that performs a rotation
pred insertRotateTransition {
    insertRotate[nextInsertNode]
    Tree.step' = add[Tree.step, 1]
}

// Transition that performs a re-coloring
pred insertRecolorTransition {
    insertRecolor[nextInsertNode]
    Tree.step' = add[Tree.step, 1]
}

// Transition that does a binary tree insert
pred insertTransition {
    some n: Node | insert[n]
    Tree.step' = add[Tree.step, 1]
}

// Trace that combines all transitions
pred insertTraces {
    init
    always (
        insertTransition or
        insertRotateTransition or
        insertRecolorTransition or
        terminateTransition
    )
}
