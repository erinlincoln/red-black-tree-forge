#lang forge "final" "jpqtay573rwx8pc6@gmail.com"

open "tree_electrum.frg"

pred insert[n : Node] {
    // Tree is assumed to be wellformed BST before node is added

    // Don't insert until done deleting
    no dbNode

    -- Don't insert until the previous insert is cleaned up
    no nextInsertNode

    -- New node is not in the current tree
    n not in treeNode

    -- New node is in the next state
    n in treeNode'

    -- New node must not be DoubleBlack
    no n.type
    no n.nullNode

    -- All colors stay the same except
    -- the new node is red
    color' = (color - (n -> Color)) + n -> Red

    -- type and null stays the same
    type' = type
    nullNode' = nullNode

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
        root' = root

        // Insertion into an existing tree
        // Find the correct parent node
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

pred insertRecolorEnabled[n: Node] {
    -- Must be in the process of inserting
    some nextInsertNode

    n.color = Red
    n.grandparent.color = Black or no n.grandparent
    n.parent.color = Red or no n.parent
    n.uncle.color = Red or (no n.uncle and no n.grandparent)
}

pred insertRecolor[n: Node] {
    insertRecolorEnabled[n]

    root' = root
    left' = left
    right' = right

    type' = type
    nullNode' = nullNode

    no n.grandparent and no n.parent => {
        color' = (color - (n -> Color)) + n -> Black
    }

    no n.grandparent and some n.parent => {
        color' = color
    }

    some n.grandparent and some n.parent => {
        let g = n.grandparent, p = n.parent, u = n.uncle | {
            color' = (color - ((g + p + u) -> Color)) +
                g -> Red +
                p -> Black +
                u -> Black
        }
    }
}

pred replaceGrandparent[prev: Node, next: Node] {
    (prev = root) => {
        root' = next
    } else {
        root' = root

        prev.parent.color' = prev.parent.color

        (some prev.~left) => {
            prev.parent.left' = next
            prev.parent.right' = prev.parent.right
        } else {
            prev.parent.right' = next
            prev.parent.left' = prev.parent.left
        }
    }
}

pred insertRotateEnabled[n: Node] {
    -- Must be in the process of inserting
    some nextInsertNode

    n.color = Red
    some n.grandparent

    -- If n's parent is black, there is no fixing required, so therefore no rotation happens
    -- If n is not the root and the parent is also Red, then rotation/recoloring must take place 
    n.parent.color = Red

    -- Uncle is either missing or is Black (otherwise only recoloring is needed)
    no n.uncle or n.uncle.color = Black
}

pred insertRotate[n : Node] {
    insertRotateEnabled[n]

    -- Since parent is red, and n is red, the coloring is violated
    -- Grandparent must always be black, since parent is red
    -- Uncle may be missing

    type' = type
    nullNode' = nullNode
    
    let p = n.parent, g = n.grandparent, u = n.uncle | {
        -- Let everything else stay the same
        -- Uncle does not change in this case
        all o: Node | (o not in (n + p + g + g.parent)) => {
            o.left' = o.left
            o.right' = o.right
            o.color' = o.color
        }

        -- Left Left case
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
// This node is used for identifying which node(s) must be
// rotated or recolored
fun nextInsertNode: lone Node {
    {root.color = Red} => root
    else { n : Node | n.parent.color = Red and n.color = Red }
}

pred init {
    wellformed_rb
    Tree.step = 0
}

pred terminateTransition {
    // Don't terminate until done inserting
    no nextInsertNode
    // Don't terminate until done deleting
    no dbNode

    left' = left
    right' = right
    value' = value
    color' = color
    rootNode' = rootNode
    step' = step

    type' = type
    nullNode' = nullNode
}

pred insertRotateTransition {
    insertRotate[nextInsertNode]
    Tree.step' = add[Tree.step, 1]
}

pred insertRecolorTransition {
    insertRecolor[nextInsertNode]
    Tree.step' = add[Tree.step, 1]
}

pred insertTransition {
    some n: Node | insert[n]
    Tree.step' = add[Tree.step, 1]
}

pred insertTraces {
    init
    always (
        insertTransition or
        insertRotateTransition or
        insertRecolorTransition or
        terminateTransition
    )
}
