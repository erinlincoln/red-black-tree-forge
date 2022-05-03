#lang forge "final" "jpqtay573rwx8pc6@gmail.com"

open "tree_electrum.frg"

fun grandparent: set Node -> Node {
    parent.parent
}

// The sibling of a node's parent
fun uncle: set Node -> Node {
    // Include both of the grandparent's immediate children, but remove the parent,
    // thus there is at most a single uncle for every node
    grandparent.immediateChildren - parent
}

// HERE IS THE INITIAL WORK FOR INSERTION:
// The basic idea is that the first transition is node_added where (hopefully)
// nothing changes except that there is now a new node in the tree at the bottom,
// such that it is still a binary tree. I'm not sure if this transition state needs
// to be separated into the steps that it takes in order to add the node to the tree.

// Then, the predicate insertion_rotation_recolor, performs the intermediary steps
// where the node that was added, and the surrounding nodes, are rotated and recolored
// based on how they are positioned in the tree.

// The main thing that still remains (that I just breifly sketched out in the prediate
// insertion) is the fact that these transition states happen for indeterminate amounts of
// time until the wellformed_rb predicate is satisfied. One of the parts that I am most
// challenged by for filling this out is the fact that the insertion_rotation_recolor
// predicate will have to take in different nodes for n during each transition. The node
// that it will have to take in can be found using the function next_node_to_restructure,
// however, I still have not figured out how to put it all together

pred insert[n : Node] {
    // Tree is assumed to be wellformed BST before node is added

    -- New node is not in the current tree
    not (n in treeNode)

    -- New node is in the next state
    n in treeNode'

    -- All colors stay the same except
    -- the new node is red
    color' = (color - (n -> Color)) + n -> Red

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

pred recolorEnabled[n: Node] {
    n.color = Red
    n.grandparent.color = Black
    n.parent.color = Red
    n.uncle.color = Red
}

pred recolor[n: Node] {
    recolorEnabled[n]

    root' = root
    left' = left
    right' = right

    let g = n.grandparent, p = n.parent, u = n.uncle | {
        color' = (color - ((g + p + u) -> Color)) +
            g -> Red +
            p -> Black +
            u -> Black
    }
}

pred rotateEnabled[n: Node] {
    n.color = Red
    some n.grandparent

    -- If n's parent is black, there is no fixing required, so therefore no rotation happens
    -- If n is not the root and the parent is also Red, then rotation/recoloring must take place 
    n.parent.color = Red

    -- Uncle is either missing or is Black (otherwise only recoloring is needed)
    no n.uncle or n.uncle.color = Black
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

pred rotate[n : Node] {
    rotateEnabled[n]

    -- Since parent is red, and n is red, the coloring is violated
    -- Grandparent must always be black, since parent is red
    -- Uncle may be missing
    
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

        -- Needto swap n for n.parent as node being inserted
    }
}

// Get next node that is violating wellformed
fun nextInsertNode: lone Node {
    {root.color = Red} => root
    else { n : Node | n.parent.color = Red and n.color = Red }
}

pred terminate_transition {
    // Don't terminate until done inserting
    no nextInsertNode

    left' = left
    right' = right
    value' = value
    color' = color
    rootNode' = rootNode
}

pred rotate_transition {
    // implies that tree isn't wellformed
    // TODO: Test that we only have one of these at any given time
    some nextInsertNode
    rotate[nextInsertNode]
}

pred recolor_transition {
    some nextInsertNode
    recolor[nextInsertNode]
}

pred insert_transition {
    -- Don't insert until the previous insert is cleaned up
    no nextInsertNode
    some n: Node | insert[n]
}

pred traces {
    wellformed_rb

    // insert_transition
    // next_state rotate_transition

    always {
        (
            insert_transition or
            rotate_transition or
            recolor_transition or
            terminate_transition
        )
    }
}

run { traces } for exactly 6 Node