#lang forge "final" "jpqtay573rwx8pc6@gmail.com"

option problem_type temporal

// Node of each graph - left branch, right branch, value, and color
sig Node {
    value: one Int,
    var left: lone Node,
    var right: lone Node,
    var color: one Color
}

one sig Tree {
    var rootNode: lone Node
}

// Color of nodes
abstract sig Color {}
one sig Black, Red extends Color {}

// Helper to avoid more typing
fun root: lone Node {
    Tree.rootNode
}

fun immediateChildren: set Node -> Node {
    left + right
}

// Parent is the transpose of immediateChildren
fun parent: set Node -> Node {
    ~immediateChildren
}

fun grandparent: set Node -> Node {
    parent.parent
}

// Children is *all* children in a node's subtree
fun children: set Node -> Node {
    ^immediateChildren
}

// The sibling of a node's parent
fun uncle: set Node -> Node {
    // Include both of the grandparent's immediate children, but remove the parent,
    // thus there is at most a single uncle for every node
    grandparent.immediateChildren - parent
}

pred inTree[n: Node] {
    n in treeNode
}

fun treeNode: set Node {
    root + root.children
}

// wellformed tree
pred wellformed_tree {
    // Everything not in the tree is a lone node
    all n: Node - treeNode | no n.left and no n.right
    
    // not reachable from itself
    all n : Node | n not in n.children
    
    // left and right are different
    no left & right
 
    // only one parent, root has no parent
    no root.parent
    all n: Node | lone n.parent
}

// wellformed binary search tree
pred wellformed_binary {
    // is a wellformed tree
    wellformed_tree
    
    // Left is less than parent
    // Right is greater than or equal to parent (allow duplicates on the right)
    all p: treeNode | {
        all c: (p.left + p.left.children) | c.value < p.value
        all c: (p.right + p.right.children) | c.value >= p.value
    }
}

// Counts the number of black nodes, including this one,
// between this node and the root
fun blackDepth[n: Node]: Int {
  #({ intermediate: treeNode | {
      intermediate.color = Black
      n in (intermediate + intermediate.children)
  }})
}

// wellformed red black tree
pred wellformed_rb {
    // red-black tree must be a wellformed binary search trees
    wellformed_binary

    // Root, if it exists, is always black
    root.color in Black

    // No two adjacent red nodes
    all n : treeNode | (n.color = Red) => {
        Red not in n.immediateChildren.color
    }

    // Any path from Root to a NIL goes through the same number of black nodes
    // Since NILs are not explicitly in the graph, ensure that every node that has a NIL
    // child is the same number of black nodes from Root, including itself if it is black.
    // This is the same as counting the number of black nodes *between* the NIL and the root.
    some depth: Int | {
        all n: treeNode | (no n.left or no n.right) => {
            depth = blackDepth[n]
        }
    }

    // We do not include a constraint about the leaf nodes being black because
    // NIL leaves are implicitly treated as black
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
            (n in p.right.children) => n.value >= p.value
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
                n.value >= p.value
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
    -- We are not modeling insertion into an empty tree, so the root always stays the same
    -- If n's parent is black, there is no fixing required, so therefore no rotation happens
    -- If n is not the root and the parent is also Red, then rotation/recoloring must take place 
    n.parent.color = Red

    -- Uncle is either missing or is Black (otherwise only recoloring is needed)
    no n.uncle or n.uncle.color = Black
}

pred rotate[n : Node] {
    rotateEnabled[n]

    root' = root

    -- Since parent is red, and n is red, the coloring is violated
    -- Grandparent will always exist since a red node (the parent) cannot be root
    -- Grandparent must always be black, since parent is red
    -- Uncle may be missing
    
    let p = n.parent, g = n.grandparent, u = n.uncle | {
        -- Let everything else stay the same
        -- Uncle does not change in this case
        all o: Node | (o not in (n + p + g)) => {
            o.left' = o.left
            o.right' = o.right
            o.value' = o.value
            o.color' = o.color
        }

        -- Left Left case
        (g.left.left = n) => {
            -- Replace grandparent with parent
            -- This mutates the value because we cannot change the Root
            -- node reference, and grandparent could be the root
            g.value' = p.value
            g.left' = n
            g.right' = p
            g.color' = Black

            -- Replace parent with grandparent, using the same technique
            p.value' = g.value
            p.left' = p.right
            p.right' = u
            p.color' = Red

            -- n does not change
            n.value' = n.value
            n.left' = n.left
            n.right' = n.right
            n.color' = n.color
        }

        -- Left Right case
        (g.left.right = n) => {
            -- Replace the grandparent with n (see left-left case)
            g.value' = n.value
            g.left' = p
            g.right' = n
            g.color' = Black

            -- Replace n with the grandparent
            n.value' = g.value
            n.left' = n.right -- Is this right?
            n.right' = u
            n.color' = Red

            -- Parent stays in place
            p.value' = p.value
            p.left' = p.left
            p.right' = n.left -- Is this right?
            p.color' = Red
        }

        -- Right Right case
        (g.right.right = n) => {
            -- Replace grandparent with parent (see first case)
            g.value' = p.value
            g.left' = p
            g.right' = n
            g.color' = Black

            -- Replace parent with grandparent, using the same technique
            p.value' = g.value
            p.left' = u
            p.right' = p.right
            p.color' = Red

            -- n does not change
            n.value' = n.value
            n.left' = n.left
            n.right' = n.right
            n.color' = n.color
        }

        -- Right Left case
        n.parent.parent.right.left = n => {
            -- Replace the grandparent with n (see first case)
            g.value' = n.value
            g.left' = n
            g.right' = p
            g.color' = Black

            -- Replace n with the grandparent
            n.value' = g.value
            n.left' = u
            n.right' = n.left -- Is this right?
            n.color' = Red

            -- Parent stays in place
            p.value' = p.value
            p.left' = n.right -- Is this right?
            p.right' = p.right
            p.color' = Red
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

    insert_transition
    next_state rotate_transition

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