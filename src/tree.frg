#lang forge

option problem_type temporal

// Node of a binary tree with color and delete state
sig Node {
    value: one Int,
    var left: lone Node,
    var right: lone Node,
    var color: one Color,

    // Delete-specific:
    var type: lone DoubleBlack,
    var nullNode: lone IsNull
}

// Delete-specific
one sig DoubleBlack {}
one sig IsNull {}

// State for a tree
one sig Tree {
    var rootNode: lone Node,
    var step: one Int
}

// Color of nodes
abstract sig Color {}
one sig Black, Red extends Color {}

// Helper to avoid more typing
fun root: lone Node {
    Tree.rootNode
}

// Get both immediate children
fun immediateChildren: set Node -> Node {
    left + right
}

// Get the immediate parent of a node
fun parent: set Node -> Node {
    ~immediateChildren
}

// Get *all* children in a node's subtree
fun children: set Node -> Node {
    ^immediateChildren
}

fun grandparent: set Node -> Node {
    parent.parent
}

// Wanted: X -> S
//    R    and   R
//   / \        / \
//  X   S      S   X
fun sibling: set Node -> Node {
    (~left).right + (~right).left
}

// Get the sibling of a node's parent
// Wanted: X -> U
//     R
//    / \
//   P   U    (and three related configurations)
//  /
// X
fun uncle: set Node -> Node {
    parent.sibling
}

// Wanted: X -> N
//    R    and   R
//   / \        / \
//  X   S      S   X
//       \    /
//        N  N
fun farNephew: set Node -> Node {
    // ~left creates a relation of left nodes -> their parent
    // Then (~left).right gets the sibling of all left nodes
    // Then (~left).right.right gets the right child of all left node siblings
    // Mirror for right nodes
    (~left).right.right + (~right).left.left

    // Equivalent:
    // { n, nephew : Node | {
    //     n.parent.left = n => {
    //         n.sibling.right = nephew
    //     } else {
    //         n.sibling.left = nephew
    //     }
    // }}
}

// Wanted: X -> N
//    R    and   R
//   / \        / \
//  X   S      S   X
//     /        \
//    N          N
fun nearNephew: set Node -> Node {
    // ~left creates a relation of left nodes -> their parent
    // Then (~left).right gets the sibling of all left nodes
    // Then (~left).right.left gets the left child of all left siblings
    // Mirror for right nodes
    (~left).right.left + (~right).left.right

    // Equivalent:
    // { n, nephew : Node | {
    //     n.parent.left = n => {
    //         n.sibling.left = nephew
    //     } else {
    //         n.sibling.right = nephew
    //     }
    // }}
}

// Get all nodes that are in the tree
fun treeNode: set Node {
    root + root.children
}

// Get the node that is marked DoubleBlack
fun dbNode: lone Node {
    { n : Node | n.type = DoubleBlack and n in treeNode }
}

// Requires the data to actually be a tree structure
pred wellformedTree {
    // Everything not in the tree is a lone node
    no (Node - treeNode).immediateChildren

    // not reachable from itself
    all n : Node | n not in n.children

    // left and right are different
    no left & right
 
    // only one parent, root has no parent
    no root.parent
    all n: Node | lone n.parent
}

// Constrains the data to be a Binary Search Tree
pred wellformedBST {
    // Is a wellformed tree
    wellformedTree

    // All values in left tree are less than the parent's value
    // All values in right tree are greater than the parent's value
    all p: treeNode | no p.nullNode => {
        all c: (p.left + p.left.children) | no c.nullNode => c.value < p.value
        all c: (p.right + p.right.children) | no c.nullNode => c.value > p.value
    }
}

// Counts the number of black nodes, including the specified node if it is black,
// between this node and the root
fun blackDepth[n: Node]: Int {
    // color.Black gets all black nodes
    // `children.n` gets all parents of `n`
    #(color.Black & (n + children.n))
}

// Constrains the data to be a wellformed Red-Black Tree
pred wellformedRBT {
    // Red-Black Tree must be a wellformed binary search trees
    wellformedBST

    // Root, if it exists, is always black
    root.color in Black

    // No two adjacent red nodes
    // In other words, no child of a red node is red
    Red not in ((color.Red).immediateChildren.color)
    //Equivalent for well-formed tree, but slower:
    // all n : treeNode | (n.color = Red) => {
    //     Red not in n.immediateChildren.color
    // }

    // Any path from Root to a NIL goes through the same number of black nodes
    // Since NILs are not explicitly in the graph, ensure that every node that has a NIL
    // child is the same number of black nodes from Root, including itself if it is black.
    // This is the same as counting the number of black nodes *between* the NIL and the root.
    some depth: Int | {
        all n: treeNode - ((left.Node) & (right.Node)) | {
            depth = blackDepth[n]
        }
    }

    // We do not include a constraint about the leaf nodes being black because
    // NIL leaves are implicitly treated as black

    // A wellformed RBT does not contain any DoubleBlack nodes
    // which can occur during deletion
    no treeNode.type
    no treeNode.nullNode
}
