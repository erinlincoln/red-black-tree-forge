#lang forge

option problem_type temporal

// Node of each graph - left branch, right branch, value, and color
sig Node {
    value: one Int,
    var left: lone Node,
    var right: lone Node,
    var color: one Color,

    var type: one Type,
    var nullNode: one NullNode
}

abstract sig Type {}
one sig Single, DoubleBlack extends Type {}

abstract sig NullNode {}
one sig IsNull, NotNull extends NullNode {}

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

// Children is *all* children in a node's subtree
fun children: set Node -> Node {
    ^immediateChildren
}

fun grandparent: set Node -> Node {
    parent.parent
}

// The sibling of a node's parent
fun uncle: set Node -> Node {
    // Include both of the grandparent's immediate children, but remove the parent,
    // thus there is at most a single uncle for every node
    grandparent.immediateChildren - parent
}

// Wanted: X -> S
//    R    and   R
//   / \        / \
//  X   S      S   X
fun sibling: set Node -> Node {
    (~left).right + (~right).left
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

fun treeNode: set Node {
    root + root.children
}

// wellformed tree
pred wellformed_tree {
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

// wellformed binary search tree
pred wellformed_binary {
    // is a wellformed tree
    wellformed_tree

    // Left is less than parent and right is greater than the parent
    all p: treeNode | {
        all c: (p.left + p.left.children) | c.value < p.value
        all c: (p.right + p.right.children) | c.value > p.value
    }
}

// Counts the number of black nodes, including the specified node if it is black,
// between this node and the root
fun blackDepth[n: Node]: Int {
    // color.Black gets all black nodes
    // `children.n` gets all parents of `n`
    #(color.Black & (n + children.n))
}

// wellformed red black tree
pred wellformed_rb {
    // red-black tree must be a wellformed binary search trees
    wellformed_binary

    // Root, if it exists, is always black
    root.color in Black

    // No two adjacent red nodes
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

    -- included for delete:
    all n : treeNode | {
        n.type = Single
    }
}
