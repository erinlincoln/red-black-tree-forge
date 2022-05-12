#lang forge

open "tree.frg"

// Models a regular binary tree lookup algorithm
// Included to prove lookup complexity in modeled RBT matches expected complexity.

one sig Lookup {
    var current: lone Node,
    target: one Int
}

pred initLookup {
    // Not an empty tree
    some Node

    // Require a valid RBT
    wellformedRBT

    // All nodes are in the tree
    Node in treeNode

    Lookup.current = Tree.rootNode
    Tree.step = 0
}

// When the
pred leftLookupTransition {
    some Lookup.current
    Lookup.target < Lookup.current.value
    Tree.step' = add[Tree.step, 1]
    Lookup.current' = Lookup.current.left
}

pred rightLookupTransition {
    some Lookup.current
    Lookup.target > Lookup.current.value
    Tree.step' = add[Tree.step, 1]
    Lookup.current' = Lookup.current.right
}

pred lookupCompleteTransition {
    no Lookup.current or Lookup.target = Lookup.current.value
    Tree.step' = Tree.step
    Lookup.current' = Lookup.current
}

pred lookupTransition {
    // Tree structure stays the same
    rootNode' = rootNode
    left' = left
    right' = right
    color' = color
    type' = type
    nullNode' = nullNode

    leftLookupTransition or
    rightLookupTransition or
    lookupCompleteTransition
}

pred lookupTraces {
    initLookup
    always lookupTransition
}

// Counts the total number of steps completed
fun complexity: Int {
    // If the initial state is a termination, return 0
    lookupCompleteTransition => 0
    else max[{ i: Int | eventually Tree.step = i }]
}
