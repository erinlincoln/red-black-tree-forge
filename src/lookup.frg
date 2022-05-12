#lang forge

open "tree_electrum.frg"

// Models a regular binary tree lookup algorithm
// Included to prove lookup complexity in modeled RBT matches expected complexity.

one sig Lookup {
  var current: lone Node,
  target: one Int
}

pred init_lookup {
  // Not an empty tree
  some Node

  // Require a valid RBT
  wellformed_rb

  // All nodes are in the tree
  Node in treeNode

  Lookup.current = Tree.rootNode
  Tree.step = 0
}

pred left_lookup_transition {
  some Lookup.current
  Lookup.target < Lookup.current.value
  Tree.step' = add[Tree.step, 1]
  Lookup.current' = Lookup.current.left
}

pred right_lookup_transition {
  some Lookup.current
  Lookup.target > Lookup.current.value
  Tree.step' = add[Tree.step, 1]
  Lookup.current' = Lookup.current.right
}

pred lookup_complete_transition {
  no Lookup.current or Lookup.target = Lookup.current.value
  Tree.step' = Tree.step
  Lookup.current' = Lookup.current
}

pred lookup_transition {
  // Tree structure stays the same
  rootNode' = rootNode
  left' = left
  right' = right
  color' = color
  type' = type
  nullNode' = nullNode

  left_lookup_transition or
  right_lookup_transition or
  lookup_complete_transition
}

pred lookup_traces {
  init_lookup
  always lookup_transition
}

// Counts the number of steps, not including the termination step
fun complexity: Int {
  lookup_complete_transition => 0
  else max[{ i: Int | eventually Tree.step = i }]
}
