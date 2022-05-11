#lang forge

open "../src/tree_electrum.frg"

option problem_type temporal
option max_tracelength 6

// Models a regular binary tree lookup algorithm and proves worst-case algorithm 
// complexity on a RBT. Included to prove lookup complexity in modeled RBT
// matches expected complexity.

one sig Lookup {
  var step: one Int,
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
  Lookup.step = 0
}

pred left_lookup_transition {
  some Lookup.current
  Lookup.target < Lookup.current.value
  Lookup.step' = add[Lookup.step, 1]
  Lookup.current' = Lookup.current.left
}

pred right_lookup_transition {
  some Lookup.current
  Lookup.target > Lookup.current.value
  Lookup.step' = add[Lookup.step, 1]
  Lookup.current' = Lookup.current.right
}

pred lookup_complete_transition {
  no Lookup.current or Lookup.target = Lookup.current.value
  Lookup.step' = Lookup.step
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
  else max[{ i: Int | eventually Lookup.step = i }]
}

test expect {
  vacuous1: {
    lookup_traces and complexity = 1
  } for exactly 1 Node is sat

  complexity1: {
    lookup_traces => complexity <= 1
  } for 1 Node is theorem

  vacuous2: {
    lookup_traces and complexity = 1
  } for exactly 2 Node is sat

  complexity2: {
    lookup_traces => complexity <= 2
  } for 2 Node is theorem

  vacuous3: {
    lookup_traces and complexity = 3
  } for exactly 4 Node is sat

  complexity3: {
    lookup_traces => complexity <= 3
  } for 5 Node is theorem

  vacuous4: {
    lookup_traces
    complexity = 4
  } for exactly 6 Node is sat

  complexity4: {
    lookup_traces => complexity <= 4
  } for 7 Node is theorem
  // Could do 9 Node but that takes too long

}
