#lang forge

open "../src/tree.frg"
// Tests that demonstrate the maximum height of a RBT for a given number of nodes.
// Included to demontrate essential properties of RBTs.

// Since these tests are on static trees, just use one instance
option max_tracelength 1

fun leaves: set Node {
  treeNode - (left + right).Node
}

// Returns the height of the tree
//
// IMPORTANT: This actually returns off-by-one since it does not include the leaf
// nodes themselves. However, this has the benefit of allowing a taller height value
// in the same Int bitwidth.
fun height: one Int {
  no treeNode => 0
  else max[{ i: Int | { some n: leaves | #(children.n) = i }}]
}

test expect {
  // There is a tree with 1 node and height 1
  height1: {
    wellformedRBT
    height = 0
  } for exactly 1 Node is sat

  // All trees with <= 1 node have height <= 1
  maxHeight1: {
    wellformedRBT => height = 0
  } for 1 Node is theorem

  // There is a tree with 2 nodes and height 2
  height2: {
    wellformedRBT
    height = 1
  } for exactly 2 Node is sat

  // All trees with <= 3 nodes have height <= 2
  maxHeight2: {
    wellformedRBT => height <= 1
  } for 3 Node is theorem

  // There is a tree with 4 nodes and height 3
  height3: {
    wellformedRBT
    height = 2
  } for exactly 4 Node is sat

  // All trees with <= 5 nodes have height <= 3
  maxHeight3: {
    wellformedRBT => height <= 2
  } for 5 Node is theorem

  // There is a tree with 6 nodes and height 4
  height4: {
    wellformedRBT
    height = 3
  } for exactly 6 Node is sat

  // All trees with <= 7 nodes have height <= 4
  maxHeight4: {
    wellformedRBT => height <= 3
  } for 7 Node is theorem
  // Could do 9 Node but that takes too long

  // These take too long:
  // height5: {
  //   wellformedRBT
  //   height = 4
  // } for exactly 10 Node is sat
  //
  // height6: {
  //   wellformedRBT
  //   height = 5
  // } for exactly 14 Node is sat
}
