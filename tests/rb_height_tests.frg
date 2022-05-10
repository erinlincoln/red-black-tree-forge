#lang forge

open "../src/tree_electrum.frg"
// Tests that demonstrate the maximum height of a RBT for a given number of nodes.
// Included to demontrate essential properties of RBTs.

// Since these tests are on static trees, just use one instance
option max_tracelength 1

fun leaves: set Node {
  treeNode - (left + right).Node
}

// Returns the height of the tree
//
// This actually returns off-by-one since it does not include the leaf nodes
// themselves. However, this has the benefit of allowing a taller height value
// in the same Int bit-width.
fun height: one Int {
  no treeNode => 0
  else max[{ i: Int | { some n: leaves | #(children.n) = i }}]
}

test expect {
  height1: {
    wellformed_rb
    height = 0
  } for exactly 1 Node is sat

  maxHeight1: {
    wellformed_rb => height = 0
  } for 1 Node is theorem

  height2: {
    wellformed_rb
    height = 1
  } for exactly 2 Node is sat

  maxHeight2: {
    wellformed_rb => height <= 1
  } for 3 Node is theorem

  height3: {
    wellformed_rb
    height = 2
  } for exactly 4 Node is sat

  maxHeight3: {
    wellformed_rb => height <= 2
  } for 5 Node is theorem

  height4: {
    wellformed_rb
    height = 3
  } for exactly 6 Node is sat

  maxHeight4: {
    wellformed_rb => height <= 3
  } for 7 Node is theorem
  // Could do 9 Node but that takes too long

  // These take too long:
  // height5: {
  //   wellformed_rb
  //   height = 4
  // } for exactly 10 Node is sat*/

  //
  // height6: {
  //   wellformed_rb
  //   height = 5
  // } for exactly 14 Node is sat
}
