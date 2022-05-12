#lang forge "final" "jpqtay573rwx8pc6@gmail.com"

// Tests for the basic BST insertion. Includes both properties and cases for insertion.

open "../src/tree.frg"
open "../src/insert.frg"

// Use a trace length of 2, which is enough to prove properties by induction
// Put longer tests in another file
option max_tracelength 2

test expect {
  canInsertIntoEmpty: {
    wellformedRBT
    no root
    some n: Node | insert[n]
  } for exactly 1 Node is sat

  canInsertIntoExisting: {
    wellformedRBT
    #treeNode = 1
    some n: Node | insert[n]
  } for exactly 2 Node is sat

  canInsertIntoThreeNodeTree: {
    wellformedRBT
    some root
    some root.left
    some root.right
    some n: Node | insert[n]
  } for exactly 4 Node is sat

  cannotInsertExisting: {
    wellformedBST => { no n: treeNode | insert[n] }
  } for 4 Node is theorem

  insertedNodeIsRedLeaf: {
    wellformedBST => {
      all n: Node | (insert[n]) => {
        no n.(left' + right')
        n.color' = Red
      }
    }
  } for 4 Node is theorem

  insertIncreasesTreeSize: {
    (wellformedBST and (some n: Node | insert[n])) => {
      #treeNode' = add[#treeNode, 1]
    }
  } for 5 Node is theorem

  insertPreservesWellformedBST: {
      (wellformedBST and (some n: Node | insert[n])) => next_state wellformedBST
  } for exactly 6 Node is theorem

  // some nextInsertNode implies tree is not wellformed
  nextInsertImpliesWellformed: {
    some nextInsertNode => not wellformedRBT
  } for 4 Node is theorem
}