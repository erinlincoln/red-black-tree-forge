#lang forge "final" "jpqtay573rwx8pc6@gmail.com"

// Tests for the basic BST insertion

open "tree_electrum.frg"
open "red_black.frg"

// Use a trace length of 2, which is enough to prove properties by induction
// Put longer tests in another file
option max_tracelength 2

test expect {
  canInsertIntoEmpty: {
    wellformed_rb
    no root
    some n: Node | insert[n]
  } for exactly 1 Node is sat

  canInsertIntoExisting: {
    wellformed_rb
    #treeNode = 1
    some n: Node | insert[n]
  } for exactly 2 Node is sat

  canInsertIntoThreeNodeTree: {
    wellformed_rb
    some root
    some root.left
    some root.right
    some n: Node | insert[n]
  } for exactly 4 Node is sat

  cannotInsertExisting: {
    wellformed_binary => { all n: treeNode | {
      not insert[n]
    } }
  } for exactly 3 Node is theorem

  insertedNodeIsRedLeaf: {
    wellformed_binary => { all n: Node | {
      (insert[n]) => {
        no n.(left' + right')
        n.color' = Red
      }
    } }
  } for 3 Node is theorem

  insertIncreasesTreeSize: {
    (wellformed_binary and (some n: Node | insert[n])) => {
      #treeNode' = add[#treeNode, 1]
    }
  } for 5 Node is theorem

  insertPreservesWellformedBST: {
      (wellformed_binary and (some n: Node | insert[n])) => next_state wellformed_binary
  } for exactly 6 Node is theorem
}