#lang forge "final" "jpqtay573rwx8pc6@gmail.com"

// Tests for rotating after insertion

open "tree_electrum.frg"
open "red_black.frg"

option problem_type temporal
option max_tracelength 3

test expect {
  // Try to rotate a tree that involves rotating the root
  exampleLeftLeftRotate: {
    //       3B
    //      /  \
    //     2R   4B
    //    /
    //   1R (inserted)
    //
    // (Note that this tree does not begin well-formed)
    some n1, n2, n3, n4: Node | {
      root = n3
      value = n1 -> 1 + n2 -> 2 + n3 -> 3 + n4 -> 4
      color = (n1 + n2) -> Red + (n3 + n4) -> Black
      left = n3 -> n2 + n2 -> n1
      right = n3 -> n4

      rotate[n1]
    }
  } for exactly 4 Node is sat

    exampleLeftRightRotate: {
    //       3B
    //      /  \
    //     1R   4B
    //       \
    //        2R (inserted)
    //
    // (Note that this tree does not begin well-formed)
    some n1, n2, n3, n4: Node | {
      root = n3
      value = n1 -> 1 + n2 -> 2 + n3 -> 3 + n4 -> 4
      color = (n1 + n2) -> Red + (n3 + n4) -> Black
      left = n3 -> n1
      right = n1 -> n2 + n3 -> n4

      rotate[n2]
    }
  } for exactly 4 Node is sat

  exampleRightRightRotate: {
    //       2B
    //      /  \
    //     1B   3R
    //            \
    //             4R (inserted)
    //
    // (Note that this tree does not begin well-formed)
    some n1, n2, n3, n4: Node | {
      root = n2
      value = n1 -> 1 + n2 -> 2 + n3 -> 3 + n4 -> 4
      color = (n1 + n2) -> Black + (n3 + n4) -> Red
      left = n2 -> n1
      right = n2 -> n3 + n3 -> n4

      rotate[n4]
    }
  } for exactly 4 Node is sat

  exampleRightLeftRotate: {
    //       2B
    //      /  \
    //     1B   4R
    //         /
    //        3R (inserted)
    //
    // (Note that this tree does not begin well-formed)
    some n1, n2, n3, n4: Node | {
      root = n2
      value = n1 -> 1 + n2 -> 2 + n3 -> 3 + n4 -> 4
      color = (n1 + n2) -> Black + (n3 + n4) -> Red
      left = n2 -> n1 + n4 -> n3
      right = n2 -> n4

      rotate[n3]
    }
  } for exactly 4 Node is sat

  rotatePreservesAllNodes: {
    (wellformed_binary and (some n: treeNode | rotate[n])) =>
      treeNode' = treeNode
  } for 5 Node is theorem
}
