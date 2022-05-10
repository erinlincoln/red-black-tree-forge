#lang forge "final" "jpqtay573rwx8pc6@gmail.com"

// Tests for recoloring after insertion. Includes both examples and properties
// of trees that will or have undergone recoloring.

open "../src/tree_electrum.frg"
open "../src/insert.frg"

option problem_type temporal
option max_tracelength 3

test expect {
  // Try to recolor a tree that involves recoloring the root
  exampleRecoloring: {
    //       3B
    //      /  \
    //     2R   4R
    //    /
    //   1R (inserted)
    some n1, n2, n3, n4: Node | {
      root = n3

      value = n1 -> 1 + n2 -> 2 + n3 -> 3 + n4 -> 4
      color = (n1 + n2 + n4) -> Red + n3 -> Black

      left = n3 -> n2 + n2 -> n1
      right = n3 -> n4

      recolor[n1]

      next_state {
        n1.color = Red
        n2.color = Black
        n4.color = Black
        n3.color = Red
      }
    }
  } for exactly 4 Node is sat

  // Try recolor a tree that doesn't involve changing the root node
  exampleRecoloringSubtree: {
    //          5B
    //         /  \
    //       3B    6B
    //      /  \
    //     2R   4R
    //    /
    //   1R (inserted)
    some n1, n2, n3, n4, n5, n6: Node | {
      root = n5

      value = n1 -> 1 + n2 -> 2 + n3 -> 3 + n4 -> 4 + n5 -> 5 + n6 -> 6
      color = (n1 + n2 + n4) -> Red + (n3 + n5 + n6) -> Black

      left = n5 -> n3 + n3 -> n2 + n2 -> n1
      right = n5 -> n6 + n3 -> n4

      recolor[n1]

      next_state {
        color = (n1 + n3) -> Red + (n2 + n4 + n5 + n6) -> Black
        wellformed_rb
      }
    }
  } for exactly 6 Node is sat

  neverCanRecolorIfWellformed: {
    wellformed_rb => {
      no n: Node | recolor[n]
    }
  } for 6 Node is theorem

  recoloringOnlyChangesThreeNodeColors: {
    (wellformed_tree and (some n: Node | recolor[n])) => {
      left' = left
      right' = right
      #((color' - color).Color) <= 3
    }
  } for 8 Node is theorem

  // Note that recoloring after an insert *may* produce a correct tree,
  // but this is not always the case (for example, if the root is colored red)
  insertAndRecolorCanProduceWellformedRBT: {
    {
      wellformed_rb
      some n: Node | { insert[n] and next_state recolor[n] }
    } => next_state next_state wellformed_rb
  } for 8 Node is sat
}
