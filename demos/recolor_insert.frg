#lang forge

open "../src/tree_electrum.frg"
open "../src/insert.frg"

//        0B
//     /      \
//   -2B       3B
//            /  \
//          2R   4R
//         /
//       1R <- Insert

run {
    some n1, n2, n3, n4, n5, n6 : Node | {
      value = n1 -> 0 + n2-> -2 + n3 -> 3 + n4->2 + n5->4 + n6->1

      left = n1 -> n2 + n3->n4
      right = n1 -> n3 + n3-> n5

      color = (n1 + n2 + n3) -> Black + (n4 + n5 + n6) -> Red
    }
    traces
    insert_transition
    next_state recolor_transition
    next_state next_state terminate_transition
} for exactly 6 Node