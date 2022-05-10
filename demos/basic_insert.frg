#lang forge

open "../src/tree_electrum.frg"
open "../src/insert.frg"

//        0B
//     /      \
//   -2R       2R
//   /  \     /  \
// -3B -1B   1B   3B
//                  \
//                  4R <- Insert

run {
    some n1, n2, n3, n4, n5, n6, n7, n8 : Node | {
      value = n1 -> 0 + n2-> -2 + n3 -> 2 + n4->-3 + n5->-1 + n6->1 + n7->3 
        +n8->4

      left = n1 -> n2 + n2->n4 + n3->n6
      right = n1 -> n3 + n2-> n5 + n3->n7

      color = (n1 + n4 + n5 + n6 + n7) -> Black + (n2 + n3 + n8) -> Red
    }
    traces
    insert_transition
    next_state terminate_transition
} for exactly 8 Node