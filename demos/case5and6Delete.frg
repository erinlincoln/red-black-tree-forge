#lang forge

open "../src/tree_electrum.frg"
open "../src/insert.frg"
open "../src/delete.frg"

option max_tracelength 10

// Shows a deletion with multiple recolorings and rotations

//          0B
//        /    \
//      -4B     4B
//     /   \   /   \
//   -6B  -2B 2R   6B
// del^      /  \
//          1B  3B


run { 
    init
    some n1, n2, n3, n4, n5, n6, n7, n8, n9 : Node | {
        value = n1 -> 0 + n2-> -4 + n3 -> 4 + n4->-6 + n5->-2 + n6->2 + n7->6 + n8 -> 1 + n9 -> 3

        left = n1 -> n2 + n2->n4 + n3->n6 + n6->n8
        right = n1 -> n3 + n2->n5 + n3-> n7 + n6->n9

        color = (n1 + n2 + n3 + n4 + n5 + n7 + n8 + n9) -> Black + (n6) -> Red

        delete[n4]
    }
    traces_del
} for 10 Node