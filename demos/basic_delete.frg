#lang forge

open "../src/tree_electrum.frg"
open "../src/delete.frg"

//        0B
//      /   \
//    -1R   1R <- delete

run {
    some n1, n2, n3 : Node | {
        value = n1-> 0 + n2->-1 + n3-> 1
        color = (n1) -> Black + (n2 + n3) -> Red
        left = n1->n2
        right = n1->n3

    }
    traces_del
    delete_transition
} for exactly 3 Node
