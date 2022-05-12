#lang forge

open "../src/tree.frg"
open "../src/insert.frg"
open "../src/delete.frg"

option max_tracelength 10

// Shows a basic delete with 8 Nodes, no recolors or rotations

//          0B
//        /    \
//      -4R     4R
//     /   \   /   \
//   -6B  -2R 2B   6B
//                /
//              5R <- delete

run { 
    some n1, n2, n3, n4, n5, n6, n7, n8 : Node | {
        value = n1 -> 0 + n2-> -4 + n3 -> 4 + n4->-6 + n5->-2 + n6->2 + n7->6 + n8->5

        left = n1 -> n2 + n2->n4 + n3->n6 + n7->n8
        right = n1 -> n3 + n2-> n5 + n3->n7

        color = (n1 + n4 + n5 + n6 + n7) -> Black + (n2 + n3 + n8) -> Red

        delete[n3]
    }
    deleteTraces
} for 8 Node
