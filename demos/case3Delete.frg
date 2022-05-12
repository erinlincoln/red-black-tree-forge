#lang forge

open "../src/tree.frg"
open "../src/insert.frg"
open "../src/delete.frg"

option max_tracelength 10

run { 
    init
    some n1, n2, n3, n4, n5, n6, n7 : Node | {
        value = n1 -> 0 + n2-> -4 + n3 -> 4 + n4->-6 + n5->-2 + n6->2 + n7->6

        left = n1 -> n2 + n2->n4 + n3->n6
        right = n1 -> n3 + n2->n5 + n3-> n7

        color = (n1 + n2 + n3 + n4 + n5 + n6 + n7) -> Black

        delete[n6]
    }
    deleteTraces
} for 8 Node