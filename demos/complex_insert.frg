#lang forge

open "../src/tree.frg"
open "../src/insert.frg"
option max_tracelength 4

// An example of an insert operation that requires a rotation and a recoloring to
// restore the RBT properties.
//
// Initial tree:
//               0B
//            /      \
//         -2B       2B
//        /  \      /  \
//     -4R    -1B  1B   3B
//     /  \
//   -6B  -3B          
//  /   \
// -7R  -5R
//
// Insert, then recolor, then rotate

run {
    some m8, m7, m6, m5, m4, m3, m2, m1, z, p1, p2, p3: Node | {
        value = m8 -> -8 + m7 -> -7 + m6 -> -6 + m5 -> -5 + m4 -> -4
              + m3 -> -3 + m2 -> -2 + m1 -> -1 + z -> 0
              + p1 -> 1 + p2 -> 2 + p3 -> 3

        left = z -> m2 + m2 -> m4 + m4 -> m6 + m6 -> m7
             + p2 -> p1
        right = z -> p2 + p2 -> p3
              + m2 -> m1 + m4 -> m3 + m6 -> m5

        color = (z + m6 + m3 + m2 + m1 + p1 + p2 + p3) -> Black
              + (m8 + m7 + m5 + m4) -> Red
    }

    wellformedRBT
    insertTraces

    insertTransition
    next_state insertRecolorTransition
    next_state next_state insertRotateTransition
    next_state next_state next_state terminateTransition
} for exactly 12 Node
