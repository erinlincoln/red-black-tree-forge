#lang forge

open "red_black.frg"
option max_tracelength 4

//               0B
//            /      \
//         -2B       2B
//        /  \      /  \
//     -4R    -1B  1B   3B
//     /  \
//   -5B  -3B          
//  /
// -6R

inst TallTree {
  Black = `b
  Red = `r
  Color = Black + Red

  Node = `m7 + `m6 + `m5 + `m4 + `m3 + `m2 + `m1 + `z
       + `p1 + `p2 + `p3
  Tree = `tree

  rootNode = `tree -> `z

  value = `m7 -> -7 + `m6 -> -6 + `m5 -> -5 + `m4 -> -4
        + `m3 -> -3 + `m2 -> -2 + `m1 -> -1 + `z -> 0
        + `p1 -> 1 + `p2 -> 2 + `p3 -> 3
  
  left = `z -> `m2 + `m2 -> `m4 + `m4 -> `m5 + `m5 -> `m6
       + `p2 -> `p1
  right = `z -> `p2 + `p2 -> `p3
        + `m2 -> `m1 + `m4 -> `m3

  color = `m7 -> `r + `m6 -> `r + `m5 -> `b + `m4 -> `r + `m3 -> `b
        + `m2 -> `b + `m1 -> `b + `z -> `b + `p1 -> `b + `p2 -> `b
        + `p3 -> `b
}

example tallTree is wellformed_rb for TallTree

// An example of an insert operation that requires a rotation and a recoloring to
// restore the RBT properties.

//               0B
//            /      \
//         -2B       2B
//        /  \      /  \
//     -4R    -1B  1B   3B
//     /  \
//   -6B  -3B          
//  /   \
// -7R  -5R
test expect {
  recolorAndRotate: {
    some m8, m7, m6, m5, m4, m3, m2, m1, z, p1, p2, p3: Node | {
      value = m8 -> -8 + m7 -> -7 + m6 -> -6 + m5 -> -5 + m4 -> -4
        + m3 -> -3 + m2 -> -2 + m1 -> -1 + z -> 0
        + p1 -> 1 + p2 -> 2 + p3 -> 3

      left = z -> m2 + m2 -> m4 + m4 -> m6 + m6 -> m7
           + p2 -> p1
      right = z -> p2 + p2 -> p3
            + m2 -> m1 + m4 -> m3 + m6 -> m5

      color = (z + m6 + m3 + m2 + m1 + p1 + p2 + p3) -> Black +
              (m8 + m7 + m5 + m4) -> Red
    }

    wellformed_rb
    traces

    insert_transition
    next_state recolor_transition
    next_state next_state rotate_transition
  } for exactly 12 Node is sat
}