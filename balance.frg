#lang forge

open "red_black.frg"

-- Stuff for balancing that we are not currently using


// size of path from parent to child
fun pathSize[parent: Node, child: Node]: Int {
  // path from a node to itself is 0
  (parent = child) => 0
  else #{n: Node | isChild[parent, n] and contains[n, child]}
}

// number of black nodes between parent to child
fun numBlack[parent: Node, child: Node]: Int {
  // path from a node to itself is 0
  (parent = child) => 0
  else #{n: Node | isChild[parent, n] and contains[n, child] and n.color = Black }
}

// calculate height of tree from node
fun treeHeight[n: Node]: Int {
  no n => 0
  else max[{ i: Int | (some n1, n2: Node | contains[n, n1] and contains[n1, n2] and i = pathSize[n1, n2]) }]
}

// maximum difference in height between subtrees at same level within entire tree
fun balancingFactor[n: Node]: Int {
  max[{ i: Int | (some p: Node | contains[n, p] and i = subtract[treeHeight[p.left], treeHeight[p.right]]) }]
}

pred zeroOrOne[i: Int] { i = 1 or i = 0 }

pred isBalanced {
    zeroOrOne[balancingFactor[Root]]
}
