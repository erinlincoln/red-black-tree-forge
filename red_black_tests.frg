#lang forge "final" "jpqtay573rwx8pc6@gmail.com"

open "red_black.frg"

// example sat red-black trees
example oneNodeTree is wellformed_rb for {
    Root = `root
    Node = `root
    Black = `black
    Red = `red
    Color = `black + `red
    
    value = `root -> 0
    no left
    no right
    color = `root -> `black
}
example twoNodeTreeLeft is wellformed_rb for {
    Root = `root
    Node = `root + `n1
    Black = `black
    Red = `red
    Color = `black + `red
    
    value = `root -> 1 + `n1 -> 0
    left = `root -> `n1
    no right
    color = `root -> `black + `n1 -> `red
}
example twoNodeTreeRight is wellformed_rb for {
    Root = `root
    Node = `root + `n1
    Black = `black
    Red = `red
    Color = `black + `red
    
    value = `root -> 1 + `n1 -> 2
    no left
    right = `root -> `n1
    color = `root -> `black + `n1 -> `red
}
example threeNodeBalanced is wellformed_rb for {
    Root = `root
    Node = `root + `n1 + `n2
    Black = `black
    Red = `red
    Color = `black + `red
    
    value = `root -> 1 + `n1 -> 0 + `n2 -> 3
    left = `root -> `n1
    right = `root -> `n2
    color = `root -> `black + `n1 -> `red
            + `n2 -> `red
}

// example unsat red-black trees
example oneNodeTreeRed is not wellformed_rb for {
    Root = `root
    Node = `root
    Black = `black
    Red = `red
    Color = `black + `red
    
    value = `root -> 0
    no left
    no right
    color = `root -> `red   
}
example twoNodeTreeWrongValue is not wellformed_rb for {
    Root = `root
    Node = `root + `n1
    Black = `black
    Red = `red
    Color = `black + `red
    
    value = `root -> 1 + `n1 -> 2
    left = `root -> `n1
    no right
    color = `root -> `black + `n1 -> `red
}
example twoNodeTreeLoops is not wellformed_rb for {
    Root = `root
    Node = `root + `n1
    Black = `black
    Red = `red
    Color = `black + `red
    
    value = `root -> 1 + `n1 -> 2
    left = `root -> `n1 + `n1 -> `root
    no right
    color = `root -> `black + `n1 -> `red
}
example twoNodeTreeNodeAppearsTwice is not wellformed_rb for {
    Root = `root
    Node = `root + `n1
    Black = `black
    Red = `red
    Color = `black + `red
    
    value = `root -> 1 + `n1 -> 2
    left = `root -> `n1
    right = `root -> `n1
    color = `root -> `black + `n1 -> `red
}
example threeNodeUnbalanced is not wellformed_rb for {
    Root = `root
    Node = `root + `n1 + `n2
    Black = `black
    Red = `red
    Color = `black + `red
    
    value = `root -> 1 + `n1 -> 0 + `n2 -> 0
    right = `root -> `n2 + `n2 -> `n1
    color = `root -> `black + `n1 -> `red
            + `n2 -> `red
}
example redAdjacent is not wellformed_rb for {
    Root = `root
    Node = `root + `n1 + `n2 + `n3 + `n4
    Black = `black
    Red = `red
    Color = `black + `red
    
    value = `root -> 1 + `n1 -> 0 + `n2 -> 0 +
            `n3 -> 2 + `n3 -> 2
    right = `root -> `n2 + `n2 -> `n1
    no left
    color = `root -> `black + `n1 -> `red
            + `n2 -> `red    
}
example threeNodeUnbalancedAllBlack is not wellformed_rb for {
    Root = `root
    Node = `root + `n1 + `n2
    Black = `black
    Red = `red
    Color = `black + `red
    
    value = `root -> 1 + `n1 -> 0 + `n2 -> 0
    left = `root -> `n2 + `n2 -> `n1
    no right
    color = `root -> `black + `n1 -> `black
            + `n2 -> `black
}

// all nodes are red or black (coded into node propety)
pred allRedBlack {
    all n: Node | n.color = Red or n.color = Black
}

// all leaves are black
pred blackLeaves {
    all n: Node | {no n.left and no n.right} => n.color = Black
}

// red node implies children are black
pred redImpliesBlackLeftRight {
    all n: Node | {n.color = Red} => {n.left.color = Black and n.right.color = Black}
}

// there is the same number of black nodes between child and two of its leaves
pred sameNumBlack {
    all n1, n2, n3: Node | {isChild[n1, n2] and isChild[n1, n3] 
        and no n2.left and no n2.right and no n3.left and no n3.right} => {numBlack[n1, n2] = numBlack[n1, n3]}
}

// all left nodes are less than right nodes
pred leftLessThanRight {
    all n: Node | {some n.left and some n.right} => {n.left.value < n.right.value}
}

// not a loop (is a tree)
pred isATree {
    all n: Node | n not in n.^(left) or n not in n.^(right)
}

test expect {
    vacuous: {wellformed_rb} is sat
    // 1. all nodes are either red or black
    vacuous: {wellformed_rb => allRedBlack} is sat
    // 2. all leaves are black
    blackLeavesTest: {wellformed_rb => blackLeaves} is sat
    // 3. if a node is red, children are black
    redImpliesBLackLeftRightTest: {wellformed_rb => redImpliesBlackLeftRight} is sat
    // 4. every path from node to descendant is same number of black nodes
    sameNumBlackTest: {wellformed_rb => sameNumBlack} is sat

    // all left nodes are less than right nodes
    leftLessThanRightTest: {wellformed_rb =>leftLessThanRight} is sat
    // is a tree
    treeTest: {wellformed_rb => isATree} is sat

    // as coded, there is no possibility for a sat empty tree (one Root)
    noEmptyTree: {wellformed_rb} for exactly 0 Node is unsat 
    // sat for one node in tree
    oneNode: {wellformed_rb} for exactly 1 Node is sat
    // sat for two nodes in tree
    twoNodes: { wellformed_rb } for exactly 2 Node is sat
    // sat for three nodes in tree
    threeNodes: { wellformed_rb } for exactly 3 Node is sat
    // sat for four nodes in tree
    fourNodes: { wellformed_rb } for exactly 4 Node is sat
    // sat for 5 nodes in tree
    fiveNodes: { wellformed_rb } for exactly 5 Node is sat
    // sat for 7 nodes in tree
    sevenNodes: { wellformed_rb } for exactly 7 Node, 5 Int is sat
    // sat for 10 nodes in tree
    tenNodes: { wellformed_rb } for exactly 10 Node, 5 Int is sat
    
    // sat for two nodes of different colors
    redAndBlackNodes: {
      wellformed_rb
      Red in Node.color
      Black in Node.color
    } for exactly 2 Node is sat
}