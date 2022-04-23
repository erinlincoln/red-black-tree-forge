#lang forge "final" "jpqtay573rwx8pc6@gmail.com"

open "red_black.frg"

// Use a trace length of 2, which is enough to prove properties by induction
// Put longer tests in another file
option max_tracelength 2

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

example allowNodesNotInTree is wellformed_rb for {
    Root = `r
    Node = `r + `n1 + `n2 + `n3
    Black = `black
    Red = `red
    Color = Black + Red

    value = `r -> 0 + `n1 -> 1 + `n2 -> 0 + `n3 -> 2
    no left
    right = `r -> `n1
    color = `r -> Black + `n1 -> Red + `n2 -> Black + `n3 -> Red
}

// Example unsat red-black trees

example rootIsRed is (wellformed_binary and not wellformed_rb) for {
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

// Invalid BST with left value < root value
example twoNodeUnsorted is (wellformed_tree and not wellformed_binary) for {
    Root = `root                   //    1
    Node = `root + `n1             //   /
    value = `root -> 1 + `n1 -> 2  //  2
    left = `root -> `n1
    no right
}

// Invalid BST, but to see that you need to look beyond immediate children
example threeNodeNestedUnsorted is (wellformed_tree and not wellformed_binary) for {
    Root = `root                                //    2
    Node = `root + `n1 + `n2                    //   /
    value = `root -> 2 + `n1 -> 1 + `n2 -> 3    //  1
    left = `root -> `n1                         //   \
    right = `n1 -> `n2                          //    3
}

example twoNodeLoops is not wellformed_tree for {
    Root = `root
    Node = `root + `n1
    value = `root -> 1 + `n1 -> 2
    left = `root -> `n1 + `n1 -> `root
    no right
}

example twoNodeLeftAndRightEdge is not wellformed_tree for {
    Root = `root
    Node = `root + `n1
    value = `root -> 1 + `n1 -> 2
    left = `root -> `n1
    right = `root -> `n1
}

example twoParents is not wellformed_tree for {
    Root = `r                                 //      r
    Node = `r + `n1 + `n2                     //     / \
    value = `r -> 1 + `n1 -> 2 + `n2 -> 3     //    n1  \
    left = `r -> `n1 + `n1 -> `n2             //   /     \
    right = `r -> `n2                         //  ∠-------n2
}

example threeNodeInvalidBlackDepth is (wellformed_binary and not wellformed_rb) for {
    Root = `n3                       //      3B
    Node = `n3 + `n2 + `n1           //     /
    Black = `black                   //    2R
    Red = `red                       //   /
    Color = `black + `red            //  1B

    value = `n1 -> 1 + `n2 -> 2 + `n3 -> 3
    left = `n3 -> `n2 + `n2 -> `n1
    no right
    color = `n1 -> `black + `n2 -> `red + `n3 -> `black
}

example redAdjacent is (wellformed_binary and not wellformed_rb) for {
    Root = `n1                            //  1B
    Node = `n1 + `n2 + `n3                //   \
    Black = `black                        //    2R
    Red = `red                            //     \
    Color = `black + `red                 //      3R
    value = `n1 -> 1 + `n2 -> 2 + `n3 -> 3
    no left
    right = `n1 -> `n2 + `n2 -> `n3
    color = `n1 -> `black + `n2 -> `red + `n3 -> `red
}

example threeNodeAllBlack is (wellformed_binary and not wellformed_rb) for {
    Root = `root             //     2B
    Node = `root + `n1 + `n0 //    /
    Black = `black           //   1B
    Red = `red               //  /
    Color = `black + `red    // 0B
    
    value = `root -> 2 + `n1 -> 1 + `n0 -> 0
    left = `root -> `n1 + `n1 -> `n0
    no right
    color = `root -> `black + `n1 -> `black + `n0 -> `black
}

example parentNodesOutsideOfTree is not wellformed_tree for {
    Root = `r
    Node = `r + `n1 + `n2
    value = `r -> 0 + `n1 -> 1 + `n2 -> 2
    left = `n1 -> `n2
    no right
}

// Example test for testing blackDepth function
example blackDepthTest is {
    wellformed_binary
    blackDepth[Root] = 1
    some n1: Node | n1.value = 1 and blackDepth[n1] = 2
    some n2: Node | n2.value = 2 and blackDepth[n2] = 1
    some n3: Node | n3.value = 3 and blackDepth[n3] = 2
    some n5: Node | n5.value = 5 and blackDepth[n5] = 2
    some n6: Node | n6.value = 6 and blackDepth[n6] = 2
} for {
    Root = `n4                                //           4B
    Node = `n1 + `n2 + `n3 + `n4 + `n5 + `n6  //         /   \
    Black = `b                                //       2R     6B
    Red = `r                                  //      /  \    /
    Color = `b + `r                           //     1B  3B  5R
    
    value = `n1 -> 1 + `n2 -> 2 + `n3 -> 3 + `n4 -> 4 + `n5 -> 5 + `n6 -> 6
    color = `n1 -> `b + `n2 -> `r + `n3 -> `b + `n4 -> `b + `n6 -> `b + `n5 -> `r + `n6 -> `b
    left = `n4 -> `n2 + `n2 -> `n1 + `n6 -> `n5
    right = `n4 -> `n6 + `n2 -> `n3
}

// all nodes are red or black (coded into node propety)
pred allRedBlack {
    all n: Node | n.color = Red or n.color = Black
}

// red node implies children are black
pred redImpliesBlackLeftRight {
    all n: Node | (n.color = Red) => {
        some n.left => n.left.color = Black
        some n.right => n.right.color = Black
    }
}

pred sameBlackDepth {
    // For every node in the tree ...
    all n: Node | inTree[n] => {
        // ... there is some number such that ...
        some d: Int | {
            // ... all children nodes that are "leaves" ...
            //   ["leaf" here means that it contains a NIL child]
            all c: n.children | (no c.left or no c.right) => {
                // ... have the same number of black nodes in the path from n to c, inclusive
                d = #{i: Node | {
                    contains[n, i]
                    contains[i, c]
                    i.color = Black
                }}
            }
        }
    }
}

// All nodes in a left subtree 

test expect {
    vacuous: {wellformed_rb} is sat

    // 1. All nodes are either red or black
    eitherRedBlack: { wellformed_rb => allRedBlack } is theorem

    // 2. All NIL nodes are black
    //    This is implicit with how we are treating nodes; NIL nodes are not explicitly added to the graph
    //    therefore we cannot specify their color explicitly

    // 3. If a node is red, children are black
    redImpliesBlackLeftRightTest: { wellformed_rb => redImpliesBlackLeftRight } is theorem

    // 4. every path from node to descendant is same number of black nodes
    sameNumBlackTest: { wellformed_rb => sameBlackDepth } is theorem

    // all left nodes are less than right nodes
    leftLessThanRightTest: { wellformed_binary => {
        all n: Node | {some n.left and some n.right} => {n.left.value < n.right.value}
    } } is theorem

    // Every node in a left sub-tree has value < parent, and opposite for right
    sortedTree: { wellformed_binary => {
        all n: Node | {
            all p: Node | contains[p.left, n] => n.value < p.value
            all p: Node | contains[p.right, n] => n.value >= p.value
        }
    } } is theorem
    
    // Trees don't contain cycles
    treeTest: { wellformed_tree => (all n: Node | n not in n.^(left + right)) } is theorem

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

    uncleTest: {
        wellformed_tree => {
            all n: Node | {
                n.uncle in n.parent.parent.immediateChildren
                lone n.uncle
                some n.parent => n.uncle != n.parent
            }
        }
    } is theorem

    insertPreservesWellformedBST: {
        (wellformed_binary and (some n: Node | insert[n])) => next_state wellformed_binary
    } for exactly 4 Node is theorem

    // PROPERTY TESTS
    // some nextInsertNode implies tree is not wellformed
    nextInsertImpliesWellformed: {
        some nextInsertNode => not wellformed_rb
    } is theorem
}