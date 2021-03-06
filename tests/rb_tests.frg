#lang forge "final" "jpqtay573rwx8pc6@gmail.com"

open "../src/tree.frg"

// Show basic examples and properties of a static RBT.

// Since these tests are on static trees, just use one instance
option max_tracelength 1

inst baseInst {
    Tree = `tree
    Black = `black
    Red = `red
    Color = Black + Red
    DoubleBlack = `DoubleBlack
    IsNull = `isnull

    no type
    no nullNode
}

inst singleRootInst {
    baseInst
    Node = `n1
    value = `n1 -> 1
    rootNode = Tree -> `n1
}

inst twoNodeInst {
    baseInst
    Node = `n1 + `n2
    value = `n1 -> 1 + `n2 -> 2
}

inst threeNodeInst {
    baseInst
    Node = `n1 + `n2 + `n3
    value = `n1 -> 1 + `n2 -> 2 + `n3 -> 3
}

inst fourNodeInst {
    baseInst
    Node = `n1 + `n2 + `n3 + `n4
    value = `n1 -> 1 + `n2 -> 2 + `n3 -> 3 + `n4 -> 4
}

// example sat red-black trees

example emptyTree is wellformedRBT for {
    baseInst
    no Node
    no left
    no right
}

// 1B
example oneNodeTree is wellformedRBT for {
    singleRootInst
    no left
    no right
    color = `n1 -> Black
}

//   2B
//  /
// 1R
example twoNodeTreeLeft is wellformedRBT for {
    twoNodeInst
    rootNode = Tree -> `n2
    left = `n2 -> `n1
    no right
    color = `n2 -> Black + `n1 -> Red
}

// 1B
//   \
//    2R
example twoNodeTreeRight is wellformedRBT for {
    twoNodeInst
    rootNode = Tree -> `n1
    no left
    right = `n1 -> `n2
    color = `n1 -> Black + `n2 -> Red
}

//   2B
//  /  \
// 1R  3R
example threeNodeBalanced is wellformedRBT for {
    threeNodeInst
    rootNode = Tree -> `n2
    left = `n2 -> `n1
    right = `n2 -> `n3
    color = `n2 -> Black + `n1 -> Red + `n3 -> Red
}

// 1B
//   \
//    2R
//
// Not in tree: 3B 4R
example allowNodesNotInTree is wellformedRBT for {
    fourNodeInst
    rootNode = Tree -> `n1
    no left
    right = `n1 -> `n2
    color = `n1 -> Black + `n2 -> Red + `n3 -> Black + `n4 -> Red
}

// Example unsat red-black trees

example rootIsRed is (wellformedBST and not wellformedRBT) for {
    singleRootInst
    no left
    no right
    color = `n1 -> Red
}

// Invalid BST with left value < root value
//    1
//   /
//  2
example twoNodeUnsorted is (wellformedTree and not wellformedBST) for {
    twoNodeInst
    rootNode = Tree -> `n1
    left = `n1 -> `n2
    no right
}

// Invalid BST, but to see that you need to look beyond immediate children
//    2
//   /
//  1
//   \
//    3
example threeNodeNestedUnsorted is (wellformedTree and not wellformedBST) for {
    threeNodeInst
    rootNode = Tree -> `n2
    left = `n2 -> `n1
    right = `n1 -> `n3
}

//   n1
//  /  \
// n2   |
//   \_/
example twoNodeLoops is not wellformedTree for {
    twoNodeInst
    rootNode = Tree -> `n1
    left = `n1 -> `n2
    right = `n2 -> `n1
}

//   n1
//  /  \
//  \  /
//   n2
example twoNodeLeftAndRightEdge is not wellformedTree for {
    twoNodeInst
    rootNode = Tree -> `n1
    left = `n1 -> `n2
    right = `n1 -> `n2
}

 //      n2
 //     /  \
 //    n1   \
 //   /      \
 //  ???--------n3
example twoParents is not wellformedTree for {
    threeNodeInst
    rootNode = Tree -> `n2
    left = `n2 -> `n1 + `n1 -> `n3
    right = `n2 -> `n3
}

//      3B
//     /
//    2R
//   /
//  1B
example threeNodeInvalidBlackDepth is (wellformedBST and not wellformedRBT) for {
    threeNodeInst
    rootNode = Tree -> `n3
    left = `n3 -> `n2 + `n2 -> `n1
    no right
    color = `n1 -> Black + `n2 -> Red + `n3 -> Black
}

//  1B
//   \
//    2R
//     \
//      3R
example redAdjacent is (wellformedBST and not wellformedRBT) for {
    threeNodeInst
    rootNode = Tree -> `n1
    no left
    right = `n1 -> `n2 + `n2 -> `n3
    color = `n1 -> Black + `n2 -> Red + `n3 -> Red
}

//     3B
//    /
//   2B
//  /
// 1B
example threeNodeAllBlack is (wellformedBST and not wellformedRBT) for {
    threeNodeInst
    rootNode = Tree -> `n3
    left = `n3 -> `n2 + `n2 -> `n1
    no right
    color = `n1 -> Black + `n2 -> Black + `n3 -> Black
}

// Root      Outside
//  n1         n2
//            /
//           n3
example parentNodesOutsideOfTree is not wellformedTree for {
    threeNodeInst
    rootNode = Tree -> `n1
    left = `n2 -> `n3
    no right
}

//       4B
//     /   \
//   2R     6B
//  /  \    /
// 1B  3B  5R
inst SixNodeExample {
    baseInst
    rootNode = Tree -> `n4
    Node = `n1 + `n2 + `n3 + `n4 + `n5 + `n6
    value = `n1 -> 1 + `n2 -> 2 + `n3 -> 3 + `n4 -> 4 + `n5 -> 5 + `n6 -> 6
    color = `n1 -> Black + `n2 -> Red + `n3 -> Black +
            `n4 -> Black + `n5 -> Red + `n6 -> Black
    left = `n4 -> `n2 + `n2 -> `n1 + `n6 -> `n5
    right = `n4 -> `n6 + `n2 -> `n3
}

example blackDepthTest is {
    wellformedBST
    blackDepth[root] = 1
    some n1: Node | n1.value = 1 and blackDepth[n1] = 2
    some n2: Node | n2.value = 2 and blackDepth[n2] = 1
    some n3: Node | n3.value = 3 and blackDepth[n3] = 2
    some n5: Node | n5.value = 5 and blackDepth[n5] = 2
    some n6: Node | n6.value = 6 and blackDepth[n6] = 2
} for SixNodeExample

example siblingExample is {
    wellformedBST
    some n1, n3: Node | {
        n1.value = 1
        n3.value = 3
        n1.sibling = n3
        n3.sibling = n1
    }

    some n2, n6: Node | {
        n2.value = 2
        n6.value = 6
        n2.sibling = n6
        n6.sibling = n2
    }

    some n5: Node | n5.value = 5 and no n5.sibling
    some n4: Node | n4.value = 4 and no n4.sibling
} for SixNodeExample

// Example test for testing blackDepth function
//       4B
//     /   \
//   2R     6B
//  /  \    / \
// 1B  3B  5R  7R
inst SevenNodeExample {
    baseInst
    rootNode = Tree -> `n4
    Node = `n1 + `n2 + `n3 + `n4 + `n5 + `n6 + `n7
    value = `n1 -> 1 + `n2 -> 2 + `n3 -> 3 + `n4 -> 4 + `n5 -> 5 + `n6 -> 6 + `n7 -> 7
    color = `n1 -> Black + `n2 -> Red + `n3 -> Black +
            `n4 -> Black + `n5 -> Red + `n6 -> Black + `n7 -> Red
    left = `n4 -> `n2 + `n2 -> `n1 + `n6 -> `n5
    right = `n4 -> `n6 + `n2 -> `n3 + `n6 -> `n7
}

example farNearNephewExample is {
    wellformedBST

    some n1, n2, n3, n5, n6, n7: Node | {
        (n1 -> 1 + n2 -> 2 + n3 -> 3 + n5 -> 5 + n6 -> 6 + n7 -> 7) in value

        n6.farNephew = n1
        n6.nearNephew = n3

        n2.farNephew = n7
        n2.nearNephew = n5

        no (Node - (n2 + n6)).farNephew
        no (Node - (n2 + n6)).nearNephew
    }
} for SevenNodeExample

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
    all n: Node | (n in treeNode) => {
        // ... there is some number such that ...
        some d: Int | {
            // ... all children nodes that are "leaves" ...
            //   ["leaf" here means that it contains a NIL child]
            all c: n.children | (no c.left or no c.right) => {
                // ... have the same number of black nodes in the path from n to c, inclusive
                d = #{i: Node | {
                    i in (n + n.children)
                    c in (i + i.children)
                    i.color = Black
                }}
            }
        }
    }
}

test expect {
    vacuous: {wellformedRBT} is sat

    // 1. All nodes are either red or black
    eitherRedBlack: { wellformedRBT => allRedBlack } is theorem

    // 2. All NIL nodes are black
    //    This is implicit with how we are treating nodes; NIL nodes are not explicitly added to the graph
    //    therefore we cannot specify their color explicitly

    // 3. If a node is red, children are black
    redImpliesBlackLeftRightTest: { wellformedRBT => redImpliesBlackLeftRight } is theorem

    // 4. every path from node to descendant is same number of black nodes
    sameNumBlackTest: { wellformedRBT => sameBlackDepth } is theorem

    // all left nodes are less than right nodes
    leftLessThanRightTest: { wellformedBST => {
        all n: Node | {
            (some n.left and some n.right) and
            (no n.left.nullNode and no n.right.nullNode and no n.nullNode)
        } => {n.left.value <= n.right.value}
    } } is theorem

    // Every node in a left sub-tree has value <= parent, and opposite for right
    sortedTree: { wellformedBST => {
        all p: Node | no p.nullNode => {
            all l: (p.left + p.left.children) | no l.nullNode => l.value <= p.value
            all r: (p.right + p.right.children) | no r.nullNode => r.value >= p.value
        }
    } } is theorem
    
    // Trees don't contain cycles
    treeTest: { wellformedTree => (all n: Node | n not in n.children) } is theorem

    // sat for an empty tree (no root)
    emptyTree: {wellformedRBT} for exactly 0 Node is sat 
    // sat for one node in tree
    oneNode: {wellformedRBT} for exactly 1 Node is sat
    // sat for two nodes in tree
    twoNodes: { wellformedRBT } for exactly 2 Node is sat
    // sat for three nodes in tree
    threeNodes: { wellformedRBT } for exactly 3 Node is sat
    // sat for four nodes in tree
    fourNodes: { wellformedRBT } for exactly 4 Node is sat
    // sat for 5 nodes in tree
    fiveNodes: { wellformedRBT } for exactly 5 Node is sat
    // sat for 7 nodes in tree
    sevenNodes: { wellformedRBT } for exactly 7 Node, 5 Int is sat
    // sat for 10 nodes in tree
    tenNodes: { wellformedRBT } for exactly 10 Node, 5 Int is sat
    
    // sat for two nodes of different colors
    redAndBlackNodes: {
        wellformedRBT
        Red in Node.color
        Black in Node.color
    } for exactly 2 Node is sat

    // Test that the uncle function behaves as expected
    uncleTest: {
        wellformedTree => {
            all n: Node | {
                n.uncle in n.parent.parent.immediateChildren
                lone n.uncle
                some n.parent => n.uncle != n.parent
            }
        }
    } is theorem

    // Test that the sibling function behaves as expected
    siblingTest: {
        wellformedTree => {
            no root.sibling
            all n: Node | lone n.sibling
            all n1, n2: Node | {
                (n1.sibling = n2) => n2.sibling = n1
            }
        }
    } for 7 Node is theorem

    // Test that the far and near nephew functions behaves as expected
    farNearNephewTest: {
        wellformedTree => {
            no root.farNephew
            no root.nearNephew

            all n: Node | {
                no n.farNephew or n.farNephew != n.nearNephew
                lone n.farNephew
            }
        }
    } for 7 Node is theorem

}