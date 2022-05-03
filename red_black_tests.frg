#lang forge "final" "jpqtay573rwx8pc6@gmail.com"

open "red_black.frg"

// Use a trace length of 2, which is enough to prove properties by induction
// Put longer tests in another file
option max_tracelength 2

inst baseInst {
    Tree = `tree
    Black = `black
    Red = `red
    Color = Black + Red
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

example emptyTree is wellformed_rb for {
    baseInst
    no Node
    no left
    no right
}

// 1B
example oneNodeTree is wellformed_rb for {
    singleRootInst
    no left
    no right
    color = `n1 -> Black
}

//   2B
//  /
// 1R
example twoNodeTreeLeft is wellformed_rb for {
    twoNodeInst
    rootNode = Tree -> `n2
    left = `n2 -> `n1
    no right
    color = `n2 -> Black + `n1 -> Red
}

// 1B
//   \
//    2R
example twoNodeTreeRight is wellformed_rb for {
    twoNodeInst
    rootNode = Tree -> `n1
    no left
    right = `n1 -> `n2
    color = `n1 -> Black + `n2 -> Red
}

//   2B
//  /  \
// 1R  3R
example threeNodeBalanced is wellformed_rb for {
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
example allowNodesNotInTree is wellformed_rb for {
    fourNodeInst
    rootNode = Tree -> `n1
    no left
    right = `n1 -> `n2
    color = `n1 -> Black + `n2 -> Red + `n3 -> Black + `n4 -> Red
}

// Example unsat red-black trees

example rootIsRed is (wellformed_binary and not wellformed_rb) for {
    singleRootInst
    no left
    no right
    color = `n1 -> Red
}

// Invalid BST with left value < root value
//    1
//   /
//  2
example twoNodeUnsorted is (wellformed_tree and not wellformed_binary) for {
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
example threeNodeNestedUnsorted is (wellformed_tree and not wellformed_binary) for {
    threeNodeInst
    rootNode = Tree -> `n2
    left = `n2 -> `n1
    right = `n1 -> `n3
}

//   n1
//  /  \
// n2   |
//   \_/
example twoNodeLoops is not wellformed_tree for {
    twoNodeInst
    rootNode = Tree -> `n1
    left = `n1 -> `n2
    right = `n2 -> `n1
}

//   n1
//  /  \
//  \  /
//   n2
example twoNodeLeftAndRightEdge is not wellformed_tree for {
    twoNodeInst
    rootNode = Tree -> `n1
    left = `n1 -> `n2
    right = `n1 -> `n2
}

 //      n2
 //     /  \
 //    n1   \
 //   /      \
 //  ∠--------n3
example twoParents is not wellformed_tree for {
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
example threeNodeInvalidBlackDepth is (wellformed_binary and not wellformed_rb) for {
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
example redAdjacent is (wellformed_binary and not wellformed_rb) for {
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
example threeNodeAllBlack is (wellformed_binary and not wellformed_rb) for {
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
example parentNodesOutsideOfTree is not wellformed_tree for {
    threeNodeInst
    rootNode = Tree -> `n1
    left = `n2 -> `n3
    no right
}

// Example test for testing blackDepth function
//       4B
//     /   \
//   2R     6B
//  /  \    /
// 1B  3B  5R
example blackDepthTest is {
    wellformed_binary
    blackDepth[root] = 1
    some n1: Node | n1.value = 1 and blackDepth[n1] = 2
    some n2: Node | n2.value = 2 and blackDepth[n2] = 1
    some n3: Node | n3.value = 3 and blackDepth[n3] = 2
    some n5: Node | n5.value = 5 and blackDepth[n5] = 2
    some n6: Node | n6.value = 6 and blackDepth[n6] = 2
} for {
    baseInst
    rootNode = Tree -> `n4
    Node = `n1 + `n2 + `n3 + `n4 + `n5 + `n6
    value = `n1 -> 1 + `n2 -> 2 + `n3 -> 3 + `n4 -> 4 + `n5 -> 5 + `n6 -> 6
    color = `n1 -> Black + `n2 -> Red + `n3 -> Black +
            `n4 -> Black + `n5 -> Red + `n6 -> Black
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
                    i in (n + n.children)
                    c in (i + i.children)
                    i.color = Black
                }}
            }
        }
    }
}

fun log[nodes: set Node] : Int {
    let count = #{n : Node | n in nodes} | {
        
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
        all n: Node | {some n.left and some n.right} => {n.left.value <= n.right.value}
    } } is theorem

    // Every node in a left sub-tree has value <= parent, and opposite for right
    sortedTree: { wellformed_binary => {
        all p: Node | {
            all l: (p.left + p.left.children) | l.value <= p.value
            all r: (p.right + p.right.children) | r.value >= p.value
        }
    } } is theorem
    
    // Trees don't contain cycles
    treeTest: { wellformed_tree => (all n: Node | n not in n.^(left + right)) } is theorem

    // sat for an empty tree (no root)
    emptyTree: {wellformed_rb} for exactly 0 Node is sat 
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
}