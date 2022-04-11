#lang forge "final" "jpqtay573rwx8pc6@gmail.com"


// Node of each graph - left branch, right branch, and color
sig Node {
    value: one Int,
    left: lone Node,
    right: lone Node,
    color: one Color
}

// Root of tree (assuming no empty tree)
one sig Root extends Node {}

// Color of nodes
abstract sig Color {}
one sig Black, Red extends Color {}

// find parent of node
fun parent: set Node -> Node {
    { child, parent: Node | parent.left = child or parent.right = child }
}

// left/right contains parent-> child pair
pred isChild[parent: Node, child: Node] {
    parent->child in ^(left + right)
}

// parent and child are the same or are parent/child
pred contains[parent: Node, child: Node] {
    parent = child or isChild[parent, child]
}

// max of set
fun max[i: Int]: Int {
  { j: Int | j in i and (all k: i | k <= j) }
}

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

// calculate the number of black nodes going through from node to end of tree
fun blackHeight[n: Node]: Int {
  no n => 0
  else max[{ i: Int | {
      some n1, n2: Node | {
          contains[n, n1] and contains[n1, n2]
          i = numBlack[n1, n2]
        }
      }
  }]
}

// maximum difference in height between subtrees at same level within entire tree
fun balancingFactor[n: Node]: Int {
  max[{ i: Int | (some p: Node | contains[n, p] and i = subtract[treeHeight[p.left], treeHeight[p.right]]) }]
}

pred zeroOrOne[i: Int] { i = 1 or i = 0 }

pred isBalanced {
    zeroOrOne[balancingFactor[Root]]
}

// wellformed tree
pred wellformed_tree {
    // root reaches everything
    all n: Node | { n = Root or (Root -> n in ^(left + right)) }
    
    // not reachable from itself
    all n : Node | n not in (n.^left + n.^right)
    
    // left and right are different
    all n: Node | no (n.left & n.right)
 
    // only one parent, root has no parent
    all n: Node | (n = Root) => { no n.parent }
        else { one n.parent }
}

// wellformed binary search tree
pred wellformed_binary {
    // is a wellformed tree
    wellformed_tree
    
    // left is less than parent, right is greater than parent
    all n : Node | {
        some n.left => {n.left.value < n.value}
        some n.right => {n.right.value > n.value}
    }
}

pred allEqual[values: Int] {
    some i: Int | {
        all v: values | i = v
    }
}

// wellformed red black tree
pred wellformed_rb {
    
    // red-black tree must be a wellformed binary search trees
    wellformed_binary

    // Root is always black
    Root.color = Black

    // No two adjacent red nodes
    all n : Node | n.color = Red => {
        (n.parent.color != Red)
        (n.left != Red)
        (n.right != Red)
    }

    // runtime??
    // Any path from node to Null goes through number of black nodes
    all n: Node | {
        some height: Int | {
            all c: Node | {
                (contains[n, c] and (no c.left or no c.right)) => {
                    height = numBlack[n, c]
                }
            }
        }
    }
        
    // We do not include a constraint about the leaf nodes being black because
    // it is implied that if a Node has no left or right field then, that leaf
    // will be black
}


run { wellformed_rb} for exactly 5 Node

