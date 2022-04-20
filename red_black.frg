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

// find 'uncle' of node
fun uncle: set Node -> Node {
  { child, uncle: Node | child.parent.parent.left = uncle or child.parent.parent.right = child}
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

fun intermediateBlack[start: Node, end: Node]: Node {
  { n: Node | {
    n.color = Black
    isChild[start, n]
    isChild[n, end]
  }}
}

fun blackDepth[n: Node]: Int {
  #(intermediateBlack[Root, n])
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

// HERE IS THE INITIAL WORK FOR INSERTION:
// The basic idea is that the first transition is node_added where (hopefully)
// nothing changes except that there is now a new node in the tree at the bottom,
// such that it is still a binary tree. I'm not sure if this transition state needs
// to be separated into the steps that it takes in order to add the node to the tree.

// Then, the predicate insertion_rotation_recolor, performs the intermediary steps
// where the node that was added, and the surrounding nodes, are rotated and recolored
// based on how they are positioned in the tree.

// The main thing that still remains (that I just breifly sketched out in the prediate
// insertion) is the fact that these transition states happen for indeterminate amounts of
// time until the wellformed_rb predicate is satisfied. One of the parts that I am most
// challenged by for filling this out is the fact that the insertion_rotation_recolor
// predicate will have to take in different nodes for n during each transition. The node
// that it will have to take in can be found using the function next_node_to_restructure,
// however, I still have not figured out how to put it all together

pred node_added[n : Node] {

    -- tree must be wellformed red-black before node is added
    wellformed_rb

    -- the resulting tree must still be a wellformed_tree
    -- Is it okay that this is just automatically wellformed_binary??
    wellformed_binary'

    -- the added noded cannot be in the tree
    n != Root
    no n.parent
    no n.left
    no n.right
  
    -- the nodes remain the same (unless they have gained a child)
    all n1 : Node | {
      n1.value = n1.value'
      some n1.left => n1.left = n1.left' else {
        some n1.left' => n1.left = n
      }
      some n1.right => n1.right = n1.right' else {
        some n1.right' => n1.right = n
      }
      n1.color = n1.color'
    }

    -- the inserted node should be red
    n.color' = Red

    -- DO WE NEED ANYTHING TO CHECK THAT THE NODE ISN'T ADDED IN IN MULTIPLE SPOTS?
}

fun next_node_to_restructure: set Node -> Node {
    { prev, next : Node | prev.uncle.color = Red => next = prev.parent.parent else next = prev.parent }
}

pred insertion_rotation_recolor[n : Node] {

    -- If n is the root, then it's color is simply changed to black (insertion is complete)
    n = Root => n.color' = Black

    -- If n is not the root and the parent is also Red, then rotation/recoloring must take place 
    {
        n != Root
        n.parent.color = Red
    } => {
        n.uncle.color = Red => {
            -- recolor the uncle, parent, and grandparent
            n.parent.color' = Black
            n.uncle.color' = Black
            n.parent.parent.color' = Red

            -- Need to swap n for n.parent.parent as n being inserted
        } else {
            -- Left Left case
            n.parent.parent.left.left = n => {
                n.parent.parent.left' = n.parent.right
                n.parent.parent.right' = n.uncle

                n.parent.left' = n
                n.parent.right' = n.parent.parent
                
                n.uncle.left' = n.uncle.left
                n.uncle.right' = n.uncle.right

                n.left' = n.left
                n.right' = n.right

                n.parent.parent.color' = n.parent.color
                n.parent.color' = n.parent.parent.color

                n.color' = n.color
                n.uncle.color' = n.uncle.color

                -- DOES ANYTHING ELSE HAPPEN?
            }
            -- Left Right case
            n.parent.parent.left.right = n => {
                n.parent.parent.left' = n.right
                n.parent.parent.right' = n.uncle

                n.parent.left' = n.parent.left
                n.parent.right' = n.left

                n.uncle.left' = n.uncle.left
                n.uncle.right' = n.uncle.right

                n.left' = n.parent
                n.right' = n.parent.parent

                n.parent.parent.color' = n.color
                n.color = n.parent.parent.color

                n.parent.color' = n.parent.color
                n.uncle.color' = n.uncle.color
            }
            -- Right Right case
            n.parent.parent.right.right = n => {
                n.parent.parent.left' = n.uncle
                n.parent.parent.right' = n.parent.left

                n.parent.left' = n.parent.parent
                n.parent.right' = n

                n.uncle.left' = n.uncle.left
                n.uncle.right' = n.uncle.right

                n.left' = n.left
                n.right' = n.right

                n.parent.parent.color' = n.parent.color
                n.parent.color' = n.parent.parent.color

                n.color' = n.color
                n.uncle.color' = n.uncle.color
            }
            -- Right Left case
            n.parent.parent.right.left = n => {
                n.parent.parent.left' = n.uncle
                n.parent.parent.right' = n.left

                n.parent.left' = n.right
                n.parent.right' = n.parent.right

                n.uncle.left' = n.uncle.left
                n.uncle.right' = n.uncle.right

                n.left' = n.parent.parent
                n.right' = n.parent

                n.parent.parent.color' = n.color
                n.color' = n.parent.parent.color

                n.parent.color' = n.parent.color
                n.uncle.color' = n.uncle.color
            }
            -- Needto swap n for n.parent as node being inserted
        }
    } else {
      -- If no restructuring happens, n, the parent, uncle, and grandparent, must
      -- all stay the same
      n.parent.parent.left' = n.parent.parent.left
      n.parent.parent.right' = n.parent.parent.right

      n.parent.left' = n.parent.left
      n.parent.right' = n.parent.right

      n.uncle.left' = n.uncle.left
      n.uncle.right' = n.uncle.right

      n.left' = n.left
      n.right' = n.right

      n.parent.parent.color' = n.parent.parent.color
      n.parent.color' = n.parent.color
      n.uncle.color' = n.uncle.color
      n.color' = n.color
    }

    -- Constrain all of the other nodes (not grandparent, parent, uncle, or n) to
    -- remain the same
    all n1 : Node | {
        {
            n1 != n.parent.parent
            n1 != n.parent
            n1 != n.uncle
            n1 != n
        } => {
            n1.left' = n1.left
            n1.right' = n1.right
            n1.color' = n1.color
        }
        n1.value' = n1.value
    }
}

pred insertion[n : Node] {

    node_added[n]

    -- Somehow need to be changing that n is no longer the same n
    -- (can use the function next_node_to_restructure)
    insertion_rotation_recolor[n] until wellformed_rb

}

run { wellformed_rb} for exactly 5 Node

