#lang forge "final" "jpqtay573rwx8pc6@gmail.com"

open "tree_electrum.frg"

fun grandparent: set Node -> Node {
    parent.parent
}

fun sibling: set Node -> Node {
    { n, sib : Node | {
        sib != n
        sib in n.parent.immediateChildren}
    }
}

fun farNephew: set Node -> Node {
    { n, nephew : Node | {
        n.parent.left = n => {
            n.sibling.right = nephew
        } else {
            n.sibling.left = nephew
        }
    }}
}

fun nearNephew: set Node -> Node {
    { n, nephew : Node | {
        n.parent.left = n => {
            n.sibling.left = nephew
        } else {
            n.sibling.right = nephew
        }
    }}
}

// The sibling of a node's parent
fun uncle: set Node -> Node {
    // Include both of the grandparent's immediate children, but remove the parent,
    // thus there is at most a single uncle for every node
    grandparent.immediateChildren - parent
}

// Algorithms
fun inorderSuccessor: set Node -> Node {
    { n, succ : Node | succ in n.right.^left and no succ.left }
}

pred delete[n : Node] {
    -- Node must be in tree
    n in treeNode

    -- Node not in next state
    not (n in treeNode')

    -- remove the node from the tree
    no n.parent'
    no n.left'
    no n.right'

    -- FOR TESTING
    // some n.left and some n.right and n.color = Black

    -- the node is a leaf
    no n.left and no n.right => {
        n.color = Red => {
            n = root => {
                no root' 
            } else {
                root' = root

                n.parent.left = n => {
                    no n.parent.left'
                    n.parent.right' = n.parent.right
                } else {
                    no n.parent.right'
                    n.parent.left' = n.parent.left
                }
            }
        } else {
            some db : Node | {
                db.type = DoubleBlack
                db.color = Black
                db.nullNode = IsNull
                db not in treeNode
                db.value = n.value

                n = root => {
                    root' = db
                } else {
                    root' = root
                    replaceGrandparent[n, db]
                }
            }
        }
        n.inorderSuccessor.left' = n.inorderSuccessor.left
        n.inorderSuccessor.right' = n.inorderSuccessor.right
        n.inorderSuccessor.color' = n.inorderSuccessor.color

        n.inorderSuccessor.parent.left' = n.inorderSuccessor.parent.left
        n.inorderSuccessor.parent.right' = n.inorderSuccessor.parent.right
        n.inorderSuccessor.parent.color' = n.inorderSuccessor.parent.color
    }

    -- the node has one child
    no n.left and some n.right => {
        replaceGrandparent[n, n.right]

        n.color = Black and n.right.color = Black => {
            n.right.type' = DoubleBlack
            n.right.nullNode' = NotNull
            n.right.color' = Black
        } else {
            n.right.color' = Black
        }

        n.inorderSuccessor.left' = n.inorderSuccessor.left
        n.inorderSuccessor.right' = n.inorderSuccessor.right
        n.inorderSuccessor.color' = n.inorderSuccessor.color

        n.inorderSuccessor.parent.left' = n.inorderSuccessor.parent.left
        n.inorderSuccessor.parent.right' = n.inorderSuccessor.parent.right
        n.inorderSuccessor.parent.color' = n.inorderSuccessor.parent.color
    }
    no n.right and some n.left => {
        replaceGrandparent[n, n.left]

        n.color = Black and n.left.color = Black => {
            n.left.type' = DoubleBlack
            n.left.nullNode' = NotNull
        }
        n.left.color' = Black

        n.inorderSuccessor.left' = n.inorderSuccessor.left
        n.inorderSuccessor.right' = n.inorderSuccessor.right
        n.inorderSuccessor.color' = n.inorderSuccessor.color

        n.inorderSuccessor.parent.left' = n.inorderSuccessor.parent.left
        n.inorderSuccessor.parent.right' = n.inorderSuccessor.parent.right
        n.inorderSuccessor.parent.color' = n.inorderSuccessor.parent.color
    }

    // -- the node has two children
    some n.left and some n.right => {
        replaceGrandparent[n, n.inorderSuccessor]

        n.inorderSuccessor.left' = n.left
        n.inorderSuccessor.right' = n.right
        n.inorderSuccessor.color' = n.color

        n.left != n.inorderSuccessor => {
            n.left.color' = n.left.color
        }
        n.right != n.inorderSuccessor => {
            n.right.color' = n.right.color
        }

        n.color = Black => {
            some db : Node | {
                db.type = DoubleBlack
                db.nullNode = IsNull
                db not in treeNode

                no db.left'
                no db.right'

                n.inorderSuccessor.parent.left = n.inorderSuccessor => {
                    n.inorderSuccessor.parent.left' = db
                    n.inorderSuccessor.parent.right' = n.inorderSuccessor.parent.right
                } else {
                    n.inorderSuccessor.parent.right' = db
                    n.inorderSuccessor.parent.left' = n.inorderSuccessor.parent.left
                }
            }
        } else {
            n.inorderSuccessor.parent.left = n.inorderSuccessor => {
                no n.inorderSuccessor.parent.left'
                n.inorderSuccessor.parent.right' = n.inorderSuccessor.parent.right
            } else {
                no n.inorderSuccessor.parent.right'
                n.inorderSuccessor.parent.left' = n.inorderSuccessor.parent.left
            }
        }
        n.inorderSuccessor.parent.color' = n.inorderSuccessor.parent.color
    }

    // all o : Node | (o not in (n + n.parent + n.inorderSuccessor + n.inorderSuccessor.parent)) => {
    all o : Node | (o not in (n + n.parent + n.inorderSuccessor + n.inorderSuccessor.parent)) => {
        o.left' = o.left
        o.right' = o.right
    }

    -- Color stays the same except the left and right
    color' = color - (n.left -> Color + n.right -> Color)

    -- Type and Null stay the same
    type' = type
    nullNode' = nullNode
}

pred removeDB[db: Node] {
    no db.left'
    no db.right'
    no db.parent'
}

fun dbNode: lone Node {
    { n : Node | n.type = DoubleBlack and n in treeNode }
}


pred replaceGrandparent[prev: Node, next: Node] {
    (prev = root) => {
        root' = next
    } else {
        root' = root

        prev.parent.color' = prev.parent.color

        (some prev.~left) => {
            prev.parent.left' = next
            prev.parent.right' = prev.parent.right
        } else {
            prev.parent.right' = next
            prev.parent.left' = prev.parent.left
        }
    }
}

pred recolorDeleteEnabled {
    some dbNode
}

-- Cases are numbered using the table from: https://medium.com/analytics-vidhya/deletion-in-red-black-rb-tree-92301e1474ea
pred recolorDelete {
    -- happens when there is still a double black in the tree
    recolorDeleteEnabled

    -- Case 2: Node is root
    let db = dbNode, sib = dbNode.sibling | {
        all o : Node | (o not in (db + db.parent + db.sibling + db.farNephew + db.nearNephew)) => {
            o.left' = o.left
            o.right' = o.right
            o.color' = o.color
            o.type' = o.type
            o.nullNode' = o.nullNode
        }
        db = root => {
            db.nullNode = NotNull => {
                -- Remove DoubleBlack sign
                db.type' = Single
                db.nullNode' = NotNull
                root' = root
            } else {
                removeDB[db]
                no root'
            }

            -- Things that stay the same:
            db.left' = db.left
            db.right' = db.right
            db.color' = db.color

            sib.left' = sib.left
            sib.right' = sib.right
            sib.color' = sib.color
            sib.type' = sib.type
            sib.nullNode' = sib.nullNode

            db.parent.left' = db.parent.left
            db.parent.right' = db.parent.right
            db.parent.color' = db.parent.color
            db.parent.type' = db.parent.type
            db.parent.nullNode' = db.parent.nullNode

            db.farNephew.left' = db.farNephew.left
            db.farNephew.right' = db.farNephew.right
            db.farNephew.color' = db.farNephew.color
            db.farNephew.type' = db.farNephew.type
            db.farNephew.nullNode' = db.farNephew.nullNode

            db.nearNephew.left' = db.nearNephew.left
            db.nearNephew.right' = db.nearNephew.right
            db.nearNephew.color' = db.nearNephew.color
            db.nearNephew.type' = db.nearNephew.type
            db.nearNephew.nullNode' = db.nearNephew.nullNode
        } else {

            -- Case 3: sibling is black and the children are black
            -- also the case where there is no sibling
            {
                (sib.color = Black and 
                (sib.left.color = Black or no sib.left) and
                (sib.right.color = Black or no sib.right))
                or 
                no sib
            } => {

                root' = root

                -- if null, remove from tree, else remove db sign
                db.nullNode = IsNull => {
                    removeDB[db]
                    db.parent.left = db => {
                        no db.parent.left'
                        db.parent.right' = db.parent.right
                    } else {
                        no db.parent.right'
                        db.parent.left' = db.parent.left
                    }
                } else {
                    db.type' = Single
                    db.nullNode' = NotNull
                    db.left' = db.left
                    db.right' = db.right
                    db.color' = db.color

                    db.parent.left' = db.parent.left
                    db.parent.right' = db.parent.right
                }

                -- change sibs color to red
                sib.color' = Red

                -- if DBs parent is black, set it to double black,
                -- otherwise make parent black
                db.parent.color = Black => {
                    db.parent.type' = DoubleBlack
                    db.parent.nullNode' = NotNull

                    db.parent.color' = db.parent.color
                } else {
                    db.parent.color' = Black

                    db.parent.type' = db.parent.type
                    db.parent.nullNode' = db.parent.nullNode
                }

                -- Things that stay the same:
                sib.left' = sib.left
                sib.right' = sib.right
                sib.type' = sib.type
                sib.nullNode' = sib.nullNode

                // db.parent.left' = db.parent.left
                // db.parent.right' = db.parent.right
                db.parent.type' = db.parent.type
                db.parent.nullNode' = db.parent.nullNode

                db.farNephew.left' = db.farNephew.left
                db.farNephew.right' = db.farNephew.right
                db.farNephew.color' = db.farNephew.color
                db.farNephew.type' = db.farNephew.type
                db.farNephew.nullNode' = db.farNephew.nullNode

                db.nearNephew.left' = db.nearNephew.left
                db.nearNephew.right' = db.nearNephew.right
                db.nearNephew.color' = db.nearNephew.color
                db.nearNephew.type' = db.nearNephew.type
                db.nearNephew.nullNode' = db.nearNephew.nullNode
            }

            -- Case 4: the sibling is red
            {
                some sib
                sib.color = Red
            } => {
                -- Swap color of DBs parent with DBs sib
                db.parent.color' = sib.color
                sib.color' = db.parent.color

                -- Rotate at parent node in direction of DB node
                db.parent.left = db => {
                    replaceGrandparent[db.parent, sib]

                    sib.left' = db.parent
                    sib.right' = sib.right

                    db.parent.left' = db.parent.left
                    db.parent.right' = sib.left
                } else {
                    replaceGrandparent[db.parent, sib]

                    sib.left' = sib.left
                    sib.right' = db.parent

                    db.parent.left' = sib.right
                    db.parent.right' = db.parent.right
                }

                -- stays the same:
                db.left' = db.left
                db.right' = db.right
                db.color' = db.color
                db.type' = db.type
                db.nullNode' = db.nullNode

                db.parent.type' = db.parent.type
                db.parent.nullNode' = db.parent.nullNode

                db.farNephew.left' = db.farNephew.left
                db.farNephew.right' = db.farNephew.right
                db.farNephew.color' = db.farNephew.color
                db.farNephew.type' = db.farNephew.type
                db.farNephew.nullNode' = db.farNephew.nullNode

                db.nearNephew.left' = db.nearNephew.left
                db.nearNephew.right' = db.nearNephew.right
                db.nearNephew.color' = db.nearNephew.color
                db.nearNephew.type' = db.nearNephew.type
                db.nearNephew.nullNode' = db.nearNephew.nullNode

                sib.type' = sib.type
                sib.nullNode' = sib.nullNode
            }

            -- Case 5: sibling is black, near sibling child is red
            {
                some sib
                sib.color = Black
                (db.farNephew.color = Black or no db.farNephew)
                db.nearNephew.color = Red
            } => {
                -- Swap color of sibling with siblings red child
                sib.color' = db.nearNephew.color
                db.nearNephew.color' = sib.color

                -- Rotate at sibling node away from DB node
                db.parent.left = db => {
                    replaceGrandparent[sib, db.nearNephew]

                    db.nearNephew.left' = db.nearNephew.left
                    db.nearNephew.right' = sib

                    sib.left' = db.nearNephew.right
                    sib.right' = sib.right

                    -- stays the same:
                    db.farNephew.left' = db.farNephew.left
                    db.farNephew.right' = db.farNephew.right
                } else {
                    replaceGrandparent[sib, db.farNephew]

                    db.farNephew.left' = sib
                    db.farNephew.right' = db.farNephew.right

                    sib.left' = sib.left
                    sib.right' = db.farNephew.left

                    -- stays the same:
                    db.nearNephew.left' = db.nearNephew.left
                    db.nearNephew.right' = db.nearNephew.right
                }

                -- stays the same:
                db.left' = db.left
                db.right' = db.right
                db.color' = db.color
                db.type' = db.type
                db.nullNode' = db.nullNode

                db.parent.left' = db.parent.left
                db.parent.right' = db.parent.right
                db.parent.color' = db.parent.color
                db.parent.type' = db.parent.type
                db.parent.nullNode' = db.parent.nullNode

                db.farNephew.color' = db.farNephew.color
                db.farNephew.type' = db.farNephew.type
                db.farNephew.nullNode' = db.farNephew.nullNode

                db.nearNephew.type' = db.nearNephew.type
                db.nearNephew.nullNode' = db.nearNephew.nullNode

                sib.type' = sib.type
                sib.nullNode' = sib.nullNode
            }

            -- Case 6: sibling is black, far child is red
            {
                some sib
                sib.color = Black
                db.farNephew.color = Red
            } => {
                -- Swap color of siblings red child with color of sibling
                db.parent.color' = sib.color
                sib.color' = db.parent.color

                -- Rotate parent node in the direction of DB
                db.parent.left = db => {
                    replaceGrandparent[db.parent, sib]

                    sib.left' = db.parent
                    sib.right' = sib.right

                    db.parent.left' = db.parent.left
                    db.parent.right' = sib.left
                } else {
                    replaceGrandparent[db.parent, sib]

                    sib.left' = sib.left
                    sib.right' = db.parent

                    db.parent.left' = sib.right
                    db.parent.right' = db.parent.right
                }

                -- If DB is null, remove from tree, otherwise
                -- remove DB sign and make black
                db.nullNode = IsNull => {
                    removeDB[db]
                } else {
                    db.type' = Single
                    db.nullNode' = NotNull
                    db.color' = Black
                }

                -- Make far sibling child to black
                db.farNephew.color' = Black

                -- stays the same:
                db.left' = db.left
                db.right' = db.right

                db.parent.type' = db.parent.type
                db.parent.nullNode' = db.parent.nullNode

                db.farNephew.left' = db.farNephew.left
                db.farNephew.right' = db.farNephew.right
                db.farNephew.type' = db.farNephew.type
                db.farNephew.nullNode' = db.farNephew.nullNode

                db.nearNephew.left' = db.nearNephew.left
                db.nearNephew.right' = db.nearNephew.right
                db.nearNephew.color' = db.nearNephew.color
                db.nearNephew.type' = db.nearNephew.type
                db.nearNephew.nullNode' = db.nearNephew.nullNode

                sib.type' = sib.type
                sib.nullNode' = sib.nullNode
            }
        }
    }
}

pred insert[n : Node] {
    // Tree is assumed to be wellformed BST before node is added

    -- New node is not in the current tree
    not (n in treeNode)

    -- New node is in the next state
    n in treeNode'

    -- All colors stay the same except
    -- the new node is red
    color' = (color - (n -> Color)) + n -> Red

    -- type and null stays the same
    type' = type
    nullNode' = nullNode

    next_state {
        all p: treeNode | {
            (n in p.left.children) => n.value < p.value
            (n in p.right.children) => n.value > p.value
        }
    }

    (no root) => {
        // Insertion into an empty tree
        root' = n
        no left'
        no right'
    } else {
        root' = root

        // Insertion into an existing tree
        // Find the correct parent node
        some p: treeNode | {
            {
                n.value < p.value
                left' = left + p -> n
                right' = right
            } or {
                n.value > p.value
                right' = right + p -> n
                left' = left
            }
        }
    }


}

pred recolorEnabled[n: Node] {
    n.color = Red
    n.grandparent.color = Black
    n.parent.color = Red
    n.uncle.color = Red
}

pred recolor[n: Node] {
    recolorEnabled[n]

    root' = root
    left' = left
    right' = right

    type' = type
    nullNode' = nullNode

    let g = n.grandparent, p = n.parent, u = n.uncle | {
        color' = (color - ((g + p + u) -> Color)) +
            g -> Red +
            p -> Black +
            u -> Black
    }
}

pred rotateEnabled[n: Node] {
    n.color = Red
    some n.grandparent

    -- If n's parent is black, there is no fixing required, so therefore no rotation happens
    -- If n is not the root and the parent is also Red, then rotation/recoloring must take place 
    n.parent.color = Red

    -- Uncle is either missing or is Black (otherwise only recoloring is needed)
    no n.uncle or n.uncle.color = Black
}

pred rotate[n : Node] {
    rotateEnabled[n]

    -- Since parent is red, and n is red, the coloring is violated
    -- Grandparent must always be black, since parent is red
    -- Uncle may be missing

    type' = type
    nullNode' = nullNode
    
    let p = n.parent, g = n.grandparent, u = n.uncle | {
        -- Let everything else stay the same
        -- Uncle does not change in this case
        all o: Node | (o not in (n + p + g + g.parent)) => {
            o.left' = o.left
            o.right' = o.right
            o.color' = o.color
        }

        -- Left Left case
        (g.left.left = n) => {
            -- Replace grandparent with parent
            replaceGrandparent[g, p]

            p.left' = n
            p.right' = g
            p.color' = Black

            g.left' = p.right
            g.right' = u
            g.color' = Red

            // n does not change
            n.left' = n.left
            n.right' = n.right
            n.color' = n.color
        }

        -- Left Right case
        (g.left.right = n) => {
            -- Replace the grandparent with n
            replaceGrandparent[g, n]

            n.left' = p
            n.right' = g
            n.color' = Black

            p.left' = p.left
            p.right' = n.left
            p.color' = Red

            g.left' = n.right
            g.right' = u
            g.color' = Red
        }

        -- Right Right case
        (g.right.right = n) => {
            -- Replace grandparent with parent
            replaceGrandparent[g, p]

            p.left' = g
            p.right' = n
            p.color' = Black

            g.left' = u
            g.right' = p.left
            g.color' = Red

            n.left' = n.left
            n.right' = n.right
            n.color' = n.color
        }

        -- Right Left case
        (g.right.left = n) => {
            replaceGrandparent[g, n]

            n.left' = g
            n.right' = p
            n.color' = Black

            g.left' = u
            g.right' = n.left
            g.color' = Red

            p.left' = n.right
            p.right' = p.right
            p.color' = p.color
        }
    }
}

// Get next node that is violating wellformed
fun nextInsertNode: lone Node {
    {root.color = Red} => root
    else { n : Node | n.parent.color = Red and n.color = Red }
}

pred terminate_transition {
    // Don't terminate until done inserting
    no nextInsertNode
    // Don't terminate until done deleting
    no dbNode

    left' = left
    right' = right
    value' = value
    color' = color
    rootNode' = rootNode

    type' = type
    nullNode' = nullNode
}

pred rotate_transition {    
    // implies that tree isn't wellformed
    // TODO: Test that we only have one of these at any given time
    some nextInsertNode
    rotate[nextInsertNode]
}

pred recolor_transition {
    some nextInsertNode
    recolor[nextInsertNode]
}

pred insert_transition {
    // Don't insert until done deleting
    no dbNode

    -- Don't insert until the previous insert is cleaned up
    no nextInsertNode
    some n: Node | insert[n]
}

pred delete_transition {
    // Don't delete until done deleting
    no dbNode

    -- Don't delete if node is being inserted
    no nextInsertNode
    some n: Node | delete[n]
}

pred delete_recolor_transition {
    no nextInsertNode
    recolorDelete
}

pred traces {
    wellformed_rb

    always {
        (
            insert_transition or
            rotate_transition or
            recolor_transition or
            delete_transition or
            delete_recolor_transition or
            terminate_transition
        )
    }
}

run { traces } for exactly 6 Node