#lang forge "final" "jpqtay573rwx8pc6@gmail.com"

open "tree_electrum.frg"
open "insert.frg"

// Algorithms
fun inorderSuccessor: set Node -> Node {
//    some { n, succ : Node | succ in n.right.^left and no succ.left } => 
    // { n, succ : Node | succ in n.right.^left and no succ.left }
//    else {n, succ : Node | n.left = succ}
    {n, succ : Node | no n.right.left => {
        succ = n.right
    } else {
        succ in n.right.^left and no succ.left
    }}
}

pred delete[n : Node] {
    // Don't delete until done deleting another node
    no dbNode
    -- Don't delete if node is being inserted
    no nextInsertNode

    -- Node must be in tree
    n in treeNode

    -- Node not in next state
    // not (n in treeNode')

    -- remove the node from the tree
    // no n.parent'
    // no n.left'
    // no n.right'

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
            no n.parent'
            no n.left'
            no n.right'
        } else {
            root' = root
            n.type' = DoubleBlack
            n.color' = Black
            n.nullNode' = IsNull
            no n.left'
            no n.right'

            n.parent.left' = n.parent.left
            n.parent.right' = n.parent.right
        }

        n.parent.color' = n.parent.color

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
            no n.right.nullNode'
        }
        n.right.color' = Black

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
            no n.left.nullNode'
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

        -- REWRITTEN
        replaceGrandparent[n, n.inorderSuccessor]

        no n.left'
        no n.right'

        n.inorderSuccessor.left' = n.left
        n.left.color' = n.left.color

        -- after replacing, n is a red leaf
        {
            n.inorderSuccessor = n.right
            no n.inorderSuccessor.right
            n.inorderSuccessor.color = Red
        } => {
            no n.inorderSuccessor.right'
            n.inorderSuccessor.color' = n.color
        }

        -- after replacing, n is a black leaf
        {
            n.inorderSuccessor = n.right
            no n.inorderSuccessor.right
            n.inorderSuccessor.color = Black
        } => {
            n.inorderSuccessor.right' = n
            n.inorderSuccessor.color' = n.color

            n.color' = Black
            n.type' = DoubleBlack
            n.nullNode' = IsNull
        }

        -- after replacing, n has one right child
        {
            n.inorderSuccessor = n.right
            some n.inorderSuccessor.right
        } => {
            n.inorderSuccessor.color = Black and n.inorderSuccessor.right.color = Black => {
                n.inorderSuccessor.right.type' = DoubleBlack
                no n.inorderSuccessor.right.nullNode'
            }
            n.inorderSuccessor.right.color' = Black

            n.inorderSuccessor.right' = n.inorderSuccessor.right
            n.inorderSuccessor.color' = n.color
        }

        -- After replacing, n is a Red leaf
        {
            n.inorderSuccessor != n.right
            no n.inorderSuccessor.right
            n.inorderSuccessor.color = Red
        } => {
            n.inorderSuccessor.right' = n.right
            n.inorderSuccessor.color' = n.color

            n.inorderSuccessor.parent.left = n.inorderSuccessor => {
                no n.inorderSuccessor.parent.left'
                n.inorderSuccessor.parent.right' = n.inorderSuccessor.parent.right
            } else {
                no n.inorderSuccessor.parent.right'
                n.inorderSuccessor.parent.left' = n.inorderSuccessor.parent.left
            }
            
            n.right.color' = n.right.color
        }

        -- After replacing, n is Black leaf
        {
            n.inorderSuccessor != n.right
            no n.inorderSuccessor.right
            n.inorderSuccessor.color = Black
        } => {
            n.inorderSuccessor.right' = n.right
            n.inorderSuccessor.color' = n.color

            n.inorderSuccessor.parent.left = n.inorderSuccessor => {
                n.inorderSuccessor.parent.left' = n
                n.inorderSuccessor.parent.right' = n.inorderSuccessor.parent.right
            } else {
                n.inorderSuccessor.parent.right' = n
                n.inorderSuccessor.parent.left' = n.inorderSuccessor.parent.left
            }

            n.color' = Black
            n.type' = DoubleBlack
            n.nullNode' = IsNull

            n.right.color' = n.right.color
        }

        -- After replacing, n has one right child
        {
            n.inorderSuccessor != n.right
            some n.inorderSuccessor.right
        } => {
            n.inorderSuccessor.color = Black and n.inorderSuccessor.right.color = Black => {
                n.inorderSuccessor.right.type' = DoubleBlack
                no n.inorderSuccessor.right.nullNode'
            }
            n.inorderSuccessor.right.color' = Black

            n.inorderSuccessor.right' = n.right
            n.inorderSuccessor.color' = n.color

            n.inorderSuccessor.parent.left = n.inorderSuccessor => {
                n.inorderSuccessor.parent.left' = n.inorderSuccessor.right
                n.inorderSuccessor.parent.right' = n.inorderSuccessor.parent.right
            } else {
                n.inorderSuccessor.parent.right' = n.inorderSuccessor.right
                n.inorderSuccessor.parent.left' = n.inorderSuccessor.parent.left
            }

            n.right.color' = n.right.color
        }
    }

    // all o : Node | (o not in (n + n.parent + n.inorderSuccessor + n.inorderSuccessor.parent)) => {
    all o : Node - (n + n.parent + n.inorderSuccessor + n.inorderSuccessor.parent) | {
        o.left' = o.left
        o.right' = o.right
    }

    // CHANGED -- added subtracting set of color'
    -- Color stays the same except the left, right, inorder successor (and its right)
    color' - (n -> Color + n.left -> Color + n.right -> Color +
              n.inorderSuccessor.right -> Color +
              n.inorderSuccessor.left -> Color + 
              n.inorderSuccessor -> Color)
        = color - (n -> Color + n.left -> Color + n.right -> Color +
                   n.inorderSuccessor.right -> Color +
                   n.inorderSuccessor.left -> Color + 
                   n.inorderSuccessor -> Color)

    -- Type and Null stay the same
    type' - (n -> DoubleBlack) = type - (n -> DoubleBlack)
    nullNode' - (n -> IsNull) = nullNode - (n -> IsNull)
}

// PREVENTS IMPORT ISSUES WITH IMPORTING INSERT AND DELETE SIMULTANEOUSLY
pred del_rotate_transition{
    insertRotateTransition
}

pred removeDB[db: Node] {
    no db.left'
    no db.right'
    no db.parent'
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
        all o : Node | (o not in (db + db.parent + db.sibling + db.farNephew + db.nearNephew + db.parent.parent)) => {
            o.left' = o.left
            o.right' = o.right
            o.color' = o.color
            o.type' = o.type
            o.nullNode' = o.nullNode
        }
        db = root => {
            (no db.nullNode) => {
                -- Remove DoubleBlack sign
                no db.type'
                no db.nullNode'
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

            db.parent.parent.left' = db.parent.parent.left
            db.parent.parent.right' = db.parent.parent.right
            db.parent.parent.color' = db.parent.parent.color
            db.parent.parent.type' = db.parent.parent.type
            db.parent.parent.nullNode' = db.parent.parent.nullNode

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
                    no db.type'
                    no db.nullNode'
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
                    no db.parent.nullNode'

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

                db.parent.parent.left' = db.parent.parent.left
                db.parent.parent.right' = db.parent.parent.right
                db.parent.parent.color' = db.parent.parent.color
                db.parent.parent.type' = db.parent.parent.type
                db.parent.parent.nullNode' = db.parent.parent.nullNode

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

                db.parent.parent.type' = db.parent.parent.type
                db.parent.parent.nullNode' = db.parent.parent.nullNode

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

                // db.parent.left' = db.parent.left
                // db.parent.right' = db.parent.right
                // db.parent.color' = db.parent.color
                db.parent.type' = db.parent.type
                db.parent.nullNode' = db.parent.nullNode

                db.parent.parent.left' = db.parent.parent.left
                db.parent.parent.right' = db.parent.parent.right
                db.parent.parent.color' = db.parent.parent.color
                db.parent.parent.type' = db.parent.parent.type
                db.parent.parent.nullNode' = db.parent.parent.nullNode

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
                    no db.type'
                    no db.nullNode'
                    db.color' = Black
                }

                -- Make far sibling child to black
                db.farNephew.color' = Black

                -- stays the same:
                db.left' = db.left
                db.right' = db.right

                db.parent.type' = db.parent.type
                db.parent.nullNode' = db.parent.nullNode

                db.parent.parent.type' = db.parent.parent.type
                db.parent.parent.nullNode' = db.parent.parent.nullNode

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

pred delete_transition {
    some n: Node | delete[n]
}

pred delete_recolor_transition {
    no nextInsertNode
    recolorDelete
}

pred traces_del {
    init

    always {
        (
            insertTransition or
            insertRotateTransition or
            insertRecolorTransition or
            delete_transition or
            delete_recolor_transition or
            terminateTransition
        )
    }
}

run { 
    init
    some n1, n2, n3, n4, n5, n6, n7, n8 : Node | {
        value = n1 -> 0 + n2-> -4 + n3 -> 4 + n4->-6 + n5->-2 + n6->2 + n7->6 + n8 -> 3

        left = n1 -> n2 + n2->n4 + n3->n6
        right = n1 -> n3 + n2->n5 + n3-> n7 + n6->n8

        color = (n1 + n2 + n6 + n7) -> Black + (n3 + n4 + n5 + n8) -> Red

        delete[n3]
    }
    traces_del
} for 10 Node