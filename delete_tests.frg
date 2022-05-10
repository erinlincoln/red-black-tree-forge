#lang forge "final" "jpqtay573rwx8pc6@gmail.com"

open "tree_electrum.frg"
open "red_black.frg"

// Tests for deletion in red-black tree

// run {
//     some n1, n2, n3, n4, n5, n6, n7, db : Node | {

//             // starting state
//             value = n1 -> 0 + n2 -> -3 + n3 -> 3 + n4 -> -5 + n5 -> -2
//                 + n6 -> 2 + n7 -> 5 + db -> 2
//             // left = n1 -> n2  // + n2 -> n4 + n3 -> n6
//             // right = n1 -> n3 // + n2 -> n5 + n3 -> n7
//             color = (n1 + n2 + n3 + n4 + n5 + n6 + n7 + db) -> Black
//             type = (n1 + n2 + n3 + n4 + n5 + n6 + n7) -> Single + db -> DoubleBlack
//             nullNode = (n1 + n2 + n3 + n4 + n5 + n6 + n7) -> NotNull + db->IsNull

//             // // replace 2 (n6) with db
//             value' = value
//             // left' = n1 -> n2 + n2 -> n4 + n3 -> db
//             // right' = right
//             color' = color
//             type' = type
//             nullNode' = nullNode

//             // // case 3: make 3 (n3) DoubleBlack and delete db, make 5 (n7) red
//             value'' = value
//             // left = n1 -> n2 + n2 -> n4
//             // right'' = right
//             // color'' = (n7) -> Red + (n1 + n2 + n3 + n4 + n5 + n6 + n7 + db) -> Black
//             // type'' = (n1 + n2 + n4 + n5 + n6 + n7) -> Single + (db + n3) -> DoubleBlack
//             nullNode'' = nullNode

//             // // case 3: root becomes db
//             value''' = value
//             // left''' = left''
//             // right''' = right
//             // color''' = color''
//             // type''' = (n2 + n3+ n4 + n5 + n6 + n7) -> Single + (db + n1) -> DoubleBlack
//             nullNode''' = nullNode

//             // // case 2: root becomes black
//             value'''' = value
//             // left'''' = left''
//             // right'''' = right
//             type'''' = type
//             nullNode'''' = nullNode

//         }

//         traces
//         delete_transition
//         next_state delete_recolor_transition
//         next_state delete_recolor_transition
    
// } for exactly 8 Node

// examples for each of the deletion cases
test expect {

    // case 1: deleted node is red leaf
    deleteRedLeaf: {
        //              0
        //            /   \
        //          -3     3
        //         /  \   /  \
        //       -5   -2  2   5
        //                   /
        //                  4 <- delete
        some n1, n2, n3, n4, n5, n6, n7, n8 : Node | {

            // starting state
            value = n1 -> 0 + n2 -> -3 + n3 -> 3 + n4 -> -5 + n5 -> -2
                + n6 -> 2 + n7 -> 5 + n8 -> 4

            left = n1 -> n2 + n2 -> n4 + n3 -> n6 + n7 -> n8
            right = n1 -> n3 + n2 -> n5 + n3 -> n7

            color = (n2 + n3 + n8) -> Red + (n1 + n4 + n5 + n6 + n7) -> Black

            type = (n1 + n2 + n3 + n4 + n5 + n6 + n7 + n8) -> Single
            nullNode = (n1 + n2 + n3 + n4 + n5 + n6 + n7 + n8) -> NotNull

            // delete n8
            value' = n1 -> 0 + n2 -> -3 + n3 -> 3 + n4 -> -5 + n5 -> -2
                + n6 -> 2 + n7 -> 5 + n8 -> 4

            left' = n1 -> n2 + n2 -> n4 + n3 -> n6
            right' = n1 -> n3 + n2 -> n5 + n3 -> n7

            color' = (n2 + n3 + n8) -> Red + (n1 + n4 + n5 + n6 + n7) -> Black

            type' = (n1 + n2 + n3 + n4 + n5 + n6 + n7 + n8) -> Single
            nullNode' = (n1 + n2 + n3 + n4 + n5 + n6 + n7 + n8) -> NotNull
        }

        wellformed_rb
        traces
        delete_transition

    } for exactly 8 Node is sat

    deleteRed: {
        //              0
        //            /   \
        //          -3     3 <- delete and replace with (4)
        //         /  \   /  \
        //       -5   -2  2   5
        //                   /
        //                  4
        some n1, n2, n3, n4, n5, n6, n7, n8 : Node | {

            // starting state
            value = n1 -> 0 + n2 -> -3 + n3 -> 3 + n4 -> -5 + n5 -> -2
                + n6 -> 2 + n7 -> 5 + n8 -> 4

            left = n1 -> n2 + n2 -> n4 + n3 -> n6 + n7 -> n8
            right = n1 -> n3 + n2 -> n5 + n3 -> n7

            color = (n2 + n3 + n8) -> Red + (n1 + n4 + n5 + n6 + n7) -> Black

            type = (n1 + n2 + n3 + n4 + n5 + n6 + n7 + n8) -> Single
            nullNode = (n1 + n2 + n3 + n4 + n5 + n6 + n7 + n8) -> NotNull

            // replace n3 (3) with n8 (4) and delete duplicate n8
            value' = n1 -> 0 + n2 -> -3 + n3 -> 3 + n4 -> -5 + n5 -> -2
                + n6 -> 2 + n7 -> 5 + n8 -> 4

            left' = n1 -> n2 + n2 -> n4 + n8 -> n6
            right' = n1 -> n8 + n2 -> n5 + n8 -> n7

            color' = (n2 + n3 + n8) -> Red + (n1 + n4 + n5 + n6 + n7) -> Black

            type' = (n1 + n2 + n3 + n4 + n5 + n6 + n7 + n8) -> Single
            nullNode' = (n1 + n2 + n3 + n4 + n5 + n6 + n7 + n8) -> NotNull
        }

        wellformed_rb
        traces
        delete_transition

    } for exactly 8 Node is sat

    // example 2: case 3 (db's sibling is red)
    dbRedSibling: {
        //              0
        //            /   \
        //          -3     3 
        //                /  \
        //     delete -> 2    5
        some n1, n2, n3, n4, n5, db : Node | {
            // starting state
            value = n1 -> 0 + n2 -> -3 + n3 -> 3 + n4 -> 2 + n5 -> 5 + db -> 2
            left = n1 -> n2 + n3 -> n4
            right = n1 -> n3 + n3 -> n5
            color = (n1 + n2 + n4 + n5 + db) -> Black + (n3) -> Red
            type = (n1 + n2 + n3 + n4 + n5) -> Single + (db) -> DoubleBlack
            nullNode = (n1 + n2 + n3 + n4 + n5) -> NotNull + (db) -> IsNull

            // 2 (n4) is replaced with dn
            value' = value
            left' = n1 -> n2 + n3-> db
            right' = right
            color' = color
            type' = type
            nullNode' = nullNode

            // db is deleted
            value'' = value
            left'' = n1 -> n2
            right'' = right
            color'' = (n1 + n2 + n3 + n4 + db) -> Black + (n5) -> Red
            type'' = type
            nullNode'' = nullNode

        }

        traces
        delete_transition
        next_state delete_recolor_transition

    } for exactly 6 Node is sat

    // example 3: case 3 + case 2 (db is root)
    dbRoot: {
        //              0
        //            /   \
        //          -3     3 
        //         /  \   /  \
        //       -5   -2  2   5
        //                ^ delete
        some n1, n2, n3, n4, n5, n6, n7, db : Node | {

            // starting state
            value = n1 -> 0 + n2 -> -3 + n3 -> 3 + n4 -> -5 + n5 -> -2
                + n6 -> 2 + n7 -> 5 + db -> 2
            // left = n1 -> n2 + n2 -> n4 + n3 -> n6
            // right = n1 -> n3 + n2 -> n5 + n3 -> n7
            color = (n1 + n2 + n3 + n4 + n5 + n6 + n7 + db) -> Black
            type = (n1 + n2 + n3 + n4 + n5 + n6 + n7) -> Single + db -> DoubleBlack
            nullNode = (n1 + n2 + n3 + n4 + n5 + n6 + n7) -> NotNull + db->IsNull

            // // replace 2 (n6) with db
            value' = value
            // left' = n1 -> n2 + n2 -> n4 + n3 -> db
            // right' = right
            color' = color
            type' = type
            nullNode' = nullNode

            // // case 3: make 3 (n3) DoubleBlack and delete db, make 5 (n7) red
            value'' = value
            // left = n1 -> n2 + n2 -> n4
            // right'' = right
            // color'' = (n7) -> Red + (n1 + n2 + n3 + n4 + n5 + n6 + n7 + db) -> Black
            // type'' = (n1 + n2 + n4 + n5 + n6 + n7) -> Single + (db + n3) -> DoubleBlack
            nullNode'' = nullNode

            // // case 3: root becomes db
            value''' = value
            // left''' = left''
            // right''' = right
            // color''' = color''
            // type''' = (n2 + n3+ n4 + n5 + n6 + n7) -> Single + (db + n1) -> DoubleBlack
            nullNode''' = nullNode

            // // case 2: root becomes black
            value'''' = value
            // left'''' = left''
            // right'''' = right
            type'''' = type
            nullNode'''' = nullNode

        }

        traces
        delete_transition
        next_state delete_recolor_transition
        next_state delete_recolor_transition
    } for exactly 8 Node is sat

    //example 4: case 4(db's sibling is red)
    // dbSibRed: {
    //     //              0B
    //     //            /   \
    //     //          -3B     3B 
    //     //         /  \   /  \
    //     //       -5B -2B 2B   4R
    //     //        delete ^   /  \
    //     //                  1B  5B
    //     some n1, n2, n3, n4, n5, n6, n7, n8, n9, db : Node | {
    //         value = n1 -> 0 + n2 -> -3 + n3 -> 3 + n4 -> -5 + n5 -> -2
    //             + n6 -> 2 + n7 -> 4 + n8 -> 1 + n9 -> 5 + db -> 2
    //         left = n1 -> n2 + n2 -> n4 + n3 -> n6 + n7 -> n8
    //         right = n1 -> n3 + n2 -> n5 + n3 -> n7 + n7 -> n9
    //         color = (n1 + n2 + n3 + n4 + n5 + n6 + n8 + n9 + db) -> Black + (n7) -> Red
    //         type = (n1 + n2 + n3 + n4 + n5 + n6 + n7 + n8 + n9) -> Single + db -> DoubleBlack
    //         nullNode = (n1 + n2 + n3 + n4 + n5 + n6 + n7 + n8 + n9) -> NotNull + db->IsNull

    //         // replace n6 (2) with db null
    //         value' = value
    //         left' = n1 -> n2 + n2 -> n4 + n3 -> db + n7 -> n8
    //         right' = right
    //         color' = color
    //         type' = color
    //         nullNode' = nullNode

    //         // case 4: swap n3's color with n7's color, rotate n3 towards db
    //         value'' = value
    //         left = n1 -> n2 + n2 -> n4 + n6 -> n3 + n3-> db + n7 -> n8
    //         right = n1 -> n6 + n2 -> n5 + n6 -> n7 + n7 -> n9
            
    //     }

    // } for exactly 10 Node is sat


    // case 4: deleted node's sibling is red

    // case 5: deleted node's sibling is black, sibling's child farther from deleted
    // is black, and sibling's child closer to deleted is red

    // case 6: deleted node's sibling is black and sibling's further child is red
}


test expect {
    // vacuous: can delete
    vacuous: {
        traces
        delete_transition
    } is sat

    // CASES
    // cannot delete in empty tree
    cannotDeleteEmpty : {
        traces
        no root
        some n : Node | delete[n]
    } for exactly 2 Node is unsat

    // can delete root node in empty tree
    deleteRootEmpty : {
        traces
        some root
        no root.left
        no root.right
        delete_transition
    } for exactly 2 Node is sat

    // can delete root node in not empty tree
    deleteRootLR : {
        traces
        some root.left
        some root.right
        delete[root]
    } for exactly 4 Node is sat

    // can delete in 3 node tree
    delete3Nodes : {
        traces
        some root.left
        some root.right
        delete_transition
    } for exactly 4 Node is sat

    // // can delete in height 3 tree
    deleteHeight3: {
        traces
        #{treeNode} = 7
        delete_transition
    } for exactly 8 Node is sat

    // can delete such that there is no recolor or rotation
    deleteNoRecolorNoRotation: {
        traces
        delete_transition
        not (eventually delete_recolor_transition)
        not (eventually rotate_transition)
    } for exactly 3 Node is sat

    // can delete node with children
    deleteWithChildren: {
        traces
        some n : Node | {delete[n] and some n.children}
    } for exactly 5 Node is sat

    // PROPERTIES
    // deletion eventually means wellformed
    deleteToWellformed: {
        traces => {
            delete_transition => eventually wellformed_rb
        }
    } is theorem

    // double black node implies not wellformed
    dbNotWellformed: {
        traces => {
            some dbNode => not wellformed_rb
        }
    } is theorem

    // if a node is db, it will eventually not be in tree
    dbToOutOfTree: {
        traces => {
            some dbNode => eventually no dbNode
        }
    } is theorem

    // cannot insert while performing deletion and vice versa
    
    // can't delete a node not in tree
    cannotDeleteOutOfTree: {
        traces => { all n: {Node - treeNode} | {
            not delete[n]
        } }
    } is theorem
}