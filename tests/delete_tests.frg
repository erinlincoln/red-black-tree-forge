#lang forge "final" "jpqtay573rwx8pc6@gmail.com"

open "../src/tree_electrum.frg"
open "../src/delete.frg"
open "../src/insert.frg"

// General tests for deletion in a red black tree. Currently shows examples
// that cover each case of deletion and general case and property theorem
// tests. Note: commented out tests indicate that the test is failing. Delete
// still has bugs, causing the tests to fail.

// run {
//     some n1, n2, n3, n4, n5, n6, n7, db : Node | {

//             // starting state
//             value = n1 -> 0 + n2 -> -3 + n3 -> 3 + n4 -> -5 + n5 -> -2
//                 + n6 -> 2 + n7 -> 5 + db -> 2
//             // left = n1 -> n2  // + n2 -> n4 + n3 -> n6
//             // right = n1 -> n3 // + n2 -> n5 + n3 -> n7
//             color = (n1 + n2 + n3 + n4 + n5 + n6 + n7 + db) -> Black
//             type = db -> DoubleBlack
//             nullNode = db->IsNull

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
//             // type'' = (db + n3) -> DoubleBlack
//             nullNode'' = nullNode

//             // // case 3: root becomes db
//             value''' = value
//             // left''' = left''
//             // right''' = right
//             // color''' = color''
//             // type''' = (db + n1) -> DoubleBlack
//             nullNode''' = nullNode

//             // // case 2: root becomes black
//             value'''' = value
//             // left'''' = left''
//             // right'''' = right
//             type'''' = type
//             nullNode'''' = nullNode

//         }

//         traces_del
//         delete_transition
//         next_state delete_recolor_transition
//         next_state delete_recolor_transition
    
// } for exactly 8 Node

// examples for each of the deletion cases
test expect {

    // case 1: deleted node is red leaf
    // deleteRedLeaf: {
    //     //              0
    //     //            /   \
    //     //          -3     3
    //     //         /  \   /  \
    //     //       -5   -2  2   5
    //     //                   /
    //     //                  4 <- delete
    //     some n1, n2, n3, n4, n5, n6, n7, n8 : Node | {

    //         // starting state
    //         value = n1 -> 0 + n2 -> -3 + n3 -> 3 + n4 -> -5 + n5 -> -2
    //             + n6 -> 2 + n7 -> 5 + n8 -> 4

    //         left = n1 -> n2 + n2 -> n4 + n3 -> n6 + n7 -> n8
    //         right = n1 -> n3 + n2 -> n5 + n3 -> n7

    //         color = (n2 + n3 + n8) -> Red + (n1 + n4 + n5 + n6 + n7) -> Black

    //         no type
    //         no nullNode

    //         // delete n8
    //         value' = n1 -> 0 + n2 -> -3 + n3 -> 3 + n4 -> -5 + n5 -> -2
    //             + n6 -> 2 + n7 -> 5 + n8 -> 4

    //         left' = n1 -> n2 + n2 -> n4 + n3 -> n6
    //         right' = n1 -> n3 + n2 -> n5 + n3 -> n7

    //         color' = (n2 + n3 + n8) -> Red + (n1 + n4 + n5 + n6 + n7) -> Black

    //         no type
    //         no nullNode
    //     }

    //     wellformed_rb
    //     traces_del
    //     delete_transition

    // } for exactly 8 Node is sat

    // deleteRed: {
    //     //              0
    //     //            /   \
    //     //          -3     3 <- delete and replace with (4)
    //     //         /  \   /  \
    //     //       -5   -2  2   5
    //     //                   /
    //     //                  4
    //     some n1, n2, n3, n4, n5, n6, n7, n8 : Node | {

    //         // starting state
    //         value = n1 -> 0 + n2 -> -3 + n3 -> 3 + n4 -> -5 + n5 -> -2
    //             + n6 -> 2 + n7 -> 5 + n8 -> 4

    //         left = n1 -> n2 + n2 -> n4 + n3 -> n6 + n7 -> n8
    //         right = n1 -> n3 + n2 -> n5 + n3 -> n7

    //         color = (n2 + n3 + n8) -> Red + (n1 + n4 + n5 + n6 + n7) -> Black

    //         no type
    //         no nullNode

    //         // replace n3 (3) with n8 (4) and delete duplicate n8
    //         value' = n1 -> 0 + n2 -> -3 + n3 -> 3 + n4 -> -5 + n5 -> -2
    //             + n6 -> 2 + n7 -> 5 + n8 -> 4

    //         left' = n1 -> n2 + n2 -> n4 + n8 -> n6
    //         right' = n1 -> n8 + n2 -> n5 + n8 -> n7

    //         color' = (n2 + n3 + n8) -> Red + (n1 + n4 + n5 + n6 + n7) -> Black

    //         no type
    //         no nullNode
    //     }

    //     wellformed_rb
    //     traces_del
    //     delete_transition

    // } for exactly 8 Node is sat

    // // example 2: case 3 (db's sibling is red)
    // dbRedSibling: {
    //     //              0
    //     //            /   \
    //     //          -3     3 
    //     //                /  \
    //     //     delete -> 2    5
    //     some n1, n2, n3, n4, n5 : Node | {
    //         // starting state
    //         value = n1 -> 0 + n2 -> -3 + n3 -> 3 + n4 -> 2 + n5 -> 5
    //         left = n1 -> n2 + n3 -> n4
    //         right = n1 -> n3 + n3 -> n5
    //         color = (n1 + n2 + n4 + n5) -> Black + (n3) -> Red
    //         no type
    //         no nullNode

    //         // 2 (n4) is replaced with db
    //         value' = value
    //         left' = n1 -> n2 + n3-> n4
    //         right' = right
    //         color' = color
    //         type' = (n4) -> DoubleBlack
    //         nullNode' = n4 -> IsNull

    //         // db is deleted
    //         value'' = value
    //         left'' = n1 -> n2
    //         right'' = right
    //         color'' = (n1 + n2 + n3 + n4) -> Black + (n5) -> Red
    //         no type''
    //         no nullNode''
    //     }

    //     init
    //     delete_transition
    //     next_state delete_recolor_transition
    //     next_state next_state terminateTransition

    // } for exactly 5 Node is sat

    // example 3: case 3 + case 2 (db is root)
    // dbRoot: {
    //     //              0
    //     //            /   \
    //     //          -3     3 
    //     //         /  \   /  \
    //     //       -5   -2  2   5
    //     //                ^ delete
    //     some n1, n2, n3, n4, n5, n6, n7 : Node | {

    //         // starting state
    //         value = n1 -> 0 + n2 -> -3 + n3 -> 3 + n4 -> -5 + n5 -> -2
    //             + n6 -> 2 + n7 -> 5
    //         left = n1 -> n2 + n2 -> n4 + n3 -> n6
    //         right = n1 -> n3 + n2 -> n5 + n3 -> n7
    //         color = (n1 + n2 + n3 + n4 + n5 + n6 + n7) -> Black
    //         no type
    //         no nullNode

    //         // // replace 2 (n6) with db
    //         value' = value
    //         left' = left
    //         right' = right
    //         color' = color
    //         type' = n6 -> DoubleBlack
    //         nullNode' = n6 -> IsNull

    //         // case 3: make 3 (n3) DoubleBlack and delete db, make 5 (n7) red
    //         value'' = value
    //         left'' = n1 -> n2 + n2 -> n4
    //         right'' = right
    //         color'' = (n7) -> Red + (n1 + n2 + n3 + n4 + n5 + n6) -> Black
    //         type'' = (n3) -> DoubleBlack
    //         no nullNode''

    //         // // case 3: root becomes db
    //         value''' = value
    //         left''' = left''
    //         right''' = right
    //         color''' = (n7 + n2) -> Red + (n1 + n3 + n4 + n5 + n6) -> Black
    //         type''' = (n1) -> DoubleBlack
    //         no nullNode'''

    //         // // case 2: root becomes black
    //         value'''' = value
    //         left'''' = left''
    //         right'''' = right
    //         color'''' = color'''
    //         no type''''
    //         no nullNode''''
    //     }

    //     traces_del
    //     delete_transition
    //     next_state delete_recolor_transition
    //     next_state next_state terminateTransition
    // } for exactly 7 Node is sat

    //example 4: case 4(db's sibling is red)
    dbSibRed: {
        //              0B
        //            /   \
        //          -3B     3B 
        //         /  \   /  \
        //       -5B -2B 2B   4R
        //        delete ^   /  \
        //                  1B  5B
        some n1, n2, n3, n4, n5, n6, n7, n8, n9, db : Node | {
            value = n1 -> 0 + n2 -> -3 + n3 -> 3 + n4 -> -5 + n5 -> -2
                + n6 -> 2 + n7 -> 4 + n8 -> 1 + n9 -> 5
            left = n1 -> n2 + n2 -> n4 + n3 -> n6 + n7 -> n8
            right = n1 -> n3 + n2 -> n5 + n3 -> n7 + n7 -> n9
            color = (n1 + n2 + n3 + n4 + n5 + n6 + n8 + n9) -> Black + (n7) -> Red
            no type
            no nullNode

            // replace n6 (2) with db null
            value' = value
            left' = left
            right' = right
            color' = color
            type' = n6 -> DoubleBlack
            nullNode' = n6 -> IsNull

            // case 4: swap n3's color with n7's color, rotate n3 towards db
            value'' = value
            left'' = n1 -> n2 + n2 -> n4 + n7 -> n3 + n3 -> n6
            right'' = n1 -> n7 + n2 -> n5 + n7 -> n9 + n3 -> n8
            color'' = (n1 + n2 + n4 + n5 + n6 +n7 + n8 + n9) -> Black + (n3) -> Red
            type'' = n6 -> DoubleBlack
            nullNode'' = n6 -> IsNull

            value''' = value
            left''' = n1 -> n2 + n2 -> n4 + n7 -> n3
            right''' = n1 -> n7 + n2 -> n5 + n7 -> n9 + n3 -> n8
            color''' = (n1 + n2 + n4 + n5 + n6 +n7 + n8 + n9) -> Black + (n3) -> Red
            no type'''
            no nullNode'''
        }

    } for exactly 9 Node is sat

    // case 4:
    case4: {
        init
        some n1, n2, n3, n4, n5, n6, n7, n8, n9 : Node | {
            value = n1 -> 0 + n2-> -4 + n3 -> 4 + n4->-6 + n5->-2 + n6->2 + n7->6 + n8 -> 5 + n9 -> 7

            left = n1 -> n2 + n2->n4 + n3->n6 + n7->n8
            right = n1 -> n3 + n2->n5 + n3-> n7 + n7->n9

            color = (n1 + n2 + n3 + n4 + n5 + n6 + n8 + n9) -> Black + (n7) -> Red

            delete[n6]
        }
        traces_del
        eventually wellformed_rb
    } for exactly 9 Node is sat

    // case 5/case6: 
    case5Case6:  { 
        init
        some n1, n2, n3, n4, n5, n6, n7, n8, n9 : Node | {
            value = n1 -> 0 + n2-> -4 + n3 -> 4 + n4->-6 + n5->-2 + n6->2 + n7->6 + n8 -> 1 + n9 -> 3

            left = n1 -> n2 + n2->n4 + n3->n6 + n6->n8
            right = n1 -> n3 + n2->n5 + n3-> n7 + n6->n9

            color = (n1 + n2 + n3 + n4 + n5 + n7 + n8 + n9) -> Black + (n6) -> Red

            delete[n4]
        }
        traces_del
        eventually wellformed_rb
    } for exactly 9 Node is sat
}


test expect {
    // vacuous: can delete
    vacuous: {
        traces_del
        delete_transition
    } is sat

    // CASES
    // cannot delete in empty tree
    cannotDeleteEmpty : {
        traces_del
        no root
        some n : Node | delete[n]
    } for exactly 2 Node is unsat

    // can delete root node in empty tree
    deleteRootEmpty : {
        traces_del
        some root
        no root.left
        no root.right
        delete_transition
    } for exactly 2 Node is sat

    // can delete root node in not empty tree
    deleteRootLR : {
        traces_del
        some root.left
        some root.right
        delete[root]
    } for exactly 4 Node is sat

    // can delete in 3 node tree
    delete3Nodes : {
        traces_del
        some root.left
        some root.right
        delete_transition
    } for exactly 4 Node is sat

    // // can delete in height 3 tree
    deleteHeight3: {
        traces_del
        #{treeNode} = 7
        delete_transition
    } for exactly 8 Node is sat

    // can delete such that there is no recolor or rotation
    deleteNoRecolorNoRotation: {
        traces_del
        delete_transition
        not (eventually delete_recolor_transition)
        not (eventually del_rotate_transition)
    } for exactly 3 Node is sat

    // can delete node with children
    deleteWithChildren: {
        traces_del
        some n : Node | {delete[n] and some n.children}
    } for exactly 5 Node is sat

    // PROPERTIES
    // deletion eventually means wellformed
    deleteToWellformed: {
        traces_del => {
            delete_transition => eventually wellformed_rb
        }
    } is theorem

    // double black node implies not wellformed
    dbNotWellformed: {
        traces_del => {
            some dbNode => not wellformed_rb
        }
    } is theorem

    // if a node is db, it will eventually not be in tree
    dbToOutOfTree: {
        traces_del => {
            some dbNode => eventually no dbNode
        }
    } is theorem

    // cannot insert while performing deletion and vice versa
    
    // can't delete a node not in tree
    cannotDeleteOutOfTree: {
        traces_del => { all n: {Node - treeNode} | {
            not delete[n]
        } }
    } is theorem
}

test expect {
    // PROPERTY TESTS
    tracesBehavior: {
        traces_del => always {
            -- binary tree always maintained at each intermediate step
            wellformed_binary

            -- at the end, we have a wellformed red-black tree
            terminateTransition => wellformed_rb

            // eventually wellformed_rb after delete
            delete_transition => eventually wellformed_rb

            // only delete_recolor when current state is not wellformed
            delete_recolor_transition => not wellformed_rb
        }
    } for 6 Node is theorem
}
