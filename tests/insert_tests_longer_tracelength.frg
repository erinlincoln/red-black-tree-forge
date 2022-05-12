#lang forge "final" "jpqtay573rwx8pc6@gmail.com"

open "../src/tree.frg"
open "../src/insert.frg"

// Insert property tests with longer tracelengths for RBTs.

option max_tracelength 5

// Specific trace that forces their to be only a single insert operation
// Allows us to examine runtime complexity of an insert operation
pred simpleInsertTrace {
    init
    insertTransition
    always (
        insertRotateTransition or
        insertRecolorTransition or
        terminateTransition
    )
}



test expect {
    vacuous: {
        insertTraces
        eventually { insertTransition }
    } for exactly 1 Node is sat

    // PROPERTY TESTS
    tracesBehavior: {
        insertTraces => always {
            -- binary tree always maintained at each intermediate step
            wellformedBST

            -- at the end, we have a wellformed red-black tree
            terminateTransition => wellformedRBT

            -- if we do an insert, we will eventually have a wellformed red-black tree
            insertTransition => eventually wellformedRBT

            -- only rotate or recolor when the current state is not well-formed
            (insertRotateTransition or insertRecolorTransition) => not wellformedRBT

            -- TODO: NEED TO MOVE TO DELETE TESTS
            // // eventually wellformedRBT after delete
            // delete_transition => eventually wellformedRBT

            // // only delete_recolor when current state is not wellformed
            // delete_recolor_transition => not wellformedRBT
        }
    } for 6 Node is theorem

    canInsertWithoutRecolorOrRotate: {
        insertTraces

        some Tree.rootNode
        some Tree.rootNode.left
        some Tree.rootNode.right

        insertTransition
        next_state terminateTransition
    } for exactly 4 Node is sat

    complexInsert: {
        simpleInsertTrace
        eventually (Tree.step = 3)
    } for exactly 5 Node is sat

    insertComplexity: {
        simpleInsertTrace => {
            always (Tree.step <= 3)
        }
    } for 5 Node is theorem
}
