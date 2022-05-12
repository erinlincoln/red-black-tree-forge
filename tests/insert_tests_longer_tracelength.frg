#lang forge "final" "jpqtay573rwx8pc6@gmail.com"

open "../src/tree_electrum.frg"
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
            wellformed_binary

            // -- at the end, we have a wellformed red-black tree
            terminateTransition => wellformed_rb

            -- if we do an insert, we will eventually have a wellformed red-black tree
            insertTransition => eventually wellformed_rb

            -- only rotate or recolor when the current state is not well-formed
            (insertRotateTransition or insertRecolorTransition) => not wellformed_rb
        }
    } for 4 Node is theorem

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
