#lang forge "final" "jpqtay573rwx8pc6@gmail.com"

open "tree_electrum.frg"
open "red_black.frg"

option max_tracelength 5

test expect {
    // PROPERTY TESTS

    // some nextInsertNode implies tree is not wellformed
    nextInsertImpliesWellformed: {
        some nextInsertNode => not wellformed_rb
    } is theorem

    tracesBehavior: {
        traces => {
            always {
                -- binary tree always maintained
                wellformed_binary

                -- terminate transition implies wellformed red-black
                terminate_transition => wellformed_rb

                -- insert implies will reach wellformed red-black
                insert_transition => eventually wellformed_rb
                
                -- Root node can never disappear
                -- Note: should be removed if doing deletion
                // (some rootNode) => always (some rootNode)

                -- Only rotate or recolor when the current state is not well-formed
                (rotate_transition or recolor_transition) => not wellformed_rb

                -- when the tree recolors, the next state will be well-formed
                recolor_transition => next_state wellformed_rb

                // -- delete recolor implies not wellformed
                delete_recolor_transition => not wellformed_rb

                // -- eventually wellformed_rb after delete
                delete_transition => eventually wellformed_rb

                // -- only delete_recolor when current state is not wellformed
                delete_recolor_transition => not wellformed_rb
            }
        }
    } for exactly 6 Node is theorem

    canInsertWithoutRecolorOrRotate: {
        traces

        some Tree.rootNode
        some Tree.rootNode.left
        some Tree.rootNode.right

        insert_transition
        next_state terminate_transition
    } for exactly 4 Node is sat
}