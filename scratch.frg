#lang forge

open "tree.frg"
open "red_black.frg"

option max_tracelength 4

run {
    traces
    not {
        always {
            -- binary tree always maintained
            wellformedBST

            -- terminate transition implies wellformed red-black
            terminate_transition => wellformedRBT

            -- insert implies will reach wellformed red-black
            insert_transition => eventually wellformedRBT
            
            -- Root node can never disappear
            -- Note: should be removed if doing deletion
            // (some rootNode) => always (some rootNode)

            -- Only rotate or recolor when the current state is not well-formed
            (rotate_transition or recolor_transition) => not wellformedRBT

            -- when the tree recolors, the next state will be well-formed
            recolor_transition => next_state wellformedRBT

            // -- eventually wellformedRBT after delete
            delete_transition => eventually wellformedRBT

            // -- only delete_recolor when current state is not wellformed
            delete_recolor_transition => not wellformedRBT
        }
    }
} for exactly 6 Node
