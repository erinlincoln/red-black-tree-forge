# red-black-tree-forge

## Model Structure

TODO: ADD MODEL STRUCTURE OVERVIEW (Conrad)

### Sigs

Tree:

We have a one sig `Tree` that contains the root of the tree (which is a Node). This si so that we can have an empty tree and also so that the root can change as nodes are added and removed.

Node:

The `Node` sig represents a node in the tree. It contains a value (which must be an int that does nto change), a left and right Node and a Color. The left, right, and color are all vars so that they can change as the tree is rearranged.

Color:

We have an abstract sig `Color` which is extended by Black and Red in order to represent the fact that nodes can either be black or red.

### Predicates

Wellformed:

Our wellformed predicate is separated into three predicates for our tree: `wellformed_tree`, `wellformed_binary`, `wellformed_rb`. This is because, during transitions of the tree (ie when a node is inserted), the tree is no longer a well-formed red-black tree, however it will still be a wellformed_tree. Thus, we separated out these three predicates so that they can build on each other. A `wellformed_tree` ensures that the nodes do not reach themselves, and that they are all unique in the tree. The `wellformed_binary` predicate ensures that the tree is a wellformed_tree and also that the values follow the laws of a binary tree: the values to the left of a node are all less than their parent and the values to the right of a node are all greater than their parent. Lastly, `wellformed_rb` ensures that the tree is both wellformed_tree and wellformed_binary while also adding the properties of a red-black tree (the root must be black, there cannot be two adjacent red nodes, and any path from a node to a leaf must pass through the same number of black nodes for its left and right children).

traces:

One of the other main predicates of our model is `traces`. Traces allows us to follow changes to our tree. Traces ensures that the tree always starts as a `wellformed_rb` tree.

In the next states, it ensures that either `insert_transition`, `rotate_transition`, `recolor_transition`, `delete_transition`, `delete_recolor_transition`, or `terminate_transition` are taking place.

insert_transition:

This predicate is the first step of the insertion algorithm for a red-black tree. When `insert_transition` is satisfied it means that the starting state is a `wellformed_rb` tree, and then next state will have one more node connected to the tree (such that the tree is still a binary search tree). However, the next state will not necessarily be a `wellformed_rb` tree because the insertion algorithm will nto be completed.

rotate_transition/recolor_transition:

These predicates represent the intermediate steps in the insertion algorithm. Once a node has been added, the function `nextInsertNode` can identify a node that is causing the tree to not be wellformed. Then, depending on the current coloring, the tree will either be rotated or recolored. If the uncle of the nextInsertNode is Red, then the tree can simply be recolored. If the uncle is Black, then that means that a rotation will take place. Thus, each step of the algorithm takes place as it rotates and recolors until it is wellformed.

delete_transition:

This predicate is the first step of the deletion algorithm for a red-black tree. When the `delete_transition` predicate is satisfied, it ensures that we are starting with a `wellformed_rb` tree. From there, it will delete one of the nodes ensuring that the tree is still a binary search tree. It will also replace the node with a double black node according to the rules of red-black tree deletion.

delete_recolor_transition:

This predicate occurs if there is a DoubleBlack node in the tree. It takes the double black node and performs the necessary steps to remove it. The algorithm for deletion outlines various cases on how to handle a DoubleBlack node depending on its positioning, as well as the positioning/color of its sibling node. The predicate will perform the necessary recoloring and rotations. It will remain true until the DoubleBlack node has been removed from the tree and the resulting tree will once again be a `wellformed_rb` tree.

terminate_transition:

This predicate is the last state after the tree changes. If the termination predicate can be reached, this means that there is no `nextInsertNode` and the tree must be wellformed.

## Testing

### Model Properties

By structuring our model this way we were able to test several properties about the insertion and deletion process for red-black trees. These property tests can be found in the file `red_black_tests_longer_tracelength.frg` under tracesBehavior.

The first property that we show is that `wellformed_binary` is always maintained during traces. This is because even though during insertion and deletion the red-black properties are not always there until the process is over, the tree still uses binary insertion and deletion. Thus, the tree will always a binary tree.

Another property we showed is that `terminate_transition implies wellformed_rb`. This means that when nothing changes it should be true that our tree is a proper red-black tree.

We were also able to show properties that we specific to insertion:

One of the main properties we were able to check is that an `insert_transition` will eventually result in a `wellformed_rb` tree. This means that the insertion algorithm will  always complete and the end state will be a wellformed red-black tree.

We also were able to show specific properties related to the insertion algorithm. We showed that `rotate_transition` or `recolor_transition` only happens when the tree is not wellformed. This shows that we never have an unnecessary rotate or recoloring when the tree is already wellformed.

TODO: EXPLAIN THAT THIS DIDNT QUITE HAPPEN (Julia)

Lastly, we were able to test similar properties for the deletion algorithm.

First, we showed that a `delete_transition implies eventually wellformed_rb`. Just as with insertion, this shows that once deletion has begun, the algorithm will always complete such that the tree is a wellformed_rb tree.

Second, we also showed that `delete_recolor_transition implies not wellformed_rb`. This shows that recoloring only happens when the tree is not wellformed.

It is important to note that when running the deletion adds a significant time complexity. Thus, to be able to run the tracesBehavior test with reasonable runtime the number of nodes we recommend is 6. However, for the insertion predicates (if you comment out the deletion related code in traces and the tests) are able to run with a relatively reasonable time for 6 Nodes.

### Runtime properties

(Conrad)

### Unit tests

(Erin)

## Assumptions made

One of the major assumptions we made in the design of our model is that if a node does not have a left or a right node then that means that there is a leaf there that is colored black. This is a property of a red-black tree, however, we decided to not explicitly code the leaf since we know that we could always rely on the leaf being a black node with no value.

## Challenges

(Julia)

## Adjustments from Proposal

Our model pretty accurately encompasses what we set out to do in our proposal.

## Understanding Output/Visualization

UPDATE (Erin)

Our visualizer can be found in the file `rb_theme.js`. It runs through the `<svg>` script in Sterling. When you run, the states will appear vertically, centered around the root node. Each node is represented by a circle with their value inside. The color will either be black (for a black node), red (for a red node), or blue (for a DoubleBlack node). Each state shows one of the transitions.