# red-black-tree-forge

## Model Structure

### Sigs

Tree:

We have a one sig Tree that contains the root of the tree (which is a Node). This si so that we can have an empty tree and also so that the root can change as nodes are added and removed.

Node:

The Node sig represents a node in the tree. It contains a value (which must be an int that does nto change), a left and right Node and a Color. The left, right, and color are all vars so that they can change as the tree is rearranged.

Color:

We have an abstract sig Color which is extended by Black and Red in order to represent the fact that nodes can either be black or red.

### Predicates

Wellformed:

Our wellformed predicate is separated into three predicates for our tree: wellformed_tree, wellformed_binary, wellformed_rb. This is because, during transitions of the tree (ie when a node is inserted), the tree is no longer a well-formed red-black tree, however it will still be a wellformed_tree. Thus, we separated out these three predicates so that they can build on each other. A wellformed_tree ensures that the nodes do not reach themselves, and that they are all unique in the tree. The wellformed_binary predicate ensures that the tree is a wellformed_tree and also that the values follow the laws of a binary tree: the values to the left of a node are all less than their parent and the values to the right of a node are all greater than their parent. Lastly, wellformed_rb ensures that the tree is both wellformed_tree and wellformed_binary while also adding the properties of a red-black tree (the root must be black, there cannot be two adjacent red nodes, and any path from a node to a leaf must pass through the same number of black nodes for its left and right children).

traces:

One of the other main predicates of our model is traces. Traces allows us to follow changes to our tree. Traces ensures that the tree always starts as a wellformed_rb tree.

THIS MIGHT CHANGE

In the next states, it ensures that either insert_transition, rotate_transition, recolor_transition, or terminate_transition are taking place.

insert_transition:

This predicate is the first step of the insertion algorithm for a red-black tree. When insert_transition is satisfied it means that the starting state is a wellformed_rb tree, and then next state will have one more node connected to the tree (such that the tree is still a binary search tree). However, the next state will not necessarily be a wellformed_rb tree because the insertion algorithm will nto be completed.

rotate_transition/recolor_transition:

These predicates represent the intermediate steps in the insertion algorithm. Once a node has been added, the function nextInsertNode can identify a node that is causing the tree to not be wellformed. Then, depending on the current coloring, the tree will either be rotated or recolored. If the uncle of the nextInsertNode is Red, then the tree can simply be recolored. If the uncle is Black, then that means that a rotation will take place. Thus, each step of the algorithm takes place as it rotates and recolors until it is wellformed.

terminate_transition:

This predicate is the last state after the tree changes. If the termination predicate can be reached, this means that there is no nextInsertNode and the tree must be wellformed.

## Model Properties

By structuring our model this way we were able to test several properties about the insertion process for red-black trees.

First, we were able to check that following the insertion algorithm (starting with a wellformed_rb tree) will maintain a wellformed_rb tree when insertion is completed.

Another property of insertion that we were able to test is that a binary tree is maintained throughout the enter insertion process.

OTHER PROPERTIES???

RUNTIME PROPERTIES???

## Tradeoffs made

## Assumptions made

One of the major assumptions we made in the design of our model is that if a node does not have a left or a right node then that means that there is a leaf there that is colored black. This is a property of a red-black tree, however, we decided to not explicitly code the leaf since we know that we could always rely on the leaf being a black node with no value.

## Model Limits

## Adjustments from Proposal

Our model pretty accurately encompasses what we set out to do in our proposal.

## Understanding Output/Visualization
