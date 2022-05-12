# red-black-tree-forge

## Model Structure

Our model uses a basic binary tree structure -- each node is a `sig` with lone `left` and `right` nodes, and a tree contains a lone root node. Furthermore, our model only examines a single tree at a time. On top of these structures, we use several helper functions for calculating other relationships such as parent, sibling, etc.

Our insert model implements both the basic binary tree insert algorithm and the required rotations for preserving all properties of a red-black tree. We use Electrum to handle the steps of the insertion algorithm. The initial insert is done in one transition, and each rotation or recoloring step is a separate transition. This approach allows us to test and observe the algorithmic complexity of the fix-up algorithm.

Our delete model implements a very similar approach for modeling deletion from a red-black tree: a transition for the initial deletion followed by transition(s) that fix up the red-black properties.

Finally, we have also implemented a basic search-complexity model. This model implements each step of binary tree lookup, starting at the root node and descending one level in the tree at each transition until the target is found or shown to not exist. This allows us to test the algorithmic complexity of lookup in red-black trees.

### Sigs

* Red-black Trees (`src/tree.frg`):
  * `Tree`: A single sig that contains the state of the tree.
    * `root`: an optional `Node` that indicates the root `Node` of the tree. This may be `none` in the case of an empty tree, and may change as nodes are added, removed, or rotated.
    * `step`: a counter that counts the number of algorithm steps (insert, rotates, recolors, etc.) that have been completed in a trace. This is used to prove worst-case complexity.
  * `Node`: Represents a node in the tree.
    * `value`: an `Int` value, which allows us to compare nodes for proper placement in the binary search tree. This does not change.
    * `left`, `right`: an optional node pointing to the left or right node in the tree.
    * `color`: represents the color of the node in the red-black tree.
    * `type`: (deletion-specific) a flag to mark a "double-black" node during deletion.
    * `nullNode`: (deletion-specific) a flag to mark a "nil" node during deletion.
  * `Color`: an empty abstract sig `Color` which is extended by `Black` and `Red`, used by the `Node.color` property
  * `Type`: (deletion-specific) an empty abstract sig extended by `Single` or `DoubleBlack`, used by the `Node.type` property.
  * `NullNode`: (deletion-specific) an empty abstract sig extended by `IsNull` and `NotNull`, used by the `Node.nullNode` property.
* Lookup Traces (`src/lookup.frg`)
  * `Lookup`: A single sig that contains the lookup state
    * `target`: an integer value that is the target value to find in the tree
    * `current`: the current node that is being examined in a given trace instance

### Predicates

Wellformed:

Our wellformed predicate is separated into three predicates for our tree: `wellformed_tree`, `wellformed_binary`, `wellformed_rb`. This is because, during transitions of the tree (ie when a node is inserted), the tree is no longer a well-formed red-black tree, however it will still be a wellformed_tree. Thus, we separated out these three predicates so that they can build on each other. A `wellformed_tree` ensures that the nodes do not reach themselves, and that they are all unique in the tree. The `wellformed_binary` predicate ensures that the tree is a wellformed_tree and also that the values follow the laws of a binary tree: the values to the left of a node are all less than their parent and the values to the right of a node are all greater than their parent. Lastly, `wellformed_rb` ensures that the tree is both wellformed_tree and wellformed_binary while also adding the properties of a red-black tree (the root must be black, there cannot be two adjacent red nodes, and any path from a node to a leaf must pass through the same number of black nodes for its left and right children).

insertTraces:

One of the other main predicates of our model is `insertTraces`. Traces allows us to follow changes to our tree for insertion. Traces ensures that the tree always starts in our `init` state (wellformed).

In the next states, it ensures that either `insertTransition`, `insertRotateTransition`, `insertRecolorTransition`, or `terminateTransition` are taking place.

insertTransition:

This predicate is the first step of the insertion algorithm for a red-black tree. When `insertTransition` is satisfied it means that the starting state is a `wellformed_rb` tree, and then next state will have one more node connected to the tree (such that the tree is still a binary search tree). However, the next state will not necessarily be a `wellformed_rb` tree because the insertion algorithm will nto be completed.

insertRotateTransition/insertRecolorTransition:

These predicates represent the intermediate steps in the insertion algorithm. Once a node has been added, the function `nextInsertNode` can identify a node that is causing the tree to not be wellformed. Then, depending on the current coloring, the tree will either be rotated or recolored. If the uncle of the nextInsertNode is Red, then the tree can simply be recolored. If the uncle is Black, then that means that a rotation will take place. Thus, each step of the algorithm takes place as it rotates and recolors until it is wellformed.

terminate_transition:

This predicate is the last state after the tree changes. If the termination predicate can be reached, this means that there is no `nextInsertNode` and the tree must be wellformed.

traces_del:

We also have a traces predicate for the deletion algorithm. This predicate functions similarly as the insertTraces, but also includes the transitions necessary for deleting.

delete_transition:

This predicate is the first step of the deletion algorithm for a red-black tree. When the `delete_transition` predicate is satisfied, it ensures that we are starting with a `wellformed_rb` tree. From there, it will delete one of the nodes ensuring that the tree is still a binary search tree. It will also replace the node with a double black node according to the rules of red-black tree deletion.

delete_recolor_transition:

This predicate occurs if there is a DoubleBlack node in the tree. It takes the double black node and performs the necessary steps to remove it. The algorithm for deletion outlines various cases on how to handle a DoubleBlack node depending on its positioning, as well as the positioning/color of its sibling node. The predicate will perform the necessary recoloring and rotations. It will remain true until the DoubleBlack node has been removed from the tree and the resulting tree will once again be a `wellformed_rb` tree.

## Testing

### Model Properties

By structuring our model this way we were able to test several properties about the insertion and deletion process for red-black trees. These property tests can be found in the file `red_black_tests_longer_tracelength.frg` under tracesBehavior.

The first property that we show is that `wellformed_binary` is always maintained during traces. This is because even though during insertion and deletion the red-black properties are not always there until the process is over, the tree still uses binary insertion and deletion. Thus, the tree will always a binary tree.

Another property we showed is that `terminateTransition implies wellformed_rb`. This means that when nothing changes it should be true that our tree is a proper red-black tree.

We were also able to show properties that we specific to insertion:

One of the main properties we were able to check is that an `insertTransition` will eventually result in a `wellformed_rb` tree. This means that the insertion algorithm will  always complete and the end state will be a wellformed red-black tree.

We also were able to show specific properties related to the insertion algorithm. We showed that `insertRotateTransition` or `insertRecolorTransition` only happens when the tree is not wellformed. This shows that we never have an unnecessary rotate or recoloring when the tree is already wellformed.

Lastly, we sought to test similar properties for the deletion algorithm. However, with deletion (as this part of the algorithm was in our reach) it is not entirely complete and so the properties do not pass for more than four nodes. That being said, here are the properties we wanted to show:

First, we included a test that a `delete_transition implies eventually wellformed_rb`. Just as with insertion, this would that once deletion has begun, the algorithm will always complete such that the tree is a wellformed_rb tree.

Second, we also included a test that `delete_recolor_transition implies not wellformed_rb`. This shows that recoloring only happens when the tree is not wellformed.

It is important to note that when running the deletion adds a significant time complexity. Thus, to be able to run the tracesBehavior test with reasonable runtime the number of nodes we recommend is 4. However, for the insertion predicates (if you comment out the deletion related code in traces and the tests) are able to run with a relatively reasonable time for 6 Nodes.

### Runtime properties

(Conrad)

### Unit tests

rb_tests

These tests include both a multitude of examples of Red Black Trees and essential properties we would like to check for static trees. These tests prove we can have trees with many nodes, the essential properties of a red black tree are fulfilled (see list below), and the functions we have about the relationships between nodes are correct.

Essential Properties of Red Black Tree (which ensure balance):
1. Every node is black or red (by Node sig definition)
2. Every leaf is null and black (assumption of our model)
3. If a node is red, its children are black
4. Every path from a node to its leaves contains the same amount of black nodes (ensures balance)


rb_height_tests

These tests demonstrate the essential relationship between the number of nodes in a tree and the maximum height of a tree. In other words, the tests in this file prove that the model's trees are balanced with increasing height.

insert_tests

This file includes the basic tests for insertion that can be proved with a tracelength of 2. Essentially, this tests a basic insertion with no recolor or rotation as a result. The tests include testing that we can and cannot insert into the type of trees we expect and essential properties of insert, such as insert increasing the size of the tree and that insert will eventually lead to a wellformed tree via traces.

insert_tests_longer_tracelength

We split the tests for insert that require a longer tracelength into this file as to prevent unnecessarily long runtimes while testing basic insert properties. There are three tests: some node to insert implies the tree is not wellformed, all predicates to do with insert will eventually lead to a wellformed tree via traces, and that insert can occur without recoloring or rotating.

insert_rotate_tests

These tests are examples for rotate to ensure it behaves as expected in those examples. They cover each type of rotation. Additionally, we test that all nodes are preserved through rotation.

insert_recolor_tests

As with rotate tests, these tests include examples for each type of recoloring in terms of insertion. Additionally, there are property tests for recoloring, such as ensuring that a wellformed tree cannot be recolored, checking the maximum number of nodes possibly recolored, and ensuring that there is a case such that a recoloring results in a wellformed tree.

delete_tests

The delete tests encompass examples for each potential case of deletion in terms of the location of the DoubleBlack node. It also includes property tests for deletion, such that deletion cannot occur in an empty tree, you can delete in trees of various height and number of nodes, and that some DoubleBlack node implies that the tree is not wellformed. 
Note: some tests are commented out in this file. As noted above, our implementation of delete still has some bugs. Therefore, the commented out tests are failing.

## Assumptions made

One of the major assumptions we made in the design of our model is that if a node does not have a left or a right node then that means that there is a leaf there that is colored black. This is a property of a red-black tree, however, we decided to not explicitly code the leaf since we know that we could always rely on the leaf being a black node with no value.

## Challenges

As mentioned briefly earlier, the main area we had trouble was deletion. This part of the algorithm is both more complex and was also one of our reach goals—thus giving us less time to complete it-and we therefore did not entirely model the algorithm. We have the general structure outlined (the delete_transition and delete_recolor_transition predicates in traces) and simple cases work. However, as we have shown with tests that we have left commented out, all of the cases of the deletion algorithm that should be SAT are not necessarily SAT. One of the things tht made this particularly challenging, is the fact that the complex nature of the algorithm greatly impacted our efficiency. Thus, debugging became more challenging as running the code and finding counter examples would take a long time.  We still included the code that we were able to put together in order to show how deletion could be modeled given more time.

## Adjustments from Proposal

Our model pretty accurately encompasses what we set out to do in our proposal.

## Understanding Output/Visualization

Our visualizer can be found in the file `rb_theme.js`. It runs through the `<svg>` script in Sterling. When you run, the first state of the tree will appear in the center of the screen. Each node is represented by a circle with their value inside. The connections between parents and children are represented by lines. The color will either be black (for a black node), red (for a red node), or blue (for a DoubleBlack node). At the bottom of the screen, all states of the tree are shown with the left-most tree being the first state and the right-most tree being the last state. To change the state of the main tree (shown in the center of the page), a user can use the next or prev buttons in the top right and top left corners of the visualizer.