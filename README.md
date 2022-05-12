# red-black-tree-forge

## Model Structure

Our model uses a basic binary tree structure -- each node has an optional left and an optional right node, and a tree contains an optional root node. Our model only examines a single tree at a time. On top of these structures, we use several helper functions for calculating other relationships such as parent, sibling, etc.

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

### Wellformed Trees

The code for modeling static red-black trees is contained in `src/tree.frg`.

Our wellformed predicate is separated into three predicates for our tree: `wellformedTree`, `wellformedBST`, `wellformedRBT`. This is because, during transitions of the tree (ie when a node is inserted), the tree is no longer a well-formed RBT, however, it will still be a wellformed binary tree. Thus, we separated out these three predicates so that they can build on each other and we use them to prove different properties in different contexts.

`wellformedTree` ensures that the graph is acyclic and that left/right relations are properly defined so that each node has a single parent.

The `wellformedBST` predicate ensures that the tree is a wellformed tree and also that the nodes satisfy the properties of a binary search tree: the values to the left of a node are all less than their parent and the values to the right of a node are all greater than their parent.

Lastly, `wellformedRBT` ensures that the tree satisfies both `wellformedTree` and `wellformedBST` while also adding the properties of a red-black tree: the root must be black, there cannot be two adjacent red nodes, and any path from a node to a leaf must pass through the same number of black nodes.

### Insertion Predicates

The code modeling deletion in a RBT is contained in `src/tree.frg`. Note that throughout the insertion algorithm, we do not explicitly require the tree to be wellformed. Instead, we prove that the algorithm will always produce a wellformed red-black tree when it is complete. As outlined in the Model Structure section, we implement insertion by first inserting the node into the BST and then rotating/recoloring it to restore the RBT properties.

#### `insertTraces`

One of the other main predicates of our model is `insertTraces`. Traces allows us to follow changes to our tree for insertion. Traces ensures that the tree always starts in our `init` state, with a wellformed RBT.

In the next states, it ensures that either `insertTransition`, `insertRotateTransition`, `insertRecolorTransition`, or `terminateTransition` are taking place.

#### `insertTransition`

This predicate is the first step of the insertion algorithm for a red-black tree. When `insertTransition` is satisfied it means that then next state will have one more node connected to the tree, such that the tree is still a binary search tree. However, the next state will not necessarily be a `wellformedRBT` tree because the insertion algorithm for the red-black tree will not be completed.

#### `insertRotateTransition` and `insertRecolorTransition`

These predicates represent the intermediate steps in the insertion algorithm. Once a node has been added, the function `nextInsertNode` can identify a node that is causing the tree to not be wellformed. Then, depending on the current coloring, the tree will either be rotated or recolored. If the uncle of the nextInsertNode is red, then the tree can simply be recolored. If the uncle is black, then that means that a rotation will take place. Thus, each step of the algorithm takes place as it rotates and recolors until it is wellformed.

#### `terminateTransition`

This predicate is the last state after the tree changes. If the termination predicate can be reached, this means that there is no `nextInsertNode`, which, as our tests prove, indicates that the tree must be wellformed.

### Deletion Predicates

The code for the deletion model is contained in `src/delete.frg`.

IMPORTANT: The delete algorithm is not complete, and several desired properties are not satisfied. Our main goal for the overall project was modeling insertion, hence the deletion algorithm is not as well-implemented or well-tested.

#### `deleteTraces`

We also have a traces predicate for the deletion algorithm. This predicate functions similarly as the insertTraces, but also includes the transitions necessary for deleting. Note that this will allow both insertion and deletion in the same trace.

#### `deleteTransition`

This predicate is the first step of the deletion algorithm for a red-black tree. Starting from a wellformed RBT, it will delete one of the nodes ensuring that the tree is still a binary search tree. It will also replace the node with a double black node according to the rules of red-black tree deletion.

#### `deleteRecolorTransition`

This transition happens if there is a double-black node in the tree. It takes the double-black node and performs the necessary steps to remove it. The algorithm for deletion outlines various cases on how to handle a double-black node depending on its positioning, as well as the positioning/color of its sibling node. The predicate will perform the necessary recoloring and rotations. Successive transitions must also satisfy this transition until the double-black node has been removed from the tree and the resulting tree will once again be a `wellformedRBT` tree.

## Testing

### Model Properties

By structuring our model this way we were able to test several properties about the insertion and deletion process for red-black trees. These property tests can be found in the file `red_black_tests_longer_tracelength.frg`.

The first property that we show is that `wellformedBST` is always maintained during traces. Even though during insertion and deletion the red-black tree properties are not always satisfied until the process is complete, the tree still uses binary search tree insertions, rotations, and deletion. Thus, the tree will always a binary tree.

Another property we showed is that `terminateTransition implies wellformedRBT`. This means that when all rotations/recolorings are complete, we end with a valid red-black tree again.

We were also able to show properties that we specific to insertion:

One of the main properties we were able to check is that an `insertTransition` will eventually result in a `wellformedRBT` tree. This means that the insertion algorithm will always complete and the end state will be a wellformed red-black tree.

We also were able to show specific properties related to the insertion algorithm. We showed that `insertRotateTransition` or `insertRecolorTransition` only happens when the tree is not wellformed. This shows that we never have an unnecessary rotate or recoloring when the tree is already wellformed.

Lastly, we sought to test similar properties for the deletion algorithm. However, deletion (as this part of the algorithm was in our reach) is not entirely complete, so the properties do not pass for more than four nodes. That being said, here are the properties we wanted to show:

First, we included a test that a `deleteTransition implies eventually wellformedRBT`. Just as with insertion, this would that once deletion has begun, the algorithm will always complete such that the tree is a wellformedRBT tree.

Second, we also included a test that `deleteRecolorTransition implies not wellformedRBT`. This shows that recoloring only happens when the tree is not wellformed.

It is important to note that the deletion model adds significant performance overhead to the solver. Thus, to be able to run the `tracesBehavior` test with reasonable runtime, the maximum number of nodes we recommend is 4. However, the insertion predicates (in `insert_tests_longer_tracelength.frg`) are able to run with a relatively reasonable time for 6 Nodes.

### Runtime properties

We have modeled runtime complexity for both lookup and insertion. In order to count complexity, we added a `step` property that is increment in every non-terminal transition. Then we have tests that specify the maximum number of steps for a given number of nodes.

For example, the `insertComplexity` test in `insert_tests_longer_tracelength.frg` specifies that all 6-node trees can be inserted with only three steps (an insertion followed by two rotations/recolorings).

Also, the `src/lookup.frg` and corresponding `src/lookup_tests.frg` contain a full model for lookup complexity in a red-black tree. For example, we prove that lookup in a 5-node red-black tree will always complete in under 4 steps.

In addition, the `tests/rb_height_tests.frg` test file proves the relationship between the number of nodes in a tree and the maximum height of a tree. In other words, the tests in this file prove that red-black trees are balanced with increasing height. However, this balancing is slightly less than optimal. One can reason about the complexity of RBT lookup/insertion/deletion using only the maximum height, since each step of those algorithms should process one level of the tree, meaning that their worst-case complexity should be directly proportional to the height of the tree.

Note that for insertion and deletion, we do not model the complexity of the initial binary search insertion/deletion. An actual implementation would require an algorithm to actually find the node that is to be deleted, which is equivalent to the lookup procedure which we have modeled. Instead, this initial search step and insertion is modeled as a single transition, since we wanted to concentrate on the complexity of the fix-up steps required to preserve RBT properties.

### Unit tests

#### `tests/rb_tests.frg`

These tests include both a multitude of examples of Red Black Trees and essential properties we would like to check for static trees. These tests prove we can have trees with many nodes, the essential properties of a red black tree are fulfilled (see list below), and the functions we have about the relationships between nodes are correct.

Essential Properties of Red Black Tree (which ensure balance):
1. Every node is black or red (by Node sig definition)
2. Every leaf is null and black (assumption of our model)
3. If a node is red, its children are black
4. Every path from a node to its leaves contains the same amount of black nodes (ensures balance)

#### `tests/insert_tests.frg`

This file includes the basic tests for insertion that can be proved with a tracelength of 2. Essentially, this tests a basic insertion with no recolor or rotation as a result. The tests include testing that we can and cannot insert into the type of trees we expect and essential properties of insert, such as insert increasing the size of the tree and that insert will eventually lead to a wellformed tree via traces.

#### `tests/insert_tests_longer_tracelength.frg`

We split the tests for insert that require a longer tracelength into this file as to prevent unnecessarily long runtimes while testing basic insert properties. These tests mainly prove the model properties discussed above.

#### `tests/insert_rotate_tests.frg`

These tests are examples for rotate to ensure it behaves as expected in those examples. They cover each type of rotation. Additionally, we test using induction that all nodes are preserved during rotation.

#### `tests/insert_recolor_tests.frg`

As with rotate tests, these tests include examples for each type of recoloring in terms of insertion. Additionally, there are property tests for recoloring, such as ensuring that a wellformed tree cannot be recolored, checking the maximum number of nodes possibly recolored, and ensuring that there is a case such that a recoloring results in a wellformed tree.

#### `tests/delete_tests.frg`

The delete tests encompass examples for each potential case of deletion in terms of the location of the DoubleBlack node. It also includes property tests for deletion, such that deletion cannot occur in an empty tree, you can delete in trees of various height and number of nodes, and that some DoubleBlack node implies that the tree is not wellformed. 
Note: some tests are commented out in this file. As noted above, our implementation of delete still has some bugs. Therefore, the commented out tests are failing.

## Assumptions Made

One of the major assumptions we made in the design of our model is that if a node does not have a left or a right node then that means that there is a leaf there that is colored black. This is a property of a red-black tree, however, we decided to not explicitly code the leaf since we know that we could always rely on the leaf being a black node with no value. In other words, the terminal black nodes are included implicitly as `none` values.

## Challenges

As mentioned briefly earlier, the main area we had trouble was deletion. This part of the algorithm is both more complex and was also one of our reach goals—thus giving us less time to complete it—and we therefore did not entirely model the algorithm. We have the general structure outlined (the `deleteTransition` and `deleteRecolorTransition` predicates in traces) and simple cases work. However, as we have shown with tests that we have left commented out, all of the cases of the deletion algorithm that should be SAT are not necessarily SAT. One of the things that made this particularly challenging, is the fact that the complex nature of the algorithm greatly impacted our efficiency. Thus, debugging became more challenging as running the code and finding counter examples would take a long time.  We still included the code that we were able to put together in order to show how deletion could be modeled given more time.

In addition, we would have liked to prove that our algorithm can insert into every red-black tree. However, this would require higher-order quantification, since we would basically need to ask Forge for a set of traces given an initial state. To get around this, we have added tests for insertion in different examples and used the visualizer to examine results. Given more time and effort, we could have implemented a tool using Racket that would iterate through possible initial trees that Forge returns and prove that we have a SAT case for insertion into the tree. However, that approach is out of scope for our goals.

## Adjustments from Proposal

Our model pretty accurately encompasses what we set out to do in our proposal.

## Understanding Output/Visualization

Our visualizer can be found in the file `viz/rb_theme.js`. It runs through the `<svg>` script in Sterling. When you run, the first state of the tree will appear in the center of the screen. Each node is represented by a circle with their value inside. The connections between parents and children are represented by lines. The color will either be black (for a black node), red (for a red node), or blue (for a DoubleBlack node). At the bottom of the screen, all states of the tree are shown with the left-most tree being the first state and the right-most tree being the last state. To change the state of the main tree (shown in the center of the page), a user can use the next or prev buttons in the top right and top left corners of the visualizer.