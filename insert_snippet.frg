
pred containsEdges[subset: Node, superset: Node, newNode: Node, side: Node -> Node] {
  // all parent to child edges in the pre state exist in the post state
  all subParent, subChild: Node | {
    (contains[subset, subParent] and subParent.side = subChild) => {
      subChild = newNode or (some superParent, superChild: Node | {
        contains[superset, superParent]
        superParent.side = superChild
        // maintain the same parent and child values
        subParent.value = superParent.value
        subChild.value = superChild.value
      })
    }
  }
}

example edges is { some disj n1, n2: Node | containsEdges[n1, n2, none, left] and containsEdges[n1, n2, none, right] } for {
  Node = `N1 + `N2
  value = `N1 -> 0 +
          `N2 -> 0
}

pred preservesSort[root: Node, inserted: Node] {
  all n: Node | contains[root, n] => {
    // if the inserted node is in the left subtree of node n, its value is less than n's
    (some n.left and contains[n.left, inserted]) =>
      n.value > inserted.value
    // if the inserted node is in the right subtree of node n, its value is greater than n's
    (some n.right and contains[n.right, inserted]) =>
      n.value < inserted.value
  }
}

pred insert[pre: Node, post: Node, val: Int] {
  // same root values for the pre and post nodes
  pre.value = post.value

  no n: Node | contains[pre, n] and n.value = val

  some newNode: Node | {
    newNode.value = val
    isLeaf[newNode]
    isChild[post, newNode]
    hasOneParent[post, newNode]
    preservesSort[post, newNode]

    // all edges in the pre tree must be in the post tree on the same side
    containsEdges[pre, post, none, left]
    containsEdges[pre, post, none, right]

    // the new node must in edges of only one side of the post tree, not both
    (
      (containsEdges[post, pre, none, left] and containsEdges[post, pre, newNode, right]) or
      (containsEdges[post, pre, newNode, left] and containsEdges[post, pre, none, right])
    )
  }
}

pred doInsert[pre: Node, post: Node] {
  some i: Int | insert[pre, post, i]
}