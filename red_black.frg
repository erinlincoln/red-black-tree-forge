#lang forge "final" "jpqtay573rwx8pc6@gmail.com"


// Node of each graph - left branch, right branch, and color
sig Node {
    left: lone Node,
    right: lone Node,
    color: one Color
}

// Root of tree (assuming no empty tree)
one sig Root extends Node {}

// Color of nodes
abstract sig Color {}
one sig Black, Red extends Color {}

// wellformed
wellformed {
    // root reaches everything

    // nothing is reachable from itself

    
}