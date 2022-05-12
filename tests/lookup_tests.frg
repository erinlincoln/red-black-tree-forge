#lang forge

open "../src/tree.frg"
open "../src/lookup.frg"

option max_tracelength 6

// Proves worst-case lookup algorithm complexity on a RBT

test expect {
  vacuous1: {
    lookupTraces and complexity = 1
  } for exactly 1 Node is sat

  complexity1: {
    lookupTraces => complexity <= 1
  } for 1 Node is theorem

  vacuous2: {
    lookupTraces and complexity = 1
  } for exactly 2 Node is sat

  complexity2: {
    lookupTraces => complexity <= 2
  } for 2 Node is theorem

  vacuous3: {
    lookupTraces and complexity = 3
  } for exactly 4 Node is sat

  complexity3: {
    lookupTraces => complexity <= 3
  } for 5 Node is theorem

  vacuous4: {
    lookupTraces
    complexity = 4
  } for exactly 6 Node is sat

  complexity4: {
    lookupTraces => complexity <= 4
  } for 7 Node is theorem
  // Could do 9 Node but that takes too long

}
