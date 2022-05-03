#!/bin/bash
set -e

echo "Running basic tests"
racket red_black_tests.frg

echo
echo "Running insert tests"
racket insert_tests.frg

echo
echo "Running recolor tests"
racket recolor_tests.frg

echo
echo "Running rotate tests"
racket rotate_tests.frg

echo
echo "Running property tests"
racket red_black_tests_longer_tracelength.frg

echo
echo "Running tree-height tests"
racket height_tests.frg
