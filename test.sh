#!/bin/bash
set -e

for FILE in tests/*.frg
do
  echo "Running $FILE"
  racket "$FILE"
  echo "---------------------"
  echo
done
