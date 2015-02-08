#!/bin/bash
# Bash script for automatically running tests
# The script accepts a single argument - the directory of the tests.
# The expected tests are .scm file: just files with scheme expressions. 
# The script compiles the files to pseudo-assembly, then to an executable using a makefile, then compares the outputs of the executables
# with the outputs creates by Chez. Diff output is given.

for f in ${1}/*.scm;
do
  echo "(compile-scheme-file \"${f}\" \"${f%.scm}.c\")" | petite compiler.scm -q
  cat $f | petite -q > ${f%.scm}.txt
done
(cd $1 && make)

for f in ${1}/*;
do
  if [[ -x "$f" ]] 
  then
    ./$f > ${f}-out.txt
    diff -Z ${f}-out.txt ${f}.txt
  fi
done

