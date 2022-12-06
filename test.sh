#!/bin/sh

echo out/Test.v > _CoqProject

for file in lh-examples/*.hs; do
  echo Translating ${file}
  tmp=${file#lh-examples/}
  outfile=out/${tmp%.hs}.v
  stack run -- ${file} > ${outfile} 
  echo Translation written in ${outfile}
  [ "$CI" ] && echo ========== ${outfile} && cat ${outfile}
  echo ${outfile} | tail -n 1 >> _CoqProject 
done
