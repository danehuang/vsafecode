#!/bin/bash

pushd extract
  cp ../formalization/src/Extraction/tc.ml extracted_tc.ml
  python fix.py > tc.ml
  cp tc.ml ../typechecker/lang_coq_sc/tc.ml
popd
