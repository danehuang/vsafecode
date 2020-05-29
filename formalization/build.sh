#!/bin/bash

pushd libs

  pushd CompCert-Toolkit
    coq_makefile *.v > Makefile
    make
  popd

  pushd flocq-2.5.2
    ./configure && ./remake && ./remake install
  popd

  coqc Bits.v
  coqc Consider.v
  coqc Tactics.v
popd

pushd src
  make
popd
