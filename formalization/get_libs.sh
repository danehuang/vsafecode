#!/bin/bash

pushd libs
  git clone https://github.com/jtristan/CompCert-Toolkit.git
  patch CompCert-Toolkit/Coqlib.v CompCert-Toolkit-patches/coqlib.patch
  patch CompCert-Toolkit/Memory.v CompCert-Toolkit-patches/memory.patch
popd

pushd libs
  wget https://gforge.inria.fr/frs/download.php/file/36199/flocq-2.5.2.tar.gz
  tar -xvzf flocq-2.5.2.tar.gz flocq-2.5.2
  rm flocq-2.5.2.tar.gz
popd
