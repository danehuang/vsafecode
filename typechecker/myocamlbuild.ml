open Ocamlbuild_plugin;;

ocaml_lib ~extern:true "llvm";;
ocaml_lib ~extern:true "llvm_analysis";;
ocaml_lib ~extern:true "llvm_bitreader";;
ocaml_lib ~extern:true "llvm_bitwriter";;

flag ["link"; "ocaml"; "g++"] (S[A"-cc"; A"g++"]);;
