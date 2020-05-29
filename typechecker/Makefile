COMPILER=ocamlbuild
CHECKER=check

all: 
	$(COMPILER) -I analysis -I lang_pool_sc -I utils -I infer -I lang_coq_sc $(CHECKER).byte -pkgs llvm  


clean:
	$(COMPILER) -clean
