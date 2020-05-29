COMPILER=ocamlc
 
all: clean parsepoolinfo 

parsepoolinfo:
	$(COMPILER) -c ast.ml
	ocamlyacc parse.mly
	$(COMPILER) -c parse.mli
	$(COMPILER) -c parse.ml
	ocamllex lex.mll
	$(COMPILER) -c lex.ml
	$(COMPILER) -c main.ml
	$(COMPILER) -o ppool ast.cmo parse.cmo lex.cmo main.cmo

clean:
	-rm *.cmo *.cmi ppool parse.ml parse.mli lex.ml 
