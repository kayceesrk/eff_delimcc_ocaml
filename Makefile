all:
	ocamlbuild -lib unix queens_base_multicore.native 
	ocamlbuild -I . delimcc_paper_examples.native

eff_of_delimcc: 
	ocamlbuild -I . eff_of_delimcc.native

clean:
	ocamlbuild -clean
