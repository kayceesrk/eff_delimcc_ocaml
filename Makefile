all:
	ocamlbuild -lib unix queens_base_multicore.native
	ocamlbuild -I . delimcc_paper_examples.native

delimcc:
	# Needs delimcc library
	ocamlbuild eff_of_delimcc.native
	ocamlbuild queens_eff_of_delimcc.native

clean:
	ocamlbuild -clean
