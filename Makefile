all:
	#Needs multicore OCaml compiler
	# $ opam remote add multicore https://github.com/ocamllabs/multicore-opam.git
	# $ opam switch 4.02.2+multicore
	ocamlbuild -lib unix queens_base_multicore.native
	ocamlbuild -I . delimcc_paper_examples.native

delimcc:
	# Needs delimcc library
	ocamlbuild -pkg delimcc eff_of_delimcc.native
	ocamlbuild -pkg delimcc queens_eff_of_delimcc.native

clean:
	ocamlbuild -clean
