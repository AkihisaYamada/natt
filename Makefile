OCAMLC=ocamlc
OCAMLOPT=ocamlopt
OCAMLDEP=ocamldep
OCAMLYACC=ocamlyacc
OCAMLLEX=ocamllex
OCAMLDOC=ocamldoc -html -d htdocs -t "Termination Tool"
INCLUDES=-I +ocamlgraph
OCAMLFLAGS=$(INCLUDES)    # add other options for ocamlc here
OCAMLOPTFLAGS=$(INCLUDES) # add other options for ocamlopt here

# The list of ocaml source files
OCAML_SRCS=\
	trs_ast.ml trs_parser.mly trs_lexer.mll trs_sem.ml read.ml \
	util.ml matrix.ml params.ml proc.ml smt.ml preorder.ml mset.ml \
	abbrev.ml term.ml subst.ml trs.ml dp.ml app.ml wpo.ml nonterm.ml \
	main.ml
OCAML_CMAS=\
	graph.cma unix.cma str.cma

OCAML_MLS=$(patsubst %.mll,%.ml,$(OCAML_SRCS:%.mly=%.ml))

OCAML_CMOS=$(OCAML_MLS:%.ml=%.cmo)

OCAML_CMXS=$(OCAML_MLS:%.ml=%.cmx)

OCAML_CMXAS=$(OCAML_CMAS:%.cma=%.cmxa)

all: NaTT

install: all
	cp -f NaTT.bin NaTT xtc2tpdb.xml /usr/local/bin/

NaTT: $(OCAML_CMXS)
	$(OCAMLOPT) -o $@ $(OCAML_CMXAS) $(OCAMLFLAGS) $^

# Common rules
.SUFFIXES: .ml .mli .cmo .cmi .cmx .mll .mly

.ml.cmo:
	$(OCAMLC) $(OCAMLFLAGS) -c $<

.mli.cmi:
	$(OCAMLC) $(OCAMLFLAGS) -c $<

.ml.cmx:
	$(OCAMLOPT) $(OCAMLOPTFLAGS) -c $<

.mly.ml:
	$(OCAMLYACC) $<

.mll.ml:
	$(OCAMLLEX) $<

# Clean up
clean:
	rm -f NaTT
	rm -f *.cm[iox] *.o *.mli .depend
	rm trs_parser.ml trs_lexer.ml

# Dependencies
.depend: $(OCAML_MLS)
	$(OCAMLDEP) *.mli *.ml > .depend

include experiments.mk
-include .depend
