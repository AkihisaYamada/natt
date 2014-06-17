TARG=./NaTT
TARG_OPT=./NaTT.exe
PACKS=ocamlgraph
OCAMLC=ocamlfind ocamlc -package $(PACKS)
OCAMLOPT=ocamlfind ocamlopt -package $(PACKS)
OCAMLDEP=ocamldep
OCAMLYACC=ocamlyacc
OCAMLLEX=ocamllex
OCAMLDOC=ocamldoc -html -d htdocs -t "Termination Tool"

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

all: $(TARG_OPT)

install: all
	cp -f $(TARG_OPT) xtc2tpdb.xml /usr/local/bin/

$(TARG_OPT): $(OCAML_CMXS)
	$(OCAMLOPT) -o $@ $(OCAML_CMXAS) $(OCAMLFLAGS) $^

$(TARG): $(OCAML_CMOS)
	$(OCAMLC) -o $@ $(OCAML_CMAS) $(OCAMLFLAGS) $^

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
	rm -f $(TARG) $(TARG_OPT) *.cm[iox] *.o *.mli .depend
	rm trs_parser.ml trs_lexer.ml

# Dependencies
.depend: $(OCAML_MLS)
	$(OCAMLDEP) *.mli *.ml > .depend

-include .depend
