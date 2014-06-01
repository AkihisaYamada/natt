OCAMLC=ocamlc
OCAMLOPT=ocamlopt
OCAMLDEP=ocamldep
OCAMLYACC=ocamlyacc
OCAMLLEX=ocamllex
OCAMLDOC=ocamldoc -html -d htdocs -t "Termination Tool"
INCLUDES=-I +ocamlgraph
OCAMLFLAGS=$(INCLUDES)    # add other options for ocamlc here
OCAMLOPTFLAGS=$(INCLUDES) # add other options for ocamlopt here

# The list of common object files
COMMON_OBJS=\
	trs_ast.cmo trs_parser.cmo trs_lexer.cmo trs_sem.cmo read.cmo \
	util.cmo matrix.cmo params.cmo proc.cmo smt.cmo preorder.cmo mset.cmo \
	abbrev.cmo term.cmo subst.cmo trs.cmo dp.cmo app.cmo wpo.cmo nonterm.cmo \
	main.cmo

COMMON_CMXS= $(COMMON_OBJS:%.cmo=%.cmx)

all: depend NaTT

install: all
	cp -f NaTT.bin NaTT xtc2tpdb.xml /usr/local/bin/

NaTT: $(COMMON_OBJS)
	$(OCAMLC) -o $@ graph.cma unix.cma str.cma $(OCAMLFLAGS) $^

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
	$(OCAMLC) -c $*.mli

.mll.ml:
	$(OCAMLLEX) $<

# Clean up
clean:
	rm -f NaTT
	rm -f *.cm[iox] *.o *.mli .depend

# Dependencies
depend:
	$(OCAMLDEP) *.mli *.ml > .depend

-include experiments.mk
-include .depend
