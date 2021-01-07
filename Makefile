TARG=./NaTT
TARG_OPT=./NaTT.exe
PACKS=unix,str,ocamlgraph,xml-light
OCAMLC=ocamlfind ocamlc -package $(PACKS) -linkpkg
OCAMLOPT=ocamlfind ocamlopt -package $(PACKS) -linkpkg
OCAMLDEP=ocamldep
OCAMLYACC=ocamlyacc
OCAMLLEX=ocamllex
OCAMLDOC=ocamldoc -html -d htdocs -t "Termination Tool"

# The list of ocaml source files
OCAML_SRCS=\
	trs_ast.ml \
	trs_parser.mly \
	trs_lexer.mll \
	trs_sem.ml \
	read.ml \
	util.ml \
	io.ml \
	txtr.ml \
	MyXML.ml \
	WeightTemplate.ml \
	matrix.ml \
	params.ml \
	proc.ml \
	smt.ml \
	preorder.ml \
	mset.ml \
	abbrev.ml \
	sym.ml \
	term.ml \
	subst.ml \
	trs.ml \
	estimator.ml \
	dp.ml \
	app.ml \
	weight.ml \
	wpo_info.ml \
	wpo_printer.ml \
	wpo.ml \
	nonterm.ml \
	main.ml

OCAML_MLS=$(patsubst %.mll,%.ml,$(OCAML_SRCS:%.mly=%.ml))

OCAML_CMOS=$(OCAML_MLS:%.ml=%.cmo)

OCAML_CMXS=$(OCAML_MLS:%.ml=%.cmx)

## If you need a statically linked binary
#OCAMLFLAGS= -cclib '-static'
OCAMLFLAGS+= -g

all: $(TARG_OPT)

install: all
	cp -f $(TARG_OPT) xtc2tpdb.xml /usr/local/bin/

$(TARG_OPT): $(OCAML_CMXS)
	$(OCAMLOPT) -o $@ $(OCAMLFLAGS) $^

$(TARG): $(OCAML_CMOS)
	$(OCAMLC) -o $@ $(OCAMLFLAGS) $^

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

# Consistency test
test: $(TARG_OPT)
	TOOL=$(PWD)/NaTT.sh; \
	BENCH=$(PWD)/tpdb_info/nonterm.list; \
	cd ../TPDB/TRS_Standard; \
	if [ -e tmp_result ]; then rm tmp_result; fi; \
	while read f; do \
		$$TOOL -V $$f | tee -a tmp_result; \
		if grep -q YES tmp_result; then echo WRONG!; exit 1; fi;\
	done < $$BENCH; \
	grep -c NO tmp_result; \
	rm tmp_result



# Dependencies
.depend: $(OCAML_MLS)
	$(OCAMLDEP) *.mli *.ml > .depend

-include .depend
