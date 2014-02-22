#!/usr/bin/env make

OCAMLBUILD = ocamlbuild
OCAMLBUILD_OPT ?= -j 8

SRC = src
DOC = cal-api.docdir

ifdef DEBUG_OCAMLBUILD
	OCAMLBUILD_OPT += -classic-display
endif

all: native

byte: $(wildcard $(SRC)/*.ml $(SRC)/*.mli $(SRC)/lexer.mll $(SRC)/parser.mly)
	$(OCAMLBUILD) -use-ocamlfind $(OCAMLBUILD_OPT) $(SRC)/main.byte

native: $(wildcard $(SRC)/*.ml $(SRC)/*.mli $(SRC)/lexer.mll $(SRC)/parser.mly)
	$(OCAMLBUILD) -use-ocamlfind $(OCAMLBUILD_OPT) $(SRC)/main.native

doc: $(wildcard $(SRC)/*.ml $(SRC)/*.mli $(SRC)/lexer.mll $(SRC)/parser.mly)
	$(OCAMLBUILD) -use-ocamlfind $(OCAMLBUILD_OPT) $(SRC)/$(DOC)/index.html

test: native 
	./scripts/run_all_tests.pl main.native my myerr
	./scripts/compare_results.pl ref my referr myerr

clean:
	$(OCAMLBUILD) -clean
	rm -f tests/*.my tests/*.myerr solver.log
