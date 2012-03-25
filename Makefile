# Makefile for awesome decompiler project

OCAMLC = ocamlc -g
OCAMLLEX = ocamllex
OCAMLYACC = ocamlyacc -v
OCAMLMKTOP = ocamlmktop
MENHIR = menhir
OCAMLDEP = ocamldep
OCAMLDSORT = ocamldsort

OCAMLWHERE := $(shell $(OCAMLC) -where)

BITSTRING_PP := -pp "camlp4of bitstring/bitstring.cma \
		     bitstring/bitstring_persistent.cma \
		     $(OCAMLWHERE)/bitstring/pa_bitstring.cmo"

# Source plus generated files.
OCAMLSRC := decompiler.ml dwarfreader.ml elfreader.ml dwarfprint.ml line.ml \
	    decode_arm.ml insn.ml

OCAMLOBJ := $(shell < .depend $(OCAMLDSORT) -byte $(OCAMLSRC))

OCAMLLIBS := nums.cma unix.cma -I +bitstring bitstring.cma

OCAMLINC := -I +bitstring

TARGET = decompiler

all:	$(TARGET)

clean:
	rm -f *.cmo *.cmi $(TARGET)

cleaner: clean
	rm -f .depend

ML_ERROR:
	@echo Some sort of Ocaml dependency error occurred.
	@false

# core compiler
$(TARGET): $(OCAMLOBJ)
	$(OCAMLC) $(OCAMLLIBS) $(OCAMLOBJ) -o $@

# Also include (lex, yacc) generated files here.
.depend:	$(OCAMLSRC)
	$(OCAMLDEP) $(BITSTRING_PP) $(OCAMLSRC) > .depend

%.cmo: %.ml
	$(OCAMLC) $(OCAMLINC) $(BITSTRING_PP) $< -c -o $@

%.cmi: %.mli
	$(OCAMLC) $< -c -o $@

%.ml: %.mly
	$(MENHIR) --infer $<

%.ml: %.mll
	$(OCAMLLEX) $<

ifneq ($(MAKECMDGOALS),clean)
ifneq ($(MAKECMDGOALS),cleaner)
include .depend
endif
endif
