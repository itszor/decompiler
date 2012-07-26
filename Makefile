# Makefile for awesome decompiler project

OCAMLFIND = ocamlfind
ifeq ($(BUILD),opt)
OCAMLC = ocamlopt
else
OCAMLC = ocamlc -g
endif
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

SYNTAX := -syntax camlp4o

PACKAGES := -package camlp4.macro,bitstring,bitstring.syntax,num,unix

# Source plus generated files.
OCAMLSRC := log.ml coverage.ml elfreader.ml dwarfreader.ml dwarfprint.ml \
	    line.ml decode_arm.ml insn.ml symbols.ml mapping.ml emit.ml \
	    deque.ml ranlist.ml boolset.ml getoption.ml code.ml block.ml \
	    ctype.ml function.ml irtypes.ml ir.ml typedb.ml builtin.ml \
	    slice_section.ml binary_info.ml insn_to_ir.ml plt.ml dfs.ml \
	    dominator.ml phi.ml defs.ml ce.ml minipool.ml ptrtracking.ml \
	    sptracking.ml resolve_section.ml jumptable.ml decompiler.ml

# OCAMLOBJ := $(shell < .depend $(OCAMLDSORT) -byte $(OCAMLSRC))
ifeq ($(BUILD),opt)
OCAMLOBJ := $(OCAMLSRC:.ml=.cmx)
else
OCAMLOBJ := $(OCAMLSRC:.ml=.cmo)
endif

ifeq ($(BUILD),opt)
OCAMLLIBS := nums.cmxa unix.cmxa -I +bitstring bitstring.cmxa
else
OCAMLLIBS := nums.cma unix.cma -I +bitstring bitstring.cma
endif

OCAMLINC := -I +bitstring

TARGET = decompiler

all:	$(TARGET)

clean:
	rm -f *.cmo *.cmi *.cmx $(TARGET)

cleaner: clean
	rm -f .depend

ML_ERROR:
	@echo Some sort of Ocaml dependency error occurred.
	@false

# core compiler
$(TARGET): $(OCAMLOBJ)
	$(OCAMLFIND) $(OCAMLC) $(PACKAGES) -linkpkg $(OCAMLOBJ) -o $@

# Also include (lex, yacc) generated files here.
.depend:	$(OCAMLSRC)
	$(OCAMLFIND) ocamldep $(SYNTAX) $(PACKAGES) $(OCAMLSRC) > .depend

%.cmo: %.ml
	$(OCAMLFIND) $(OCAMLC) $(SYNTAX) $(PACKAGES) $< -c -o $@

%.cmx: %.ml
	$(OCAMLFIND) ocamlopt -inline 100 $(SYNTAX) $(PACKAGES) $< -c -o $@

%.cmi: %.mli
	$(OCAMLFIND) $(OCAMLC) $(SYNTAX) $(PACKAGES) $< -c -o $@

%.ml: %.mly
	$(MENHIR) --infer $<

%.ml: %.mll
	$(OCAMLLEX) $<

ifneq ($(MAKECMDGOALS),clean)
ifneq ($(MAKECMDGOALS),cleaner)
include .depend
endif
endif
