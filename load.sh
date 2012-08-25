#!/bin/bash

loads=()
for x in log.cmo coverage.cmo elfreader.cmo dwarfreader.cmo \
  dwarfprint.cmo line.cmo insn.cmo decode_arm.cmo symbols.cmo mapping.cmo \
  emit.cmo deque.cmo ranlist.cmo boolset.cmo getoption.cmo code.cmo \
  block.cmo ctype.cmo irtypes.cmo ir.cmo typedb.cmo ctype.cmo function.cmo \
  builtin.cmo slice_section.cmo binary_info.cmo insn_to_ir.cmo plt.cmo \
  dfs.cmo dominator.cmo phi.cmo defs.cmo ce.cmo minipool.cmo ptrtracking.cmo \
  sptracking.cmo resolve_section.cmo jumptable.cmo vartypes.cmo ctree.cmo \
  decompiler.cmo; do
  loads=("${loads[@]}" "#load \"$x\";;")
done

ledit ocaml -init <(cat << EOF
#use "topfind";;
#camlp4o;;
#require "camlp4.macro";;
#require "num";;
#require "unix";;
#require "bitstring";;
#require "bitstring.syntax";;
#require "FrontC";;
${loads[@]}
open Decompiler;;
EOF)
