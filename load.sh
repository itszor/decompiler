#!/bin/bash

loads=()
for x in log.cmo dgraph.cmo coverage.cmo elfreader.cmo dwarfreader.cmo \
  dwarfprint.cmo line.cmo insn.cmo decode_arm.cmo symbols.cmo mapping.cmo \
  deque.cmo ranlist.cmo vec.cmo boolset.cmo getoption.cmo code.cmo \
  block.cmo ctype.cmo irtypes.cmo ir.cmo eabi.cmo typedb.cmo ctype.cmo \
  function.cmo builtin.cmo slice_section.cmo binary_info.cmo external.cmo \
  insn_to_ir.cmo plt.cmo dfs.cmo dominator.cmo phi.cmo defs.cmo ce.cmo \
  dce.cmo minipool.cmo locations.cmo sptracking.cmo ptrtracking.cmo \
  dwptrtracking.cmo resolve_section.cmo jumptable.cmo restructure.cmo \
  vartypes.cmo ctree.cmo decompiler.cmo; do
  loads=("${loads[@]}" "#load \"$x\";;")
done

ledit ocaml -init <(cat << EOF
#use "topfind";;
#camlp4o;;
#require "num";;
#require "unix";;
#require "bitstring";;
#require "bitstring.syntax";;
#require "FrontC";;
#require "batteries";;
${loads[@]}
open Decompiler;;
EOF
)
