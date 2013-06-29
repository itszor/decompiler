#!/bin/bash

loads=()
for x in log.cmo dgraph.cmo coverage.cmo elfreader.cmo dwarfreader.cmo \
  dwarfprint.cmo line.cmo insn.cmo decode_arm.cmo symbols.cmo mapping.cmo \
  deque.cmo ranlist.cmo vec.cmo boolset.cmo getoption.cmo code.cmo \
  block.cmo ctype.cmo ir.cmo ltype.cmo eabi.cmo typedb.cmo \
  function.cmo builtin.cmo slice_section.cmo binary_info.cmo external.cmo \
  insn_to_ir.cmo plt.cmo dfs.cmo dominator.cmo phi.cmo defs.cmo ce.cmo \
  dce.cmo const.cmo minipool.cmo locations.cmo sptracking.cmo ptrtracking.cmo \
  vartypes.cmo imageptr.cmo dwptrtracking.cmo subst_locals.cmo \
  resolve_section.cmo jumptable.cmo restructure.cmo ctree.cmo dirutils.cmo \
  typeinjection.cmo decompiler.cmo; do
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
#require "fileutils";;
${loads[@]}
open Decompiler;;
EOF
)
