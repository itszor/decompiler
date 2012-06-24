ocamlfind ocamlmktop -syntax camlp4o -package camlp4.macro,num,unix,bitstring,bitstring.syntax \
  -linkpkg log.cmo coverage.cmo elfreader.cmo dwarfreader.cmo \
  dwarfprint.cmo line.cmo insn.cmo decode_arm.cmo symbols.cmo mapping.cmo \
  emit.cmo deque.cmo ranlist.cmo boolset.cmo getoption.cmo code.cmo \
  block.cmo ctype.cmo irtypes.cmo ir.cmo typedb.cmo ctype.cmo function.cmo \
  builtin.cmo slice_section.cmo binary_info.cmo insn_to_ir.cmo plt.cmo \
  dfs.cmo dominator.cmo phi.cmo defs.cmo ce.cmo minipool.cmo sptracking.cmo \
  resolve_section.cmo decompiler.cmo -o decomp_top
exec ledit ./decomp_top
