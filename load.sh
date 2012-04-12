ocamlfind ocamlmktop -syntax camlp4o -package camlp4.macro,num,unix,bitstring,bitstring.syntax \
  -linkpkg elfreader.cmo dwarfreader.cmo dwarfprint.cmo line.cmo insn.cmo \
  decode_arm.cmo symbols.cmo decompiler.cmo -o decomp_top
exec ledit ./decomp_top
