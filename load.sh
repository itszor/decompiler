exec ledit ocaml nums.cma unix.cma -I +bitstring bitstring.cma elfreader.cmo \
  dwarfreader.cmo dwarfprint.cmo line.cmo insn.cmo decode_arm.cmo \
  decompiler.cmo
