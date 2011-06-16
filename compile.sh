#!/bin/sh

version=$(camlp4 -version)

case "$version" in
  3.12.0)
    use_camlp4of=true
    ;;
  *)
    use_camlp4of=false
    ;;
esac

camlp4_comp() {
  local src=$1
  if $use_camlp4of; then
    ocamlc -g -I +bitstring \
      -pp "camlp4of bitstring/bitstring.cma bitstring/bitstring_persistent.cma \
            `ocamlc -where`/bitstring/pa_bitstring.cmo" \
      unix.cma bitstring.cma -c "$src"
  else
    ocamlc -g -I +bitstring \
      -pp "camlp4o bitstring/bitstring.cma bitstring/bitstring_persistent.cma \
            `ocamlc -where`/bitstring/pa_bitstring.cmo" \
      unix.cma bitstring.cma -c "$src"
  fi
}

camlp4_comp elfreader.ml
camlp4_comp dwarfreader.ml
ocamlc -g -I +bitstring -c dwarfprint.ml
ocamlc -g -I +bitstring -c decompiler.ml
ocamlc -g nums.cma unix.cma -I +bitstring bitstring.cma elfreader.cmo dwarfreader.cmo dwarfprint.cmo decompiler.cmo -o decompiler

