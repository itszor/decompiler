#!/bin/sh
ocamlc -g -I +bitstring \
     -pp "camlp4of bitstring/bitstring.cma bitstring/bitstring_persistent.cma \
            `ocamlc -where`/bitstring/pa_bitstring.cmo" \
     unix.cma bitstring.cma -c elfreader.ml
ocamlc -g -I +bitstring \
     -pp "camlp4of bitstring/bitstring.cma bitstring/bitstring_persistent.cma \
            `ocamlc -where`/bitstring/pa_bitstring.cmo" \
     unix.cma bitstring.cma -c dwarfreader.ml
ocamlc -g -I +bitstring -c dwarfprint.ml
ocamlc -g -I +bitstring -c decompiler.ml
ocamlc -g nums.cma unix.cma -I +bitstring bitstring.cma elfreader.cmo dwarfreader.cmo -o decompiler

