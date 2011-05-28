#!/bin/sh
ocamlc -I +bitstring \
     -pp "camlp4of bitstring/bitstring.cma bitstring/bitstring_persistent.cma \
            `ocamlc -where`/bitstring/pa_bitstring.cmo" \
     unix.cma bitstring.cma elfreader.ml -o elfreader

