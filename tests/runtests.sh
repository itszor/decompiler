#!/bin/sh

# set -x

SCRIPT=$(readlink -f $0)
DOTESTS=$1

SCRIPTDIR=$(dirname "$SCRIPT")
ARMCC=arm-none-linux-gnueabi-gcc
DECOMPILER=../decompiler
RESULTS=results.sum
OUTPUTS=out

declare -a TESTS

TESTS=( \
  addressable2 \
  addressable3 \
  addressable4 \
  addressable5 \
  args \
  array \
  array2 \
  arrayonstack \
  const \
  dataref \
  fnargs \
  fnargs2 \
  fncall \
  fntype \
  hello \
  incoming-args \
  rodata \
  struct \
  struct2 \
  struct3 \
  struct4 \
  structreturn \
)

pushd "$SCRIPTDIR" >& /dev/null

rm -f "$RESULTS"
rm -rf "$OUTPUTS"

for T in "${TESTS[@]}"; do
  if [ ! "$DOTESTS" ] || eval [[ "$T" = "$DOTESTS" ]]; then
    $ARMCC -g "$T.c" -o "$T"
    if [ $? -ne 0 ]; then
      echo "FAIL: $T compilation" >> "$RESULTS"
    else
      mkdir -p "$OUTPUTS/$T"
      $DECOMPILER -g 1 -i "$T" -o "$OUTPUTS/$T" -p "$SCRIPTDIR"
      if [ $? -ne 0 ]; then
        echo "FAIL: $T decompilation" >> "$RESULTS"
      else
        $ARMCC "$OUTPUTS/$T/$T.c" -o "$T.new"
        if [ $? -ne 0 ]; then
          echo "FAIL: $T recompilation" >> "$RESULTS"
        else
          echo "PASS: $T recompilation" >> "$RESULTS"
        fi
      fi
    fi
  fi
done
popd >& /dev/null
