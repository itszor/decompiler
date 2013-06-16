#!/bin/sh

# set -x

SCRIPT=$(readlink -f $0)

DEBUGLEVEL=1

case "$1" in
  -x)
    set -x
    shift
    ;;
  -g)
    DEBUGLEVEL=$2
    shift 2
    ;;
  *)
    ;;
esac

DOTESTS=$1

SCRIPTDIR=$(dirname "$SCRIPT")
ARMCC=arm-none-linux-gnueabi-gcc
ARMCFLAGS=
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
  argstruct \
  array \
  array2 \
  arrayonstack \
  bfc \
  const \
  dataref \
  fnargs \
  fnargs2 \
  fncall \
  fntype \
  global \
  globalstruct \
  hello \
  incoming-args \
  rodata \
  struct \
  struct2 \
  struct3 \
  struct4 \
  structreturn \
)

testflags () {
  local whichtest=$1
  case "$whichtest" in
    bfc)
      echo "$ARMCFLAGS -march=armv7-a"
      ;;
    *)
      echo "$ARMCFLAGS"
      ;;
  esac
}

pushd "$SCRIPTDIR" >& /dev/null

rm -f "$RESULTS"
rm -rf "$OUTPUTS"

for T in "${TESTS[@]}"; do
  if [ ! "$DOTESTS" ] || eval [[ "$T" = "$DOTESTS" ]]; then
    $ARMCC $(testflags "$T") -g "$T.c" -o "$T"
    if [ $? -ne 0 ]; then
      echo "FAIL: $T compilation" >> "$RESULTS"
    else
      mkdir -p "$OUTPUTS/$T"
      $DECOMPILER -g $DEBUGLEVEL -i "$T" -o "$OUTPUTS/$T" -p "$SCRIPTDIR"
      if [ $? -ne 0 ]; then
        echo "FAIL: $T decompilation" >> "$RESULTS"
      else
        $ARMCC $(testflags "$T") "$OUTPUTS/$T/$T.c" -o "$T.new"
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
