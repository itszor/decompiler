#!/bin/sh
if [ -d /home/jules/.opam/4.00.1 ]; then
  PATH=/home/jules/.opam/4.00.1/bin:$PATH
  PATH=/scratchbox/compilers/arm-linux-cs2010q1-202/bin:$PATH
else
  PATH=/home/jules/stuff/prefix/bin:$PATH
fi
export PATH
eval `opam config -env`
