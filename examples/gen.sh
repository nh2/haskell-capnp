#!/usr/bin/env sh

capnp compile -o- *.capnp | $(find ../dist-newstyle -type f -name capnpc-haskell)
