#!/usr/bin/env sh

set -e

cabal new-build all
cabal new-test

# Linting:
./scripts/hlint.sh

# Run stylish-haskell, and fail if it changes anything:
./scripts/format.sh
git diff --exit-code

# Regenerate the schema, and make sure they're in-sync
# with what was committed:
./scripts/regen.sh
git diff --exit-code
