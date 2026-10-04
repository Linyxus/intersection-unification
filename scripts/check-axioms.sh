#!/usr/bin/env bash
# Checks that `Intersection.decidable` depends on exactly the three standard axioms.
# Run after `lake build`, from anywhere.
set -euo pipefail
cd "$(dirname "$0")/.."
expected="'Intersection.decidable' depends on axioms: [propext, Classical.choice, Quot.sound]"
actual=$(lake env lean Check.lean)
echo "$actual"
if [ "$actual" != "$expected" ]; then
  echo "error: unexpected axioms" >&2
  exit 1
fi
