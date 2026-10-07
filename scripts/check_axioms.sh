#!/usr/bin/env bash
# Runs NccCert/Check.lean and fails unless each main theorem depends on exactly the three
# standard axioms (propext, Classical.choice, Quot.sound). Requires a completed
# `lake build NccCert OAIFourier`.
set -euo pipefail
cd "$(dirname "$0")/.."

out=$(lake env lean NccCert/Check.lean)
echo "$out"
echo

expected=$(printf '%s\n' propext Classical.choice Quot.sound | sort | tr '\n' ' ')
fail=0
for t in NccCert.not_NCC_rate_one NccCert.not_NCC_rate_one_of_exactFourier OAI.ExactFourier.main_theorem \
         NccCert.not_NCC_rate NccCert.not_NCC_rate_of_exactFourier; do
  line=$(grep -F "'$t' depends on axioms:" <<<"$out" || true)
  if [ -z "$line" ]; then
    echo "FAIL  $t: no axiom report (does it depend on no axioms, or did Check.lean fail?)"
    fail=1
    continue
  fi
  got=$(sed -E 's/.*\[(.*)\].*/\1/' <<<"$line" | tr ',' '\n' | sed 's/^ *//;s/ *$//' | sort | tr '\n' ' ')
  if [ "$got" = "$expected" ]; then
    echo "ok    $t: $got"
  else
    echo "FAIL  $t: $got"
    fail=1
  fi
done
exit $fail
