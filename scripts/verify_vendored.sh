#!/usr/bin/env bash
# Checks that OAI/Computability/FourierCircuit/ is byte-identical to
# lean/OAI/Computability/FourierCircuit/ in https://github.com/openai/math at the pinned commit.
set -euo pipefail
cd "$(dirname "$0")/.."

COMMIT=adc7f1241b42e322a6451854ab7e4b4c146bf78a
DIR=lean/OAI/Computability/FourierCircuit

tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT
git -C "$tmp" init -q
git -C "$tmp" remote add origin https://github.com/openai/math.git
git -C "$tmp" sparse-checkout set --no-cone "/$DIR/"
git -C "$tmp" fetch -q --depth 1 --filter=blob:none origin "$COMMIT"
git -C "$tmp" checkout -q FETCH_HEAD

diff -r "$tmp/$DIR" OAI/Computability/FourierCircuit
echo "OK: OAI/Computability/FourierCircuit is identical to openai/math@$COMMIT:$DIR"
