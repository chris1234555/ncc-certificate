#!/bin/bash
# Replay every declaration of each project module through the Lean kernel, one module at a time.
# Requires a completed `lake build NccCert OAIFourier`; uses `leanchecker` from the Lean toolchain.
cd "$(dirname "$0")"
fail=0
for f in OAI/Computability/FourierCircuit/*.lean NccCert/*.lean; do
  m=$(echo "${f%.lean}" | tr / .)
  if lake env leanchecker "$m" >/dev/null 2>err.tmp; then echo "ok   $m"; else echo "FAIL $m"; cat err.tmp; fail=1; fi
done
rm -f err.tmp
echo "overall fail=$fail"
exit $fail
