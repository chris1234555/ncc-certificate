import OAI.Computability.FourierCircuit.Core

/-!
# The statement of `OAI.ExactFourier.main_theorem`

`OAI.ExactFourier.MainStatement` and the circuit model it is phrased in (`Gate`, `Program`,
`Circuit`, `zeta`, `fourierMatrix`, `Circuit.Computes`) come from
`lean/OAI/Computability/FourierCircuit/Core.lean` of <https://github.com/openai/math>, vendored
unmodified. Apart from a `section` wrapper and two doc comments, that file is textually identical to
the Comparator challenge `lean/ComparatorChallenges/ExactFourier.lean` (minus its
`theorem main_theorem : MainStatement := by sorry`).

Importing OpenAI's file, instead of keeping a private copy, puts our conditional theorem and OpenAI's
`main_theorem` in one environment about the same constant `OAI.ExactFourier.MainStatement`.
(`extras/ExactFourierDefs_standalone.lean.txt` is the verbatim copy used before; it needs only part
of Mathlib.)
-/
