import Lake
open Lake DSL

package nccCert where
  leanOptions := #[⟨`autoImplicit, false⟩]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "d13f23b723b8a846827a245b89c10fc7d3f11612"

@[default_target]
lean_lib NccCert where
  globs := #[.submodules `NccCert]

/-- OpenAI's Lean proof of `OAI.ExactFourier.main_theorem`, vendored unmodified from
`lean/OAI/Computability/FourierCircuit/` of https://github.com/openai/math at commit
`adc7f1241b42e322a6451854ab7e4b4c146bf78a` (51 files; `Main` imports all of them). -/
lean_lib OAIFourier where
  roots := #[`OAI.Computability.FourierCircuit.Main]
  globs := #[.submodules `OAI.Computability.FourierCircuit]
