import NccCert.Main
import OAI.Computability.FourierCircuit.Main

/-!
# The unconditional certificate

OpenAI's `OAI.ExactFourier.main_theorem : MainStatement`, from their vendored, unmodified Lean
development, discharges the hypothesis of `not_NCC_rate_one_of_exactFourier`.
-/

namespace NccCert

/-- **The rate-one network coding conjecture is false.** On some finite undirected unit-capacity
multigraph of maximum degree three (without loops, with distinct sources and distinct sinks), a
linear network code over a finite field delivers all messages at rate one, but no concurrent
multicommodity flow of rate one exists. -/
theorem not_NCC_rate_one : ¬ NCC_rate_one :=
  not_NCC_rate_one_of_exactFourier OAI.ExactFourier.main_theorem

end NccCert
