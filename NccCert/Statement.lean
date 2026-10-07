import NccCert.Flow
import NccCert.Code

/-!
# Network codes and the (rate-one form of the) network coding conjecture

`LinearCode ends src snk F` is a scalar linear network code over the field `F` for the `k`-pairs
problem on the undirected unit-capacity multigraph `ends`: every edge is used in a single direction
and carries one symbol of `F` per channel use (the value held at its tail), the value at each vertex
is a fixed linear combination of the symbols entering it plus the messages originating there, and
the orientation is acyclic, so the values are determined by the messages. Each message is one symbol
of `F`, so such a code achieves rate `1`.

`NCC_rate_one` is the consequence of the undirected `k`-pairs (multiple-unicast) network coding
conjecture of Li and Li (2004), also posed by Harvey, Kleinberg and Lehman (2006), for unit
capacities and rate one: the conjecture says the network coding rate equals the maximum concurrent
multicommodity flow rate, so a rate-one code forces a concurrent flow of rate one.
-/

open Finset

namespace NccCert

variable {V Ed : Type*} [Fintype V] [DecidableEq V] [Fintype Ed]

/-- **Rate-one consequence of the network coding conjecture** (undirected `k`-pairs / multiple
unicast conjecture): on any finite undirected unit-capacity multigraph without self-loops, with `k`
distinct sources and `k` distinct sinks (no vertex is both), whenever the `k` messages can be
delivered at rate one by a linear network code over a finite field, a concurrent multicommodity flow
of rate one exists.

The non-degeneracy hypotheses only make the statement weaker (so its negation stronger); they rule
out counterexamples that rely on shared terminals or loops. -/
def NCC_rate_one : Prop :=
  ∀ (V Ed : Type) [Fintype V] [DecidableEq V] [Fintype Ed] (ends : Ed → V × V) (k : ℕ)
    (src snk : Fin k → V) (F : Type) [Field F] [Finite F],
    (∀ e, (ends e).1 ≠ (ends e).2) →
    Function.Injective src → Function.Injective snk → (∀ i j, src i ≠ snk j) →
    Nonempty (LinearCode ends src snk F) → Nonempty (ConcurrentFlow ends src snk 1)

end NccCert
