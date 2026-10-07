import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Field.Defs
import Mathlib.Data.Fintype.Card

/-!
# Scalar linear network codes

`LinearCode ends src snk F` is a scalar linear network code over the field `F` for the `k`-pairs
problem on the undirected unit-capacity multigraph `ends`: every edge is used in a single direction
and carries one symbol of `F` per channel use (the value held at its tail), the value at each vertex
is a fixed linear combination of the symbols entering it plus the messages originating there, and
the orientation is acyclic (so the values are determined by the messages). Each message is one
symbol of `F`, so such a code achieves rate `1`.
-/

open Finset

namespace NccCert

variable {V Ed : Type*} [Fintype V] [DecidableEq V] [Fintype Ed]

/-- Tail of an edge under an orientation. -/
def tailOf (ends : Ed → V × V) (fwd : Ed → Bool) (e : Ed) : V :=
  if fwd e then (ends e).1 else (ends e).2

/-- Head of an edge under an orientation. -/
def headOf (ends : Ed → V × V) (fwd : Ed → Bool) (e : Ed) : V :=
  if fwd e then (ends e).2 else (ends e).1

/-- A scalar linear network code of rate one over the field `F`. -/
structure LinearCode (ends : Ed → V × V) {k : ℕ} (src snk : Fin k → V) (F : Type*) [Field F] where
  fwd : Ed → Bool
  coef : Ed → F
  rank : V → ℕ
  acyclic : ∀ e, rank (tailOf ends fwd e) < rank (headOf ends fwd e)
  solves : ∀ msg : Fin k → F, ∃ val : V → F,
    (∀ w, val w = (∑ e, if headOf ends fwd e = w then coef e * val (tailOf ends fwd e) else 0) +
        ∑ i, if src i = w then msg i else 0) ∧
      ∀ i, val (snk i) = msg i

/-- In an acyclic code the vertex values are determined by the messages: any two assignments
satisfying the local coding equations agree. (So `LinearCode.solves` describes *the* behaviour of
the code, not merely some consistent assignment.) -/
lemma LinearCode.val_unique {ends : Ed → V × V} {k : ℕ} {src snk : Fin k → V} {F : Type*}
    [Field F] (c : LinearCode ends src snk F) (msg : Fin k → F) (val₁ val₂ : V → F)
    (h₁ : ∀ w, val₁ w = (∑ e, if headOf ends c.fwd e = w then
        c.coef e * val₁ (tailOf ends c.fwd e) else 0) + ∑ i, if src i = w then msg i else 0)
    (h₂ : ∀ w, val₂ w = (∑ e, if headOf ends c.fwd e = w then
        c.coef e * val₂ (tailOf ends c.fwd e) else 0) + ∑ i, if src i = w then msg i else 0) :
    val₁ = val₂ := by
  funext w
  suffices H : ∀ m, ∀ w, c.rank w = m → val₁ w = val₂ w from H _ w rfl
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro w hw
  rw [h₁ w, h₂ w]
  congr 1
  refine Finset.sum_congr rfl fun e _ => ?_
  split_ifs with h
  · rw [ih _ (hw ▸ h ▸ c.acyclic e) _ rfl]
  · rfl

end NccCert
