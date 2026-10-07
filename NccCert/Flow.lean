import Mathlib.Data.Real.Basic
import NccCert.Graph
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators

/-!
# Multicommodity flows in undirected unit-capacity networks, and the routing lower bound

This file contains the combinatorial half of the "coding beats routing" argument:

* `ConcurrentFlow`: a concurrent multicommodity flow of rate `r` in an undirected multigraph
  whose edges all have capacity `1` (shared by all commodities and both directions).
* `flow_rate_mul_le`: if `F` commodities have their sink outside the radius-`T` ball around their
  source, then `r * ((T+1) * F) ≤ #edges` (each such commodity needs `T+1` edges per unit).
-/

open Finset

namespace NccCert

variable {V Ed : Type*} [Fintype V] [DecidableEq V] [Fintype Ed]

/-! ### Flows -/

/-- Net flow out of `x` for a signed edge flow `f`; `f e > 0` means flow from `(ends e).1` to
`(ends e).2`. -/
def netOut (ends : Ed → V × V) (f : Ed → ℝ) (x : V) : ℝ :=
  (∑ e, if (ends e).1 = x then f e else 0) - ∑ e, if (ends e).2 = x then f e else 0

/-- A concurrent multicommodity flow of rate `r` in the undirected multigraph `ends`, where every
edge has capacity `1`, shared by all commodities and both directions. Commodity `i` sends `r` units
from `src i` to `snk i`. -/
structure ConcurrentFlow (ends : Ed → V × V) {k : ℕ} (src snk : Fin k → V) (r : ℝ) where
  f : Fin k → Ed → ℝ
  conserve : ∀ i x, netOut ends (f i) x =
    r * ((if x = src i then 1 else 0) - if x = snk i then 1 else 0)
  capacity : ∀ e, ∑ i, |f i e| ≤ 1

lemma sum_mul_netOut (ends : Ed → V × V) (f : Ed → ℝ) (φ : V → ℝ) :
    ∑ x, φ x * netOut ends f x = ∑ e, f e * (φ (ends e).1 - φ (ends e).2) := by
  have h1 : ∀ x, φ x * netOut ends f x =
      (∑ e, if (ends e).1 = x then φ x * f e else 0) -
        ∑ e, if (ends e).2 = x then φ x * f e else 0 := by
    intro x
    simp only [netOut, mul_sub, Finset.mul_sum, mul_ite, mul_zero]
  simp only [h1, Finset.sum_sub_distrib]
  rw [Finset.sum_comm, Finset.sum_comm (f := fun x e => if (ends e).2 = x then φ x * f e else 0)]
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [Finset.sum_ite_eq, Finset.sum_ite_eq]
  simp only [Finset.mem_univ, if_true]
  ring

/-- The basic potential bound: for any potential that changes by at most `1` along every edge,
commodity `i` pays at least `r * (φ (snk i) - φ (src i))` in total edge usage. -/
lemma flow_potential_le (ends : Ed → V × V) {k : ℕ} {src snk : Fin k → V} {r : ℝ}
    (fl : ConcurrentFlow ends src snk r) (φ : V → ℝ)
    (hφ : ∀ e, |φ (ends e).1 - φ (ends e).2| ≤ 1) (i : Fin k) :
    r * (φ (snk i) - φ (src i)) ≤ ∑ e, |fl.f i e| := by
  have key := sum_mul_netOut ends (fl.f i) φ
  have lhs : ∑ x, φ x * netOut ends (fl.f i) x = r * (φ (src i) - φ (snk i)) := by
    simp only [fl.conserve, mul_sub, mul_ite, mul_one, mul_zero, Finset.sum_sub_distrib]
    rw [Finset.sum_ite_eq', Finset.sum_ite_eq']
    simp only [Finset.mem_univ, if_true]
    ring
  have bound : ∀ e, -|fl.f i e| ≤ fl.f i e * (φ (ends e).1 - φ (ends e).2) := by
    intro e
    have h := abs_mul (fl.f i e) (φ (ends e).1 - φ (ends e).2)
    have h2 : |fl.f i e| * |φ (ends e).1 - φ (ends e).2| ≤ |fl.f i e| :=
      mul_le_of_le_one_right (abs_nonneg _) (hφ e)
    have h3 := neg_abs_le (fl.f i e * (φ (ends e).1 - φ (ends e).2))
    linarith
  have hsum : -(∑ e, |fl.f i e|) ≤ ∑ e, fl.f i e * (φ (ends e).1 - φ (ends e).2) := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_le_sum fun e _ => bound e
  linarith

variable [DecidableEq Ed]

lemma pot_lipschitz (ends : Ed → V × V) (v : V) (T : ℕ) (e : Ed) :
    |(pot ends v T (ends e).1 : ℝ) - pot ends v T (ends e).2| ≤ 1 := by
  have hadj : Adj ends (ends e).1 (ends e).2 := ⟨e, Or.inl rfl⟩
  have h1 := pot_le_succ_of_adj ends v T hadj
  have h2 := pot_le_succ_of_adj ends v T ((adj_comm ends).mp hadj)
  rw [abs_le]
  constructor
  · have : (pot ends v T (ends e).2 : ℝ) ≤ pot ends v T (ends e).1 + 1 := by exact_mod_cast h1
    linarith
  · have : (pot ends v T (ends e).1 : ℝ) ≤ pot ends v T (ends e).2 + 1 := by exact_mod_cast h2
    linarith

/-- **Routing lower bound.** If the commodities in `far` have their sink outside the radius-`T`
ball of their source, every concurrent flow of rate `r` satisfies `r * ((T+1) * #far) ≤ #edges`. -/
theorem flow_rate_mul_le (ends : Ed → V × V) {k : ℕ} {src snk : Fin k → V} {r : ℝ}
    (fl : ConcurrentFlow ends src snk r) (T : ℕ) :
    r * ((T + 1) * ((univ.filter fun i => snk i ∉ ball ends (src i) T).card : ℝ)) ≤
      Fintype.card Ed := by
  set far := univ.filter fun i => snk i ∉ ball ends (src i) T
  have hi : ∀ i ∈ far, r * (T + 1) ≤ ∑ e, |fl.f i e| := by
    intro i hi
    have h := flow_potential_le ends fl (fun x => (pot ends (src i) T x : ℝ))
      (pot_lipschitz ends (src i) T) i
    simp only [Finset.mem_filter, far] at hi
    rw [pot_far ends (src i) T hi.2, pot_self] at h
    push_cast at h
    linarith
  calc r * ((T + 1) * (far.card : ℝ)) = ∑ _i ∈ far, r * (T + 1) := by
        rw [Finset.sum_const, nsmul_eq_mul]; ring
    _ ≤ ∑ i ∈ far, ∑ e, |fl.f i e| := Finset.sum_le_sum hi
    _ ≤ ∑ i, ∑ e, |fl.f i e| :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          (fun i _ _ => Finset.sum_nonneg fun e _ => abs_nonneg _)
    _ = ∑ e, ∑ i, |fl.f i e| := Finset.sum_comm
    _ ≤ ∑ _e : Ed, (1 : ℝ) := Finset.sum_le_sum fun e _ => fl.capacity e
    _ = Fintype.card Ed := by simp

end NccCert
