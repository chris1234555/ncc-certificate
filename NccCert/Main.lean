import NccCert.Fourier
import NccCert.Statement
import Mathlib.Data.Nat.Log
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum

/-!
# Exact Fourier circuits of size `o(n log n)` refute the network coding conjecture

`not_NCC_rate_one_of_exactFourier : OAI.ExactFourier.MainStatement → ¬ NCC_rate_one`.

Proof sketch. Take a circuit `C` for the `n`-point DFT with fewer than `n log₂ n / 64` gates,
`n ≥ 2¹⁸`. Specialise its coefficients (together with `ζₙ` and `1/n`) to a finite field `K`
(`shiftData_of_circuit`). Two copies of the resulting DAG, joined by a diagonal layer and with every
use of a value given its own relay vertex, form a graph of maximum degree `3` with at most
`8|C| + 2n` edges; for every cyclic shift `s` it carries a rate-one linear code delivering message `j`
from input `j` to output `τ(j + s)` (`ShiftCode.code`). In a graph of maximum degree `3`, some shift
`s` puts at least `n/2` pairs at distance `> T = ⌊log₄ (n/2)⌋` (`exists_shift_far`), so any concurrent
flow of rate one needs more than `(T + 1) n / 2 > (log₂ n - 1) n / 4` edges (`flow_rate_mul_le`). This
exceeds `8|C| + 2n < n log₂ n / 8 + 2n` once `log₂ n ≥ 18`.
-/

open Finset OAI.ExactFourier

namespace NccCert

lemma card_ed_le {n : ℕ} [NeZero n] (S : ShiftData n) :
    Fintype.card (ShiftCode.Ed S.D) ≤ 8 * S.size + 2 * n := by
  have h1 : Fintype.card (ShiftCode.Ed S.D) = 2 * (2 * ∑ v, (S.D.ops v).length + n) := by
    simp only [ShiftCode.Ed, ShiftCode.Use, Fintype.card_prod, Fintype.card_sum, Fintype.card_bool,
      Fintype.card_sigma, Fintype.card_fin]
    ring
  have h2 := S.len_sum
  omega

/-- The shift-code instance is non-degenerate: no loops, distinct sources, distinct sinks, and no
vertex is both a source and a sink. -/
lemma shift_instance_nondegenerate {n : ℕ} [NeZero n] (S : ShiftData n) (s : Fin n) :
    (∀ e, (ShiftCode.ends S.D e).1 ≠ (ShiftCode.ends S.D e).2) ∧
    Function.Injective (ShiftCode.msgSrc S.D) ∧
    Function.Injective (fun j => ShiftCode.outV S.D (tau (j + s))) ∧
    (∀ i j, ShiftCode.msgSrc S.D i ≠ ShiftCode.outV S.D (tau (j + s))) := by
  refine ⟨fun e h => ?_, fun a b h => ?_, fun a b h => ?_, fun i j h => ?_⟩
  · have := ShiftCode.rank_lt S.D e
    rw [h] at this
    exact lt_irrefl _ this
  · simp only [ShiftCode.msgSrc, Sum.inl.injEq, Prod.mk.injEq, true_and, Fin.mk.injEq] at h
    exact Fin.ext h
  · simp only [ShiftCode.outV, Sum.inl.injEq, Prod.mk.injEq, true_and] at h
    exact add_right_cancel (tau_injective (S.out_inj h))
  · simp only [ShiftCode.msgSrc, ShiftCode.outV, Sum.inl.injEq, Prod.mk.injEq] at h
    exact absurd h.1 (by decide)

theorem not_NCC_rate_one_of_exactFourier (hF : MainStatement) : ¬ NCC_rate_one := by
  intro hN
  unfold NCC_rate_one at hN
  obtain ⟨n, hn, C, hC, hsize⟩ := hF (1 / 64) (by norm_num) (2 ^ 18) (by norm_num)
  have hn2 : 2 ≤ n := le_trans (by norm_num) hn
  haveI : NeZero n := ⟨by omega⟩
  obtain ⟨S, hS⟩ := shiftData_of_circuit hn2 C hC
  -- the shift with many far pairs
  set T := Nat.log 4 (n / 2) with hTdef
  have hdeg : ∀ x, (nbrs (ShiftCode.ends S.D) x).card ≤ 3 :=
    fun x => ShiftCode.card_nbrs_le S.D x
  have hB : Function.Injective fun t : Fin n => ShiftCode.outV S.D (tau t) := by
    intro a b h
    simp only [ShiftCode.outV, Sum.inl.injEq, Prod.mk.injEq, true_and] at h
    exact tau_injective (S.out_inj h)
  obtain ⟨s, hs⟩ := exists_shift_far (ShiftCode.ends S.D) (ShiftCode.msgSrc S.D)
    (fun t => ShiftCode.outV S.D (tau t)) hB hdeg T
  -- the rate-one code for shift `s`, and the flow that the conjecture would provide
  have code := ShiftCode.code S.D (S.d s) (fun j => tau (j + s)) S.M S.computes (S.inv s)
  obtain ⟨hloop, hsrc, hsnk, hdisj⟩ := shift_instance_nondegenerate S s
  obtain ⟨fl⟩ := hN _ _ (ShiftCode.ends S.D) n (ShiftCode.msgSrc S.D)
    (fun j => ShiftCode.outV S.D (tau (j + s))) S.K hloop hsrc hsnk hdisj ⟨code⟩
  have hflow := flow_rate_mul_le (ShiftCode.ends S.D) fl T
  set far := (univ.filter fun j : Fin n =>
    ShiftCode.outV S.D (tau (j + s)) ∉ ball (ShiftCode.ends S.D) (ShiftCode.msgSrc S.D j) T).card
    with hfar_def
  have hfar : n - 4 ^ T ≤ far := hs
  have hcard : Fintype.card (ShiftCode.Ed S.D) ≤ 8 * C.size + 2 * n := by
    have h8 : 8 * S.size + 2 * n = 8 * C.size + 2 * n := by rw [hS]
    exact (card_ed_le S).trans h8.le
  -- natural-number facts about `T`
  have hT1 : 4 ^ T ≤ n / 2 := Nat.pow_log_le_self 4 (by omega)
  have hT2 : n / 2 < 4 ^ (T + 1) := Nat.lt_pow_succ_log_self (by norm_num) _
  have hfar2 : n ≤ 2 * far := by omega
  have hn4 : n < 2 ^ (2 * T + 3) := by
    have : 2 ^ (2 * T + 3) = 2 * 4 ^ (T + 1) := by
      rw [show 2 * T + 3 = 1 + 2 * (T + 1) by ring, pow_add, pow_mul]; norm_num
    omega
  -- real-number facts
  set L := Real.logb 2 (n : ℝ) with hL
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hL18 : (18 : ℝ) ≤ L := by
    have h1 : ((2 : ℝ) ^ (18 : ℕ)) ≤ n := by exact_mod_cast hn
    have h2 := Real.logb_le_logb_of_le (b := 2) (by norm_num) (by positivity) h1
    rwa [Real.logb_pow, Real.logb_self_eq_one (by norm_num), mul_one] at h2
  have hLT : L < 2 * T + 3 := by
    have h1 : (n : ℝ) < (2 : ℝ) ^ (2 * T + 3) := by exact_mod_cast hn4
    have h2 := Real.logb_lt_logb (b := 2) (by norm_num) hnpos h1
    rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num), mul_one] at h2
    push_cast at h2
    linarith
  have hflowR : ((T : ℝ) + 1) * far ≤ 8 * C.size + 2 * n := by
    have h := hflow
    rw [one_mul] at h
    have : (Fintype.card (ShiftCode.Ed S.D) : ℝ) ≤ 8 * C.size + 2 * n := by exact_mod_cast hcard
    linarith
  have hfarR : (n : ℝ) ≤ 2 * far := by exact_mod_cast hfar2
  have hsizeR : (C.size : ℝ) < 1 / 64 * n * L := hsize
  -- (L - 1)/2 < T + 1, so (T + 1) * far ≥ (L - 1) n / 4
  have hT1R : (L - 1) / 2 < (T : ℝ) + 1 := by linarith
  have hfar0 : (0 : ℝ) ≤ far := by positivity
  have hlow : (L - 1) / 2 * (n / 2) ≤ ((T : ℝ) + 1) * far := by
    have hpos : 0 ≤ (L - 1) / 2 := by linarith
    calc (L - 1) / 2 * (n / 2) ≤ ((T : ℝ) + 1) * (n / 2) :=
          mul_le_mul_of_nonneg_right hT1R.le (by positivity)
      _ ≤ ((T : ℝ) + 1) * far := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have key : (n : ℝ) * (L - 18) < 0 := by nlinarith
  have : (0 : ℝ) ≤ n * (L - 18) := mul_nonneg hnpos.le (by linarith)
  linarith

end NccCert
