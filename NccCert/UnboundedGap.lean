import NccCert.Main
import NccCert.Unconditional

/-!
# The coding advantage is unbounded

`NCC_rate r` says: whenever a rate-one scalar linear code exists on a (non-degenerate) undirected
unit-capacity instance, a concurrent multicommodity flow of rate `r` exists. The Li–Li conjecture
implies `NCC_rate 1`, and `NCC_rate 1 → NCC_rate r` for every `r ≤ 1`.

`not_NCC_rate` shows `¬ NCC_rate r` for *every* `r > 0`: for each `ε > 0` there is an undirected
instance where a linear code achieves rate `1` but no concurrent flow achieves rate `ε`. So the
coding/routing gap in undirected graphs is not merely nonzero but unbounded (it is at most
`O(log |V|)` by the sparsest-cut bound).

Same argument as `not_NCC_rate_one_of_exactFourier`, with `c = r / 64` and `n ≥ 2 ^ m`, where
`m ≥ max 18 (16 / r + 2)`.
-/

open Finset OAI.ExactFourier

namespace NccCert

/-- Rate-`r` form of the conjecture's consequence. -/
def NCC_rate (r : ℝ) : Prop :=
  ∀ (V Ed : Type) [Fintype V] [DecidableEq V] [Fintype Ed] (ends : Ed → V × V) (k : ℕ)
    (src snk : Fin k → V) (F : Type) [Field F] [Finite F],
    (∀ e, (ends e).1 ≠ (ends e).2) →
    Function.Injective src → Function.Injective snk → (∀ i j, src i ≠ snk j) →
    Nonempty (LinearCode ends src snk F) → Nonempty (ConcurrentFlow ends src snk r)

/-- Sanity check: `NCC_rate 1` is literally `NCC_rate_one`. -/
example : NCC_rate 1 ↔ NCC_rate_one := Iff.rfl

theorem not_NCC_rate_of_exactFourier (hF : MainStatement) {r : ℝ} (hr : 0 < r) :
    ¬ NCC_rate r := by
  intro hN
  set m : ℕ := max 18 (⌈16 / r⌉₊ + 2) with hm
  have hm18 : 18 ≤ m := le_max_left _ _
  have hm2 : ⌈16 / r⌉₊ + 2 ≤ m := le_max_right _ _
  have hN0 : 2 ≤ 2 ^ m :=
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) (by omega)
  obtain ⟨n, hn, C, hC, hsize⟩ := hF (r / 64) (by positivity) (2 ^ m) hN0
  have hn18 : 2 ^ 18 ≤ n := le_trans (Nat.pow_le_pow_right (by norm_num) hm18) hn
  have hn2 : 2 ≤ n := le_trans (by norm_num) hn18
  have : NeZero n := ⟨by omega⟩
  obtain ⟨S, hS⟩ := shiftData_of_circuit hn2 C hC
  set T := Nat.log 4 (n / 2) with hTdef
  have hdeg : ∀ x, (nbrs (ShiftCode.ends S.D) x).card ≤ 3 :=
    fun x => ShiftCode.card_nbrs_le S.D x
  have hB : Function.Injective fun t : Fin n => ShiftCode.outV S.D (tau t) := by
    intro a b h
    simp only [ShiftCode.outV, Sum.inl.injEq, Prod.mk.injEq, true_and] at h
    exact tau_injective (S.out_inj h)
  obtain ⟨s, hs⟩ := exists_shift_far (ShiftCode.ends S.D) (ShiftCode.msgSrc S.D)
    (fun t => ShiftCode.outV S.D (tau t)) hB hdeg T
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
  have hT1 : 4 ^ T ≤ n / 2 := Nat.pow_log_le_self 4 (by omega)
  have hT2 : n / 2 < 4 ^ (T + 1) := Nat.lt_pow_succ_log_self (by norm_num) _
  have hfar2 : n ≤ 2 * far := by omega
  have hn4 : n < 2 ^ (2 * T + 3) := by
    have : 2 ^ (2 * T + 3) = 2 * 4 ^ (T + 1) := by
      rw [show 2 * T + 3 = 1 + 2 * (T + 1) by ring, pow_add, pow_mul]; norm_num
    omega
  set L := Real.logb 2 (n : ℝ) with hL
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hLm : (m : ℝ) ≤ L := by
    have h1 : ((2 : ℝ) ^ m) ≤ n := by exact_mod_cast hn
    have h2 := Real.logb_le_logb_of_le (b := 2) (by norm_num) (by positivity) h1
    rwa [Real.logb_pow, Real.logb_self_eq_one (by norm_num), mul_one] at h2
  have hLT : L < 2 * T + 3 := by
    have h1 : (n : ℝ) < (2 : ℝ) ^ (2 * T + 3) := by exact_mod_cast hn4
    have h2 := Real.logb_lt_logb (b := 2) (by norm_num) hnpos h1
    rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num), mul_one] at h2
    push_cast at h2
    linarith
  -- `r * L ≥ 16 + 2 r`
  have hm16 : 16 / r + 2 ≤ (m : ℝ) := by
    have h1 : 16 / r ≤ (⌈16 / r⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : ((⌈16 / r⌉₊ + 2 : ℕ) : ℝ) ≤ m := by exact_mod_cast hm2
    push_cast at h2
    linarith
  have hrL : 16 + 2 * r ≤ r * L := by
    have h1 : 16 / r + 2 ≤ L := hm16.trans hLm
    have h2 := mul_le_mul_of_nonneg_left h1 hr.le
    rw [mul_add, mul_div_cancel₀ _ hr.ne'] at h2
    linarith
  have hflowR : r * (((T : ℝ) + 1) * far) ≤ 8 * C.size + 2 * n := by
    have : (Fintype.card (ShiftCode.Ed S.D) : ℝ) ≤ 8 * C.size + 2 * n := by exact_mod_cast hcard
    linarith
  have hfarR : (n : ℝ) ≤ 2 * far := by exact_mod_cast hfar2
  have hsizeR : (C.size : ℝ) < r / 64 * n * L := hsize
  have hT1R : (L - 1) / 2 < (T : ℝ) + 1 := by linarith
  have hlow : (L - 1) / 2 * (n / 2) ≤ ((T : ℝ) + 1) * far := by
    calc (L - 1) / 2 * (n / 2) ≤ ((T : ℝ) + 1) * (n / 2) :=
          mul_le_mul_of_nonneg_right hT1R.le (by positivity)
      _ ≤ ((T : ℝ) + 1) * far := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have h1 : r * ((L - 1) / 2 * (n / 2)) ≤ 8 * C.size + 2 * n :=
    (mul_le_mul_of_nonneg_left hlow hr.le).trans hflowR
  have h3 : 0 ≤ (n : ℝ) * (r * L - 16 - 2 * r) := mul_nonneg hnpos.le (by linarith)
  nlinarith

/-- **Unbounded coding advantage.** For every `r > 0` there is an undirected unit-capacity instance
(maximum degree three, no loops, distinct terminals) with a rate-one scalar linear code but no
concurrent multicommodity flow of rate `r`. -/
theorem not_NCC_rate {r : ℝ} (hr : 0 < r) : ¬ NCC_rate r :=
  not_NCC_rate_of_exactFourier OAI.ExactFourier.main_theorem hr

end NccCert

