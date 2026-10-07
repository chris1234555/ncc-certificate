import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fin.Basic
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Ring
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Algebra.Group.Fin.Basic

/-!
# Balls in bounded-degree multigraphs

* `ball`: vertices within distance `t`; `card_ball_le`: at most `(Δ+1)^t` of them.
* `pot`: a truncated distance (`0` at the centre, `T+1` outside the radius-`T` ball, changing by at
  most one along an edge).
* `exists_shift_far`: among the `n` cyclic shift instances `j ↦ (A j, B (j + s))` (with `B`
  injective) some shift has at least `n - (Δ+1)^T` pairs at distance `> T`.
-/

open Finset

namespace NccCert

variable {V Ed : Type*} [Fintype V] [DecidableEq V] [Fintype Ed]

/-! ### Balls and the truncated distance potential -/

/-- Undirected adjacency. -/
def Adj (ends : Ed → V × V) (x y : V) : Prop := ∃ e, ends e = (x, y) ∨ ends e = (y, x)

instance [DecidableEq Ed] (ends : Ed → V × V) (x y : V) : Decidable (Adj ends x y) := by
  unfold Adj; infer_instance

variable [DecidableEq Ed]

/-- Neighbours of `x`. -/
def nbrs (ends : Ed → V × V) (x : V) : Finset V := univ.filter (Adj ends x)

/-- Vertices within distance `t` of `v`. -/
def ball (ends : Ed → V × V) (v : V) : ℕ → Finset V
  | 0 => {v}
  | t + 1 => ball ends v t ∪ (ball ends v t).biUnion (nbrs ends)

lemma ball_succ_mono (ends : Ed → V × V) (v : V) (t : ℕ) :
    ball ends v t ⊆ ball ends v (t + 1) := Finset.subset_union_left

lemma ball_mono (ends : Ed → V × V) (v : V) {t t' : ℕ} (h : t ≤ t') :
    ball ends v t ⊆ ball ends v t' := by
  induction h with
  | refl => exact le_rfl
  | step _ ih => exact ih.trans (ball_succ_mono ends v _)

lemma mem_ball_self (ends : Ed → V × V) (v : V) (t : ℕ) : v ∈ ball ends v t :=
  ball_mono ends v (Nat.zero_le t) (by simp [ball])

lemma mem_ball_succ_of_adj (ends : Ed → V × V) (v : V) {t : ℕ} {x y : V}
    (hx : x ∈ ball ends v t) (hxy : Adj ends x y) : y ∈ ball ends v (t + 1) := by
  simp only [ball, Finset.mem_union, Finset.mem_biUnion]
  exact Or.inr ⟨x, hx, by simp [nbrs, hxy]⟩

omit [Fintype V] [DecidableEq V] [Fintype Ed] [DecidableEq Ed] in
lemma adj_comm (ends : Ed → V × V) {x y : V} : Adj ends x y ↔ Adj ends y x := by
  unfold Adj; exact ⟨fun ⟨e, h⟩ => ⟨e, h.symm⟩, fun ⟨e, h⟩ => ⟨e, h.symm⟩⟩

lemma card_ball_le (ends : Ed → V × V) {Δ : ℕ} (hdeg : ∀ x, (nbrs ends x).card ≤ Δ)
    (v : V) (t : ℕ) : (ball ends v t).card ≤ (Δ + 1) ^ t := by
  induction t with
  | zero => simp [ball]
  | succ t ih =>
    calc (ball ends v (t + 1)).card
        ≤ (ball ends v t).card + ((ball ends v t).biUnion (nbrs ends)).card :=
          Finset.card_union_le _ _
      _ ≤ (ball ends v t).card + ∑ x ∈ ball ends v t, (nbrs ends x).card := by
          gcongr; exact Finset.card_biUnion_le
      _ ≤ (ball ends v t).card + ∑ _x ∈ ball ends v t, Δ := by
          gcongr with x; exact hdeg x
      _ = (Δ + 1) * (ball ends v t).card := by
          rw [Finset.sum_const, smul_eq_mul]; ring
      _ ≤ (Δ + 1) * (Δ + 1) ^ t := by gcongr
      _ = (Δ + 1) ^ (t + 1) := by ring

/-- Truncated distance from `v`: the number of radii `t ≤ T` whose ball misses `x`. -/
def pot (ends : Ed → V × V) (v : V) (T : ℕ) (x : V) : ℕ :=
  ((range (T + 1)).filter fun t => x ∉ ball ends v t).card

lemma pot_self (ends : Ed → V × V) (v : V) (T : ℕ) : pot ends v T v = 0 := by
  simp [pot, mem_ball_self]

lemma pot_far (ends : Ed → V × V) (v : V) (T : ℕ) {x : V} (hx : x ∉ ball ends v T) :
    pot ends v T x = T + 1 := by
  unfold pot
  rw [Finset.filter_true_of_mem, Finset.card_range]
  intro t ht hxt
  exact hx (ball_mono ends v (Nat.lt_succ_iff.mp (Finset.mem_range.mp ht)) hxt)

lemma pot_le_succ_of_adj (ends : Ed → V × V) (v : V) (T : ℕ) {x y : V} (hxy : Adj ends x y) :
    pot ends v T y ≤ pot ends v T x + 1 := by
  unfold pot
  set A := (range (T + 1)).filter fun t => x ∉ ball ends v t
  set B := (range (T + 1)).filter fun t => y ∉ ball ends v t
  have hsub : B ⊆ insert 0 (A.image (· + 1)) := by
    intro t ht
    rcases t with _ | t
    · exact Finset.mem_insert_self _ _
    · refine Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨t, ?_, rfl⟩)
      simp only [B, Finset.mem_filter, Finset.mem_range] at ht
      simp only [A, Finset.mem_filter, Finset.mem_range]
      refine ⟨by omega, fun hx => ht.2 (mem_ball_succ_of_adj ends v hx hxy)⟩
  calc B.card ≤ (insert 0 (A.image (· + 1))).card := Finset.card_le_card hsub
    _ ≤ (A.image (· + 1)).card + 1 := Finset.card_insert_le _ _
    _ ≤ A.card + 1 := Nat.add_le_add_right Finset.card_image_le 1


/-- **Some cyclic shift is far.** In a graph of maximum degree `Δ`, if `B` is injective then for
some shift `s` at least `n - (Δ+1)^T` of the pairs `(A j, B (j + s))` are at distance `> T`. -/
theorem exists_shift_far (ends : Ed → V × V) {n : ℕ} [NeZero n] (A B : Fin n → V)
    (hB : Function.Injective B) {Δ : ℕ} (hdeg : ∀ x, (nbrs ends x).card ≤ Δ) (T : ℕ) :
    ∃ s : Fin n, n - (Δ + 1) ^ T ≤
      (univ.filter fun j : Fin n => B (j + s) ∉ ball ends (A j) T).card := by
  -- double counting over all shifts
  have hj : ∀ j : Fin n, n - (Δ + 1) ^ T ≤
      (univ.filter fun s : Fin n => B (j + s) ∉ ball ends (A j) T).card := by
    intro j
    have hin : (univ.filter fun s : Fin n => B (j + s) ∈ ball ends (A j) T).card ≤ (Δ + 1) ^ T := by
      refine le_trans ?_ (card_ball_le ends hdeg (A j) T)
      refine Finset.card_le_card_of_injOn (fun s => B (j + s)) ?_ ?_
      · intro s hs; simpa using hs
      · intro s₁ _ s₂ _ h; exact add_left_cancel (hB h)
    have hsplit := Finset.card_filter_add_card_filter_not
      (s := (univ : Finset (Fin n))) (fun s : Fin n => B (j + s) ∈ ball ends (A j) T)
    simp only [Finset.card_univ, Fintype.card_fin] at hsplit
    omega
  have htot : ∑ _s : Fin n, (n - (Δ + 1) ^ T) ≤
      ∑ s : Fin n, (univ.filter fun j : Fin n => B (j + s) ∉ ball ends (A j) T).card := by
    calc ∑ _s : Fin n, (n - (Δ + 1) ^ T) = ∑ _j : Fin n, (n - (Δ + 1) ^ T) := rfl
      _ ≤ ∑ j : Fin n, (univ.filter fun s : Fin n => B (j + s) ∉ ball ends (A j) T).card :=
          Finset.sum_le_sum fun j _ => hj j
      _ = ∑ s : Fin n, (univ.filter fun j : Fin n => B (j + s) ∉ ball ends (A j) T).card := by
          simp only [Finset.card_filter]
          exact Finset.sum_comm
  obtain ⟨s, -, hs⟩ := Finset.exists_le_of_sum_le Finset.univ_nonempty htot
  exact ⟨s, hs⟩

end NccCert
