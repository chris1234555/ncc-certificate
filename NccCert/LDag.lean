import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.BigOperators.Ring.List
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Ring.Hom.Defs
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.Ring

/-!
# Linear straight-line DAGs

A linear straight-line program over a commutative ring `R` with `n` inputs: nodes `0, …, N-1`;
nodes `< n` are the inputs and every other node is a linear combination of at most two earlier
nodes. `out` designates `n` output nodes.
-/

open Finset

namespace NccCert

structure LDag (R : Type*) (n N : ℕ) where
  hn : n ≤ N
  ops : Fin N → List (Fin N × R)
  ops_lt : ∀ v, ∀ p ∈ ops v, p.1 < v
  ops_input : ∀ v : Fin N, (v : ℕ) < n → ops v = []
  ops_len : ∀ v, (ops v).length ≤ 2
  out : Fin n → Fin N

namespace LDag

variable {R S : Type*} [CommRing R] [CommRing S] {n N : ℕ}

/-- Value of every node on input `x`. -/
def val (D : LDag R n N) (x : Fin n → R) (v : Fin N) : R :=
  if h : (v : ℕ) < n then x ⟨v, h⟩
  else ((D.ops v).attach.map fun p => p.1.2 * D.val x p.1.1).sum
termination_by (v : ℕ)
decreasing_by exact D.ops_lt v p.1 p.2

lemma val_eq (D : LDag R n N) (x : Fin n → R) (v : Fin N) :
    D.val x v = if h : (v : ℕ) < n then x ⟨v, h⟩
      else ((D.ops v).map fun p => p.2 * D.val x p.1).sum := by
  rw [val]
  split_ifs with h
  · rfl
  · congr 1
    rw [List.map_attach_eq_pmap]
    exact List.pmap_eq_map (f := fun p : Fin N × R => p.2 * D.val x p.1) _

lemma val_input (D : LDag R n N) (x : Fin n → R) (v : Fin N) (h : (v : ℕ) < n) :
    D.val x v = x ⟨v, h⟩ := by
  rw [val_eq, dite_eq_left_of_eq_true (eq_true h)]

lemma val_gate (D : LDag R n N) (x : Fin n → R) (v : Fin N) (h : ¬ (v : ℕ) < n) :
    D.val x v = ((D.ops v).map fun p => p.2 * D.val x p.1).sum := by
  rw [val_eq, dite_eq_right_of_eq_false (eq_false h)]

/-- Change of coefficient ring along a ring homomorphism. -/
abbrev map (D : LDag R n N) (f : R →+* S) : LDag S n N where
  hn := D.hn
  ops v := (D.ops v).map fun p => (p.1, f p.2)
  ops_lt v p hp := by
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
    exact D.ops_lt v q hq
  ops_input v hv := by simp [D.ops_input v hv]
  ops_len v := by simpa using D.ops_len v
  out := D.out

@[simp] lemma map_out (D : LDag R n N) (f : R →+* S) : (D.map f).out = D.out := rfl
lemma map_ops (D : LDag R n N) (f : R →+* S) (v : Fin N) :
    (D.map f).ops v = (D.ops v).map fun p => (p.1, f p.2) := rfl

lemma val_map (D : LDag R n N) (f : R →+* S) (x : Fin n → R) (v : Fin N) :
    (D.map f).val (fun i => f (x i)) v = f (D.val x v) := by
  suffices H : ∀ m, ∀ v : Fin N, (v : ℕ) = m → (D.map f).val (fun i => f (x i)) v = f (D.val x v)
    from H _ v rfl
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro v hm
  by_cases h : (v : ℕ) < n
  · rw [val_input (D.map f) _ v h, val_input D _ v h]
  · rw [val_gate (D.map f) _ v h, val_gate D _ v h, map_list_sum, map_ops, List.map_map,
      List.map_map]
    congr 1
    refine List.map_congr_left fun p hp => ?_
    simp only [Function.comp_apply, map_mul]
    congr 1
    exact ih p.1 (hm ▸ D.ops_lt v p hp) p.1 rfl

private lemma list_sum_mul_finset_sum {α ι : Type*} [Fintype ι] (L : List (α × R)) (g : α → ι → R) :
    (L.map fun p => p.2 * ∑ l, g p.1 l).sum = ∑ l, (L.map fun p => p.2 * g p.1 l).sum := by
  induction L with
  | nil => simp
  | cons a L ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [ih, Finset.mul_sum, Finset.sum_add_distrib]

/-- Values are linear in the input. -/
lemma val_linear (D : LDag R n N) (x : Fin n → R) (v : Fin N) :
    D.val x v = ∑ l, x l * D.val (Pi.single l 1) v := by
  suffices H : ∀ m, ∀ v : Fin N, (v : ℕ) = m → D.val x v = ∑ l, x l * D.val (Pi.single l 1) v
    from H _ v rfl
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro v hm
  by_cases h : (v : ℕ) < n
  · simp only [val_input _ _ _ h]
    rw [Finset.sum_eq_single ⟨v, h⟩]
    · simp
    · intro b _ hb; simp [Pi.single_apply, Ne.symm hb]
    · simp
  · simp only [val_gate _ _ _ h]
    have : ∀ p ∈ D.ops v, D.val x p.1 = ∑ l, x l * D.val (Pi.single l 1) p.1 :=
      fun p hp => ih p.1 (hm ▸ D.ops_lt v p hp) p.1 rfl
    rw [List.map_congr_left (fun p hp => by rw [this p hp]),
      list_sum_mul_finset_sum (D.ops v) (fun u l => x l * D.val (Pi.single l 1) u)]
    refine Finset.sum_congr rfl fun l _ => ?_
    have hfun : (fun p : Fin N × R => p.2 * (x l * D.val (Pi.single l 1) p.1)) =
        fun p => x l * (p.2 * D.val (Pi.single l 1) p.1) := by funext p; ring
    rw [hfun, List.sum_map_mul_left]

/-- `D` computes the matrix `M`. -/
def Computes (D : LDag R n N) (M : Fin n → Fin n → R) : Prop :=
  ∀ x i, D.val x (D.out i) = ∑ l, M i l * x l

lemma computes_of_basis (D : LDag R n N) (M : Fin n → Fin n → R)
    (h : ∀ i l, D.val (Pi.single l 1) (D.out i) = M i l) : D.Computes M := by
  intro x i
  rw [val_linear]
  exact Finset.sum_congr rfl fun l _ => by rw [h, mul_comm]

end LDag

end NccCert
