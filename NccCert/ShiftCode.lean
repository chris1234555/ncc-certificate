import NccCert.Graph
import NccCert.Code
import NccCert.LDag
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Fintype.Prod
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases

/-!
# A rate-one network code from a circuit, on a graph of maximum degree three

Given a linear DAG `D` over a field `K` computing a matrix `M`, coefficients `d` and a map `σ` with
`∑ l, M (σ j) l * d l * M l m = [m = j]`, we build a linear network code that delivers message `j`
from input `j` of a first copy of `D` to output `σ j` of a second copy (whose inputs are
`d k • (output k of the first copy)`). Every use of a value is given its own relay vertex, chained
behind the previous use of the same value, so every vertex has at most three neighbours.
The graph depends only on the shape of `D` (not on `d`, `σ`, or the coefficients).
-/

open Finset

namespace NccCert
namespace ShiftCode

set_option linter.unusedSectionVars false

variable {K : Type*} [Field K] {n N : ℕ} (D : LDag K n N)

/-- Uses of node values: operand `i` of node `v` in copy `b`, or the `k`-th diagonal link. -/
abbrev Use := (Fin 2 × Σ v : Fin N, Fin (D.ops v).length) ⊕ Fin n

/-- A node of one of the two copies. -/
@[nolint unusedArguments]
abbrev Node (_D : LDag K n N) : Type := Fin 2 × Fin N

/-- Vertices: nodes of the two copies, and one relay vertex per use. -/
abbrev Vtx := Node D ⊕ Use D

/-- Edges: two per use (into its relay vertex, and from it to the consumer). -/
abbrev Ed := Use D × Bool

/-- The node whose value a use carries. -/
def src : Use D → Node D
  | .inl (b, ⟨v, i⟩) => (b, ((D.ops v).get i).1)
  | .inr k => (0, D.out k)

/-- The node consuming a use. -/
def cons : Use D → Node D
  | .inl (b, ⟨v, _⟩) => (b, v)
  | .inr k => (1, ⟨k, lt_of_lt_of_le k.2 D.hn⟩)

/-- An enumeration of uses (used to chain the uses of a node). -/
noncomputable def idx (e : Use D) : ℕ := (Fintype.equivFin (Use D) e : ℕ)

lemma idx_lt (e : Use D) : idx D e < Fintype.card (Use D) := (Fintype.equivFin (Use D) e).2

lemma idx_injective : Function.Injective (idx D) := by
  intro a b h
  exact (Fintype.equivFin (Use D)).injective (Fin.ext h)

/-- Earlier uses of the same value. -/
noncomputable def prevs (e : Use D) : Finset (Use D) :=
  univ.filter fun e' => src D e' = src D e ∧ idx D e' < idx D e

/-- The vertex feeding the relay vertex of `e`: the relay of the previous use of the same value,
or the node itself for its first use. -/
noncomputable def predV (e : Use D) : Vtx D :=
  if h : (prevs D e).Nonempty then
    .inr (Classical.choose ((prevs D e).exists_max_image (idx D) h))
  else .inl (src D e)

lemma predV_spec (e : Use D) :
    (predV D e = .inl (src D e) ∧ prevs D e = ∅) ∨
      ∃ e', predV D e = .inr e' ∧ e' ∈ prevs D e ∧ ∀ e'' ∈ prevs D e, idx D e'' ≤ idx D e' := by
  unfold predV
  split_ifs with h
  · right
    obtain ⟨h1, h2⟩ := Classical.choose_spec ((prevs D e).exists_max_image (idx D) h)
    exact ⟨_, rfl, h1, h2⟩
  · left
    exact ⟨rfl, Finset.not_nonempty_iff_eq_empty.mp h⟩

/-- The network. -/
noncomputable def ends : Ed D → Vtx D × Vtx D
  | (e, false) => (predV D e, .inr e)
  | (e, true) => (.inr e, .inl (cons D e))

/-! ### Values of the code -/

/-- Inputs of the second copy. -/
def y (d : Fin n → K) (x : Fin n → K) : Fin n → K := fun k => d k * D.val x (D.out k)

/-- Value of a node. -/
def nodeVal (d x : Fin n → K) (a : Node D) : K :=
  if a.1 = 0 then D.val x a.2 else D.val (y D d x) a.2

/-- Value of a vertex (relays copy the value they carry). -/
def vval (d x : Fin n → K) : Vtx D → K
  | .inl a => nodeVal D d x a
  | .inr e => nodeVal D d x (src D e)

/-- Coefficient applied at the consumer of a use. -/
def useCoef (d : Fin n → K) : Use D → K
  | .inl (_, ⟨v, i⟩) => ((D.ops v).get i).2
  | .inr k => d k

/-- Edge coefficients: relay edges copy, delivery edges apply the use coefficient. -/
def edgeCoef (d : Fin n → K) : Ed D → K
  | (_, false) => 1
  | (e, true) => useCoef D d e

/-- Message `j` enters at input `j` of the first copy. -/
def msgSrc (j : Fin n) : Vtx D := .inl (0, ⟨j, lt_of_lt_of_le j.2 D.hn⟩)

/-- Output `t` of the second copy. -/
def outV (t : Fin n) : Vtx D := .inl (1, D.out t)

/-! ### Structural lemmas -/

lemma sum_ed (f : Ed D → K) : ∑ ε, f ε = ∑ e, (f (e, true) + f (e, false)) := by
  rw [Fintype.sum_prod_type]
  exact Finset.sum_congr rfl fun e _ => by rw [Fintype.sum_bool]

lemma predV_eq_inr_unique {e e₁ e₂ : Use D} (h₁ : predV D e₁ = .inr e) (h₂ : predV D e₂ = .inr e) :
    e₁ = e₂ := by
  rcases predV_spec D e₁ with ⟨h, -⟩ | ⟨a, ha, ha1, ha2⟩
  · rw [h] at h₁; cases h₁
  rcases predV_spec D e₂ with ⟨h, -⟩ | ⟨b, hb, hb1, hb2⟩
  · rw [h] at h₂; cases h₂
  rw [ha] at h₁; rw [hb] at h₂
  cases h₁; cases h₂
  simp only [prevs, Finset.mem_filter, Finset.mem_univ, true_and] at ha1 hb1
  by_contra hne
  rcases lt_or_gt_of_ne (fun h => hne (idx_injective D h)) with hlt | hlt
  · have : e₁ ∈ prevs D e₂ := by
      simp only [prevs, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨ha1.1.symm.trans hb1.1, hlt⟩
    have := hb2 e₁ this
    omega
  · have : e₂ ∈ prevs D e₁ := by
      simp only [prevs, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨hb1.1.symm.trans ha1.1, hlt⟩
    have := ha2 e₂ this
    omega

lemma predV_eq_inl_unique {a : Node D} {e₁ e₂ : Use D} (h₁ : predV D e₁ = .inl a)
    (h₂ : predV D e₂ = .inl a) : e₁ = e₂ := by
  rcases predV_spec D e₁ with ⟨h, hp₁⟩ | ⟨_, h, -⟩
  swap; · rw [h] at h₁; cases h₁
  rcases predV_spec D e₂ with ⟨h', hp₂⟩ | ⟨_, h', -⟩
  swap; · rw [h'] at h₂; cases h₂
  rw [h] at h₁; rw [h'] at h₂
  cases h₁; injection h₂ with h₂
  by_contra hne
  rcases lt_or_gt_of_ne (fun h => hne (idx_injective D h)) with hlt | hlt
  · have : e₁ ∈ prevs D e₂ := by
      simp only [prevs, Finset.mem_filter, Finset.mem_univ, true_and]; exact ⟨h₂.symm, hlt⟩
    rw [hp₂] at this; simp at this
  · have : e₂ ∈ prevs D e₁ := by
      simp only [prevs, Finset.mem_filter, Finset.mem_univ, true_and]; exact ⟨h₂, hlt⟩
    rw [hp₁] at this; simp at this

/-! ### Maximum degree three -/

lemma card_cons_le (a : Node D) : (univ.filter fun e : Use D => cons D e = a).card ≤ 2 := by
  obtain ⟨b, v⟩ := a
  by_cases hv : (v : ℕ) < n
  · -- only the diagonal link can enter an input node
    have hsub : (univ.filter fun e : Use D => cons D e = (b, v)) ⊆ {.inr ⟨v, hv⟩} := by
      intro e he
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at he
      rcases e with ⟨b', ⟨v', i⟩⟩ | k
      · simp only [cons, Prod.mk.injEq] at he
        obtain ⟨-, rfl⟩ := he
        have := D.ops_input v' hv
        exact absurd i.2 (by simp [this])
      · simp only [cons, Prod.mk.injEq] at he
        simp only [Finset.mem_singleton, Sum.inr.injEq]
        ext; simp [← he.2]
    exact (Finset.card_le_card hsub).trans (by simp)
  · have hsub : (univ.filter fun e : Use D => cons D e = (b, v)) ⊆
        (univ : Finset (Fin (D.ops v).length)).image fun i => .inl (b, ⟨v, i⟩) := by
      intro e he
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at he
      rcases e with ⟨b', ⟨v', i⟩⟩ | k
      · simp only [cons, Prod.mk.injEq] at he
        obtain ⟨rfl, rfl⟩ := he
        exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
      · simp only [cons, Prod.mk.injEq] at he
        exact absurd (by rw [← he.2]; exact k.2) hv
    refine (Finset.card_le_card hsub).trans (Finset.card_image_le.trans ?_)
    simpa using D.ops_len v

lemma card_nbrs_le (x : Vtx D) [DecidableEq (Use D)] : (nbrs (ends D) x).card ≤ 3 := by
  classical
  rcases x with a | e
  · -- a node: its first relay, and the relays of the uses it consumes
    have hsub : nbrs (ends D) (.inl a) ⊆
        (univ.filter fun e : Use D => predV D e = .inl a).image Sum.inr ∪
          (univ.filter fun e : Use D => cons D e = a).image Sum.inr := by
      intro z hz
      simp only [nbrs, Finset.mem_filter, Finset.mem_univ, true_and, Adj] at hz
      obtain ⟨⟨e, b⟩, h⟩ := hz
      cases b <;> simp only [ends, Prod.mk.injEq] at h
      · rcases h with ⟨h1, rfl⟩ | ⟨-, h2⟩
        · exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨e, by simp [h1], rfl⟩)
        · cases h2
      · rcases h with ⟨h1, -⟩ | ⟨rfl, h2⟩
        · cases h1
        · exact Finset.mem_union_right _ (Finset.mem_image.mpr
            ⟨e, by simpa using (Sum.inl.inj h2), rfl⟩)
    have h1 : (univ.filter fun e : Use D => predV D e = .inl a).card ≤ 1 :=
      Finset.card_le_one.mpr fun e₁ he₁ e₂ he₂ => by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at he₁ he₂
        exact predV_eq_inl_unique D he₁ he₂
    calc (nbrs (ends D) (.inl a)).card ≤ _ := Finset.card_le_card hsub
      _ ≤ _ := Finset.card_union_le _ _
      _ ≤ 1 + 2 := add_le_add (Finset.card_image_le.trans h1)
            (Finset.card_image_le.trans (card_cons_le D a))
  · -- a relay: its predecessor, its consumer, and the next relay of the same value
    have hsub : nbrs (ends D) (.inr e) ⊆
        {predV D e, .inl (cons D e)} ∪
          (univ.filter fun e' : Use D => predV D e' = .inr e).image Sum.inr := by
      intro z hz
      simp only [nbrs, Finset.mem_filter, Finset.mem_univ, true_and, Adj] at hz
      obtain ⟨⟨e', b⟩, h⟩ := hz
      cases b <;> simp only [ends, Prod.mk.injEq] at h
      · rcases h with ⟨h1, rfl⟩ | ⟨rfl, h2⟩
        · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨e', by simp [h1], rfl⟩)
        · cases h2; simp
      · rcases h with ⟨h1, rfl⟩ | ⟨-, h2⟩
        · cases h1; simp
        · cases h2
    have h1 : (univ.filter fun e' : Use D => predV D e' = .inr e).card ≤ 1 :=
      Finset.card_le_one.mpr fun e₁ he₁ e₂ he₂ => by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at he₁ he₂
        exact predV_eq_inr_unique D he₁ he₂
    calc (nbrs (ends D) (.inr e)).card ≤ _ := Finset.card_le_card hsub
      _ ≤ _ := Finset.card_union_le _ _
      _ ≤ 2 + 1 := add_le_add (Finset.card_le_two) (Finset.card_image_le.trans h1)

/-! ### Acyclicity -/

/-- Position of a node: all of copy `0` before copy `1`, in node order. -/
def blk (a : Node D) : ℕ := (a.1 : ℕ) * (N + 1) + a.2

/-- Rank: a node, followed by the relays of its uses (in use order). -/
noncomputable def rank : Vtx D → ℕ
  | .inl a => blk D a * (Fintype.card (Use D) + 2)
  | .inr e => blk D (src D e) * (Fintype.card (Use D) + 2) + 1 + idx D e

lemma blk_src_lt_cons (e : Use D) : blk D (src D e) < blk D (cons D e) := by
  rcases e with ⟨b, ⟨v, i⟩⟩ | k
  · simp only [src, cons, blk]
    have := D.ops_lt v _ (List.get_mem (D.ops v) i)
    have h : (((D.ops v).get i).1 : ℕ) < v := this
    omega
  · simp only [src, cons, blk]
    have := (D.out k).2
    simp
    omega

lemma rank_lt (ε : Ed D) : rank D (ends D ε).1 < rank D (ends D ε).2 := by
  obtain ⟨e, b⟩ := ε
  cases b
  · simp only [ends]
    rcases predV_spec D e with ⟨h, -⟩ | ⟨e', h, he', -⟩
    · rw [h]; simp only [rank]; omega
    · rw [h]
      simp only [prevs, Finset.mem_filter, Finset.mem_univ, true_and] at he'
      simp only [rank, he'.1]
      omega
  · simp only [ends, rank]
    have h1 := blk_src_lt_cons D e
    have h2 := idx_lt D e
    have : (blk D (src D e) + 1) * (Fintype.card (Use D) + 2) ≤
        blk D (cons D e) * (Fintype.card (Use D) + 2) := Nat.mul_le_mul_right _ h1
    have h3 : blk D (src D e) * (Fintype.card (Use D) + 2) + 1 + idx D e <
        (blk D (src D e) + 1) * (Fintype.card (Use D) + 2) := by
      rw [Nat.add_mul, Nat.one_mul, Nat.add_assoc]
      exact Nat.add_lt_add_left (by omega) _
    exact lt_of_lt_of_le h3 this

/-! ### The code -/

lemma sum_inl_part (b : Fin 2) (v : Fin N)
    (F : (p : Fin 2 × Σ v : Fin N, Fin (D.ops v).length) → K) :
    ∑ p : Fin 2 × Σ v : Fin N, Fin (D.ops v).length,
        (if (p.1, p.2.1) = (b, v) then F p else 0) =
      ∑ i : Fin (D.ops v).length, F (b, ⟨v, i⟩) := by
  rw [Fintype.sum_prod_type, Finset.sum_eq_single b]
  · rw [Fintype.sum_sigma, Finset.sum_eq_single v]
    · simp
    · intro v' _ hv'
      exact Finset.sum_eq_zero fun i _ => by simp [hv']
    · simp
  · intro b' _ hb'
    exact Finset.sum_eq_zero fun p _ => by simp [hb']
  · simp

lemma consistent (d : Fin n → K) (x : Fin n → K) (w : Vtx D) :
    vval D d x w =
      (∑ ε, if (ends D ε).2 = w then edgeCoef D d ε * vval D d x (ends D ε).1 else 0) +
        ∑ j, if msgSrc D j = w then x j else 0 := by
  classical
  rw [sum_ed]
  rcases w with ⟨b, v⟩ | e
  · -- a node
    have hmsg : (∑ j, if msgSrc D j = Sum.inl (b, v) then x j else 0) =
        if h : b = 0 ∧ (v : ℕ) < n then x ⟨v, h.2⟩ else 0 := by
      split_ifs with h
      · rw [Finset.sum_eq_single ⟨v, h.2⟩]
        · simp [msgSrc, h.1]
        · intro j _ hj
          rw [if_neg]
          intro hc
          simp only [msgSrc, Sum.inl.injEq, Prod.mk.injEq] at hc
          exact hj (Fin.ext (by simpa using congrArg Fin.val hc.2))
        · simp
      · refine Finset.sum_eq_zero fun j _ => ?_
        rw [if_neg]
        intro hc
        simp only [msgSrc, Sum.inl.injEq, Prod.mk.injEq] at hc
        exact h ⟨hc.1.symm, by
          have := congrArg Fin.val hc.2
          simp only at this
          rw [← this]; exact j.2⟩
    rw [hmsg]
    simp only [ends, edgeCoef, reduceCtorEq, if_false, add_zero, Sum.inl.injEq]
    rw [Fintype.sum_sum_type]
    have hinl : (∑ p : Fin 2 × Σ v : Fin N, Fin (D.ops v).length,
        if cons D (.inl p) = (b, v) then useCoef D d (.inl p) * vval D d x (.inr (.inl p)) else 0) =
        ∑ i : Fin (D.ops v).length,
          ((D.ops v).get i).2 * nodeVal D d x (b, ((D.ops v).get i).1) := by
      have hc : ∀ p : Fin 2 × Σ v : Fin N, Fin (D.ops v).length,
          cons D (.inl p) = (p.1, p.2.1) := fun p => by rcases p with ⟨b, ⟨v, i⟩⟩; rfl
      simp only [hc]
      rw [sum_inl_part D b v (fun p => useCoef D d (.inl p) * vval D d x (.inr (.inl p)))]
      rfl
    rw [hinl]
    have hlist : ∑ i : Fin (D.ops v).length,
        ((D.ops v).get i).2 * nodeVal D d x (b, ((D.ops v).get i).1) =
        ((D.ops v).map fun p => p.2 * nodeVal D d x (b, p.1)).sum := by
      rw [← Fin.sum_univ_fun_getElem]
      rfl
    rw [hlist]
    by_cases hv : (v : ℕ) < n
    · have hops := D.ops_input v hv
      rw [hops]
      simp only [List.map_nil, List.sum_nil, zero_add]
      fin_cases b
      · simp only [Fin.zero_eta, Fin.isValue, and_true, hv, dite_true]
        have : (∑ k : Fin n, if cons D (.inr k) = ((0 : Fin 2), v) then
            useCoef D d (.inr k) * vval D d x (.inr (.inr k)) else 0) = 0 :=
          Finset.sum_eq_zero fun k _ => by simp [cons]
        rw [this, zero_add]
        simp [vval, nodeVal, LDag.val_input _ _ _ hv]
      · simp only [Fin.mk_one, Fin.isValue, one_ne_zero, false_and, dite_false, add_zero]
        rw [Finset.sum_eq_single ⟨v, hv⟩]
        · simp [cons, vval, nodeVal, useCoef, src, y, LDag.val_input _ _ _ hv]
        · intro k _ hk
          rw [if_neg]
          intro hc
          simp only [cons, Prod.mk.injEq] at hc
          exact hk (Fin.ext (by simpa using congrArg Fin.val hc.2))
        · simp
    · have hdiag : (∑ k : Fin n, if cons D (.inr k) = (b, v) then
          useCoef D d (.inr k) * vval D d x (.inr (.inr k)) else 0) = 0 :=
        Finset.sum_eq_zero fun k _ => by
          rw [if_neg]
          intro hc
          simp only [cons, Prod.mk.injEq] at hc
          exact hv (hc.2 ▸ k.2)
      rw [hdiag, add_zero, dif_neg (fun h => hv h.2), add_zero]
      simp only [vval, nodeVal]
      split_ifs with hb
      · rw [LDag.val_gate _ _ _ hv]
      · rw [LDag.val_gate _ _ _ hv]
  · -- a relay vertex
    have hmsg : (∑ j, if msgSrc D j = Sum.inr e then x j else 0) = 0 :=
      Finset.sum_eq_zero fun j _ => by simp [msgSrc]
    rw [hmsg, add_zero]
    simp only [ends, edgeCoef, reduceCtorEq, if_false, zero_add, Sum.inr.injEq, one_mul]
    rw [Finset.sum_ite_eq']
    simp only [Finset.mem_univ, if_true]
    rcases predV_spec D e with ⟨h, -⟩ | ⟨e', h, he', -⟩
    · rw [h]; rfl
    · rw [h]
      simp only [prevs, Finset.mem_filter, Finset.mem_univ, true_and] at he'
      simp [vval, he'.1]

/-- **The code.** -/
noncomputable def code (d : Fin n → K) (σ : Fin n → Fin n) (M : Fin n → Fin n → K)
    (hM : D.Computes M) (hinv : ∀ j m, ∑ l, M (σ j) l * d l * M l m = if m = j then 1 else 0) :
    LinearCode (ends D) (msgSrc D) (fun j => outV D (σ j)) K where
  fwd _ := true
  coef := edgeCoef D d
  rank := rank D
  acyclic ε := by simpa [tailOf, headOf] using rank_lt D ε
  solves x := by
    refine ⟨vval D d x, fun w => by simpa [tailOf, headOf] using consistent D d x w, fun j => ?_⟩
    simp only [outV, vval, nodeVal, Fin.isValue, one_ne_zero, if_false]
    rw [hM (y D d x) (σ j)]
    simp only [y]
    have : ∀ l, M (σ j) l * (d l * D.val x (D.out l)) =
        ∑ m, M (σ j) l * d l * M l m * x m := by
      intro l
      rw [hM x l, Finset.mul_sum, Finset.mul_sum]
      exact Finset.sum_congr rfl fun m _ => by ring
    simp only [this]
    rw [Finset.sum_comm]
    simp only [← Finset.sum_mul, hinv, ite_mul, one_mul, zero_mul]
    simp

end ShiftCode
end NccCert
