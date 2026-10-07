import NccCert.ExactFourierDefs
import NccCert.ShiftCode
import NccCert.Specialize
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Field.GeomSum

/-!
# From exact Fourier circuits to shift codes over a finite field

* `toLDag`: an `OAI.ExactFourier.Circuit` as a linear DAG (with coefficients chosen per gate).
* `cyclic_identity`: `∑ₗ ζ^{σ(j)·l} · (n⁻¹ ζ^{l·s}) · ζ^{l·m} = [m = j]` for `σ(j) = -(j+s)`.
* `shiftData_of_circuit`: a Fourier circuit yields a finite field `K` and a single linear DAG over
  `K` (with the same shape) together with, for every shift `s`, coefficients making
  `ShiftCode.code` deliver message `j` to output `τ (j + s)`.
-/

open Finset OAI.ExactFourier

namespace NccCert

variable {n : ℕ}

/-- `omega` after normalising `Nat.add` applications produced by pattern matching. -/
local macro "nomega" : tactic =>
  `(tactic| ((try simp only [Nat.add_eq, Fin.val_last, Fin.coe_castSucc] at *) <;> omega))

/-! ### Circuits as linear DAGs -/

/-- The gate at position `t` of a program. -/
def progGate : {k : ℕ} → Program n k → (t : Fin k) → Gate (n + 1 + (t : ℕ))
  | 0, .nil, t => t.elim0
  | _ + 1, .step p g, t =>
      Fin.lastCases (motive := fun t => Gate (n + 1 + (t : ℕ))) g (fun i => progGate p i) t

lemma eval_castSucc {k : ℕ} (p : Program n k) (g : Gate (n + 1 + k)) (x : Fin n → ℂ)
    (u : Fin (n + 1 + k)) : (Program.step p g).eval x (Fin.castSucc u) = p.eval x u := by
  simp [Program.eval]

lemma eval_last {k : ℕ} (p : Program n k) (g : Gate (n + 1 + k)) (x : Fin n → ℂ) :
    (Program.step p g).eval x (Fin.last (n + 1 + k)) = g.eval (p.eval x) := by
  simp [Program.eval]

lemma eval_gate : ∀ {k : ℕ} (p : Program n k) (x : Fin n → ℂ) (t : Fin k),
    p.eval x ⟨n + 1 + t, by have := t.isLt; omega⟩ =
      (progGate p t).eval (fun u => p.eval x (Fin.castLE (by have := t.isLt; omega) u))
  | 0, .nil, _, t => t.elim0
  | k + 1, .step p g, x, t => by
    induction t using Fin.lastCases with
    | last =>
      have h1 : (⟨n + 1 + (Fin.last k : ℕ), by nomega⟩ : Fin (n + 1 + (k + 1))) =
          Fin.last (n + 1 + k) := Fin.ext rfl
      rw [h1, eval_last]
      simp only [progGate, Fin.lastCases_last]
      congr 1
      funext u
      have h2 : (Fin.castLE (by omega) u : Fin (n + 1 + (k + 1))) = Fin.castSucc u := Fin.ext rfl
      rw [h2, eval_castSucc]
    | cast i =>
      have h1 : (⟨n + 1 + (Fin.castSucc i : ℕ), by have := i.isLt; nomega⟩ :
          Fin (n + 1 + (k + 1))) = Fin.castSucc ⟨n + 1 + i, by have := i.isLt; nomega⟩ :=
        Fin.ext rfl
      rw [h1, eval_castSucc, eval_gate p x i]
      simp only [progGate, Fin.lastCases_castSucc]
      congr 1
      funext u
      have h2 : (Fin.castLE (by have := i.isLt; nomega) u : Fin (n + 1 + (k + 1))) =
          Fin.castSucc (Fin.castLE (by have := i.isLt; nomega) u) := Fin.ext rfl
      rw [h2, eval_castSucc]

lemma eval_input : ∀ {k : ℕ} (p : Program n k) (x : Fin n → ℂ) (v : ℕ) (h : v < n),
    p.eval x ⟨v, by omega⟩ = x ⟨v, h⟩
  | 0, .nil, x, v, h => by
    have : (⟨v, by omega⟩ : Fin (n + 1 + 0)) = Fin.castSucc ⟨v, h⟩ := Fin.ext rfl
    rw [this]
    exact Fin.snoc_castSucc (α := fun _ => ℂ) _ _ _
  | k + 1, .step p g, x, v, h => by
    have : (⟨v, by nomega⟩ : Fin (n + 1 + (k + 1))) = Fin.castSucc ⟨v, by nomega⟩ := Fin.ext rfl
    rw [this, eval_castSucc, eval_input p x v h]

lemma eval_zero : ∀ {k : ℕ} (p : Program n k) (x : Fin n → ℂ), p.eval x ⟨n, by omega⟩ = 0
  | 0, .nil, x => by
    have : (⟨n, by omega⟩ : Fin (n + 1 + 0)) = Fin.last n := Fin.ext rfl
    rw [this]
    exact Fin.snoc_last (α := fun _ => ℂ) _ _
  | k + 1, .step p g, x => by
    have : (⟨n, by nomega⟩ : Fin (n + 1 + (k + 1))) = Fin.castSucc ⟨n, by nomega⟩ := Fin.ext rfl
    rw [this, eval_castSucc, eval_zero p x]

/-- Operand list of a gate, with the coefficient of a scale gate supplied by `c₀`. -/
def gateOps {R : Type*} [CommRing R] {w N : ℕ} (h : w ≤ N) (c₀ : R) : Gate w → List (Fin N × R)
  | .add i j => [(Fin.castLE h i, 1), (Fin.castLE h j, 1)]
  | .sub i j => [(Fin.castLE h i, 1), (Fin.castLE h j, -1)]
  | .scale _ i => [(Fin.castLE h i, c₀)]

lemma gateOps_length_le {R : Type*} [CommRing R] {w N : ℕ} (h : w ≤ N) (c₀ : R) (g : Gate w) :
    (gateOps h c₀ g).length ≤ 2 := by
  cases g <;> simp [gateOps]

lemma gateOps_lt {R : Type*} [CommRing R] {w N : ℕ} (h : w ≤ N) (c₀ : R) (g : Gate w) :
    ∀ p ∈ gateOps h c₀ g, (p.1 : ℕ) < w := by
  cases g <;> simp [gateOps]

/-- The coefficient of gate `t` (zero for additions and subtractions). -/
def gateCoef {w : ℕ} : Gate w → ℂ
  | .scale c _ => c
  | _ => 0

/-- A circuit as a linear DAG; the coefficient of the scale gate at position `t` is `cf t`. -/
def toLDag {R : Type*} [CommRing R] (C : Circuit n) (cf : Fin C.size → R) :
    LDag R n (n + 1 + C.size) where
  hn := by omega
  ops v :=
    if h : n + 1 ≤ (v : ℕ) then
      gateOps (w := n + 1 + ((⟨v - (n + 1), by have := v.isLt; omega⟩ : Fin C.size) : ℕ))
        (by have := v.isLt; simp only [Fin.val_mk]; omega)
        (cf ⟨v - (n + 1), by have := v.isLt; omega⟩)
        (progGate C.program ⟨v - (n + 1), by have := v.isLt; omega⟩)
    else []
  ops_lt v p hp := by
    split_ifs at hp with h
    · have := gateOps_lt _ _ _ p hp
      show (p.1 : ℕ) < v
      simp at this
      omega
    · simp at hp
  ops_input v hv := by
    rw [dif_neg (by omega)]
  ops_len v := by
    split_ifs
    · exact gateOps_length_le _ _ _
    · simp
  out := C.outputs

lemma gateOps_map {R S : Type*} [CommRing R] [CommRing S] {w N : ℕ} (h : w ≤ N) (c₀ : R)
    (f : R →+* S) (g : Gate w) :
    (gateOps h c₀ g).map (fun p => (p.1, f p.2)) = gateOps h (f c₀) g := by
  cases g <;> simp [gateOps]

lemma toLDag_map {R S : Type*} [CommRing R] [CommRing S] (C : Circuit n) (cf : Fin C.size → R)
    (f : R →+* S) : (toLDag C cf).map f = toLDag C (fun t => f (cf t)) := by
  simp only [LDag.map, toLDag]
  congr 1
  funext v
  split_ifs
  · exact gateOps_map _ _ _ _
  · rfl

/-- The complex DAG of a circuit computes the same values. -/
lemma toLDag_val (C : Circuit n) (x : Fin n → ℂ) (v : Fin (n + 1 + C.size)) :
    (toLDag C (fun t => gateCoef (progGate C.program t))).val x v = C.program.eval x v := by
  suffices H : ∀ m, ∀ v : Fin (n + 1 + C.size), (v : ℕ) = m →
      (toLDag C (fun t => gateCoef (progGate C.program t))).val x v = C.program.eval x v
    from H _ v rfl
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro v hm
  set D := toLDag C (fun t => gateCoef (progGate C.program t))
  have hvlt := v.isLt
  by_cases h : (v : ℕ) < n
  · rw [LDag.val_input D x v h]
    exact (eval_input C.program x v h).symm
  · rw [LDag.val_gate D x v h]
    by_cases h' : n + 1 ≤ (v : ℕ)
    · set t : Fin C.size := ⟨v - (n + 1), by omega⟩ with ht_def
      have htv : (t : ℕ) = v - (n + 1) := rfl
      have hv : v = ⟨n + 1 + t, by omega⟩ := Fin.ext (by simp only [Fin.val_mk]; omega)
      have hops : D.ops v = gateOps (w := n + 1 + (t : ℕ)) (by omega)
          (gateCoef (progGate C.program t)) (progGate C.program t) := by
        show (toLDag C _).ops v = _
        simp only [toLDag, dif_pos h']
        rfl
      rw [hops]
      conv_rhs => rw [hv, eval_gate C.program x t]
      have hval : ∀ u : Fin (n + 1 + (t : ℕ)),
          D.val x (Fin.castLE (by omega) u) = C.program.eval x (Fin.castLE (by omega) u) := by
        intro u
        have hlt : ((Fin.castLE (by omega) u : Fin (n + 1 + C.size)) : ℕ) < m := by
          rw [Fin.coe_castLE, ← hm]
          have hu := u.isLt
          omega
        exact ih _ hlt _ rfl
      generalize progGate C.program t = g at hval ⊢
      cases g <;> simp [gateOps, gateCoef, Gate.eval, hval, sub_eq_add_neg]
    · have hvn : (v : ℕ) = n := by omega
      have hops : D.ops v = [] := by
        show (toLDag C _).ops v = _
        simp only [toLDag, dif_neg h']
      rw [hops]
      have : v = ⟨n, by omega⟩ := Fin.ext hvn
      rw [this, eval_zero]
      simp

/-! ### Roots of unity -/

lemma two_pi_I_ne_zero : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
  simp [Real.pi_ne_zero, Complex.I_ne_zero]

lemma zeta_pow (n a : ℕ) : zeta n ^ a = Complex.exp (a * (2 * Real.pi * Complex.I / n)) := by
  rw [zeta, ← Complex.exp_nat_mul]

/-- `ζₙ^a = 1 ↔ n ∣ a`. -/
lemma zeta_pow_eq_one_iff {n : ℕ} (hn : n ≠ 0) (a : ℕ) : zeta n ^ a = 1 ↔ n ∣ a := by
  rw [zeta_pow, Complex.exp_eq_one_iff]
  have hn' : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  constructor
  · rintro ⟨k, hk⟩
    have h1 : ((a : ℂ) / n) * (2 * Real.pi * Complex.I) = (k : ℂ) * (2 * Real.pi * Complex.I) := by
      rw [← hk]; ring
    have h2 := mul_right_cancel₀ two_pi_I_ne_zero h1
    rw [div_eq_iff hn'] at h2
    have h3 : (a : ℤ) = k * n := by exact_mod_cast h2
    exact Int.natCast_dvd_natCast.mp ⟨k, by rw [h3]; ring⟩
  · rintro ⟨q, rfl⟩
    refine ⟨q, ?_⟩
    push_cast
    field_simp

lemma zeta_ne_zero (n : ℕ) : zeta n ≠ 0 := Complex.exp_ne_zero _

lemma zeta_pow_inj {n : ℕ} (hn : n ≠ 0) {a b : ℕ} (ha : a < n) (hb : b < n)
    (h : zeta n ^ a = zeta n ^ b) : a = b := by
  rcases le_total a b with hab | hab
  · obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le hab
    rw [pow_add] at h
    have hc : zeta n ^ c = 1 := by
      have h0 : zeta n ^ a ≠ 0 := pow_ne_zero _ (zeta_ne_zero n)
      exact (mul_eq_left₀ h0).mp h.symm
    obtain ⟨q, hq⟩ := (zeta_pow_eq_one_iff hn c).mp hc
    rcases q with _ | q
    · simp at hq; omega
    · have : n ≤ c := by rw [hq]; exact Nat.le_mul_of_pos_right n (Nat.succ_pos q)
      omega
  · obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le hab
    rw [pow_add] at h
    have hc : zeta n ^ c = 1 := by
      have h0 : zeta n ^ b ≠ 0 := pow_ne_zero _ (zeta_ne_zero n)
      exact (mul_eq_left₀ h0).mp h
    obtain ⟨q, hq⟩ := (zeta_pow_eq_one_iff hn c).mp hc
    rcases q with _ | q
    · simp at hq; omega
    · have : n ≤ c := by rw [hq]; exact Nat.le_mul_of_pos_right n (Nat.succ_pos q)
      omega


/-- The output index receiving message `j` under shift `s` is `τ (j + s)`, `τ t = -t`. -/
def tau [NeZero n] (t : Fin n) : Fin n :=
  ⟨(n - t) % n, Nat.mod_lt _ (Nat.pos_of_ne_zero (NeZero.ne n))⟩

lemma tau_injective [NeZero n] : Function.Injective (tau (n := n)) := by
  intro a b h
  simp only [tau, Fin.mk.injEq] at h
  have hn := Nat.pos_of_ne_zero (NeZero.ne n)
  have ha := a.2; have hb := b.2
  apply Fin.ext
  rcases Nat.eq_zero_or_pos (a : ℕ) with h0 | h0 <;>
    rcases Nat.eq_zero_or_pos (b : ℕ) with h1 | h1
  · omega
  · rw [h0, Nat.sub_zero, Nat.mod_self, Nat.mod_eq_of_lt (by omega)] at h; omega
  · rw [h1, Nat.sub_zero, Nat.mod_self, Nat.mod_eq_of_lt (by omega)] at h; omega
  · rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at h; omega

lemma cast_tau_add [NeZero n] (j s : Fin n) :
    (((tau (j + s) : Fin n) : ℕ) : ZMod n) = -((j : ℕ) : ZMod n) - ((s : ℕ) : ZMod n) := by
  have hn := Nat.pos_of_ne_zero (NeZero.ne n)
  have hle : ((j : ℕ) + s) % n ≤ n := (Nat.mod_lt _ hn).le
  have e1 : ((tau (j + s) : Fin n) : ℕ) = (n - ((j : ℕ) + s) % n) % n := rfl
  rw [e1, ZMod.natCast_mod, Nat.cast_sub hle, ZMod.natCast_self, ZMod.natCast_mod]
  push_cast
  ring

lemma cyclic_identity [NeZero n] (j s m : Fin n) :
    ∑ l : Fin n, zeta n ^ ((tau (j + s) : ℕ) * l) * ((n : ℂ)⁻¹ * zeta n ^ ((l : ℕ) * s)) *
        zeta n ^ ((l : ℕ) * m) = if m = j then 1 else 0 := by
  have hn0 : n ≠ 0 := NeZero.ne n
  set a : ℕ := (tau (j + s) : ℕ) + s + m
  have hterm : ∀ l : Fin n, zeta n ^ ((tau (j + s) : ℕ) * l) * ((n : ℂ)⁻¹ * zeta n ^ ((l : ℕ) * s)) *
      zeta n ^ ((l : ℕ) * m) = (n : ℂ)⁻¹ * (zeta n ^ a) ^ (l : ℕ) := by
    intro l
    rw [← pow_mul, show a * (l : ℕ) = (tau (j + s) : ℕ) * l + l * s + l * m by simp only [a]; ring,
      pow_add, pow_add]
    ring
  simp only [hterm]
  rw [← Finset.mul_sum, Fin.sum_univ_eq_sum_range (fun l => (zeta n ^ a) ^ l)]
  have hdvd : n ∣ a ↔ m = j := by
    rw [← ZMod.natCast_eq_zero_iff]
    simp only [a]
    push_cast
    rw [cast_tau_add]
    constructor
    · intro h
      have : ((m : ℕ) : ZMod n) = ((j : ℕ) : ZMod n) := by linear_combination h
      rw [ZMod.natCast_eq_natCast_iff'] at this
      exact Fin.ext (by rwa [Nat.mod_eq_of_lt m.2, Nat.mod_eq_of_lt j.2] at this)
    · rintro rfl; ring
  split_ifs with hmj
  · have : zeta n ^ a = 1 := (zeta_pow_eq_one_iff hn0 a).mpr (hdvd.mpr hmj)
    simp [this, hn0]
  · have hne : zeta n ^ a ≠ 1 := fun h => hmj (hdvd.mp ((zeta_pow_eq_one_iff hn0 a).mp h))
    have hpow : (zeta n ^ a) ^ n = 1 := by
      rw [← pow_mul, mul_comm, pow_mul, (zeta_pow_eq_one_iff hn0 n).mpr dvd_rfl, one_pow]
    rw [geom_sum_eq hne, hpow, sub_self, zero_div, mul_zero]

lemma outputs_injective [NeZero n] (hn : 2 ≤ n) (C : Circuit n)
    (hC : C.Computes (fourierMatrix n)) : Function.Injective C.outputs := by
  intro a b h
  have key : ∀ i, C.eval (Pi.single ⟨1, by omega⟩ 1) i = zeta n ^ (i : ℕ) := by
    intro i
    rw [hC]
    simp [Matrix.mulVec, dotProduct, fourierMatrix, Pi.single_apply]
  have := key a
  rw [Circuit.eval, h, ← Circuit.eval, key b] at this
  exact Fin.ext (zeta_pow_inj (NeZero.ne n) b.2 a.2 this).symm

/-! ### Specialisation to a finite field -/

/-- Everything the main argument needs about a Fourier circuit, over a finite field. -/
structure ShiftData (n : ℕ) [NeZero n] where
  K : Type
  [field : Field K]
  [finite : Finite K]
  size : ℕ
  D : LDag K n (n + 1 + size)
  len_sum : ∑ v, (D.ops v).length ≤ 2 * size
  out_inj : Function.Injective D.out
  M : Fin n → Fin n → K
  computes : D.Computes M
  d : Fin n → Fin n → K
  inv : ∀ s j m, ∑ l, M (tau (j + s)) l * d s l * M l m = if m = j then 1 else 0

attribute [instance] ShiftData.field ShiftData.finite

lemma len_sum_toLDag {R : Type*} [CommRing R] (C : Circuit n) (cf : Fin C.size → R) :
    ∑ v, ((toLDag C cf).ops v).length ≤ 2 * C.size := by
  have h : ∀ v : Fin (n + 1 + C.size), ((toLDag C cf).ops v).length ≤
      if n + 1 ≤ (v : ℕ) then 2 else 0 := by
    intro v
    simp only [toLDag]
    split_ifs with h
    · exact gateOps_length_le _ _ _
    · simp
  calc ∑ v, ((toLDag C cf).ops v).length
      ≤ ∑ v : Fin (n + 1 + C.size), (if n + 1 ≤ (v : ℕ) then 2 else 0) := Finset.sum_le_sum fun v _ => h v
    _ = ∑ i : Fin (n + 1), (if n + 1 ≤ ((Fin.castAdd C.size i : Fin _) : ℕ) then 2 else 0) +
          ∑ t : Fin C.size, (if n + 1 ≤ ((Fin.natAdd (n + 1) t : Fin _) : ℕ) then 2 else 0) :=
        Fin.sum_univ_add _
    _ = 2 * C.size := by
        have h1 : ∀ i : Fin (n + 1), ¬ n + 1 ≤ ((Fin.castAdd C.size i : Fin _) : ℕ) := by
          intro i; have := i.isLt; simp only [Fin.coe_castAdd]; omega
        have h2 : ∀ t : Fin C.size, n + 1 ≤ ((Fin.natAdd (n + 1) t : Fin _) : ℕ) := by
          intro t; simp only [Fin.coe_natAdd]; omega
        rw [Finset.sum_eq_zero fun i _ => if_neg (h1 i), zero_add,
          Finset.sum_congr rfl fun t _ => if_pos (h2 t), Finset.sum_const, Finset.card_univ,
          Fintype.card_fin, smul_eq_mul, mul_comm]

/-- Variables for the symbolic circuit: one per gate, plus `ζ` and `1/n`. -/
abbrev SymVars (C : Circuit n) : Type := Fin C.size ⊕ Fin 2

/-- The evaluation of the symbolic variables at the actual complex coefficients. -/
noncomputable def symHom (C : Circuit n) : MvPolynomial (SymVars C) ℤ →+* ℂ :=
  MvPolynomial.eval₂Hom (Int.castRingHom ℂ)
    (Sum.elim (fun t => gateCoef (progGate C.program t)) ![zeta n, (n : ℂ)⁻¹])

lemma symHom_inl (C : Circuit n) (t : Fin C.size) :
    symHom C (MvPolynomial.X (Sum.inl t)) = gateCoef (progGate C.program t) := by
  rw [symHom, MvPolynomial.eval₂Hom_X']; rfl

lemma symHom_zeta (C : Circuit n) : symHom C (MvPolynomial.X (Sum.inr 0)) = zeta n := by
  rw [symHom, MvPolynomial.eval₂Hom_X']; rfl

lemma symHom_inv (C : Circuit n) : symHom C (MvPolynomial.X (Sum.inr 1)) = (n : ℂ)⁻¹ := by
  rw [symHom, MvPolynomial.eval₂Hom_X']; rfl

theorem shiftData_of_circuit [NeZero n] (hn : 2 ≤ n) (C : Circuit n)
    (hC : C.Computes (fourierMatrix n)) :
    ∃ S : ShiftData n, S.size = C.size := by
  classical
  -- symbolic coefficients: one variable per gate, plus `ζ` and `1/n`
  let DS : LDag (MvPolynomial (SymVars C) ℤ) n (n + 1 + C.size) :=
    toLDag C (fun t => MvPolynomial.X (Sum.inl t))
  let φ := symHom C
  have hDφ : DS.map φ = toLDag C (fun t => gateCoef (progGate C.program t)) := by
    rw [toLDag_map]
    congr 1
    funext t
    exact symHom_inl C t
  -- symbolic matrix entries
  let E : Fin n → Fin n → MvPolynomial (SymVars C) ℤ := fun i l => DS.val (Pi.single l 1) (C.outputs i)
  have hsingle : ∀ {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (l : Fin n),
      (fun i => f ((Pi.single l (1 : R) : Fin n → R) i)) = Pi.single l 1 := by
    intro R S _ _ f l
    funext i
    by_cases h : i = l
    · subst h; simp
    · simp [Pi.single_apply, h]
  have hE : ∀ i l, φ (E i l) = zeta n ^ ((i : ℕ) * l) := by
    intro i l
    simp only [E]
    rw [← LDag.val_map, hsingle, hDφ, toLDag_val]
    have h2 := congrFun (hC (Pi.single l 1)) i
    simp only [Circuit.eval] at h2
    rw [h2]
    simp [Matrix.mulVec, dotProduct, fourierMatrix, Pi.single_apply]
  -- specialise
  obtain ⟨K, _, _, ψ, hψ⟩ := exists_finite_field φ
  let ω : K := ψ (MvPolynomial.X (Sum.inr 0))
  let ν : K := ψ (MvPolynomial.X (Sum.inr 1))
  refine ⟨{
    K := K
    size := C.size
    D := DS.map ψ
    len_sum := by
      have := len_sum_toLDag C (fun t => (MvPolynomial.X (Sum.inl t) : MvPolynomial (SymVars C) ℤ))
      simpa [LDag.map_ops] using this
    out_inj := outputs_injective hn C hC
    M := fun i l => ψ (E i l)
    computes := by
      refine LDag.computes_of_basis _ _ fun i l => ?_
      rw [← hsingle ψ l, LDag.val_map]
      rfl
    d := fun s l => ν * ω ^ ((l : ℕ) * s)
    inv := by
      intro s j m
      let P : MvPolynomial (SymVars C) ℤ := ∑ l, E (tau (j + s)) l *
          (MvPolynomial.X (Sum.inr 1) * MvPolynomial.X (Sum.inr 0) ^ ((l : ℕ) * s)) * E l m -
        (if m = j then 1 else 0)
      have hX0 : φ (MvPolynomial.X (Sum.inr 0)) = zeta n := symHom_zeta C
      have hX1 : φ (MvPolynomial.X (Sum.inr 1)) = (n : ℂ)⁻¹ := symHom_inv C
      have hsum : φ (∑ l, E (tau (j + s)) l *
          (MvPolynomial.X (Sum.inr 1) * MvPolynomial.X (Sum.inr 0) ^ ((l : ℕ) * s)) * E l m) =
          if m = j then 1 else 0 := by
        simp only [map_sum, map_mul, map_pow, hE, hX0, hX1]
        exact cyclic_identity j s m
      have hP : φ P = 0 := by
        simp only [P, map_sub, hsum]
        split_ifs <;> simp
      have := hψ P hP
      simp only [P, map_sub, map_sum, map_mul, map_pow] at this
      rw [sub_eq_zero] at this
      convert this using 1
      split_ifs <;> simp }, rfl⟩

end NccCert
