import Mathlib.RingTheory.Jacobson.Ring
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.RingTheory.FiniteType
import Mathlib.Algebra.Algebra.ZMod
import Mathlib.RingTheory.Finiteness.Cardinality
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Mathlib.Algebra.Ring.Int.Field
import Mathlib.Algebra.CharP.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic.Linarith

/-!
# Specialising complex identities to a finite field

If finitely many integer polynomial identities have a solution over `ℂ`, they have a solution in a
finite field. Concretely: for every ring homomorphism `φ : ℤ[X_i]_{i ∈ ι} → ℂ` (with `ι` finite)
there is a finite field `F` and a ring homomorphism `ψ : ℤ[X_i] → F` killing `ker φ`.
This is the arithmetic Nullstellensatz: `ℤ` is a Jacobson ring, so residue fields of finitely
generated `ℤ`-algebras at maximal ideals are finite.
-/

namespace NccCert

open Ideal

/-- `ℤ` is a Jacobson ring. -/
instance : IsJacobsonRing ℤ := by
  rw [isJacobsonRing_iff_prime_eq]
  intro P hP
  by_cases h : P = ⊥
  · subst h
    refine le_antisymm (fun x hx => ?_) Ideal.le_jacobson
    rw [Ideal.mem_jacobson_bot] at hx
    have h1 := hx 1
    have h2 := hx (-1)
    rw [Int.isUnit_iff] at h1 h2
    rw [Ideal.mem_bot]
    omega
  · haveI : P.IsMaximal := IsPrime.to_maximal_ideal h
    exact Ideal.jacobson_eq_self_of_isMaximal

/-- A field that is a finitely generated `ℤ`-module is finite. -/
lemma finite_of_moduleFinite_int (F : Type*) [Field F] [Module.Finite ℤ F] : Finite F := by
  by_cases hc : ringChar F = 0
  · exfalso
    haveI : CharZero F := (CharP.ringChar_zero_iff_CharZero (R := F)).mp hc
    have hinj : Function.Injective (algebraMap ℤ F) := (algebraMap ℤ F).injective_int
    haveI : Algebra.IsIntegral ℤ F := Algebra.IsIntegral.of_finite ℤ F
    exact Int.not_isField (isField_of_isIntegral_of_isField hinj (Field.toIsField F))
  · haveI : NeZero (ringChar F) := ⟨hc⟩
    haveI : CharP F (ringChar F) := ringChar.charP F
    letI : Algebra (ZMod (ringChar F)) F := ZMod.algebra F (ringChar F)
    haveI : Module.Finite (ZMod (ringChar F)) F :=
      Module.Finite.of_restrictScalars_finite ℤ (ZMod (ringChar F)) F
    exact Module.finite_of_finite (ZMod (ringChar F))

/-- **Specialisation.** -/
theorem exists_finite_field {ι : Type} [Finite ι] (φ : MvPolynomial ι ℤ →+* ℂ) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (ψ : MvPolynomial ι ℤ →+* F),
      ∀ p, φ p = 0 → ψ p = 0 := by
  obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ (RingHom.ker_ne_top φ)
  letI : Field (MvPolynomial ι ℤ ⧸ M) := Ideal.Quotient.field M
  haveI : Algebra.FiniteType ℤ (MvPolynomial ι ℤ ⧸ M) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ ℤ M) (Ideal.Quotient.mkₐ_surjective ℤ M)
  haveI : Module.Finite ℤ (MvPolynomial ι ℤ ⧸ M) :=
    finite_of_finite_type_of_isJacobsonRing ℤ (MvPolynomial ι ℤ ⧸ M)
  refine ⟨MvPolynomial ι ℤ ⧸ M, inferInstance, finite_of_moduleFinite_int _,
    Ideal.Quotient.mk M, fun p hp => ?_⟩
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (hle (RingHom.mem_ker.mpr hp))

end NccCert
