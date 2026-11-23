import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SandwichMaps
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps

namespace GlobalTheory

theorem exists_poly_aeval_eq_zero_map_separable :
    ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [CharZero C] (φ : ℤ_[p] →+* C) (Λ : Type)
      [CommRing Λ] [IsDomain Λ] [Algebra ℤ_[p] Λ] [Module.Finite ℤ_[p] Λ]
      [FaithfulSMul ℤ_[p] Λ] (a : Λ),
      ∃ f : Polynomial ℤ_[p], Polynomial.aeval a f = 0 ∧ (f.map φ).Separable := by
  intro p _ C _ _ φ Λ _ _ _ _ _ a
  have hint : IsIntegral ℤ_[p] a := Algebra.IsIntegral.isIntegral a
  refine ⟨minpoly ℤ_[p] a, minpoly.aeval _ _, ?_⟩
  have hirr : Irreducible ((minpoly ℤ_[p] a).map (algebraMap ℤ_[p] ℚ_[p])) :=
    ((minpoly.monic hint).irreducible_iff_irreducible_map_fraction_map (K := ℚ_[p])).1
      (minpoly.irreducible hint)
  have hsep := hirr.separable
  have hinj : Function.Injective φ := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    by_contra h
    have hs := PadicInt.unitCoeff_spec h
    rw [hs, map_mul, map_pow, map_natCast] at hx
    rcases mul_eq_zero.1 hx with h1 | h1
    · exact (((PadicInt.unitCoeff h).isUnit).map φ).ne_zero h1
    · exact (pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero)) h1
  let ψ : ℚ_[p] →+* C := IsFractionRing.lift (K := ℚ_[p]) hinj
  have hcomp : ψ.comp (algebraMap ℤ_[p] ℚ_[p]) = φ := by
    ext x
    exact IsFractionRing.lift_algebraMap hinj x
  have := hsep.map (f := ψ)
  rwa [Polynomial.map_map, hcomp] at this

end GlobalTheory
