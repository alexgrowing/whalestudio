import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvDer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffSubstEqZeroOfDegreeLt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffSubstRestrictSumVariables
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat GlobalTheory.LawDer

namespace GlobalTheory

theorem invDer_coeff_eq_zero_of_degree_lt :
    ∀ (R : Type) [CommRing R] (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R),
      (∀ i, constantCoeff (μ i) = 0) → ∀ (u : Fin d → R) (F : MvPowerSeries (Fin d) R) (r : ℕ),
      (∀ α : Fin d →₀ ℕ, α.degree < r + 1 → coeff α F = 0) →
      ∀ α : Fin d →₀ ℕ, α.degree < r → coeff α (invDer μ u F) = 0 := by
  intro R _ d μ hμ u F r hF α hα
  unfold invDer
  rw [map_sum]
  apply Finset.sum_eq_zero
  intro i _
  rw [map_smul]
  unfold atZero
  rw [(coeff_subst_restrict_sum (pderiv R (Sum.inr i) (subst μ F))).1 α, coeff_pderiv]
  have h := coeff_subst_eq_zero_of_degree_lt R (Fin d) (Fin d ⊕ Fin d) μ F (r + 1) hμ hF
    (α.mapDomain Sum.inl + Finsupp.single (Sum.inr i) 1) (by
      rw [map_add, Finsupp.degree_mapDomain, Finsupp.degree_single]; omega)
  rw [h, zero_mul, smul_zero]

end GlobalTheory
