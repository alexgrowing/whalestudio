import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgHomEqMulPowOfEqLocalizationAway
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCombIn
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_pow_mul_eq_of_algebraMap_localizationAway_eq : ∀ (R' A S : Type) [CommRing R'] [CommRing A] [CommRing S] [Algebra R' A] [Algebra R' S]
    [Algebra.FiniteType R' A] (χ₁ χ₂ : A →ₐ[R'] S) (g : S),
    (∀ x, algebraMap S (Localization.Away g) (χ₁ x) = algebraMap S (Localization.Away g) (χ₂ x)) →
    ∃ N : ℕ, ∀ x, g ^ N * χ₁ x = g ^ N * χ₂ x := by
  first | exact @GlobalTheory.algHom_eq_mul_pow_of_eq_localizationAway | exact GlobalTheory.algHom_eq_mul_pow_of_eq_localizationAway | (intros; apply GlobalTheory.algHom_eq_mul_pow_of_eq_localizationAway <;> assumption)
