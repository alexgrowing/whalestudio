import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HasDerivAtOfContinuousHom
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WirtingerCombinationNeZero

namespace PositivityTheory.Rg.Cz

theorem hasDerivAt_of_mulHom (χ : ℝ → ℂ) (hc : Continuous χ) (h0 : χ 0 = 1) (hm : ∀ s t, χ (s + t) = χ s * χ t) :
    ∃ c : ℂ, ∀ t, HasDerivAt χ (c * χ t) t :=
  GlobalTheory.CompanionTheory.CharDeriv.hasDerivAt_of_continuous_hom χ hc h0 hm

theorem wirtinger_ne_zero (χ : ℂ → ℂ) (hc : Continuous χ) (hm : ∀ z w, χ (z + w) = χ z * χ w) (hn : ∀ z, ‖χ z‖ = 1)
    (ht : ∃ z, χ z ≠ 1) (D : ℂ → ℂ) (hD : ∀ z, HasDerivAt (fun t : ℝ => χ (t * z)) (D z) 0) (β : ℂ) (hβ : β ≠ 0) :
    D β - Complex.I * D (β * Complex.I) ≠ 0 :=
  GlobalTheory.CompanionTheory.Unitary.wirtinger_combination_ne_zero χ hc hm hn ht D hD β hβ

end PositivityTheory.Rg.Cz
