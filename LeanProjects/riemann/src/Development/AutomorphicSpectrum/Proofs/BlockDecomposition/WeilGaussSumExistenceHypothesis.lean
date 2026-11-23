import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.LocalWhittakerDuality.WSteps
import GroundTheory.LocalFields.QuadraticAbelian.WeilRepQuadratic
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NormFormIntegralFourierFactorizationStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NormFormBallIntegralStabilizesStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NormFormBallIntegralScalingStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NonNormBallIntegralVanishesStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NonNormGaussIntegralSignStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NonNormWeilConstantValueStatement

open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K.GL2LocalData
open GroundTheory.LocalField.FiltrationCocycleLiftCriterion.WeilRep
open scoped ValuativeRel

noncomputable section

namespace GlobalTheory.CompanionTheory.WGaussEx

theorem wGaussEx : Ad3.K.GL2LocalData.WGaussEx := by
  intro F _ _ _ _ _ _ _ χ hχ hχ1 E _ _ _ _ _ _ _ hfr hcont σ hσ η hη
  have hcore := GlobalTheory.T.norm_form_integral_fourier_factorization F χ hχ hχ1 E hfr hcont σ hσ η hη
  have hst := GlobalTheory.T.norm_form_ball_integral_stabilizes GlobalTheory.T.norm_form_integral_fourier_factorization F χ hχ hχ1 E hfr hcont σ hσ η hη
  have hsc := GlobalTheory.T.norm_form_ball_integral_scaling F χ hχ hχ1 E hfr hcont σ hσ η hη
  have hnon := GlobalTheory.T.non_norm_weil_constant_value (GlobalTheory.T.non_norm_gauss_integral_sign GlobalTheory.T.non_norm_ball_integral_vanishes) F χ hχ hχ1 E hfr hcont σ hσ η hη
  choose c n₀ hc using hst
  refine ⟨c 1, fun a Φ hΦ => ?_⟩
  obtain ⟨n₁, h₁⟩ := hcore a Φ hΦ
  have hL := h₁ (min n₁ (n₀ a)) (min_le_left _ _)
  rw [hc a _ (min_le_right _ _)] at hL
  rw [hL]
  congr 1
  have hne : ((modulus (a : F) : ℝ) : ℂ) ≠ 0 := by
    have : (modulus (a : F) : ℝ) ≠ 0 := by
      simpa using modulus_ne_zero a.ne_zero
    exact_mod_cast this
  by_cases ha : ∃ t : Eˣ, Algebra.norm F (t : E) = a
  · obtain ⟨t, ht⟩ := ha
    have hn : nsg E (a : F) = 1 := by
      rw [nsg, if_pos ⟨t, ht⟩]
    let m := min (n₀ a) (min (n₀ 1) (n₀ 1 - ord (t : E)))
    have e := hsc t m
    have e1 : ∫ u in (valBall E m : Set E), (χ (Algebra.norm F (t : E) * Algebra.norm F u) : ℂ) ∂muE E χ = c a := by
      rw [ht]; exact hc a m (min_le_left _ _)
    have e2 : ∫ u in (valBall E (m + ord (t : E)) : Set E), (χ (Algebra.norm F u) : ℂ) ∂muE E χ = c 1 := by
      have := hc 1 (m + ord (t : E)) (by
        have : m ≤ n₀ 1 - ord (t : E) := (min_le_right _ _).trans (min_le_right _ _)
        omega)
      simpa using this
    rw [e1, e2, ht] at e
    rw [e, hn]
    push_cast
    ring
  · have hn : nsg E (a : F) = -1 := by
      rw [nsg, if_neg ha]
    obtain ⟨m₁, hm₁, m₂, hm₂, e⟩ := hnon a ha (min (n₀ 1) (n₀ a))
    have e1 : ∫ u in (valBall E m₁ : Set E), (χ (Algebra.norm F u) : ℂ) ∂muE E χ = c 1 := by
      have := hc 1 m₁ (hm₁.trans (min_le_left _ _))
      simpa using this
    rw [e1, hc a m₂ (hm₂.trans (min_le_right _ _))] at e
    rw [hn]
    push_cast
    field_simp
    linear_combination e

end GlobalTheory.CompanionTheory.WGaussEx
