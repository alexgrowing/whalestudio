import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.KFiniteThetaLifts.RationalPrimesBelowPlaces
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.SquareIntegrable.SSmooth
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TemperedBoundGL2
import GroundTheory.LocalFields.QuadraticAbelian.WeilRepQuadratic
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSmoothCharCompNorm
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WcEqZero
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeilWhittakerBoundQuadraticExtensionStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeilWhittakerSupportQuadraticExtensionStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeilCharacterTwistNontrivialGaloisStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeilWhittakerGaloisConjugateStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeilWhittakerNontrivialGaloisIntegralStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompactTranslateEntriesBoundedStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsOpenNormImageUnitsStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NormImageNeighbourhoodEventuallyStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeilWhittakerContinuityQuadraticExtensionStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeilWhittakerMeasureIndependenceStatement
open NumberField IsDedekindDomain MeasureTheory GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Global.AdicLiesOver
open scoped ValuativeRel
open GlobalTheory.CompanionTheory.DualHol
open GlobalTheory.CompanionTheory.WcB
open scoped Topology

namespace GlobalTheory.CompanionTheory.WcB.Decay

theorem gaussI_decay : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (E : Type) [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] [MeasurableSpace E] [BorelSpace E] [Algebra F E] [ValuativeExtension F E] [FiniteDimensional F E] [Algebra.IsSeparable F E] [Fact (Module.finrank F E = 2)] (χ : AddChar F Circle), Continuous χ → χ ≠ 1 → ∀ σ : E ≃ₐ[F] E, σ ≠ AlgEquiv.refl → ∀ (μ : Measure E) [μ.IsAddHaarMeasure] (Φ : E → ℂ), IsLocallyConstant Φ → HasCompactSupport Φ → ∃ C : ℝ, ∀ (κ : F) (ξ : E), ‖gaussI χ μ Φ κ ξ‖ * max 1 (modulus κ : ℝ) ≤ C := by
  intro F _ _ _ _ _ _ E _ _ _ _ _ _ _ _ _ _ _ χ hχ hχ1 σ hσ μ _ Φ hΦ hΦc
  obtain ⟨C₁, hC₁, hlat⟩ := GlobalTheory.T.weil_whittaker_support_quadratic_extension F E χ hχ hχ1 Φ hΦ hΦc
  obtain ⟨C₂, hC₂, hvol⟩ := GlobalTheory.T.weil_character_twist_nontrivial_galois F E σ hσ μ
  obtain ⟨B, hB⟩ := hΦ.continuous.bounded_above_of_compact_support hΦc
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  have hnorm : ∀ (κ : F) (ξ u : E), ‖(χ (κ * Algebra.norm F u - Algebra.trace F E (ξ * u)) : ℂ) * Φ u‖ = ‖Φ u‖ := by
    intro κ ξ u
    rw [norm_mul, Circle.norm_coe, one_mul]
  have hA : ∀ (κ : F) (ξ : E), ‖gaussI χ μ Φ κ ξ‖ ≤ ∫ u, ‖Φ u‖ ∂μ := by
    intro κ ξ
    unfold gaussI
    refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
    exact integral_congr_ae (Filter.Eventually.of_forall fun u => hnorm κ ξ u)
  refine ⟨max (∫ u, ‖Φ u‖ ∂μ) (B * (C₂ * C₁)), fun κ ξ => ?_⟩
  rcases le_or_gt (modulus κ : ℝ) 1 with h1 | h1
  · rw [max_eq_left h1, mul_one]
    exact (hA κ ξ).trans (le_max_left _ _)
  · rw [max_eq_right h1.le]
    have hκ : κ ≠ 0 := by
      rintro rfl
      have h0 : (modulus (0 : F) : ℝ) = 0 := by simp
      linarith
    have hpos : (0 : ℝ) < modulus κ := by linarith
    obtain ⟨M, hMc, hMo, hMΦ, hMχ, hMx⟩ := hlat κ
    have hI := GlobalTheory.T.weil_whittaker_bound_quadratic_extension F E χ hχ σ hσ μ Φ hΦ hΦc κ ξ M hMc hMo hMΦ hMχ
    set S : Set E := {u : E | ∀ r ∈ M, χ (Algebra.trace F E ((algebraMap F E κ * σ u - ξ) * r)) = 1} with hS
    set T : Set E := {u : E | (modulus (algebraMap F E κ * σ u - ξ) : ℝ) ≤ C₁ * (modulus κ : ℝ)} with hT
    have hST : S ⊆ T := by
      intro u hu
      have := hMx _ hu
      rwa [max_eq_right h1.le] at this
    have hR : 0 < C₁ * (modulus κ : ℝ) := mul_pos hC₁ hpos
    have hμT : μ T ≤ ENNReal.ofReal (C₂ * (C₁ * (modulus κ : ℝ)) / (modulus κ : ℝ) ^ 2) := hvol κ hκ ξ _ hR
    have hμS : μ S ≤ ENNReal.ofReal (C₂ * (C₁ * (modulus κ : ℝ)) / (modulus κ : ℝ) ^ 2) :=
      (measure_mono hST).trans hμT
    have hfin : μ S < ⊤ := hμS.trans_lt ENNReal.ofReal_lt_top
    have hreal : μ.real S ≤ C₂ * (C₁ * (modulus κ : ℝ)) / (modulus κ : ℝ) ^ 2 :=
      ENNReal.toReal_le_of_le_ofReal (by positivity) hμS
    have hbound : ‖gaussI χ μ Φ κ ξ‖ ≤ B * μ.real S := by
      rw [hI]
      refine norm_setIntegral_le_of_norm_le_const hfin fun u _ => ?_
      rw [hnorm]
      exact hB u
    calc ‖gaussI χ μ Φ κ ξ‖ * (modulus κ : ℝ)
        ≤ (B * (C₂ * (C₁ * (modulus κ : ℝ)) / (modulus κ : ℝ) ^ 2)) * (modulus κ : ℝ) := by
          refine mul_le_mul_of_nonneg_right (hbound.trans ?_) hpos.le
          exact mul_le_mul_of_nonneg_left hreal hB0
      _ = B * (C₂ * C₁) := by
          field_simp
      _ ≤ _ := le_max_right _ _
end GlobalTheory.CompanionTheory.WcB.Decay
