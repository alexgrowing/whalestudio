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
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerBoundOnBoundedRows
open NumberField IsDedekindDomain MeasureTheory GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Global.AdicLiesOver
open scoped ValuativeRel
open GlobalTheory.CompanionTheory.DualHol
open GlobalTheory.CompanionTheory.WcB
open scoped Topology

namespace GlobalTheory.CompanionTheory.WcB.GaussSupport

theorem gauss_support : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (E : Type) [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] [MeasurableSpace E] [BorelSpace E] [Algebra F E] [ValuativeExtension F E] [FiniteDimensional F E] [Algebra.IsSeparable F E] [Fact (Module.finrank F E = 2)] (χ : AddChar F Circle), Continuous χ → χ ≠ 1 → ∀ σ : E ≃ₐ[F] E, σ ≠ AlgEquiv.refl → ∀ (μ : Measure E) [μ.IsAddHaarMeasure] (Φ : E → ℂ), IsLocallyConstant Φ → HasCompactSupport Φ → ∃ R : ℝ, ∀ (κ : F) (ξ : E), gaussI χ μ Φ κ ξ ≠ 0 → (modulus ξ : ℝ) ≤ R * max 1 ((modulus κ : ℝ) ^ 2) := by
  intro F _ _ _ _ _ _ E _ _ _ _ _ _ _ _ _ _ _ χ hχ hχ1 σ hσ μ _ Φ hΦ hc
  obtain ⟨C, hC0, hC⟩ := GlobalTheory.T.weil_whittaker_support_quadratic_extension F E χ hχ hχ1 Φ hΦ hc
  have hcont : Continuous fun u : E => (modulus u : ℝ) :=
    NNReal.continuous_coe.comp continuous_modulus
  obtain ⟨R₀, hR₀⟩ := (hc.isCompact.image hcont).bddAbove
  have hσm : ∀ u : E, modulus (σ u) = modulus u := by
    intro u
    rcases GroundTheory.LocalField.FiltrationCocycleLiftCriterion.WeilRep.eq_one_or_eq_conj (K := F) (E := E) σ with h | h
    · exact absurd h hσ
    · rw [h]; exact GroundTheory.LocalField.FiltrationCocycleLiftCriterion.WeilRep.modulus_conj (K := F) u
  refine ⟨max R₀ C, fun κ ξ hne => ?_⟩
  obtain ⟨M, hMc, hMo, hM1, hM2, hM3⟩ := hC κ
  have hI := GlobalTheory.T.weil_whittaker_bound_quadratic_extension F E χ hχ σ hσ μ Φ hΦ hc κ ξ M hMc hMo hM1 hM2
  have hex : ∃ u : E, (∀ r ∈ M, χ (Algebra.trace F E ((algebraMap F E κ * σ u - ξ) * r)) = 1) ∧
      Φ u ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    apply hne
    rw [hI]
    apply setIntegral_eq_zero_of_forall_eq_zero
    intro u hu
    rw [hcon u hu, mul_zero]
  obtain ⟨u, hu, hΦu⟩ := hex
  have b1 : (modulus u : ℝ) ≤ R₀ := hR₀ ⟨u, subset_tsupport _ hΦu, rfl⟩
  have b2 := hM3 _ hu
  have b3 : modulus (algebraMap F E κ * σ u) = modulus κ ^ 2 * modulus u := by
    rw [modulus_mul, GroundTheory.LocalField.FiltrationCocycleLiftCriterion.WeilRep.modulus_algebraMap (K := F), hσm]
  have b4 : modulus ξ ≤ max (modulus (algebraMap F E κ * σ u))
      (modulus (algebraMap F E κ * σ u - ξ)) := by
    have e : ξ = algebraMap F E κ * σ u + -(algebraMap F E κ * σ u - ξ) := by ring
    calc modulus ξ = modulus (algebraMap F E κ * σ u + -(algebraMap F E κ * σ u - ξ)) := by
          rw [← e]
      _ ≤ _ := GlobalTheory.CompanionTheory.GJTwo.WhitBound.modulus_add_le_max _ _
      _ ≤ _ := max_le_max le_rfl (GlobalTheory.CompanionTheory.GJTwo.WhitBound.modulus_neg_le _)
  have b5 : (modulus ξ : ℝ) ≤ max ((modulus κ : ℝ) ^ 2 * (modulus u : ℝ))
      (modulus (algebraMap F E κ * σ u - ξ) : ℝ) := by
    rw [b3] at b4
    exact_mod_cast b4
  have hm : (0 : ℝ) ≤ (modulus κ : ℝ) := NNReal.coe_nonneg _
  have hT : 0 < max R₀ C := lt_max_of_lt_right hC0
  have hmax : max 1 (modulus κ : ℝ) ≤ max 1 ((modulus κ : ℝ) ^ 2) := by
    rcases le_total (modulus κ : ℝ) 1 with h | h
    · exact max_le (le_max_left _ _) (h.trans (le_max_left _ _))
    · exact max_le (le_max_left _ _) (le_max_of_le_right (by nlinarith))
  refine b5.trans (max_le ?_ ?_)
  · calc (modulus κ : ℝ) ^ 2 * (modulus u : ℝ)
        ≤ max 1 ((modulus κ : ℝ) ^ 2) * max R₀ C :=
          mul_le_mul (le_max_right _ _) (b1.trans (le_max_left _ _)) (NNReal.coe_nonneg _)
            (by positivity)
      _ = _ := mul_comm _ _
  · calc _ ≤ C * max 1 (modulus κ : ℝ) := b2
      _ ≤ max R₀ C * max 1 ((modulus κ : ℝ) ^ 2) :=
          mul_le_mul (le_max_right _ _) hmax (by positivity) hT.le

end GlobalTheory.CompanionTheory.WcB.GaussSupport
