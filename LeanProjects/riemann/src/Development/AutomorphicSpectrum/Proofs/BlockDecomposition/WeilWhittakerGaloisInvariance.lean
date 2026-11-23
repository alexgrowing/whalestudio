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
open scoped NNReal

namespace GlobalTheory.CompanionTheory.WcB

theorem value_lower_ne : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (E : Type) [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] [MeasurableSpace E] [BorelSpace E] [Algebra F E] [ValuativeExtension F E] [FiniteDimensional F E] [Algebra.IsSeparable F E] [Fact (Module.finrank F E = 2)] (χ : AddChar F Circle) (σ : E ≃ₐ[F] E), σ ≠ AlgEquiv.refl → ∀ (μ : Measure E) [μ.IsAddHaarMeasure] (lam : ℂ) (c : Eˣ →* ℂˣ), IsUnit1 c → ∀ (Φ : E → ℂ) (g : GL (Fin 2) F), g.val 1 0 ≠ 0 → GL2LocalData.Wc χ σ μ lam c Φ g ≠ 0 → ∃ t : Eˣ, Algebra.norm F (t : E) = (g.val).det ∧ ‖GL2LocalData.Wc χ σ μ lam c Φ g‖ = ‖lam‖ * (modulus (g.val).det : ℝ) ^ (1 / 2 : ℝ) * (modulus (g.val 1 0) : ℝ)⁻¹ * ‖gaussI χ μ Φ (g.val 1 1 / g.val 1 0) (algebraMap F E ((g.val).det / g.val 1 0) * (t : E)⁻¹)‖ := by
  intro F _ _ _ _ _ _ E _ _ _ _ _ _ _ _ _ _ _ χ σ hσ μ _ lam c hc Φ g h10 hW
  classical
  by_cases h : ∃ t : Eˣ, Algebra.norm F (t : E) = (g.val).det
  · refine ⟨h.choose, h.choose_spec, ?_⟩
    have hN : Algebra.norm F ((h.choose : Eˣ) : E) = (g.val).det := h.choose_spec
    have hd0 : (g.val).det ≠ 0 :=
      ((Matrix.isUnit_iff_isUnit_det _).1 g.isUnit).ne_zero
    have hcc : g.val 1 0 / (g.val).det ≠ 0 := div_ne_zero h10 hd0
    have hct : ‖((c h.choose : ℂˣ) : ℂ)‖ = 1 := hc.2 _
    have hn : ∀ a : F, ‖GL2LocalData.nsg E a‖ = 1 := by
      intro a
      unfold GL2LocalData.nsg
      split_ifs <;> simp
    have hpos : (0 : ℝ) < (modulus (g.val).det : ℝ) := by
      exact_mod_cast modulus_pos hd0
    have hpos10 : (0 : ℝ) < (modulus (g.val 1 0) : ℝ) := by
      exact_mod_cast modulus_pos h10
    have hcp : ‖(((modulus (g.val).det : ℝ) : ℂ)) ^ (1 / 2 : ℂ)‖ = (modulus (g.val).det : ℝ) ^ (1 / 2 : ℝ) := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hpos]
      norm_num
    have hm : ∀ r : ℝ≥0, ‖(((r : ℝ)⁻¹ : ℝ) : ℂ)‖ = (r : ℝ)⁻¹ := by
      intro r
      rw [Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.2 (NNReal.coe_nonneg _))]
    have hmt : (modulus ((h.choose : Eˣ) : E) : ℝ) = (modulus (g.val).det : ℝ) := by
      rw [← GroundTheory.LocalField.FiltrationCocycleLiftCriterion.WeilRep.modulus_norm (K := F) ((h.choose : Eˣ) : E), hN]
    have hmc : (modulus (g.val 1 0 / (g.val).det) : ℝ) =
        (modulus (g.val 1 0) : ℝ) * (modulus (g.val).det : ℝ)⁻¹ := by
      rw [div_eq_mul_inv, modulus_mul, modulus_inv, NNReal.coe_mul, NNReal.coe_inv]
    have k1 : g.val 1 1 / (g.val 1 0 / (g.val).det * Algebra.norm F ((h.choose : Eˣ) : E)) =
        g.val 1 1 / g.val 1 0 := by
      rw [hN, div_mul_cancel₀ _ hd0]
    have k2 : (algebraMap F E (g.val 1 0 / (g.val).det))⁻¹ =
        algebraMap F E ((g.val).det / g.val 1 0) := by
      rw [← map_inv₀, inv_div]
    rw [Wc_eq_wS χ σ μ lam c Φ g h]
    unfold wS
    rw [GlobalTheory.T.weil_whittaker_nontrivial_galois_integral F E χ σ hσ μ lam Φ _ _ _ _ hcc h.choose, k1, k2]
    simp only [norm_mul, hct, hcp, hn, hm, Circle.norm_coe, mul_one, one_mul]
    rw [hmt, hmc]
    field_simp
  · exact absurd (Wc_eq_zero χ σ μ lam c Φ g h) hW

end GlobalTheory.CompanionTheory.WcB
