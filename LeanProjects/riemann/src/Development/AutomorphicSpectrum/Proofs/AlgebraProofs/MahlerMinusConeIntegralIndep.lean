import Mathlib
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.IsSigmaCompactConeInter
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.IntegralFubiniStudySumConeStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.SphereMeanNormalizedGroupsStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.AePolynomialNonvanishingRowsStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ChowFormFibreSpecializationStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.AeFibrePointsCardEqDegreeStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.GaussianMatrixMeasurePosFiniteStatement
set_option maxSynthPendingDepth 1
open GroundTheory.Heights₂.Heights MeasureTheory MvPolynomial Matrix GlobalTheory.CompanionTheory.Ar.Short.Crofton
open scoped ENNReal

namespace GlobalTheory.CompanionTheory.Ar.Short.Crofton

theorem log_norm_sub_fsSum_eq {n e : ℕ} (h : HermNorm n) (u : Fin n → ℂ)
    (S : Set (EuclideanSpace ℂ (Fin n))) (π : Fin (e + 1) → Fin n → ℂ) (c z : ℂ)
    (hfin : (fibrePts S π).Finite) (hc : c ≠ 0)
    (hz : z = c * ∏ᶠ y ∈ fibrePts S π, ∑ j, u j * h.pointOf y j) (hz0 : z ≠ 0) :
    Real.log ‖z‖ - fsSum h u S π = Real.log ‖c‖ + ∑ y ∈ hfin.toFinset, Real.log ‖y‖ := by
  rw [finprod_mem_eq_finite_toFinset_prod _ hfin] at hz
  have hprod : ∏ y ∈ hfin.toFinset, ∑ j, u j * h.pointOf y j ≠ 0 :=
    fun h0 => hz0 (by rw [hz, h0, mul_zero])
  have hne := Finset.prod_ne_zero_iff.mp hprod
  have key : ∀ y ∈ hfin.toFinset, fsLog h u (h.pointOf y) =
      Real.log ‖∑ j, u j * h.pointOf y j‖ - Real.log ‖y‖ := by
    intro y hy
    have hy0 : y ≠ 0 := by
      rintro rfl
      apply hne _ hy
      show ∑ j, u j * (h.matᵀ *ᵥ (0 : Fin n → ℂ)) j = 0
      simp
    rw [fsLog, ConeFsLog.dualNorm_pointOf,
      Real.log_div (norm_ne_zero_iff.2 (hne y hy)) (norm_ne_zero_iff.2 hy0)]
  rw [fsSum, finsum_mem_eq_finite_toFinset_sum _ hfin, Finset.sum_congr rfl key,
    Finset.sum_sub_distrib, hz, norm_mul, norm_prod,
    Real.log_mul (norm_ne_zero_iff.2 hc)
      (Finset.prod_ne_zero_iff.mpr fun y hy => norm_ne_zero_iff.2 (hne y hy)),
    Real.log_prod (fun y hy => norm_ne_zero_iff.2 (hne y hy))]
  ring

theorem defect_eq_of_linForm_notMem : ∀ (n e δ : ℕ) (h : HermNorm n) (W : Ideal (MvPolynomial (Fin n) ℂ))
    (g : MvPolynomial (Fin (e + 1) × Fin n) ℂ) (u u' : Fin n → ℂ),
    IsProjPrime W → IsChowForm W (e + 1) g → IsMultiHomog δ g → linForm u ∉ W → linForm u' ∉ W →
      mahler h e (specFirst g u) - coneIntegral h W e (fsLog h u) =
        mahler h e (specFirst g u') - coneIntegral h W e (fsLog h u') := by
  intro n e δ h W g u u' hW hg hδ hu hu'
  have hq := SpecFirstNe.full ℂ n e W g u hW hg hu
  have hq' := SpecFirstNe.full ℂ n e W g u' hW hg hu'
  have hh := SpecFirstHomog.proof n e δ g u hδ
  have hh' := SpecFirstHomog.proof n e δ g u' hδ
  obtain ⟨hΓ0, hΓ⟩ := GlobalTheory.T.gaussian_matrix_measure_pos_finite (e + 1) n
  have hΓr : (gaussM (e + 1) n Set.univ).toReal ≠ 0 := (ENNReal.toReal_pos hΓ0.ne' hΓ.ne).ne'
  have hae : ∀ᵐ π : Fin (e + 1) → Fin n → ℂ,
      Real.log ‖eval (nrmGroups h e (coefRows h π)) (specFirst g u)‖ - fsSum h u (coneSet h W) π =
        Real.log ‖eval (nrmGroups h e (coefRows h π)) (specFirst g u')‖ -
          fsSum h u' (coneSet h W) π := by
    filter_upwards [GlobalTheory.T.ae_fibre_points_card_eq_degree n e δ h W g hW hg hδ, GlobalTheory.T.ae_polynomial_nonvanishing_rows n e δ h _ hq hh,
      GlobalTheory.T.ae_polynomial_nonvanishing_rows n e δ h _ hq' hh'] with π hcount h1 h2
    rw [EvalSpecFirst.proof] at h1 h2 ⊢
    rw [EvalSpecFirst.proof]
    obtain ⟨c, hc, hfac⟩ := GlobalTheory.T.chow_form_fibre_specialization n e δ h W g π u hW hg hδ hcount h1
    have hfin : (fibrePts (coneSet h W) π).Finite := Set.finite_of_encard_eq_coe hcount
    rw [log_norm_sub_fsSum_eq h u _ π c _ hfin hc (hfac u) h1,
      log_norm_sub_fsSum_eq h u' _ π c _ hfin hc (hfac u') h2]
  have haeG := (withDensity_absolutelyContinuous (volume : Measure (Fin (e + 1) → Fin n → ℂ))
    matGauss).ae_le hae
  obtain ⟨i1, e1⟩ := GlobalTheory.T.sphere_mean_normalized_groups n e h (fun w => Real.log ‖eval w (specFirst g u)‖)
    (MahlerIntegrand.proof n e δ h _ hq hh)
  obtain ⟨i1', e1'⟩ := GlobalTheory.T.sphere_mean_normalized_groups n e h (fun w => Real.log ‖eval w (specFirst g u')‖)
    (MahlerIntegrand.proof n e δ h _ hq' hh')
  obtain ⟨i2, e2⟩ := GlobalTheory.T.integral_fubini_study_sum_cone n e δ h W g u hW hg hδ hu
  obtain ⟨i2', e2'⟩ := GlobalTheory.T.integral_fubini_study_sum_cone n e δ h W g u' hW hg hδ hu'
  have hint := integral_congr_ae (μ := gaussM (e + 1) n) haeG
  rw [integral_sub i1 i2, integral_sub i1' i2', e1, e2, e1', e2'] at hint
  apply mul_left_cancel₀ hΓr
  rw [mul_sub, mul_sub]
  exact hint

end GlobalTheory.CompanionTheory.Ar.Short.Crofton
