import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.LocallyConstantMajorants.GammaSplitting.ComplexMatrixMajorantIntegrable
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegrableMulCIff

noncomputable section

open MeasureTheory Matrix
open Ad3.K Ad3.K.LC Ad3.K.LC.C GlobalTheory.CompanionTheory.GodementFE

namespace GlobalTheory.CompanionTheory.GodementFE

theorem psiC_add_tri (a b : ℂ) : psiC (a + b) = psiC a * psiC b := by
  simp only [psiC, ← Complex.exp_add]
  congr 1
  simp only [Complex.add_re]
  push_cast
  ring

theorem norm_ph_tri_of_ne (n : ℤ) {z : ℂ} (hz : z ≠ 0) : ‖ph n z‖ = 1 := by
  have h : ‖z / (‖z‖ : ℂ)‖ = 1 := by
    have h0 : ‖z‖ ≠ 0 := norm_ne_zero_iff.2 hz
    rw [norm_div, Complex.norm_real, norm_norm, div_self h0]
  rw [ph, norm_zpow, h, _root_.one_zpow]

theorem norm_ph_tri_le (n : ℤ) (z : ℂ) : ‖ph n z‖ ≤ 1 := by
  by_cases hz : z = 0
  · subst hz
    by_cases hn : n = 0
    · simp [ph, hn]
    · simp [ph, _root_.zero_zpow n hn]
  · exact (norm_ph_tri_of_ne n hz).le

theorem norm_inner_tri (g : (Fin 2 → ℂ) → ℂ) (a b d : ℂ) (hd : d ≠ 0) :
    ‖∫ y : ℂ, g ![a, b + d * y] * psiC (-y)‖ = (‖d‖ ^ 2)⁻¹ * ‖sF g a d⁻¹‖ := by
  have h := integral_comp_mul d hd (fun u : ℂ => g ![a, b + u] * psiC (-(u * d⁻¹)))
  have e2 : ∀ y : ℂ, d * y * d⁻¹ = y := fun y => by field_simp
  simp only [e2] at h
  have h2 : ∫ u : ℂ, g ![a, b + u] * psiC (-(u * d⁻¹)) = psiC (b * d⁻¹) * sF g a d⁻¹ := by
    have h3 := integral_add_left_eq_self (μ := (volume : Measure ℂ))
      (fun u : ℂ => g ![a, u] * psiC (-((u - b) * d⁻¹))) b
    simp only [add_sub_cancel_left] at h3
    rw [h3, sF, ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    have e3 : -((u - b) * d⁻¹) = -(u * d⁻¹) + b * d⁻¹ := by ring
    simp only [e3, psiC_add_tri]
    ring
  rw [h, h2, norm_mul, norm_mul, norm_psiC, one_mul, Complex.norm_real,
    Real.norm_of_nonneg (by positivity)]

theorem norm_whittakerGL2_triangular_le : ∀ (k : ℕ) (f f' : SchwartzMap (Fin 2 → ℂ) ℂ) (κ : Matrix (Fin 2) (Fin 2) ℂ) (A B D : ℂ),
    A ≠ 0 → D ≠ 0 → ‖κ.det‖ = 1 → (∀ v, f' v = f (Matrix.vecMul v κ)) →
    ‖W2 k f (!![A, B; 0, D] * κ)‖ ≤
      ‖A‖ * ‖D‖⁻¹ * ∫ t : ℂ, (‖t‖ ^ 2)⁻¹ * ‖sF f' (t * A) (t * D)⁻¹‖ := by
  intro k f f' κ A B D _ hD hκ hf
  have hn : ‖(!![A, B; 0, D] * κ).det‖ = ‖A‖ * ‖D‖ := by
    rw [Matrix.det_mul, Matrix.det_fin_two_of, norm_mul, hκ, mul_one]
    simp
  have hv : ∀ t y : ℂ, f (Matrix.vecMul ![t, t * y] (!![A, B; 0, D] * κ)) =
      f' ![t * A, t * B + t * D * y] := by
    intro t y
    rw [hf, ← Matrix.vecMul_vecMul]
    congr 2
    ext i
    fin_cases i
    · simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two]
    · simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two]
      ring
  have hD0 : ‖D‖ ≠ 0 := norm_ne_zero_iff.2 hD
  have hI : ‖∫ t : ℂ, ph (4 * (k : ℤ) - 4) t *
        ∫ y : ℂ, f (Matrix.vecMul ![t, t * y] (!![A, B; 0, D] * κ)) * psiC (-y)‖ ≤
      (‖D‖ ^ 2)⁻¹ * ∫ t : ℂ, (‖t‖ ^ 2)⁻¹ * ‖sF f' (t * A) (t * D)⁻¹‖ := by
    refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
    rw [← integral_const_mul]
    refine integral_congr_ae ?_
    filter_upwards [compl_mem_ae_iff.2 (measure_singleton (0 : ℂ))] with t ht
    have ht0 : t ≠ 0 := ht
    simp only [hv]
    rw [norm_mul, norm_ph_tri_of_ne _ ht0, one_mul,
      norm_inner_tri _ _ _ _ (mul_ne_zero ht0 hD), norm_mul, mul_pow, mul_inv]
    ring
  set J : ℝ := ∫ t : ℂ, (‖t‖ ^ 2)⁻¹ * ‖sF f' (t * A) (t * D)⁻¹‖ with hJ
  unfold W2
  rw [norm_mul, norm_mul, Complex.norm_real, norm_norm, hn]
  have hp := norm_ph_tri_le (2 * (k : ℤ) - 2) (!![A, B; 0, D] * κ).det
  have hAD : 0 ≤ ‖A‖ * ‖D‖ := by positivity
  calc _ ≤ 1 * (‖A‖ * ‖D‖) * ((‖D‖ ^ 2)⁻¹ * J) :=
        mul_le_mul (mul_le_mul_of_nonneg_right hp hAD) hI (norm_nonneg _) (by positivity)
    _ = ‖A‖ * ‖D‖⁻¹ * J := by
        field_simp

end GlobalTheory.CompanionTheory.GodementFE
