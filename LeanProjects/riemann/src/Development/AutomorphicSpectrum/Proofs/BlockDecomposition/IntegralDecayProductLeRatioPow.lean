import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.LocallyConstantMajorants.GammaSplitting.ComplexMatrixMajorantIntegrable
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegrableMulCIff

noncomputable section

open MeasureTheory Matrix
open Ad3.K Ad3.K.LC Ad3.K.LC.C GlobalTheory.CompanionTheory.GodementFE

namespace GlobalTheory.CompanionTheory.GodementFE.TInt

theorem dd_le_rpow (e : ℝ) (h0 : 0 ≤ e) (h2 : e ≤ 2) (x : ℂ) (hx : x ≠ 0) :
    dd x ≤ ‖x‖ ^ (-e) := by
  have hr : 0 < ‖x‖ := norm_pos_iff.2 hx
  rcases le_total ‖x‖ 1 with h | h
  · have h1 : 1 ≤ ‖x‖ ^ (-e) :=
      Real.one_le_rpow_of_pos_of_le_one_of_nonpos hr h (by linarith)
    have h3 : dd x ≤ 1 := by
      unfold dd
      exact inv_le_one_of_one_le₀ (by nlinarith [sq_nonneg ‖x‖])
    linarith
  · have h1 : ‖x‖ ^ (-2 : ℝ) ≤ ‖x‖ ^ (-e) :=
      Real.rpow_le_rpow_of_exponent_le h (by linarith)
    have h3 : dd x ≤ ‖x‖ ^ (-2 : ℝ) := by
      unfold dd
      rw [Real.rpow_neg hr.le, Real.rpow_two]
      exact inv_anti₀ (by positivity) (by linarith)
    linarith

theorem dd_inv (y : ℂ) (hy : y ≠ 0) : dd y⁻¹ = ‖y‖ ^ 2 * dd y := by
  have hr : ‖y‖ ≠ 0 := norm_ne_zero_iff.2 hy
  have h1 : (1 + ‖y‖ ^ 2) ≠ 0 := by positivity
  have h2 : (1 + (‖y‖⁻¹) ^ 2) ≠ 0 := by positivity
  simp only [dd, norm_inv]
  field_simp
  ring

theorem integrable_comp_mulRight (H : ℂ → ℝ) (hH : Integrable H) (D : ℂ) (hD : D ≠ 0) :
    Integrable fun t : ℂ => H (t * D) := by
  have hd : LinearMap.det ((mulL D : ℂ →L[ℝ] ℂ) : ℂ →ₗ[ℝ] ℂ) ≠ 0 := by
    have := det_mulL D
    rw [ContinuousLinearMap.det] at this
    rw [this]
    exact (Complex.normSq_pos.2 hD).ne'
  have hmap := Measure.map_linearMap_addHaar_eq_smul_addHaar (volume : Measure ℂ) hd
  let e : ℂ ≃ₜ ℂ := Homeomorph.mulLeft₀ D hD
  have he : ⇑e = (((mulL D : ℂ →L[ℝ] ℂ) : ℂ →ₗ[ℝ] ℂ) : ℂ → ℂ) := by
    ext z
    simp [e, mulL]
  have h1 : Integrable H (Measure.map e volume) := by
    rw [he, hmap]
    exact hH.smul_measure ENNReal.ofReal_ne_top
  have h2 := (e.measurableEmbedding.integrable_map_iff).1 h1
  refine h2.congr (Filter.Eventually.of_forall fun t => ?_)
  simp [e, mul_comm]

theorem integral_comp_mulRight (H : ℂ → ℝ) (D : ℂ) (hD : D ≠ 0) :
    ∫ t : ℂ, H (t * D) = (‖D‖ ^ 2)⁻¹ * ∫ u : ℂ, H u := by
  have h := integral_comp_mul D hD (fun u => (H u : ℂ))
  have h1 : ∫ y : ℂ, ((H (D * y) : ℝ) : ℂ) = ((∫ y : ℂ, H (D * y) : ℝ) : ℂ) := integral_ofReal
  have h2 : ∫ u : ℂ, ((H u : ℝ) : ℂ) = ((∫ u : ℂ, H u : ℝ) : ℂ) := integral_ofReal
  rw [h1, h2] at h
  have h3 : ∫ y : ℂ, H (D * y) = (‖D‖ ^ 2)⁻¹ * ∫ u : ℂ, H u := by exact_mod_cast h
  simpa [mul_comm] using h3

theorem tint : ∀ e : ℝ, 0 < e → e < 2 → ∃ c : ℝ, 0 ≤ c ∧ ∀ A D : ℂ, A ≠ 0 → D ≠ 0 →
    Integrable (fun t : ℂ => (‖t‖ ^ 2)⁻¹ * (dd (t * A) * dd (t * D)⁻¹)) ∧
    ∫ t : ℂ, (‖t‖ ^ 2)⁻¹ * (dd (t * A) * dd (t * D)⁻¹) ≤ c * (‖A‖ / ‖D‖) ^ (-e) := by
  intro e he0 he2
  have hH : Integrable fun z : ℂ => ‖z‖ ^ (-e) * dd z := by
    have h := wt_vol (1 - e / 2) (by linarith) (by linarith)
    have e1 : 2 * (1 - e / 2) - 2 = -e := by ring
    rwa [e1] at h
  refine ⟨∫ z : ℂ, ‖z‖ ^ (-e) * dd z,
    integral_nonneg fun z => mul_nonneg (by positivity) (dd_pos z).le, fun A D hA hD => ?_⟩
  have hAp : 0 < ‖A‖ := norm_pos_iff.2 hA
  have hDp : 0 < ‖D‖ := norm_pos_iff.2 hD
  set K : ℝ := (‖A‖ / ‖D‖) ^ (-e) * ‖D‖ ^ 2 with hK
  have hK0 : 0 ≤ K := by positivity
  have hHD := integrable_comp_mulRight _ hH D hD
  have hdm := continuous_dd.measurable
  have hmeas : AEStronglyMeasurable
      (fun t : ℂ => (‖t‖ ^ 2)⁻¹ * (dd (t * A) * dd (t * D)⁻¹)) volume := by
    have h1 : Measurable fun t : ℂ => dd (t * A) := hdm.comp (by fun_prop)
    have h2 : Measurable fun t : ℂ => dd (t * D)⁻¹ := hdm.comp (by fun_prop)
    have h3 : Measurable fun t : ℂ => (‖t‖ ^ 2)⁻¹ := by fun_prop
    exact (h3.mul (h1.mul h2)).aestronglyMeasurable
  have hb : ∀ t : ℂ, t ≠ 0 → (‖t‖ ^ 2)⁻¹ * (dd (t * A) * dd (t * D)⁻¹) ≤
      K * (‖t * D‖ ^ (-e) * dd (t * D)) := by
    intro t ht
    have htp : 0 < ‖t‖ := norm_pos_iff.2 ht
    have hy : t * D ≠ 0 := mul_ne_zero ht hD
    have hx : t * A ≠ 0 := mul_ne_zero ht hA
    have h1 := dd_le_rpow e he0.le he2.le (t * A) hx
    have e1 : ‖t * A‖ = (‖A‖ / ‖D‖) * ‖t * D‖ := by
      rw [norm_mul, norm_mul]
      field_simp
    rw [e1, Real.mul_rpow (by positivity) (norm_nonneg _)] at h1
    have e2 : (‖t‖ ^ 2)⁻¹ * (dd (t * A) * dd (t * D)⁻¹) = ‖D‖ ^ 2 * dd (t * D) * dd (t * A) := by
      rw [dd_inv _ hy, norm_mul]
      field_simp
    rw [e2, hK]
    have hp : 0 ≤ ‖D‖ ^ 2 * dd (t * D) := mul_nonneg (by positivity) (dd_pos _).le
    calc ‖D‖ ^ 2 * dd (t * D) * dd (t * A)
        ≤ ‖D‖ ^ 2 * dd (t * D) * ((‖A‖ / ‖D‖) ^ (-e) * ‖t * D‖ ^ (-e)) :=
          mul_le_mul_of_nonneg_left h1 hp
      _ = _ := by ring
  have hae : ∀ᵐ t : ℂ, t ≠ 0 := compl_mem_ae_iff.2 (measure_singleton (0 : ℂ))
  have hint : Integrable (fun t : ℂ => (‖t‖ ^ 2)⁻¹ * (dd (t * A) * dd (t * D)⁻¹)) := by
    refine (hHD.const_mul K).mono' hmeas ?_
    filter_upwards [hae] with t ht
    have hnn : 0 ≤ (‖t‖ ^ 2)⁻¹ * (dd (t * A) * dd (t * D)⁻¹) :=
      mul_nonneg (by positivity) (mul_nonneg (dd_pos _).le (dd_pos _).le)
    rw [Real.norm_of_nonneg hnn]
    exact hb t ht
  refine ⟨hint, ?_⟩
  have h1 : ∫ t : ℂ, (‖t‖ ^ 2)⁻¹ * (dd (t * A) * dd (t * D)⁻¹) ≤
      ∫ t : ℂ, K * (‖t * D‖ ^ (-e) * dd (t * D)) := by
    refine integral_mono_ae hint (hHD.const_mul K) ?_
    filter_upwards [hae] with t ht
    exact hb t ht
  have h2 : ∫ t : ℂ, K * (‖t * D‖ ^ (-e) * dd (t * D)) =
      K * ((‖D‖ ^ 2)⁻¹ * ∫ z : ℂ, ‖z‖ ^ (-e) * dd z) := by
    rw [integral_const_mul,
      integral_comp_mulRight (fun z : ℂ => ‖z‖ ^ (-e) * dd z) D hD]
  rw [h2] at h1
  refine h1.trans (le_of_eq ?_)
  rw [hK]
  field_simp

end GlobalTheory.CompanionTheory.GodementFE.TInt
