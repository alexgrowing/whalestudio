import Formalism.HermitianCurvature.CompositeFormulaLevelZero
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

open MeasureTheory Real
open scoped FourierTransform RealInnerProductSpace ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBO

def isoQ : ℂ ≃ₗᵢ[ℝ] ℂ where
  toFun s := conj (Complex.I * s)
  invFun w := -Complex.I * conj w
  map_add' a b := by simp [mul_add]
  map_smul' c a := by
    simp only [RingHom.id_apply, Complex.real_smul, map_mul, Complex.conj_ofReal]
    ring
  left_inv a := by
    simp only [map_mul, Complex.conj_I, Complex.conj_conj]
    ring_nf
    simp
  right_inv w := by
    simp only [map_mul, map_neg, Complex.conj_I, Complex.conj_conj]
    ring_nf
    simp [Complex.I_sq]
  norm_map' s := by simp

theorem isoQ_apply (s : ℂ) : isoQ s = conj (Complex.I * s) := rfl

theorem fsv_smul (s u z : ℂ) : P5.fsv s u * z = 𝐞 (-⟪u, (π⁻¹ : ℝ) • isoQ s⟫) • z := by
  unfold P5.fsv
  simp [Circle.smul_def, isoQ_apply]
  left
  rw [Real.fourierChar_apply]
  congr 1
  have hπ : π ≠ 0 := Real.pi_ne_zero
  apply Complex.ext <;> simp <;> field_simp <;> ring

theorem norm_le_integral_fsv (φ : ℂ → ℂ) (hφ : Continuous φ) (hi : MeasureTheory.Integrable φ)
    (hΞ : MeasureTheory.Integrable (fun s : ℂ => ∫ t : ℂ, P5.fsv s t * φ t)) (t : ℂ) :
    ‖φ t‖ ≤ ∫ s : ℂ, ‖∫ u : ℂ, P5.fsv s u * φ u‖ := by
  have hc : (π⁻¹ : ℝ) ≠ 0 := inv_ne_zero Real.pi_ne_zero
  have hL : ∀ s : ℂ, (∫ u : ℂ, P5.fsv s u * φ u) = 𝓕 φ ((π⁻¹ : ℝ) • isoQ s) := by
    intro s
    rw [fourier_eq]
    exact integral_congr_ae (Filter.Eventually.of_forall fun u => fsv_smul s u (φ u))
  have hmp : MeasurePreserving isoQ := isoQ.measurePreserving
  have hme : MeasurableEmbedding isoQ := isoQ.toHomeomorph.measurableEmbedding
  have hint1 : Integrable (fun s : ℂ => 𝓕 φ ((π⁻¹ : ℝ) • s)) := by
    have h1 : Integrable ((fun s : ℂ => 𝓕 φ ((π⁻¹ : ℝ) • s)) ∘ isoQ) := by
      have h2 := hΞ
      simp_rw [hL] at h2
      exact h2
    exact (hmp.integrable_comp_emb hme).mp h1
  have hint : Integrable (𝓕 φ) := by
    first
      | exact (integrable_comp_smul_iff volume (𝓕 φ) hc).mp hint1
      | exact (MeasureTheory.integrable_comp_smul_iff (volume : Measure ℂ) (𝓕 φ) hc).mp hint1
      | exact (Integrable.comp_smul_iff hc).mp hint1
  have hinv : 𝓕⁻ (𝓕 φ) t = φ t := by
    first
      | exact hi.fourier_inversion hint hφ.continuousAt
      | exact hi.fourierInv_fourier_eq hint hφ.continuousAt
      | exact hφ.fourierInv_fourier_eq hi hint t
      | exact Continuous.fourierInv_fourier_eq hφ hi hint t
      | exact hi.fourierInv_fourier hint hφ.continuousAt
      | exact hφ.fourierInv_fourier hi hint t
      | exact MeasureTheory.Integrable.fourier_inversion hi hint hφ.continuousAt
  have hb : ‖φ t‖ ≤ ∫ w : ℂ, ‖𝓕 φ w‖ := by
    rw [← hinv]
    first
      | rw [fourierInv_eq]
      | rw [Real.fourierInv_eq]
      | rw [fourierInv_eq']
      | rw [fourierInv_eq_fourier_neg, fourier_eq]
    refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
    congr 1
    funext w
    first
      | exact Circle.norm_smul _ _
      | simp
  have e1 := hmp.integral_comp hme (fun s : ℂ => ‖𝓕 φ ((π⁻¹ : ℝ) • s)‖)
  have e2 := Measure.integral_comp_smul (volume : Measure ℂ) (fun w : ℂ => ‖𝓕 φ w‖) (π⁻¹ : ℝ)
  try dsimp only at e1
  try dsimp only at e2
  have heq : (∫ s : ℂ, ‖∫ u : ℂ, P5.fsv s u * φ u‖) =
      |((π⁻¹ : ℝ) ^ 2)⁻¹| • ∫ w : ℂ, ‖𝓕 φ w‖ := by
    simp_rw [hL]
    rw [e1, e2, Complex.finrank_real_complex]
  rw [heq, smul_eq_mul]
  have h0 : 0 ≤ ∫ w : ℂ, ‖𝓕 φ w‖ := integral_nonneg fun _ => norm_nonneg _
  have hπ : 1 ≤ |((π⁻¹ : ℝ) ^ 2)⁻¹| := by
    rw [inv_pow, inv_inv, abs_of_pos (by positivity)]
    nlinarith [Real.pi_gt_three]
  nlinarith

end Formalism.FourierDecayAlt.P.PBO
