import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MeasurableDet

noncomputable section

open MeasureTheory Matrix Complex Ad3 Ad3.LR Ad3.K.GL2LocalData Ad3.K.GL2LocalData.WR GlobalTheory.CompanionTheory.GL2LocalData.RealWhittakerFirst GlobalTheory.CompanionTheory.GL2LocalData.RealWhittakerFirst.BndFin

namespace GlobalTheory.CompanionTheory.GL2LocalData.RealWhittakerFirst.BndFin.DInt

def gam (s t : ℝ) : ℝ :=
  if 0 < t then t ^ s * Real.exp (-(2 * Real.pi) * t) else 0

theorem gam_nonneg (s t : ℝ) : 0 ≤ gam s t := by
  unfold gam; split_ifs with h
  · have := h.le; positivity
  · exact le_rfl

theorem measurable_gam (s : ℝ) : Measurable (gam s) := by
  unfold gam
  exact Measurable.ite measurableSet_Ioi (by fun_prop) measurable_const

theorem measurable_dK (β K N : ℝ) : Measurable (dK β K N) := by
  unfold dK
  exact Measurable.ite measurableSet_Ioi (by fun_prop) measurable_const

theorem lintegral_gam_ne_top {s : ℝ} (hs : -1 < s) :
    ∫⁻ t, ENNReal.ofReal (gam s t) ≠ ⊤ := by
  have hb : (0 : ℝ) < 2 * Real.pi := by positivity
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := s) (b := 2 * Real.pi) hs zero_lt_one hb
  simp only [Real.rpow_one] at h
  have hi : Integrable (gam s) := by
    have : gam s = (Set.Ioi (0 : ℝ)).indicator
        (fun t => t ^ s * Real.exp (-(2 * Real.pi) * t)) := by
      funext t
      simp only [gam, Set.indicator, Set.mem_Ioi]
    rw [this]
    exact (integrable_indicator_iff measurableSet_Ioi).2 h
  exact hi.lintegral_lt_top.ne

theorem lintegral_scale {f : ℝ → ENNReal} (hf : Measurable f) {N : ℝ} (hN : 0 < N) :
    ∫⁻ d, f (N⁻¹ * d) = ENNReal.ofReal N * ∫⁻ t, f t := by
  have hm : Measurable fun d : ℝ => N⁻¹ * d := by fun_prop
  have h := Real.map_volume_mul_left (a := N⁻¹) (inv_ne_zero hN.ne')
  rw [← lintegral_map hf hm, h, lintegral_smul_measure, inv_inv, abs_of_pos hN]
  rfl

theorem real_key {β K N t : ℝ} (hN : 0 < N) (ht : 0 < t) (E : ℝ) :
    ((N * t) ^ 2)⁻¹ * ((N * t) ^ β * t ^ K * E) = N ^ (β - 2) * (t ^ (β + K - 2) * E) := by
  rw [Real.mul_rpow hN.le ht.le, Real.rpow_sub hN, Real.rpow_sub ht, Real.rpow_add ht]
  simp only [Real.rpow_two]
  have h1 := hN.ne'
  have h2 := ht.ne'
  field_simp

theorem pointwise (β K : ℝ) {N : ℝ} (hN : 0 < N) (d : ℝ) :
    ENNReal.ofReal (d ^ 2)⁻¹ * ENNReal.ofReal (dK β K N d) =
      ENNReal.ofReal (N ^ (β - 2)) * ENNReal.ofReal (gam (β + K - 2) (N⁻¹ * d)) := by
  by_cases hd : 0 < d
  · have ht : 0 < N⁻¹ * d := by positivity
    have hd' : d = N * (N⁻¹ * d) := by field_simp
    have hdN : d / N = N⁻¹ * d := by field_simp
    rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    simp only [dK, gam, if_pos hd, if_pos ht, hdN]
    have h := real_key (β := β) (K := K) hN ht (Real.exp (-2 * Real.pi * (N⁻¹ * d)))
    rw [← hd'] at h
    rw [h]
    simp only [neg_mul]
  · have ht : ¬ 0 < N⁻¹ * d := by
      exact not_lt.2 (mul_nonpos_of_nonneg_of_nonpos (by positivity) (not_lt.1 hd))
    simp [dK, gam, if_neg hd, if_neg ht]

theorem main : ∀ β K : ℝ, 0 < β → 2 ≤ K → ∃ C : ENNReal, C ≠ ⊤ ∧ ∀ N : ℝ, 0 < N →
    ∫⁻ d, ENNReal.ofReal (dK β K N d) ∂(volume.withDensity fun d : ℝ => ENNReal.ofReal (d ^ 2)⁻¹) =
      C * ENNReal.ofReal (N ^ (β - 1)) := by
  intro β K hβ hK
  refine ⟨∫⁻ t, ENNReal.ofReal (gam (β + K - 2) t), lintegral_gam_ne_top (by linarith), ?_⟩
  intro N hN
  have hdens : Measurable fun d : ℝ => ENNReal.ofReal (d ^ 2)⁻¹ := by fun_prop
  have hg : Measurable fun t : ℝ => ENNReal.ofReal (gam (β + K - 2) t) :=
    (measurable_gam _).ennreal_ofReal
  rw [lintegral_withDensity_eq_lintegral_mul _ hdens (measurable_dK β K N).ennreal_ofReal]
  simp only [Pi.mul_apply, pointwise β K hN]
  have hc : Measurable fun d : ℝ => ENNReal.ofReal (gam (β + K - 2) (N⁻¹ * d)) :=
    ((measurable_gam _).comp (by fun_prop : Measurable fun d : ℝ => N⁻¹ * d)).ennreal_ofReal
  have hs : ∫⁻ d, ENNReal.ofReal (gam (β + K - 2) (N⁻¹ * d)) =
      ENNReal.ofReal N * ∫⁻ t, ENNReal.ofReal (gam (β + K - 2) t) := lintegral_scale hg hN
  rw [lintegral_const_mul _ hc, hs]
  have hpow : N ^ (β - 1) = N ^ (β - 2) * N := by
    rw [show β - 1 = (β - 2) + 1 by ring, Real.rpow_add hN, Real.rpow_one]
  rw [hpow, ENNReal.ofReal_mul (by positivity)]
  ring

end GlobalTheory.CompanionTheory.GL2LocalData.RealWhittakerFirst.BndFin.DInt

end
