import Mathlib
import GroundTheory.AutomorphicForms.PartialDifferential.Sobolev

namespace GroundTheory.Automorphic.Sobolev

open TemperedDistribution MeasureTheory FourierTransform
open scoped SchwartzMap ENNReal ContDiff

noncomputable section

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

theorem memLp_two_pow_mul_weight {s : ℝ} {j : ℕ}
    (hj : (Module.finrank ℝ E : ℝ) < 2 * (s - j)) :
    MemLp (fun ξ : E ↦ ‖ξ‖ ^ j * (1 + ‖ξ‖ ^ 2) ^ (-s / 2)) 2 (volume : Measure E) := by
  have hint := integrable_rpow_neg_one_add_norm_sq (E := E) (μ := (volume : Measure E)) hj
  have hmeas : AEStronglyMeasurable (fun ξ : E ↦ ‖ξ‖ ^ j * (1 + ‖ξ‖ ^ 2) ^ (-s / 2))
      (volume : Measure E) := by
    apply Continuous.aestronglyMeasurable
    exact (continuous_norm.pow j).mul
      ((continuous_const.add (continuous_norm.pow 2)).rpow_const
        fun ξ ↦ Or.inl (by positivity : (0 : ℝ) < 1 + ‖ξ‖ ^ 2).ne')
  rw [memLp_two_iff_integrable_sq_norm hmeas]
  refine hint.mono' (hmeas.norm.pow 2) (ae_of_all _ fun ξ ↦ ?_)
  have h0 : (0 : ℝ) < 1 + ‖ξ‖ ^ 2 := by positivity
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]
  calc (‖ξ‖ ^ j * (1 + ‖ξ‖ ^ 2) ^ (-s / 2)) ^ 2
      = (‖ξ‖ ^ 2) ^ j * ((1 + ‖ξ‖ ^ 2) ^ (-s / 2)) ^ 2 := by ring
    _ ≤ (1 + ‖ξ‖ ^ 2) ^ j * ((1 + ‖ξ‖ ^ 2) ^ (-s / 2)) ^ 2 := by
        gcongr; linarith
    _ = (1 + ‖ξ‖ ^ 2) ^ (-(2 * (s - j)) / 2) := by
        have e1 : ((1 + ‖ξ‖ ^ 2) ^ (-s / 2)) ^ 2 = (1 + ‖ξ‖ ^ 2) ^ (-s) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul h0.le]; congr 1; push_cast; ring
        have e2 : (1 + ‖ξ‖ ^ 2) ^ j = (1 + ‖ξ‖ ^ 2) ^ (j : ℝ) := (Real.rpow_natCast _ _).symm
        rw [e1, e2, ← Real.rpow_add h0]; congr 1; ring

theorem memLp_two_weight_mul_norm_fourierFun {s : ℝ} (u : SobolevSpace E F s) :
    MemLp (fun ξ : E ↦ (1 + ‖ξ‖ ^ 2) ^ (s / 2) * ‖fourierFun u ξ‖) 2 (volume : Measure E) := by
  have h := Lp.memLp (𝓕 (SobolevSpace.bessel s u) : Lp F 2 (volume : Measure E))
  refine h.norm.congr_norm ?_ ?_
  · have hc : Continuous (fun ξ : E ↦ (1 + ‖ξ‖ ^ 2) ^ (s / 2)) :=
      (continuous_const.add (continuous_norm.pow 2)).rpow_const
        fun ξ ↦ Or.inl (by positivity : (0 : ℝ) < 1 + ‖ξ‖ ^ 2).ne'
    exact hc.aestronglyMeasurable.mul (fourierFun_aestronglyMeasurable u).norm
  · refine ae_of_all _ fun ξ ↦ ?_
    rw [← weight_smul_fourierFun, norm_norm, norm_smul, norm_weight, norm_mul, norm_norm,
      Real.norm_eq_abs, abs_of_nonneg (by positivity)]

theorem integrable_pow_mul_norm_fourierFun {s : ℝ} {j : ℕ}
    (hj : (Module.finrank ℝ E : ℝ) < 2 * (s - j)) (u : SobolevSpace E F s) :
    Integrable (fun ξ : E ↦ ‖ξ‖ ^ j * ‖fourierFun u ξ‖) (volume : Measure E) := by
  have h := (memLp_two_pow_mul_weight (s := s) hj).integrable_mul
    (memLp_two_weight_mul_norm_fourierFun u)
  refine h.congr (ae_of_all _ fun ξ ↦ ?_)
  have h0 : (0 : ℝ) < 1 + ‖ξ‖ ^ 2 := by positivity
  simp only [Pi.mul_apply]
  rw [mul_assoc, ← mul_assoc ((1 + ‖ξ‖ ^ 2) ^ (-s / 2)), ← Real.rpow_add h0,
    show -s / 2 + s / 2 = 0 by ring, Real.rpow_zero, one_mul]

theorem integrable_fourierFun {s : ℝ} (hs : (Module.finrank ℝ E : ℝ) < 2 * s)
    (u : SobolevSpace E F s) : Integrable (fourierFun u) (volume : Measure E) := by
  have h := integrable_pow_mul_norm_fourierFun (j := 0) (by simpa using hs) u
  simp only [pow_zero, one_mul] at h
  exact (integrable_norm_iff (fourierFun_aestronglyMeasurable u)).1 h

theorem integral_fourierInv_smul_eq_of_integrable (φ : 𝓢(E, ℂ)) {g : E → F}
    (hg : Integrable g (volume : Measure E)) :
    ∫ ξ, 𝓕⁻ (φ : E → ℂ) ξ • g ξ = ∫ x, φ x • 𝓕⁻ g x := by
  have hflip : (-innerₗ E).flip = -innerₗ E := by
    ext x y; simp [real_inner_comm]
  have h := VectorFourier.integral_fourierIntegral_smul_eq_flip (L := -innerₗ E)
    Real.continuous_fourierChar
    (by simp only [LinearMap.neg_apply, innerₗ_apply_apply]; fun_prop)
    (φ.integrable (μ := (volume : Measure E))) hg
  rw [hflip] at h
  exact h

theorem toDistribution_apply_eq_integral {s : ℝ} (hs : (Module.finrank ℝ E : ℝ) < 2 * s)
    (u : SobolevSpace E F s) (φ : 𝓢(E, ℂ)) :
    SobolevSpace.toDistribution u φ = ∫ x, φ x • 𝓕⁻ (fourierFun u) x := by
  have h : 𝓕⁻ (𝓕 (SobolevSpace.toDistribution u)) = SobolevSpace.toDistribution u :=
    FourierTransform.fourierInv_fourier_eq _
  conv_lhs => rw [← h]
  rw [TemperedDistribution.fourierInv_apply, fourier_apply_eq_integral,
    SchwartzMap.fourierInv_coe, integral_fourierInv_smul_eq_of_integrable φ (integrable_fourierFun hs u)]

theorem integrable_pow_mul_norm_fourierFun_neg {s : ℝ} {j : ℕ}
    (hj : (Module.finrank ℝ E : ℝ) < 2 * (s - j)) (u : SobolevSpace E F s) :
    Integrable (fun ξ : E ↦ ‖ξ‖ ^ j * ‖fourierFun u (-ξ)‖) (volume : Measure E) := by
  have h := (integrable_pow_mul_norm_fourierFun hj u).comp_neg
  simpa [Function.comp_def, norm_neg] using h

theorem sobolev_embedding {s : ℝ} (k : ℕ)
    (hs : (k : ℝ) + (Module.finrank ℝ E : ℝ) / 2 < s) (u : SobolevSpace E F s) :
    ∃ g : E → F, ContDiff ℝ k g ∧
      (∀ i : ℕ, i ≤ k → ∃ C, ∀ x, ‖iteratedFDeriv ℝ i g x‖ ≤ C) ∧
      ∀ φ : 𝓢(E, ℂ), SobolevSpace.toDistribution u φ = ∫ x, φ x • g x := by
  have hj : ∀ j : ℕ, j ≤ k → (Module.finrank ℝ E : ℝ) < 2 * (s - j) := fun j hj ↦ by
    have : (j : ℝ) ≤ k := by exact_mod_cast hj
    linarith
  have hs0 : (Module.finrank ℝ E : ℝ) < 2 * s := by simpa using hj 0 (Nat.zero_le _)
  set f : E → F := fun ξ ↦ fourierFun u (-ξ)
  have hg : 𝓕⁻ (fourierFun u) = 𝓕 f := Real.fourierInv_eq_fourier_comp_neg _
  have hint : ∀ n : ℕ, (n : ℕ∞) ≤ (k : ℕ∞) → Integrable (fun v ↦ ‖v‖ ^ n * ‖f v‖)
      (volume : Measure E) := fun n hn ↦
    integrable_pow_mul_norm_fourierFun_neg (hj n (by exact_mod_cast hn)) u
  have hmeas : AEStronglyMeasurable f (volume : Measure E) :=
    (fourierFun_aestronglyMeasurable u).comp_measurePreserving
      (Measure.measurePreserving_neg (volume : Measure E))
  refine ⟨𝓕⁻ (fourierFun u), ?_, ?_, toDistribution_apply_eq_integral hs0 u⟩
  · rw [hg]
    exact Real.contDiff_fourier hint
  · intro i hi
    refine ⟨∫ v, ‖(fun v ↦ VectorFourier.fourierPowSMulRight (innerSL ℝ) f v i) v‖, fun x ↦ ?_⟩
    rw [hg, Real.iteratedFDeriv_fourier hint hmeas (by exact_mod_cast hi)]
    exact VectorFourier.norm_fourierIntegral_le_integral_norm _ _ _ _ _

end

end GroundTheory.Automorphic.Sobolev
