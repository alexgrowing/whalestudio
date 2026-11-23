import Mathlib

noncomputable section

open MeasureTheory Filter Metric Complex
open scoped Topology NNReal ENNReal Real

namespace PositivityTheory.Rg.Rsw.L.LCfRel

theorem circle_entire_mul (c : ℂ → ℂ) (hc : Differentiable ℂ c) (f : ℂ → ℂ) (s₀ : ℂ) {ε : ℝ} (hε : 0 < ε)
    (hf : ContinuousOn f (sphere s₀ ε)) (k : ℕ) (hk : 1 ≤ k)
    (h0 : ∀ j, k < j → (∮ z in C(s₀, ε), (z - s₀) ^ (j - 1) * f z) = 0) :
    (∮ z in C(s₀, ε), (z - s₀) ^ (k - 1) * (c z * f z)) = c s₀ * ∮ z in C(s₀, ε), (z - s₀) ^ (k - 1) * f z := by
  obtain ⟨M, hM⟩ := (isCompact_sphere s₀ ε).exists_bound_of_continuousOn hf
  have hps := hc.hasFPowerSeriesOnBall s₀ (R := 1) one_pos
  set p := cauchyPowerSeries c s₀ 1 with hp
  have hfc : Continuous fun θ => f (circleMap s₀ ε θ) :=
    hf.comp_continuous (continuous_circleMap s₀ ε) fun θ => circleMap_mem_sphere s₀ hε.le θ
  let T : ℕ → ℝ → ℂ := fun i θ => deriv (circleMap s₀ ε) θ •
    ((circleMap s₀ ε θ - s₀) ^ (k - 1) * ((circleMap s₀ ε θ - s₀) ^ i * p.coeff i * f (circleMap s₀ ε θ)))
  have hT : ∀ i, Continuous (T i) := fun i => by
    simp only [T, deriv_circleMap]
    exact ((continuous_circleMap 0 ε).mul continuous_const).smul
      ((((continuous_circleMap s₀ ε).sub continuous_const).pow _).mul
        (((((continuous_circleMap s₀ ε).sub continuous_const).pow _).mul continuous_const).mul hfc))
  have hsum : HasSum (fun i => ∫ θ in (0 : ℝ)..2 * π, T i θ)
      (∮ z in C(s₀, ε), (z - s₀) ^ (k - 1) * (c z * f z)) := by
    refine intervalIntegral.hasSum_integral_of_dominated_convergence
      (fun i _ => ε * ε ^ (k - 1) * M * (‖p i‖ * ε ^ i)) (fun i => (hT i).aestronglyMeasurable)
      (fun i => ae_of_all _ fun θ _ => ?_) (ae_of_all _ fun θ _ => ?_) intervalIntegrable_const
      (ae_of_all _ fun θ _ => ?_)
    · have h1 : ‖circleMap s₀ ε θ - s₀‖ = ε := by rw [circleMap_sub_center, norm_circleMap_zero, abs_of_pos hε]
      have h2 := hM _ (circleMap_mem_sphere s₀ hε.le θ)
      simp only [T, deriv_circleMap, smul_eq_mul, norm_mul, norm_pow, h1, norm_circleMap_zero, abs_of_pos hε,
        Complex.norm_I, mul_one, ← p.norm_apply_eq_norm_coef]
      have hpos : 0 ≤ ε * ε ^ (k - 1) * (‖p i‖ * ε ^ i) := by positivity
      nlinarith [mul_le_mul_of_nonneg_left h2 hpos]
    · have hr : ((ε.toNNReal : ℝ≥0) : ℝ≥0∞) < p.radius := lt_of_lt_of_le ENNReal.coe_lt_top hps.r_le
      have hs : Summable fun n => ‖p n‖ * ε ^ n := by
        simpa [Real.coe_toNNReal _ hε.le] using p.summable_norm_mul_pow hr
      exact hs.mul_left _
    · have := hps.hasSum_sub (y := circleMap s₀ ε θ) (Metric.mem_eball.2 (edist_lt_top _ _))
      simp only [FormalMultilinearSeries.apply_eq_pow_smul_coeff, smul_eq_mul] at this
      exact ((this.mul_right (f (circleMap s₀ ε θ))).mul_left ((circleMap s₀ ε θ - s₀) ^ (k - 1))).const_smul _
  have hterm : ∀ i, ∫ θ in (0 : ℝ)..2 * π, T i θ = p.coeff i * ∮ z in C(s₀, ε), (z - s₀) ^ (k + i - 1) * f z := by
    intro i
    simp only [circleIntegral, T]
    rw [← intervalIntegral.integral_const_mul, show k + i - 1 = k - 1 + i by omega]
    congr 1; ext θ
    simp only [smul_eq_mul, pow_add]; ring
  have hc0 : p.coeff 0 = c s₀ := hps.hasFPowerSeriesAt.coeff_zero 1
  have hval : (fun i => ∫ θ in (0 : ℝ)..2 * π, T i θ) =
      fun i => if i = 0 then c s₀ * ∮ z in C(s₀, ε), (z - s₀) ^ (k - 1) * f z else 0 := by
    funext i; rw [hterm]; split_ifs with h
    · subst h; rw [hc0, Nat.add_zero]
    · rw [h0 (k + i) (by omega), mul_zero]
  rw [hval] at hsum
  exact hsum.unique (hasSum_ite_eq 0 _)

end PositivityTheory.Rg.Rsw.L.LCfRel

end
