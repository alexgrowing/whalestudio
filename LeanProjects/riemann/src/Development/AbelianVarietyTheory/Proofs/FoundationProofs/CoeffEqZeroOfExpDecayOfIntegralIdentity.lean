import Development.AbelianVarietyTheory.Definitions.Foundations.IsDCReps
open GlobalTheory.HeckeFamilyMatrices Polynomial UpperHalfPlane
open scoped MatrixGroups ModularForm
open scoped Manifold
open Filter Topology Set MeasureTheory

namespace GlobalTheory

theorem ode_coeff_zero_of_decay_ends : ∀ (v : ℝ → ℂ) (K c : ℂ) (C α β : ℝ) (w : ℕ), 1 ≤ w → 0 < α → 0 < β → K ≠ 0 → (∀ y : ℝ, 0 < y → ‖v y‖ ≤ C * y ^ ((w : ℝ) / 2) * Real.exp (-α * y)) → (∀ a b : ℝ, 0 < a → a ≤ b → v b - v a = K * c * ∫ y in a..b, (y : ℂ) ^ w * (Real.exp (-β * y) : ℂ)) → c = 0 := by
  intro v K c C α β w hw hα hβ hK hbound hdiff
  set g : ℝ → ℝ := fun y => y ^ w * Real.exp (-β * y) with hg
  have gcont : Continuous g := by fun_prop
  have hint : ∀ a b : ℝ, (∫ y in a..b, (y : ℂ) ^ w * (Real.exp (-β * y) : ℂ)) = ((∫ y in a..b, g y : ℝ) : ℂ) := by
    intro a b
    rw [← intervalIntegral.integral_ofReal]
    congr 1
    ext y
    simp [g]
  set I := ∫ y in (1:ℝ)..2, g y with hIdef
  have hI : 0 < I := intervalIntegral.intervalIntegral_pos_of_pos_on (gcont.intervalIntegrable _ _)
    (fun x hx => by
      have : 0 < x := by linarith [hx.1]
      simp only [g]; positivity) (by norm_num)
  have key : ∀ a b : ℝ, 0 < a → a ≤ 1 → 2 ≤ b → ‖K * c‖ * I ≤ ‖v b‖ + ‖v a‖ := by
    intro a b ha ha1 hb2
    have h1 := hdiff a b ha (by linarith)
    have hmono : I ≤ ∫ y in a..b, g y := by
      apply intervalIntegral.integral_mono_interval ha1 (by norm_num) hb2
      · filter_upwards [ae_restrict_mem measurableSet_Ioc] with y hy
        have : 0 < y := lt_trans ha hy.1
        simp only [g, Pi.zero_apply]; positivity
      · exact gcont.intervalIntegrable _ _
    calc ‖K * c‖ * I ≤ ‖K * c‖ * ∫ y in a..b, g y := mul_le_mul_of_nonneg_left hmono (norm_nonneg _)
      _ ≤ ‖K * c‖ * |∫ y in a..b, g y| := mul_le_mul_of_nonneg_left (le_abs_self _) (norm_nonneg _)
      _ = ‖v b - v a‖ := by rw [h1, hint, norm_mul (K * c) _, Complex.norm_real, Real.norm_eq_abs]
      _ ≤ ‖v b‖ + ‖v a‖ := norm_sub_le _ _
  have hw2 : (0:ℝ) < (w:ℝ) / 2 := by
    have : (1:ℝ) ≤ w := by exact_mod_cast hw
    linarith
  have h0 : Tendsto (fun a => ‖v a‖) (𝓝[>] 0) (𝓝 0) := by
    have hc : Tendsto (fun a : ℝ => C * a ^ ((w:ℝ)/2) * Real.exp (-α * a)) (𝓝[>] 0) (𝓝 0) := by
      have hca : ContinuousAt (fun a : ℝ => C * a ^ ((w:ℝ)/2) * Real.exp (-α * a)) 0 := by
        apply ContinuousAt.mul
        · exact ContinuousAt.mul continuousAt_const (Real.continuousAt_rpow_const _ _ (Or.inr hw2.le))
        · fun_prop
      have h := hca.tendsto
      simp only [Real.zero_rpow hw2.ne', mul_zero, zero_mul] at h
      exact tendsto_nhdsWithin_of_tendsto_nhds h
    apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) _ hc
    filter_upwards [self_mem_nhdsWithin] with a ha using hbound a ha
  have hinf : Tendsto (fun b => ‖v b‖) atTop (𝓝 0) := by
    have hc : Tendsto (fun b : ℝ => C * (b ^ ((w:ℝ)/2) * Real.exp (-α * b))) atTop (𝓝 0) := by
      simpa using (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero ((w:ℝ)/2) α hα).const_mul C
    apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) _ hc
    filter_upwards [eventually_gt_atTop 0] with b hb
    rw [← mul_assoc]; exact hbound b hb
  have step : ∀ b : ℝ, 2 ≤ b → ‖K * c‖ * I ≤ ‖v b‖ := by
    intro b hb
    have ht : Tendsto (fun a => ‖v b‖ + ‖v a‖) (𝓝[>] 0) (𝓝 (‖v b‖ + 0)) := tendsto_const_nhds.add h0
    rw [add_zero] at ht
    apply ge_of_tendsto ht
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Iio_mem_nhds (show (0:ℝ) < 1 by norm_num))] with a ha ha1
    exact key a b ha (le_of_lt ha1) hb
  have hle : ‖K * c‖ * I ≤ 0 :=
    ge_of_tendsto hinf (by filter_upwards [eventually_ge_atTop 2] with b hb using step b hb)
  have hKc : ‖K * c‖ = 0 := le_antisymm (by nlinarith [norm_nonneg (K * c)]) (norm_nonneg _)
  rw [norm_eq_zero, mul_eq_zero] at hKc
  exact hKc.resolve_left hK

end GlobalTheory
