import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.Carries
import GroundTheory.AutomorphicForms.TraceNormComp
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.AvSpec

open MeasureTheory GroundTheory.Automorphic PositivityTheory.Rg.Tf.IntegralApplyAeEq Set Filter Topology UpperTheory.V.Z.IntegralApplyAeEq
open scoped InnerProductSpace FourierTransform ComplexConjugate

theorem UpperTheory.V.Z.IntegralApplyAeEq.avApprox :
    (∀ a b : ℝ, a < b → ∃ ψ, Bump ψ a b) ∧ (∀ ψ a b, Bump ψ a b → HasCompactSupport ψ ∧ Integrable (fun t => (ψ t : ℂ)) ∧ ∫ t, ψ t ^ 2 ≤ 2 / (b - a)) ∧
      ∀ {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (F : Flow H) (h : H) (ε : ℝ), 0 < ε → ∃ δ > 0, ∀ ψ a b, Bump ψ a b → -δ ≤ a → b ≤ δ → ‖F.av (fun t => (ψ t : ℂ)) h - h‖ ≤ ε := by
  have two : ∀ ψ a b, Bump ψ a b → HasCompactSupport ψ ∧ Integrable (fun t => (ψ t : ℂ)) ∧ ∫ t, ψ t ^ 2 ≤ 2 / (b - a) := by
    intro ψ a b h
    have hs : HasCompactSupport ψ := HasCompactSupport.intro isCompact_Icc h.supp
    have hi : Integrable ψ := h.cont.integrable_of_hasCompactSupport hs
    refine ⟨hs, hi.ofReal, ?_⟩
    have : ∫ t, ψ t ^ 2 ≤ ∫ t, 2 / (b - a) * ψ t :=
      integral_mono_of_nonneg (Eventually.of_forall fun t => sq_nonneg _) (hi.const_mul _)
        (Eventually.of_forall fun t => by show ψ t ^ 2 ≤ _; rw [sq]; exact mul_le_mul_of_nonneg_right (h.le t) (h.nonneg t))
    rwa [integral_const_mul, h.total, mul_one] at this
  refine ⟨fun a b hab => ?_, two, ?_⟩
  · have hd : 0 < b - a := sub_pos.2 hab
    let f : ℝ → ℝ := fun t => 6 / (b - a) ^ 3 * max 0 ((t - a) * (b - t))
    have hsupp : ∀ t, t ∉ Icc a b → f t = 0 := fun t ht => by
      have : (t - a) * (b - t) ≤ 0 := by
        rcases not_and_or.1 ht with h | h <;> push Not at h <;> nlinarith
      simp [f, max_eq_left this]
    refine ⟨f, by fun_prop, fun t => by positivity, fun t => ?_, hsupp, ?_⟩
    · have : max 0 ((t - a) * (b - t)) ≤ (b - a) ^ 2 / 4 := max_le (by positivity) (by nlinarith [sq_nonneg (a + b - 2 * t)])
      calc f t ≤ 6 / (b - a) ^ 3 * ((b - a) ^ 2 / 4) := by simp only [f]; gcongr
        _ = 3 / 2 / (b - a) := by field_simp; norm_num
        _ ≤ 2 / (b - a) := by gcongr; norm_num
    · rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hsupp, integral_Icc_eq_integral_Ioc,
        ← intervalIntegral.integral_of_le hab.le]
      have : ∫ t in a..b, f t = ∫ t in a..b, 6 / (b - a) ^ 3 * (-t ^ 2 + (a + b) * t - a * b) := by
        refine intervalIntegral.integral_congr fun t ht => ?_
        rw [uIcc_of_le hab.le] at ht
        simp only [f]
        rw [max_eq_right (mul_nonneg (sub_nonneg.2 ht.1) (sub_nonneg.2 ht.2))]; ring
      rw [this, intervalIntegral.integral_const_mul, intervalIntegral.integral_sub, intervalIntegral.integral_add,
        intervalIntegral.integral_neg, intervalIntegral.integral_const_mul, integral_pow, integral_id, intervalIntegral.integral_const]
      · simp only [smul_eq_mul]; field_simp; ring
      all_goals exact Continuous.intervalIntegrable (by fun_prop) _ _
  · intro H _ _ _ F h ε hε
    obtain ⟨δ, hδ, H1⟩ := Metric.continuousAt_iff.1 ((F.cont h).continuousAt (x := 0)) ε hε
    refine ⟨δ / 2, by positivity, fun ψ a b hψ ha hb => ?_⟩
    obtain ⟨hs, hi, -⟩ := two ψ a b hψ
    obtain ⟨i, e⟩ := ((avSpec F).2.2.2 _ hi).1 h
    have hr : Integrable ψ := hψ.cont.integrable_of_hasCompactSupport hs
    have e2 : h = ∫ t, (ψ t : ℂ) • h := by rw [integral_smul_const, integral_complex_ofReal, hψ.total]; simp
    rw [e]
    conv_lhs => rw [show (∫ t, (ψ t : ℂ) • F.U t h) - h = (∫ t, (ψ t : ℂ) • F.U t h) - ∫ t, (ψ t : ℂ) • h from congrArg _ e2]
    rw [← integral_sub i (hi.smul_const h)]
    refine (norm_integral_le_of_norm_le (hr.mul_const ε) (Eventually.of_forall fun t => ?_)).trans_eq
      (by rw [integral_mul_const, hψ.total, one_mul])
    rw [← smul_sub, norm_smul, Complex.norm_real, Real.norm_of_nonneg (hψ.nonneg t)]
    by_cases ht : t ∈ Icc a b
    · have := H1 (x := t) (by rw [Real.dist_eq, sub_zero, abs_lt]; constructor <;> linarith [ht.1, ht.2])
      rw [F.zero, dist_eq_norm] at this
      exact mul_le_mul_of_nonneg_left this.le (hψ.nonneg t)
    · simp [hψ.supp t ht]
