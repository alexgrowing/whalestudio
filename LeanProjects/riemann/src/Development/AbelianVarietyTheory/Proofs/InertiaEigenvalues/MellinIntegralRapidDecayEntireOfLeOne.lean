import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousOfMemSmoothSpan
open NumberField Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.ThetaPoisson GroundTheory.Global GroundTheory.Global.IdeleGroup
open scoped ComplexConjugate nonZeroDivisors ContDiff

namespace GlobalTheory

theorem integral_mul_cpow_of_rapid_decay_entire :
    ∀ (X : Type) [MeasurableSpace X] (ν : Measure X) (δ : X → ℝ) (F : X → ℂ), Measurable δ →
      (∀ᵐ x ∂ν, 0 < δ x ∧ δ x ≤ 1) → Integrable δ ν → AEStronglyMeasurable F ν →
      (∀ K : ℕ, ∃ C : ℝ, ∀ᵐ x ∂ν, ‖F x‖ ≤ C * δ x ^ K) →
      (∀ s : ℂ, Integrable (fun x => F x * (δ x : ℂ) ^ s) ν) ∧
        Differentiable ℂ fun s : ℂ => ∫ x, F x * (δ x : ℂ) ^ s ∂ν := by
  intro X _ ν δ F hδm hδ hδi hF hdec
  have key : ∀ t : ℝ, ∃ C : ℝ, ∀ᵐ x ∂ν, ‖F x‖ * δ x ^ t ≤ C * δ x := by
    intro t
    obtain ⟨K, hK⟩ : ∃ K : ℕ, 1 - t ≤ K := exists_nat_ge (1 - t)
    obtain ⟨C, hC⟩ := hdec K
    refine ⟨C, ?_⟩
    filter_upwards [hC, hδ] with x hx hx'
    obtain ⟨h0, h1⟩ := hx'
    have hpK : 0 < δ x ^ K := pow_pos h0 K
    have hC0 : 0 ≤ C := by
      by_contra hc
      push_neg at hc
      have := mul_neg_of_neg_of_pos hc hpK
      linarith [norm_nonneg (F x)]
    have hpt : 0 ≤ δ x ^ t := Real.rpow_nonneg h0.le t
    calc ‖F x‖ * δ x ^ t ≤ C * δ x ^ K * δ x ^ t := mul_le_mul_of_nonneg_right hx hpt
      _ = C * δ x ^ ((K : ℝ) + t) := by rw [Real.rpow_add h0, Real.rpow_natCast]; ring
      _ ≤ C * δ x ^ (1 : ℝ) :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_ge h0 h1 (by linarith)) hC0
      _ = C * δ x := by rw [Real.rpow_one]
  have hcm : ∀ s : ℂ, Measurable fun x => (δ x : ℂ) ^ s :=
    fun s => (Complex.measurable_ofReal.comp hδm).pow_const s
  have hmeas : ∀ s : ℂ, AEStronglyMeasurable (fun x => F x * (δ x : ℂ) ^ s) ν :=
    fun s => hF.mul (hcm s).aestronglyMeasurable
  have hint : ∀ s : ℂ, Integrable (fun x => F x * (δ x : ℂ) ^ s) ν := by
    intro s
    obtain ⟨C, hC⟩ := key s.re
    refine Integrable.mono' (hδi.const_mul C) (hmeas s) ?_
    filter_upwards [hC, hδ] with x hx hx'
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx'.1]
    exact hx
  refine ⟨hint, fun s₀ => ?_⟩
  obtain ⟨C, hC⟩ := key (s₀.re - 2)
  have hF'm : AEStronglyMeasurable
      (fun x => F x * ((δ x : ℂ) ^ s₀ * Complex.log (δ x))) ν :=
    hF.mul ((hcm s₀).mul (Complex.measurable_log.comp
      (Complex.measurable_ofReal.comp hδm))).aestronglyMeasurable
  have hd := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := ν) (x₀ := s₀)
    (F := fun s x => F x * (δ x : ℂ) ^ s)
    (F' := fun s x => F x * ((δ x : ℂ) ^ s * Complex.log (δ x)))
    (bound := fun x => C * δ x) (Metric.ball_mem_nhds s₀ zero_lt_one)
    (Filter.Eventually.of_forall hmeas) (hint s₀) hF'm ?_ (hδi.const_mul C) ?_
  · exact hd.2.differentiableAt
  · filter_upwards [hC, hδ] with x hx hx'
    obtain ⟨h0, h1⟩ := hx'
    intro s hs
    rw [Metric.mem_ball, Complex.dist_eq] at hs
    have hre : s₀.re - 1 ≤ s.re := by
      have h := Complex.abs_re_le_norm (s - s₀)
      rw [Complex.sub_re] at h
      linarith [neg_abs_le (s.re - s₀.re)]
    have hlog : ‖Complex.log (δ x)‖ = |Real.log (δ x)| := by
      rw [← Complex.ofReal_log h0.le, Complex.norm_real, Real.norm_eq_abs]
    have hl := Real.abs_log_mul_self_lt (δ x) h0 h1
    rw [abs_mul, abs_of_pos h0] at hl
    have e1 : δ x ^ s.re ≤ δ x ^ (s₀.re - 1) := Real.rpow_le_rpow_of_exponent_ge h0 h1 hre
    have e2 : δ x ^ (s₀.re - 1) = δ x ^ (s₀.re - 2) * δ x := by
      rw [← Real.rpow_add_one h0.ne']; ring_nf
    have hp2 : 0 ≤ δ x ^ (s₀.re - 2) := Real.rpow_nonneg h0.le _
    have e3 : δ x ^ s.re * |Real.log (δ x)| ≤ δ x ^ (s₀.re - 2) := by
      calc δ x ^ s.re * |Real.log (δ x)| ≤ δ x ^ (s₀.re - 1) * |Real.log (δ x)| :=
            mul_le_mul_of_nonneg_right e1 (abs_nonneg _)
        _ = δ x ^ (s₀.re - 2) * (|Real.log (δ x)| * δ x) := by rw [e2]; ring
        _ ≤ δ x ^ (s₀.re - 2) * 1 := mul_le_mul_of_nonneg_left hl.le hp2
        _ = δ x ^ (s₀.re - 2) := mul_one _
    rw [norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos h0, hlog]
    calc ‖F x‖ * (δ x ^ s.re * |Real.log (δ x)|) ≤ ‖F x‖ * δ x ^ (s₀.re - 2) :=
          mul_le_mul_of_nonneg_left e3 (norm_nonneg _)
      _ ≤ C * δ x := hx
  · filter_upwards [hδ] with x hx' s _
    exact ((Complex.hasStrictDerivAt_const_cpow (x := (δ x : ℂ)) (y := s)
      (Or.inl (Complex.ofReal_ne_zero.mpr hx'.1.ne'))).hasDerivAt).const_mul (F x)

end GlobalTheory
