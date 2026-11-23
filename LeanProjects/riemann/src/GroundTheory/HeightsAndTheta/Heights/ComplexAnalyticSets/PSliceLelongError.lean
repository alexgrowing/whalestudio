import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSliceLelongError
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSliceCutChain
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSliceWeightBound
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSliceBandEnergy
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Filter Topology Matrix

noncomputable section

namespace SliceLelongError

theorem deriv_smoothTransition_eq_zero {s : ℝ} (hs : s < 0 ∨ 1 < s) :
    deriv Real.smoothTransition s = 0 ∧ deriv (deriv Real.smoothTransition) s = 0 := by
  have hloc : deriv Real.smoothTransition =ᶠ[𝓝 s] fun _ => (0 : ℝ) := by
    rcases hs with hs | hs
    · filter_upwards [Iio_mem_nhds hs] with r hr
      have hc : Real.smoothTransition =ᶠ[𝓝 r] fun _ => (0 : ℝ) := by
        filter_upwards [Iio_mem_nhds (show r < 0 from hr)] with q hq
        exact Real.smoothTransition.zero_of_nonpos (le_of_lt hq)
      rw [hc.deriv_eq, deriv_const]
    · filter_upwards [Ioi_mem_nhds hs] with r hr
      have hc : Real.smoothTransition =ᶠ[𝓝 r] fun _ => (1 : ℝ) := by
        filter_upwards [Ioi_mem_nhds (show 1 < r from hr)] with q hq
        exact Real.smoothTransition.one_of_one_le (le_of_lt hq)
      rw [hc.deriv_eq, deriv_const]
  exact ⟨hloc.eq_of_nhds, by rw [hloc.deriv_eq, deriv_const]⟩

theorem continuous_derivs :
    Continuous (deriv Real.smoothTransition) ∧ Continuous (deriv (deriv Real.smoothTransition)) := by
  have h1 := contDiff_infty_iff_deriv.mp (Real.smoothTransition.contDiff (n := ⊤))
  exact ⟨h1.2.continuous, (contDiff_infty_iff_deriv.mp h1.2).2.continuous⟩

theorem exists_bound_derivs : ∃ M₁ M₂ : ℝ, (∀ s, |deriv Real.smoothTransition s| ≤ M₁) ∧
    ∀ s, |deriv (deriv Real.smoothTransition) s| ≤ M₂ := by
  have hsupp : ∀ f : ℝ → ℝ, (∀ s, s < 0 ∨ 1 < s → f s = 0) → HasCompactSupport f := fun f hf =>
    HasCompactSupport.intro (isCompact_Icc (a := (0 : ℝ)) (b := 1)) fun s hs => hf s (by
      rw [Set.mem_Icc, not_and_or, not_le, not_le] at hs; exact hs)
  obtain ⟨M₁, hM₁⟩ := continuous_derivs.1.bounded_above_of_compact_support
    (hsupp _ fun s hs => (deriv_smoothTransition_eq_zero hs).1)
  obtain ⟨M₂, hM₂⟩ := continuous_derivs.2.bounded_above_of_compact_support
    (hsupp _ fun s hs => (deriv_smoothTransition_eq_zero hs).2)
  exact ⟨M₁, M₂, fun s => by simpa [Real.norm_eq_abs] using hM₁ s,
    fun s => by simpa [Real.norm_eq_abs] using hM₂ s⟩

theorem bound_aux {P Q A B k : ℝ} (hk : 0 ≤ k) (hP : |P| ≤ A)
    (hQ : |Q| ≤ B * (2 * (k + 1) - (k + 1) + 1)) :
    |-(k + 1)⁻¹ * P + (k + 1)⁻¹ ^ 2 * Q| ≤ (|A| + 2 * |B|) / (k + 1) := by
  have hk1 : 0 < k + 1 := by linarith
  have ha : 0 < (k + 1)⁻¹ := inv_pos.mpr hk1
  have ha1 : (k + 1)⁻¹ * (k + 1) = 1 := inv_mul_cancel₀ hk1.ne'
  have hale : (k + 1)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith)
  have hP' : |P| ≤ |A| := hP.trans (le_abs_self A)
  have hQ' : |Q| ≤ |B| * (k + 2) := hQ.trans (by
    rw [show 2 * (k + 1) - (k + 1) + 1 = k + 2 by ring]
    exact mul_le_mul_of_nonneg_right (le_abs_self B) (by linarith))
  have key : (k + 1)⁻¹ ^ 2 * (k + 2) ≤ 2 * (k + 1)⁻¹ := by nlinarith
  calc |-(k + 1)⁻¹ * P + (k + 1)⁻¹ ^ 2 * Q|
      ≤ (k + 1)⁻¹ * |P| + (k + 1)⁻¹ ^ 2 * |Q| := by
        refine (abs_add_le _ _).trans (le_of_eq ?_)
        rw [abs_mul, abs_mul, abs_neg, abs_of_pos ha, abs_of_pos (pow_pos ha 2)]
    _ ≤ (k + 1)⁻¹ * |A| + (k + 1)⁻¹ ^ 2 * (|B| * (k + 2)) := by gcongr
    _ ≤ (|A| + 2 * |B|) / (k + 1) := by
        rw [div_eq_mul_inv]
        nlinarith [mul_le_mul_of_nonneg_left key (abs_nonneg B), abs_nonneg A]

theorem proof (h₁ : SliceCutChain.Statement) (h₂ : SliceWeightBound.Statement)
    (h₃ : SliceBandEnergy.Statement) : SliceLelongError.Statement := by
  intro n e h J F u ℓ hJ hF hu hℓ hℓW
  obtain ⟨M₁, M₂, hM₁, hM₂⟩ := exists_bound_derivs
  obtain ⟨C₂, hC₂⟩ := h₂ n e h J F u ℓ hJ hF hu hℓ
  obtain ⟨C₃, hC₃⟩ := h₃ n e h J F u ℓ hJ hF hu hℓ hℓW
  have hL : Measurable fun x : Fin n → ℂ => Real.log (h.dualNorm x) :=
    Real.measurable_log.comp (SliceCut.continuous_dualNorm h).measurable
  refine squeeze_zero_norm (a := fun k : ℕ => (|C₂ * M₁| + 2 * |C₃ * M₂|) / ((k : ℝ) + 1))
    (fun k => ?_) (tendsto_const_nhds.div_atTop
      (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds))
  have hk : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hw : Measurable fun x : Fin n → ℂ => 2 - Real.log (h.dualNorm x) / ((k : ℝ) + 1) :=
    measurable_const.sub (hL.div_const _)
  have e1 := hC₂ (fun x => deriv Real.smoothTransition (2 - Real.log (h.dualNorm x) / ((k : ℝ) + 1))) M₁
    (continuous_derivs.1.measurable.comp hw) fun x => hM₁ _
  have e2 := hC₃
    (fun x => deriv (deriv Real.smoothTransition) (2 - Real.log (h.dualNorm x) / ((k : ℝ) + 1))) M₂
    ((k : ℝ) + 1) (2 * ((k : ℝ) + 1)) (continuous_derivs.2.measurable.comp hw) (fun x => hM₂ _)
    (by linarith) fun x hx => by
      by_contra hb
      rw [not_and_or, not_le, not_le] at hb
      refine hx (deriv_smoothTransition_eq_zero ?_).2
      rcases hb with hb | hb
      · have : Real.log (h.dualNorm x) / ((k : ℝ) + 1) < 1 := (div_lt_one hk).mpr hb
        right; linarith
      · have : 2 < Real.log (h.dualNorm x) / ((k : ℝ) + 1) := (lt_div_iff₀ hk).mpr hb
        left; linarith
  rw [Real.norm_eq_abs, h₁ n e h J F u ℓ k hJ hF hu hℓ]
  exact bound_aux (Nat.cast_nonneg k) e1 e2

end SliceLelongError

end

end GroundTheory.Heights₂.Heights
