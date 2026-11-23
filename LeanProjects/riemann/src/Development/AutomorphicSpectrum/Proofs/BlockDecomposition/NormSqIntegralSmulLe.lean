import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsNormEmbId

open MeasureTheory GlobalTheory.CompanionTheory.UnitaryFramesMetricPeriods
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.CompanionTheory.Godement

section Unitary

variable {Γ : Type} [Group Γ] [TopologicalSpace Γ] {B : Type} [NormedAddCommGroup B] [InnerProductSpace ℂ B]

theorem inner_map {ρ : Γ → (B →L[ℂ] B)} (hU : IsU ρ) (g : Γ) (x y : B) : ⟪ρ g x, ρ g y⟫_ℂ = ⟪x, y⟫_ℂ := by
  obtain ⟨-, -, hnorm, -⟩ := hU
  exact (LinearIsometry.mk (ρ g : B →ₗ[ℂ] B) (hnorm g)).inner_map_map x y

theorem inner_orbit {ρ : Γ → (B →L[ℂ] B)} (hU : IsU ρ) (v : B) (g h : Γ) :
    ⟪ρ g v, ρ h v⟫_ℂ = ⟪v, ρ (g⁻¹ * h) v⟫_ℂ := by
  rw [← GlobalTheory.CompanionTheory.Godement.inner_map hU g v (ρ (g⁻¹ * h) v)]
  obtain ⟨-, hmul, -, -⟩ := hU
  congr 1
  calc ρ h v = ρ (g * (g⁻¹ * h)) v := by rw [mul_inv_cancel_left]
    _ = ρ g (ρ (g⁻¹ * h) v) := by rw [hmul g (g⁻¹ * h), ContinuousLinearMap.mul_apply]

end Unitary

theorem mul_le_half_add (a b : ℝ≥0∞) : a * b ≤ 2⁻¹ * (a ^ 2 + b ^ 2) := by
  have h := ENNReal.young_inequality a b Real.HolderConjugate.two_two
  rw [ENNReal.rpow_two, ENNReal.rpow_two, ENNReal.ofReal_ofNat] at h
  calc a * b ≤ a ^ 2 / 2 + b ^ 2 / 2 := h
    _ = 2⁻¹ * (a ^ 2 + b ^ 2) := by
      rw [div_eq_mul_inv, div_eq_mul_inv, mul_comm (a ^ 2), mul_comm (b ^ 2), mul_add]

theorem norm_sq_integral_smul_le : ∀ {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [LocallyCompactSpace Γ]
    [SecondCountableTopology Γ] [MeasurableSpace Γ] [BorelSpace Γ] (ν : Measure Γ) [ν.IsHaarMeasure] [ν.IsMulRightInvariant]
    {B : Type} [NormedAddCommGroup B] [InnerProductSpace ℂ B] [CompleteSpace B] (ρ : Γ → (B →L[ℂ] B)), IsU ρ → ∀ v : B, Integrable (fun g => ⟪v, ρ g v⟫_ℂ) ν → ∀ f : Γ → ℂ, Measurable f → Integrable f ν →
    Integrable (fun g => ‖f g‖ ^ 2) ν →
    ‖∫ g, f g • ρ g v ∂ν‖ ^ 2 ≤ (∫ g, ‖f g‖ ^ 2 ∂ν) * ∫ g, ‖⟪v, ρ g v⟫_ℂ‖ ∂ν := by
  intro Γ _ _ _ _ _ _ _ ν _ _ B _ _ _ ρ hU v hφ f hf hfi hf2
  obtain ⟨-, -, -, hcont⟩ := id hU
  have hA : 0 ≤ ∫ g, ‖f g‖ ^ 2 ∂ν := integral_nonneg fun g => sq_nonneg _
  have hB : 0 ≤ ∫ g, ‖⟪v, ρ g v⟫_ℂ‖ ∂ν := integral_nonneg fun g => norm_nonneg _
  by_cases hF : Integrable (fun g => f g • ρ g v) ν
  swap
  · rw [integral_undef hF, norm_zero, zero_pow two_ne_zero]
    exact mul_nonneg hA hB
  have hψc : Continuous fun x : Γ => ‖⟪v, ρ x v⟫_ℂ‖ₑ := (continuous_const.inner (hcont v)).enorm
  have hψ : Measurable fun x : Γ => ‖⟪v, ρ x v⟫_ℂ‖ₑ := hψc.measurable
  have hfe : Measurable fun g : Γ => ‖f g‖ₑ ^ 2 := hf.enorm.pow_const 2
  have hswap : ∀ g h : Γ, ‖⟪v, ρ (h⁻¹ * g) v⟫_ℂ‖ₑ = ‖⟪v, ρ (g⁻¹ * h) v⟫_ℂ‖ₑ := by
    intro g h
    rw [← GlobalTheory.CompanionTheory.Godement.inner_orbit hU v h g, ← GlobalTheory.CompanionTheory.Godement.inner_orbit hU v g h,
      ← inner_conj_symm (ρ h v) (ρ g v), RCLike.enorm_conj]
  have hswapm : AEMeasurable (Function.uncurry fun h g : Γ =>
      2⁻¹ * (‖f g‖ₑ ^ 2 * ‖⟪v, ρ (h⁻¹ * g) v⟫_ℂ‖ₑ)) (ν.prod ν) := by
    apply Measurable.aemeasurable
    exact measurable_const.mul ((hfe.comp measurable_snd).mul
      (hψ.comp (measurable_fst.inv.mul measurable_snd)))
  have hm3 : Measurable fun h => 2⁻¹ * ‖f h‖ₑ ^ 2 * ∫⁻ x, ‖⟪v, ρ x v⟫_ℂ‖ₑ ∂ν :=
    (measurable_const.mul hfe).mul_const _
  have hm4 : Measurable fun h => 2⁻¹ * ‖f h‖ₑ ^ 2 := measurable_const.mul hfe
  have hII : ⟪∫ g, f g • ρ g v ∂ν, ∫ g, f g • ρ g v ∂ν⟫_ℂ =
      ∫ h, f h * starRingEnd ℂ (∫ g, f g * ⟪ρ h v, ρ g v⟫_ℂ ∂ν) ∂ν := by
    rw [← integral_inner hF]
    refine integral_congr_ae ?_
    filter_upwards with h
    rw [inner_smul_right, ← inner_conj_symm, ← integral_inner hF]
    simp only [inner_smul_right]
  have key : ‖⟪∫ g, f g • ρ g v ∂ν, ∫ g, f g • ρ g v ∂ν⟫_ℂ‖ₑ ≤
      (∫⁻ g, ‖f g‖ₑ ^ 2 ∂ν) * ∫⁻ x, ‖⟪v, ρ x v⟫_ℂ‖ₑ ∂ν := by
    rw [hII]
    calc ‖∫ h, f h * starRingEnd ℂ (∫ g, f g * ⟪ρ h v, ρ g v⟫_ℂ ∂ν) ∂ν‖ₑ
        ≤ ∫⁻ h, ‖f h * starRingEnd ℂ (∫ g, f g * ⟪ρ h v, ρ g v⟫_ℂ ∂ν)‖ₑ ∂ν :=
          enorm_integral_le_lintegral_enorm _
      _ ≤ ∫⁻ h, ∫⁻ g, 2⁻¹ * (‖f h‖ₑ ^ 2 + ‖f g‖ₑ ^ 2) * ‖⟪v, ρ (h⁻¹ * g) v⟫_ℂ‖ₑ ∂ν ∂ν := by
          refine lintegral_mono fun h => ?_
          beta_reduce
          rw [enorm_mul, RCLike.enorm_conj]
          calc ‖f h‖ₑ * ‖∫ g, f g * ⟪ρ h v, ρ g v⟫_ℂ ∂ν‖ₑ
              ≤ ‖f h‖ₑ * ∫⁻ g, ‖f g * ⟪ρ h v, ρ g v⟫_ℂ‖ₑ ∂ν := by
                gcongr
                exact enorm_integral_le_lintegral_enorm _
            _ ≤ ∫⁻ g, ‖f h‖ₑ * ‖f g * ⟪ρ h v, ρ g v⟫_ℂ‖ₑ ∂ν := lintegral_const_mul_le _ _
            _ ≤ _ := by
                refine lintegral_mono fun g => ?_
                beta_reduce
                rw [enorm_mul, GlobalTheory.CompanionTheory.Godement.inner_orbit hU, ← mul_assoc]
                gcongr ?_ * _
                exact GlobalTheory.CompanionTheory.Godement.mul_le_half_add _ _
      _ = ∫⁻ h, (2⁻¹ * ‖f h‖ₑ ^ 2 * ∫⁻ x, ‖⟪v, ρ x v⟫_ℂ‖ₑ ∂ν +
            ∫⁻ g, 2⁻¹ * (‖f g‖ₑ ^ 2 * ‖⟪v, ρ (h⁻¹ * g) v⟫_ℂ‖ₑ) ∂ν) ∂ν := by
          refine lintegral_congr fun h => ?_
          have hm : Measurable fun g => ‖⟪v, ρ (h⁻¹ * g) v⟫_ℂ‖ₑ := hψ.comp (measurable_const_mul h⁻¹)
          have hm2 : Measurable fun g => 2⁻¹ * ‖f h‖ₑ ^ 2 * ‖⟪v, ρ (h⁻¹ * g) v⟫_ℂ‖ₑ :=
            measurable_const.mul hm
          calc ∫⁻ g, 2⁻¹ * (‖f h‖ₑ ^ 2 + ‖f g‖ₑ ^ 2) * ‖⟪v, ρ (h⁻¹ * g) v⟫_ℂ‖ₑ ∂ν
              = ∫⁻ g, (2⁻¹ * ‖f h‖ₑ ^ 2 * ‖⟪v, ρ (h⁻¹ * g) v⟫_ℂ‖ₑ +
                  2⁻¹ * (‖f g‖ₑ ^ 2 * ‖⟪v, ρ (h⁻¹ * g) v⟫_ℂ‖ₑ)) ∂ν :=
                lintegral_congr fun g => by ring
            _ = ∫⁻ g, 2⁻¹ * ‖f h‖ₑ ^ 2 * ‖⟪v, ρ (h⁻¹ * g) v⟫_ℂ‖ₑ ∂ν +
                  ∫⁻ g, 2⁻¹ * (‖f g‖ₑ ^ 2 * ‖⟪v, ρ (h⁻¹ * g) v⟫_ℂ‖ₑ) ∂ν :=
                lintegral_add_left hm2 _
            _ = _ := by
                rw [lintegral_const_mul _ hm,
                  lintegral_mul_left_eq_self (fun x => ‖⟪v, ρ x v⟫_ℂ‖ₑ) h⁻¹]
      _ = (∫⁻ h, 2⁻¹ * ‖f h‖ₑ ^ 2 * ∫⁻ x, ‖⟪v, ρ x v⟫_ℂ‖ₑ ∂ν ∂ν) +
            ∫⁻ h, ∫⁻ g, 2⁻¹ * (‖f g‖ₑ ^ 2 * ‖⟪v, ρ (h⁻¹ * g) v⟫_ℂ‖ₑ) ∂ν ∂ν :=
          lintegral_add_left hm3 _
      _ = 2⁻¹ * (∫⁻ g, ‖f g‖ₑ ^ 2 ∂ν) * (∫⁻ x, ‖⟪v, ρ x v⟫_ℂ‖ₑ ∂ν) +
            2⁻¹ * (∫⁻ g, ‖f g‖ₑ ^ 2 ∂ν) * (∫⁻ x, ‖⟪v, ρ x v⟫_ℂ‖ₑ ∂ν) := by
          congr 1
          · rw [lintegral_mul_const _ hm4, lintegral_const_mul _ hfe]
          · rw [lintegral_lintegral_swap hswapm]
            calc ∫⁻ g, ∫⁻ h, 2⁻¹ * (‖f g‖ₑ ^ 2 * ‖⟪v, ρ (h⁻¹ * g) v⟫_ℂ‖ₑ) ∂ν ∂ν
                = ∫⁻ g, 2⁻¹ * ‖f g‖ₑ ^ 2 * ∫⁻ x, ‖⟪v, ρ x v⟫_ℂ‖ₑ ∂ν ∂ν := by
                  refine lintegral_congr fun g => ?_
                  have hm : Measurable fun h => ‖⟪v, ρ (g⁻¹ * h) v⟫_ℂ‖ₑ :=
                    hψ.comp (measurable_const_mul g⁻¹)
                  simp_rw [hswap g]
                  rw [← lintegral_mul_left_eq_self (fun x => ‖⟪v, ρ x v⟫_ℂ‖ₑ) g⁻¹,
                    ← lintegral_const_mul _ hm]
                  exact lintegral_congr fun h => by ring
              _ = _ := by
                  rw [lintegral_mul_const _ hm4, lintegral_const_mul _ hfe]
      _ = (∫⁻ g, ‖f g‖ₑ ^ 2 ∂ν) * ∫⁻ x, ‖⟪v, ρ x v⟫_ℂ‖ₑ ∂ν := by
          rw [← two_mul, ← mul_assoc, ← mul_assoc,
            ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_mul]
  have hX : ENNReal.ofReal (∫ g, ‖f g‖ ^ 2 ∂ν) = ∫⁻ g, ‖f g‖ₑ ^ 2 ∂ν := by
    rw [ofReal_integral_eq_lintegral_ofReal hf2 (Filter.Eventually.of_forall fun g => sq_nonneg _)]
    refine lintegral_congr fun g => ?_
    rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm_eq_enorm]
  have hY : ENNReal.ofReal (∫ g, ‖⟪v, ρ g v⟫_ℂ‖ ∂ν) = ∫⁻ x, ‖⟪v, ρ x v⟫_ℂ‖ₑ ∂ν := by
    rw [ofReal_integral_eq_lintegral_ofReal hφ.norm (Filter.Eventually.of_forall fun g => norm_nonneg _)]
    exact lintegral_congr fun g => ofReal_norm_eq_enorm _
  have hL : ‖∫ g, f g • ρ g v ∂ν‖ ^ 2 = ‖⟪∫ g, f g • ρ g v ∂ν, ∫ g, f g • ρ g v ∂ν⟫_ℂ‖ := by
    rw [inner_self_eq_norm_sq_to_K]
    simp
  rw [hL, ← ENNReal.ofReal_le_ofReal_iff (mul_nonneg hA hB), ENNReal.ofReal_mul hA, hX, hY,
    ofReal_norm_eq_enorm]
  exact key

end GlobalTheory.CompanionTheory.Godement
