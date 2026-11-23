import Mathlib
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.EffectiveHS

open MeasureTheory Set Filter Topology
open scoped ENNReal

noncomputable section

namespace DivisionNearS

theorem exists_bound_of_iteratedFDeriv_eq_zero {D : ℕ} {f : (Fin D → ℂ) → ℂ}
    {w₀ : Fin D → ℂ} (hf : AnalyticAt ℂ f w₀) (m : ℕ)
    (h0 : ∀ k < m, iteratedFDeriv ℂ k f w₀ = 0) :
    ∃ C : ℝ, ∀ᶠ w in 𝓝 w₀, ‖f w‖ ≤ C * ‖w - w₀‖ ^ m := by
  obtain ⟨p, r, hp⟩ := hf
  have hps : ∀ y, p.partialSum m y = 0 := by
    intro y
    refine Finset.sum_eq_zero fun k hk => ?_
    have h1 := hp.factorial_smul y k
    rw [h0 k (Finset.mem_range.mp hk)] at h1
    have h2 : (k.factorial : ℂ) • p k (fun _ => y) = 0 := by
      rw [Nat.cast_smul_eq_nsmul]; simpa using h1
    exact (smul_eq_zero.mp h2).resolve_left (by exact_mod_cast k.factorial_ne_zero)
  obtain ⟨C, hC⟩ := (hp.hasFPowerSeriesAt.isBigO_sub_partialSum_pow m).bound
  refine ⟨C, ?_⟩
  have ht : Tendsto (fun w => w - w₀) (𝓝 w₀) (𝓝 0) := by
    simpa using (tendsto_id.sub_const w₀ : Tendsto (fun w => w - w₀) (𝓝 w₀) (𝓝 (w₀ - w₀)))
  filter_upwards [ht.eventually hC] with w hw
  simpa [hps, norm_pow, norm_norm] using hw

theorem exists_lowerBound_of_det_ne_zero {D : ℕ} {σ : (Fin D → ℂ) → (Fin D → ℂ)}
    {L : (Fin D → ℂ) →L[ℂ] (Fin D → ℂ)} {w₀ : Fin D → ℂ} (hσ : HasFDerivAt σ L w₀)
    (hL : LinearMap.det (L : (Fin D → ℂ) →ₗ[ℂ] (Fin D → ℂ)) ≠ 0) (h0 : σ w₀ = 0) :
    ∃ κ > (0 : ℝ), ∀ᶠ w in 𝓝 w₀, κ * ‖w - w₀‖ ≤ ‖σ w‖ := by
  have hu : IsUnit (L : (Fin D → ℂ) →ₗ[ℂ] (Fin D → ℂ)) :=
    (LinearMap.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hL)
  have hinj : Function.Injective (L : (Fin D → ℂ) →ₗ[ℂ] (Fin D → ℂ)) :=
    ((Module.End.isUnit_iff _).mp hu).injective
  obtain ⟨K, hK0, hK⟩ :=
    (L : (Fin D → ℂ) →ₗ[ℂ] (Fin D → ℂ)).exists_antilipschitzWith (LinearMap.ker_eq_bot.mpr hinj)
  have hb : ∀ v, ‖v‖ ≤ K * ‖L v‖ := fun v =>
    ZeroHomClass.bound_of_antilipschitz (L : (Fin D → ℂ) →ₗ[ℂ] (Fin D → ℂ)) hK v
  have hKpos : (0 : ℝ) < K := by exact_mod_cast hK0
  have hε := hσ.isLittleO.bound (c := 1 / (2 * K)) (by positivity)
  refine ⟨1 / (2 * K), by positivity, ?_⟩
  filter_upwards [hε] with w hw
  rw [h0, sub_zero] at hw
  have h2 : ‖L (w - w₀)‖ ≤ ‖σ w‖ + 1 / (2 * K) * ‖w - w₀‖ := by
    calc ‖L (w - w₀)‖ = ‖σ w - (σ w - L (w - w₀))‖ := by congr 1; abel
      _ ≤ ‖σ w‖ + ‖σ w - L (w - w₀)‖ := norm_sub_le _ _
      _ ≤ _ := by gcongr
  have h3 : ‖w - w₀‖ ≤ K * ‖σ w‖ + ‖w - w₀‖ / 2 := by
    calc ‖w - w₀‖ ≤ K * ‖L (w - w₀)‖ := hb _
      _ ≤ K * (‖σ w‖ + 1 / (2 * K) * ‖w - w₀‖) := by gcongr
      _ = K * ‖σ w‖ + ‖w - w₀‖ / 2 := by field_simp
  have h4 : ‖w - w₀‖ ≤ 2 * K * ‖σ w‖ := by linarith
  calc 1 / (2 * K) * ‖w - w₀‖ ≤ 1 / (2 * K) * (2 * K * ‖σ w‖) := by gcongr
    _ = ‖σ w‖ := by field_simp

theorem finrank_real_fin_complex (D : ℕ) : Module.finrank ℝ (Fin D → ℂ) = 2 * D := by
  rw [Module.finrank_pi_fintype]
  simp [Complex.finrank_real_complex, mul_comm]

theorem lintegral_ball_rpow_lt_top {D : ℕ} (hD : 1 ≤ D) (w₀ : Fin D → ℂ) (ε a : ℝ)
    (ha : -(2 * D : ℝ) < a) :
    ∫⁻ w in Metric.ball w₀ ε, ENNReal.ofReal (‖w - w₀‖ ^ a) < ⊤ := by
  have : Nonempty (Fin D) := ⟨⟨0, hD⟩⟩
  have hint : IntegrableOn (fun x : Fin D → ℂ => ‖x‖ ^ a) (Metric.ball 0 ε) volume := by
    rw [integrableOn_fun_norm_addHaar volume (f := fun y : ℝ => y ^ a), finrank_real_fin_complex]
    have hr : -1 < ((2 * D - 1 : ℕ) : ℝ) + a := by
      have : ((2 * D - 1 : ℕ) : ℝ) = 2 * D - 1 := by
        rw [Nat.cast_sub (by omega)]; push_cast; ring
      rw [this]; linarith
    have hII := intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := ε) hr
    rcases le_or_gt ε 0 with hε | hε
    · simp [Ioo_eq_empty (not_lt.mpr hε)]
    · have hon : IntegrableOn (fun y : ℝ => y ^ (((2 * D - 1 : ℕ) : ℝ) + a)) (Ioo 0 ε) :=
        ((intervalIntegrable_iff_integrableOn_Ioc_of_le hε.le).mp hII).mono_set Ioo_subset_Ioc_self
      refine (integrableOn_congr_fun (fun y hy => ?_) measurableSet_Ioo).mp hon
      simp only [smul_eq_mul]
      rw [Real.rpow_add hy.1, Real.rpow_natCast]
  have h1 := hint.lintegral_lt_top
  have h2 : ∫⁻ w in Metric.ball w₀ ε, ENNReal.ofReal (‖w - w₀‖ ^ a) =
      ∫⁻ y in Metric.ball (0 : Fin D → ℂ) ε, ENNReal.ofReal (‖y‖ ^ a) := by
    rw [← lintegral_indicator measurableSet_ball, ← lintegral_indicator measurableSet_ball]
    rw [← lintegral_sub_right_eq_self (fun y => (Metric.ball (0 : Fin D → ℂ) ε).indicator
      (fun y => ENNReal.ofReal (‖y‖ ^ a)) y) w₀]
    congr 1
    funext w
    simp only [indicator, Metric.mem_ball, dist_eq_norm, sub_zero]
  rw [h2]; exact h1

end DivisionNearS

end

end GroundTheory.Heights₂.Heights.EffectiveHS
