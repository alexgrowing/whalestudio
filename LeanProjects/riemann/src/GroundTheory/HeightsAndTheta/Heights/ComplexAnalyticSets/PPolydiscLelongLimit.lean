import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StPolydiscLelongLimit
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.ProjectiveLineZeroFormHolds
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.HessCRestrictThm
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.ContDiffOfContDiffOnZeroOff
import ReciprocityTheory.AnalyticForms.AnalyticCharts.Osgood
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A
open scoped ContDiff

noncomputable section

namespace PolydiscLelongLimit

theorem hypIncl_mem_ball {d : ℕ} {r : ℝ} (w : Fin d → ℂ) :
    hypIncl w ∈ Metric.ball (0 : Fin (d + 1) → ℂ) r ↔ w ∈ Metric.ball 0 r := by
  rcases le_or_gt r 0 with hr | hr
  · simp [Metric.ball_eq_empty.2 hr]
  · simp only [mem_ball_zero_iff, pi_norm_lt_iff hr, Fin.forall_fin_succ, hypIncl, Fin.cons_zero,
      Fin.cons_succ, norm_zero, hr, true_and]

theorem extend_by_zero {D : ℕ} {r ρ : ℝ} {χ : (Fin D → ℂ) → ℝ} (hρ : ρ < r)
    (hχ : ContDiffOn ℝ ∞ χ (Metric.ball 0 r))
    (hsupp : ∀ τ ∈ Metric.ball (0 : Fin D → ℂ) r, χ τ ≠ 0 → τ ∈ Metric.ball 0 ρ) :
    ContDiff ℝ ∞ ((Metric.ball (0 : Fin D → ℂ) r).indicator χ) ∧
      HasCompactSupport ((Metric.ball (0 : Fin D → ℂ) r).indicator χ) ∧
      tsupport ((Metric.ball (0 : Fin D → ℂ) r).indicator χ) ⊆ Metric.closedBall 0 ρ ∧
      Set.EqOn ((Metric.ball (0 : Fin D → ℂ) r).indicator χ) χ (Metric.ball 0 r) := by
  have h0 : ∀ τ ∉ Metric.closedBall (0 : Fin D → ℂ) ρ,
      (Metric.ball (0 : Fin D → ℂ) r).indicator χ τ = 0 := by
    intro τ hτ
    by_cases hU : τ ∈ Metric.ball (0 : Fin D → ℂ) r
    · rw [Set.indicator_of_mem hU]
      by_contra h
      exact hτ (Metric.ball_subset_closedBall (hsupp τ hU h))
    · exact Set.indicator_of_notMem hU _
  have heq : Set.EqOn ((Metric.ball (0 : Fin D → ℂ) r).indicator χ) χ (Metric.ball 0 r) :=
    fun τ hτ => Set.indicator_of_mem hτ _
  exact ⟨contDiff_of_contDiffOn_zero_off Metric.isOpen_ball Metric.isClosed_closedBall
    (Metric.closedBall_subset_ball hρ) (hχ.congr heq) h0,
    HasCompactSupport.intro (isCompact_closedBall 0 ρ) h0,
    closure_minimal (fun τ hτ => by_contra fun h => (Function.mem_support.1 hτ) (h0 τ h))
      Metric.isClosed_closedBall, heq⟩

theorem logReg_contDiffOn {D : ℕ} {U : Set (Fin D → ℂ)} (hU : IsOpen U) {F : (Fin D → ℂ) → ℂ}
    (hF : DifferentiableOn ℂ F U) {ε : ℝ} (hε : 0 < ε) :
    ContDiffOn ℝ ∞ (fun τ => Real.log (‖F τ‖ ^ 2 + ε) / 2) U := by
  intro z hz
  have h1 : ContDiffAt ℝ ∞ F z :=
    ((ReciprocityTheory.AnForm.Osgood.osgood D U F hU hF z hz).contDiffAt (n := ∞)).restrict_scalars ℝ
  have h2 : ContDiffAt ℝ ∞ (fun τ => ‖F τ‖ ^ 2 + ε) z := (h1.norm_sq ℝ).add contDiffAt_const
  exact ((h2.log (by positivity)).div_const 2).contDiffWithinAt

end PolydiscLelongLimit

open PolydiscLelongLimit in

theorem PolydiscLelongLimit.proof : PolydiscLelongLimit.Statement := by
  intro d m r ρ F χ ψ hρ hF hχ hsupp hψ
  obtain ⟨H, hHd, hH0, hFH⟩ := hF
  have h3 : (3 : WithTop ℕ∞) ≤ ∞ := WithTop.coe_le_coe.2 le_top
  obtain ⟨hv, hvc, hvt, hvχ⟩ := extend_by_zero hρ hχ hsupp
  set U : Set (Fin (d + 1) → ℂ) := Metric.ball 0 r with hUdef
  set v := U.indicator χ with hvdef
  have hU : IsOpen U := Metric.isOpen_ball
  have hvU : tsupport v ⊆ U := hvt.trans (Metric.closedBall_subset_ball hρ)
  have hFd : DifferentiableOn ℂ F U :=
    (((differentiable_apply 0).pow m).differentiableOn.mul hHd).congr fun t ht => hFH t ht
  have hFne : ∀ τ ∈ U, τ 0 ≠ 0 → F τ ≠ 0 := fun τ hτ h0 => by
    rw [hFH τ hτ]; exact mul_ne_zero (pow_ne_zero _ h0) (hH0 τ hτ)
  have hdens0 : ∀ τ, τ ∉ tsupport v → densV v ψ τ = 0 := fun τ hτ => maDens_cons_eq_zero ψ hτ
  have hIon : ∀ f : (Fin (d + 1) → ℂ) → ℝ, IntegrableOn (fun z => f z * densV v ψ z) U →
      Integrable (fun z => f z * densV v ψ z) := fun f h =>
    (integrableOn_iff_integrable_of_support_subset fun z hz => by_contra fun h' =>
      (Function.mem_support.1 hz) (mul_eq_zero_of_right _ (hdens0 z fun h'' => h' (hvU h'')))).1 h

  have hgood : ∀ ε : ℝ, 0 < ε →
      Integrable (fun τ => Real.log (‖F τ‖ ^ 2 + ε) / 2 * densV v ψ τ) ∧
      maInt (Matrix.vecCons (fun τ => Real.log (‖F τ‖ ^ 2 + ε) / 2) ψ) χ U =
        ∫ τ, Real.log (‖F τ‖ ^ 2 + ε) / 2 * densV v ψ τ := by
    intro ε hε
    have hP := parts_thm d ψ v (fun τ => Real.log (‖F τ‖ ^ 2 + ε) / 2) U
      ⟨hU, (hv.of_le h3).contDiffOn, hvc, hvU, (logReg_contDiffOn hU hFd hε).of_le h3,
        fun k => (hψ k).of_le h3⟩
    refine ⟨hIon _ hP.2.1, ?_⟩
    calc maInt (Matrix.vecCons (fun τ => Real.log (‖F τ‖ ^ 2 + ε) / 2) ψ) χ U
        = maInt (Fin.cons (fun τ => Real.log (‖F τ‖ ^ 2 + ε) / 2) ψ) v U := by
          unfold maInt
          exact setIntegral_congr_fun hU.measurableSet fun τ hτ => by
            simp only [hvχ hτ]; try rfl
      _ = maInt (Fin.cons v ψ) (fun τ => Real.log (‖F τ‖ ^ 2 + ε) / 2) U := hP.2.2.2.2.symm
      _ = ∫ τ, Real.log (‖F τ‖ ^ 2 + ε) / 2 * densV v ψ τ := by
          unfold maInt
          exact setIntegral_eq_integral_of_forall_compl_eq_zero fun τ hτ =>
            mul_eq_zero_of_right _ (hdens0 τ fun h => hτ (hvU h))

  have hL0 := log_norm_integral_formula_unit d (m : ℤ) U v ψ H ⟨hU, hv.of_le h3, hvc, hvU, hψ⟩ hHd hH0
  have hlogF : (fun z => Real.log ‖F z‖ * densV v ψ z) =
      fun z => Real.log ‖z 0 ^ (m : ℤ) * H z‖ * densV v ψ z := by
    funext z
    by_cases hz : z ∈ U
    · rw [hFH z hz, zpow_natCast]
    · rw [hdens0 z fun h => hz (hvU h), mul_zero, mul_zero]
  have hint : Integrable (fun τ => Real.log ‖F τ‖ * densV v ψ τ) := by rw [hlogF]; exact hL0.1
  have hdensI : Integrable (densV v ψ) := by
    have hP1 := parts_thm d ψ v (fun _ => (1 : ℝ)) U
      ⟨hU, (hv.of_le h3).contDiffOn, hvc, hvU, contDiffOn_const, fun k => (hψ k).of_le h3⟩
    exact (hIon (fun _ => 1) hP1.2.1).congr (Eventually.of_forall fun z => one_mul _)
  obtain ⟨C, hC⟩ : ∃ C, ∀ τ ∈ tsupport v, ‖(1 / 2 : ℝ) * Real.log (‖F τ‖ ^ 2 + 1)‖ ≤ C :=
    hvc.isCompact.exists_bound_of_continuousOn fun τ hτ =>
      (continuousAt_const.mul ((((hFd.continuousOn.continuousAt (hU.mem_nhds (hvU hτ))).norm.pow 2).add
        continuousAt_const).log (by positivity : ‖F τ‖ ^ 2 + 1 ≠ 0))).continuousWithinAt

  have hlim : Tendsto (fun ε : ℝ => ∫ τ, Real.log (‖F τ‖ ^ 2 + ε) / 2 * densV v ψ τ) (𝓝[>] 0)
      (𝓝 (∫ τ, Real.log ‖F τ‖ * densV v ψ τ)) := by
    refine tendsto_integral_filter_of_dominated_convergence
      (fun τ => |Real.log ‖F τ‖ * densV v ψ τ| + C * |densV v ψ τ|)
      (eventually_mem_nhdsWithin.mono fun ε hε => (hgood ε hε).1.aestronglyMeasurable) ?_
      (hint.abs.add (hdensI.abs.const_mul C)) ?_
    · filter_upwards [Ioc_mem_nhdsGT (one_pos : (0 : ℝ) < 1)] with ε hε
      filter_upwards [ae_coord_ne_zero (0 : Fin (d + 1))] with τ hτ0
      by_cases hτ : τ ∈ tsupport v
      · have h1 := gReg_abs_le hε.1 hε.2 (hFne τ (hvU hτ) hτ0)
        have h2 := hC τ hτ
        rw [Real.norm_eq_abs] at h2
        have e : Real.log (‖F τ‖ ^ 2 + ε) / 2 = gReg ε (F τ) := by unfold gReg; ring
        have h4 : |gReg ε (F τ)| ≤ |Real.log ‖F τ‖| + C :=
          h1.trans (by linarith [le_abs_self ((1 / 2 : ℝ) * Real.log (‖F τ‖ ^ 2 + 1))])
        rw [Real.norm_eq_abs, abs_mul, abs_mul, e]
        calc |gReg ε (F τ)| * |densV v ψ τ| ≤ (|Real.log ‖F τ‖| + C) * |densV v ψ τ| :=
              mul_le_mul_of_nonneg_right h4 (abs_nonneg _)
          _ = _ := by ring
      · rw [hdens0 τ hτ]; simp
    · filter_upwards [ae_coord_ne_zero (0 : Fin (d + 1))] with τ hτ0
      by_cases hτ : τ ∈ U
      · have hpos : 0 < ‖F τ‖ ^ 2 := pow_pos (norm_pos_iff.2 (hFne τ hτ hτ0)) 2
        have hc : Tendsto (fun ε : ℝ => ‖F τ‖ ^ 2 + ε) (𝓝[>] 0) (𝓝 (‖F τ‖ ^ 2 + 0)) :=
          (tendsto_const_nhds.add tendsto_id).mono_left nhdsWithin_le_nhds
        rw [add_zero] at hc
        have e : Real.log ‖F τ‖ = Real.log (‖F τ‖ ^ 2) / 2 := by rw [Real.log_pow]; push_cast; ring
        rw [e]
        exact (((Real.continuousAt_log hpos.ne').tendsto.comp hc).div_const 2).mul_const _
      · rw [hdens0 τ fun h => hτ (hvU h)]
        simp only [mul_zero]
        exact tendsto_const_nhds

  have hR : ∫ w in Metric.ball (0 : Fin d → ℂ) r, χ (hypIncl w) * densHyp ψ w =
      ∫ w, v (hypIncl w) * densHyp ψ w := by
    rw [setIntegral_congr_fun (g := fun w => v (hypIncl w) * densHyp ψ w)
      Metric.isOpen_ball.measurableSet fun w hw => by
      simp only [hvχ ((hypIncl_mem_ball w).2 hw)]]
    exact setIntegral_eq_integral_of_forall_compl_eq_zero fun w hw =>
      mul_eq_zero_of_left (Set.indicator_of_notMem (mt (hypIncl_mem_ball w).1 hw) _) _
  have hlimF : ∫ τ, Real.log ‖F τ‖ * densV v ψ τ = (m : ℝ) * ∫ w, v (hypIncl w) * densHyp ψ w := by
    rw [hlogF, hL0.2, Int.cast_natCast]
  rw [hR, ← hlimF]
  exact hlim.congr' (eventually_mem_nhdsWithin.mono fun ε hε => (hgood ε hε).2.symm)

end

end GroundTheory.Heights₂.Heights
