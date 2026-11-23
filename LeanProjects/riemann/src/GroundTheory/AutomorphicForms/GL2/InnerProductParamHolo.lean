import Mathlib
import GroundTheory.GlobalFields.ComplexMultiplication.Residue

open MeasureTheory Set Filter Topology Metric

namespace GroundTheory.Automorphic

noncomputable section

namespace PseudoEisenstein

theorem differentiableOn_integral_of_bound {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {F : ℂ → α → ℂ} {U : Set ℂ} (hU : IsOpen U) (hF : ∀ x, DifferentiableOn ℂ (fun s => F s x) U)
    (hmeas : ∀ s ∈ U, AEStronglyMeasurable (F s) μ)
    (hbound : ∀ s₀ ∈ U, ∃ ε > 0, closedBall s₀ ε ⊆ U ∧ ∃ B : α → ℝ, Integrable B μ ∧
      ∀ s ∈ closedBall s₀ ε, ∀ x, ‖F s x‖ ≤ B x) :
    DifferentiableOn ℂ (fun s => ∫ x, F s x ∂μ) U := by
  classical
  intro s₀ hs₀
  obtain ⟨ε, hε, hsub, B, hB, hle⟩ := hbound s₀ hs₀
  set r := ε / 2 with hr
  have hr0 : 0 < r := by rw [hr]; linarith
  have hball : ∀ s ∈ ball s₀ r, closedBall s r ⊆ closedBall s₀ ε := by
    intro s hs z hz
    rw [mem_closedBall] at hz ⊢
    rw [mem_ball] at hs
    calc dist z s₀ ≤ dist z s + dist s s₀ := dist_triangle _ _ _
      _ ≤ r + r := add_le_add hz hs.le
      _ = ε := by rw [hr]; ring
  have hderiv : ∀ x, ∀ s ∈ U, HasDerivAt (fun z => F z x) (deriv (fun z => F z x) s) s :=
    fun x s hs => ((hF x).differentiableAt (hU.mem_nhds hs)).hasDerivAt

  have hF'meas : AEStronglyMeasurable (fun x => deriv (fun z => F z x) s₀) μ := by
    have hev : ∀ᶠ n : ℕ in atTop, s₀ + ((n : ℂ) + 1)⁻¹ ∈ U := by
      have ht : Tendsto (fun n : ℕ => s₀ + ((n : ℂ) + 1)⁻¹) atTop (𝓝 s₀) := by
        have := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℂ)
        simpa [one_div] using (tendsto_const_nhds (x := s₀)).add this
      exact ht (hU.mem_nhds hs₀)
    set q : ℕ → α → ℂ := fun n x => if s₀ + ((n : ℂ) + 1)⁻¹ ∈ U then
      ((n : ℂ) + 1) * (F (s₀ + ((n : ℂ) + 1)⁻¹) x - F s₀ x) else 0 with hq
    refine aestronglyMeasurable_of_tendsto_ae atTop (f := q) (fun n => ?_)
      (Eventually.of_forall fun x => ?_)
    · simp only [hq]
      split_ifs with h
      · exact aestronglyMeasurable_const.mul ((hmeas _ h).sub (hmeas s₀ hs₀))
      · exact aestronglyMeasurable_const
    · have hsl := (hasDerivAt_iff_tendsto_slope.1 (hderiv x s₀ hs₀))
      have hseq : Tendsto (fun n : ℕ => s₀ + ((n : ℂ) + 1)⁻¹) atTop (𝓝[≠] s₀) := by
        refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun n => ?_⟩
        · have := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℂ)
          simpa [one_div] using (tendsto_const_nhds (x := s₀)).add this
        · simp only [mem_compl_iff, mem_singleton_iff, add_eq_left, inv_eq_zero]
          exact_mod_cast Nat.succ_ne_zero n
      refine (hsl.comp hseq).congr' ?_
      filter_upwards [hev] with n hn
      simp only [hq, Function.comp_apply, if_pos hn, slope, vsub_eq_sub, add_sub_cancel_left,
        inv_inv, smul_eq_mul]
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ) (x₀ := s₀)
    (F := F) (F' := fun s x => deriv (fun z => F z x) s) (bound := fun x => B x / r)
    (ball_mem_nhds s₀ hr0)
    (eventually_of_mem (hU.mem_nhds hs₀) hmeas)
    (hB.mono' (hmeas s₀ hs₀) (Eventually.of_forall fun x => hle s₀ (mem_closedBall_self hε.le) x))
    hF'meas
    (Eventually.of_forall fun x s hs => ?_) (hB.div_const r)
    (Eventually.of_forall fun x s hs => hderiv x s (hsub (hball s hs (mem_closedBall_self hr0.le))))
  · exact key.2.differentiableAt.differentiableWithinAt
  · refine Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hr0 ?_ fun z hz =>
      hle z (hball s hs (sphere_subset_closedBall hz)) x
    refine DifferentiableOn.diffContOnCl ?_
    rw [closure_ball s hr0.ne']
    exact (hF x).mono ((hball s hs).trans hsub)

open GroundTheory.Global.Elliptic in

theorem residue_integral_eq {α : Type*} [MeasurableSpace α] {μ : Measure α} {F A : ℂ → α → ℂ}
    {R : α → ℂ} {p : ℂ} {ε : ℝ} (hε : 0 < ε) (hR : Integrable R μ)
    (hA : DifferentiableOn ℂ (fun s => ∫ x, A s x ∂μ) (ball p ε))
    (hAint : ∀ s ∈ ball p ε, Integrable (A s) μ)
    (hFA : ∀ s ∈ ball p ε, s ≠ p → ∀ x, F s x = R x * (s - p)⁻¹ + A s x) :
    residue (fun s => ∫ x, F s x ∂μ) p = ∫ x, R x ∂μ := by
  refine residue_eq_of_eventuallyEq (u := fun s => ∫ x, A s x ∂μ)
    (hA.analyticAt (isOpen_ball.mem_nhds (mem_ball_self hε))) ?_
  rw [EventuallyEq, eventually_nhdsWithin_iff]
  filter_upwards [isOpen_ball.mem_nhds (mem_ball_self hε)] with s hs hsp
  rw [show (fun x => F s x) = fun x => R x * (s - p)⁻¹ + A s x from funext (hFA s hs hsp),
    integral_add (hR.mul_const _) (hAint s hs), integral_mul_const]

open GroundTheory.Global.Elliptic in

theorem residue_mul_eq {Φ H u : ℂ → ℂ} {p c : ℂ} (hH : AnalyticAt ℂ H p) (hu : AnalyticAt ℂ u p)
    (hΦ : Φ =ᶠ[𝓝[≠] p] fun z => c * (z - p)⁻¹ + u z) :
    residue (fun z => H z * Φ z) p = H p * c := by
  have hd : AnalyticAt ℂ (dslope H p) p := by
    obtain ⟨pf, hpf⟩ := hH
    exact ⟨_, hpf.has_fpower_series_dslope_fslope⟩
  refine residue_eq_of_eventuallyEq (u := fun z => c * dslope H p z + H z * u z)
    ((analyticAt_const.mul hd).add (hH.mul hu)) ?_
  filter_upwards [hΦ, self_mem_nhdsWithin] with z hz hzp
  rw [hz, dslope_of_ne _ hzp, slope_def_field]
  have : z - p ≠ 0 := sub_ne_zero.2 hzp
  field_simp
  ring

end PseudoEisenstein

end

end GroundTheory.Automorphic
