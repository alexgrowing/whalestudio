import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.LocalUnfoldBStatementHolds
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.CuspidalExponentialDecay
import Development.AbelianVarietyTheory.Definitions.ThetaValues.Generic
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology GlobalTheory.Shares
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory

theorem isBigO_norm_pow_of_le_rpow_sub_half {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [Nontrivial E] (a : ℕ) (g : E → ℂ) (ρ C : ℝ) (hρ : 0 < ρ)
    (hd : DifferentiableOn ℂ g (Metric.ball 0 ρ))
    (hb : ∀ z : E, z ≠ 0 → ‖z‖ < ρ → ‖g z‖ ≤ C * ‖z‖ ^ ((a : ℝ) - 1 / 2)) :
    g =O[𝓝 0] fun z => ‖z‖ ^ a := by
  have hball : Metric.ball (0 : E) ρ ∈ 𝓝 (0 : E) := Metric.ball_mem_nhds _ hρ
  have hc : ContinuousAt g 0 := hd.continuousOn.continuousAt hball
  cases a with
  | zero =>
    simp only [pow_zero]
    exact hc.tendsto.isBigO_one ℝ
  | succ m =>
    have he : ((m + 1 : ℕ) : ℝ) - 1 / 2 = (m : ℝ) + 1 / 2 := by push_cast; ring
    rw [he] at hb
    have hpos : (0 : ℝ) < (m : ℝ) + 1 / 2 := by positivity
    have hb' : ∀ z : E, z ≠ 0 → ‖z‖ < ρ → ‖g z‖ ≤ |C| * ‖z‖ ^ ((m : ℝ) + 1 / 2) :=
      fun z hz hzρ => (hb z hz hzρ).trans
        (mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity))
    have hpow : ∀ s : ℝ, 0 < s →
        Filter.Tendsto (fun z : E => |C| * ‖z‖ ^ s) (𝓝 0) (𝓝 0) := by
      intro s hs
      have h1 : Continuous (fun z : E => |C| * ‖z‖ ^ s) :=
        continuous_const.mul (continuous_norm.rpow_const fun _ => Or.inr hs.le)
      have h2 := h1.tendsto 0
      simpa [Real.zero_rpow hs.ne'] using h2
    have hg0 : g 0 = 0 := by
      haveI : (𝓝[≠] (0 : E)).NeBot := Module.punctured_nhds_neBot ℂ E 0
      have h1 : Filter.Tendsto g (𝓝[≠] 0) (𝓝 (g 0)) := hc.tendsto.mono_left nhdsWithin_le_nhds
      have h2 : Filter.Tendsto g (𝓝[≠] 0) (𝓝 0) := by
        refine squeeze_zero_norm' ?_ ((hpow _ hpos).mono_left nhdsWithin_le_nhds)
        filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds hball] with z hz hzρ
        exact hb' z hz (mem_ball_zero_iff.1 hzρ)
      exact tendsto_nhds_unique h1 h2
    have hb'' : ∀ z : E, ‖z‖ < ρ → ‖g z‖ ≤ |C| * ‖z‖ ^ ((m : ℝ) + 1 / 2) := by
      intro z hz
      rcases eq_or_ne z 0 with rfl | h
      · rw [hg0, norm_zero]; positivity
      · exact hb' z h hz
    have hmaps : Set.MapsTo g (Metric.ball 0 ρ)
        (Metric.closedBall (g 0) (|C| * ρ ^ ((m : ℝ) + 1 / 2))) := by
      intro z hz
      have hz' := mem_ball_zero_iff.1 hz
      rw [hg0, mem_closedBall_zero_iff]
      refine (hb'' z hz').trans ?_
      gcongr
    have ho : (fun w => g w - g 0) =o[𝓝 0] (fun w : E => ‖w - 0‖ ^ m) := by
      simp only [hg0, sub_zero]
      rw [Asymptotics.isLittleO_iff]
      intro ε hε
      filter_upwards [hball, (hpow (1 / 2) (by norm_num)).eventually (gt_mem_nhds hε)]
        with z hz hzε
      refine (hb'' z (mem_ball_zero_iff.1 hz)).trans ?_
      rw [Real.rpow_add' (norm_nonneg z) hpos.ne', Real.rpow_natCast, norm_pow, norm_norm]
      calc |C| * (‖z‖ ^ m * ‖z‖ ^ (1 / 2 : ℝ)) = (|C| * ‖z‖ ^ (1 / 2 : ℝ)) * ‖z‖ ^ m := by ring
        _ ≤ ε * ‖z‖ ^ m := by gcongr
    refine Asymptotics.IsBigO.of_bound (|C| * ρ ^ ((m : ℝ) + 1 / 2) / ρ ^ (m + 1)) ?_
    filter_upwards [hball] with z hz
    have key := Complex.dist_le_mul_div_pow_of_mapsTo_ball_of_isLittleO hd hmaps ho hz
    rw [hg0, dist_zero_right, dist_zero_right, div_pow] at key
    rw [norm_pow, norm_norm]
    refine key.trans_eq ?_
    ring

theorem isBigO_norm_pow_of_le_rpow_sub_half_euclidean :
    ∀ (n a : ℕ) (g : V n → ℂ) (ρ C : ℝ), 0 < n → 0 < ρ → DifferentiableOn ℂ g (Metric.ball 0 ρ) → (∀ z : V n, z ≠ 0 → ‖z‖ < ρ → ‖g z‖ ≤ C * ‖z‖ ^ ((a : ℝ) - 1 / 2)) → g =O[𝓝 0] fun z => ‖z‖ ^ a := by
  intro n a g ρ C hn hρ hd hb
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  haveI : Nontrivial (V n) := inferInstance
  exact isBigO_norm_pow_of_le_rpow_sub_half a g ρ C hρ hd hb

end GlobalTheory
