import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StNbarChartSemipos
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology

theorem NbarSemipos.proof (h : NbarChartSemipos.Statement) : NbarSemipos.Statement := by
  intro II Ψ _ _ K _ ι _ Ω _ _ E _ _ D O Lt _ _ _ X B p q hp _
  obtain ⟨c, hc, hX⟩ := h II Ψ K ι Ω E D O Lt X
  have hpc : 0 < (p : ℝ) * c := mul_pos (by exact_mod_cast hp) hc
  have hlim : Tendsto (fun t => (q : ℝ) * (4 * X.S.Cη * X.S.e1 t)) (𝓝[>] 0) (𝓝 0) := by
    simpa using (X.S_tied.e1_tendsto_zero.const_mul (4 * X.S.Cη)).const_mul (q : ℝ)
  have hall : ∀ᶠ t in 𝓝[>] (0 : ℝ), IsSemipositiveH (mCoordIdeal D.y) (X.NbarQ B p q t) := by
    filter_upwards [X.S.eventually_chartLevi X.S_tied, hlim.eventually (eventually_le_nhds hpc)] with t ht hq
    exact hX B p q t _ ht.1 ht.2 hq
  obtain ⟨u, hu, hsub⟩ := mem_nhdsGT_iff_exists_Ioc_subset.1 hall
  exact ⟨u, hu, fun t ht0 ht1 => hsub ⟨ht0, ht1⟩⟩

end GroundTheory.Heights₂.Heights.LowerBoundFree
