import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PStokesLimitTTop
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterNamed
import Development.AutomorphicSpectrum.Proofs.MetricProofs.LogRatio
import Development.AutomorphicSpectrum.Proofs.MetricProofs.RegularizedWeightTendstoC2Statement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.RegularChartDataPropertiesStatement
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar.Giv.Mix

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Giv.Mix

theorem tendstoUniformlyOn_regWeight_of_isCompact_subset_Yo : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (n : ℕ) (M : CxModel P n) (Xo : Set ((Σ k, ι k) → ℂ)) (B : HermLine ι) (S : LogLogRegularisationSetting M Xo B), S.IsTied → ∀ K' ⊆ S.R.Yo, IsCompact K' → TendstoUniformlyOn S.regWeight S.R.ph (𝓝[>] 0) K' := by
  intro K _ ι _ P n M Xo B S hS K' hK' hc
  have hYo : IsOpen S.R.Yo := (GlobalTheory.T.regular_chart_data_properties n M.Xc M.atlas S.R).1
  rw [← tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact hc]
  intro u hu x hx
  obtain ⟨j, hj⟩ := M.atlas.cover x
  have hO : IsOpen ((M.atlas.chart j).target ∩ (M.atlas.chart j).symm ⁻¹' S.R.Yo) :=
    (M.atlas.chart j).isOpen_inter_preimage_symm hYo
  have hy : M.atlas.chart j x ∈ (M.atlas.chart j).target ∩ (M.atlas.chart j).symm ⁻¹' S.R.Yo :=
    ⟨(M.atlas.chart j).map_source hj, by
      simpa [Set.mem_preimage, (M.atlas.chart j).left_inv hj] using hK' hx⟩
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hO _ hy
  have hsub : Metric.closedBall (M.atlas.chart j x) (ε / 2) ⊆
      (M.atlas.chart j).target ∩ (M.atlas.chart j).symm ⁻¹' S.R.Yo :=
    (Metric.closedBall_subset_ball (by linarith)).trans hball
  have hU := (GlobalTheory.T.regularized_weight_tendsto_C2 K ι P n M Xo B S hS j _ hsub (isCompact_closedBall _ _)).1
  refine ⟨(M.atlas.chart j).source ∩ (M.atlas.chart j) ⁻¹' Metric.ball (M.atlas.chart j x) (ε / 2),
    mem_nhdsWithin_of_mem_nhds (((M.atlas.chart j).isOpen_inter_preimage Metric.isOpen_ball).mem_nhds
      ⟨hj, by simp [hε]⟩), ?_⟩
  filter_upwards [hU u hu] with t ht y hy'
  have h := ht (M.atlas.chart j y) (Metric.ball_subset_closedBall hy'.2)
  simpa [Function.comp, (M.atlas.chart j).left_inv hy'.1] using h

end GlobalTheory.CompanionTheory.Ar.Giv.Mix
