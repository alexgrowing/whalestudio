import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.CpRegPhRegOfNonneg
import GroundTheory.HeightsAndTheta.Heights.Regularisation.Assembly
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open Filter Topology Metric ReciprocityTheory.ChartRestriction.G.Geo
open ReciprocityTheory.AnForm (levi)

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {P : Ideal (MRing ι)} {d : ℕ} {M : CxModel P d} {Xo : Set ((Σ k, ι k) → ℂ)} {A : HermLine ι}

theorem LogLogRegularisationSetting.eventually_closedBall_subset (S : LogLogRegularisationSetting M Xo A) :
    ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ j, ∀ x ∈ closure (S.R.mid j),
      closedBall (S.R.chart j x) t ⊆ (S.R.chart j).target := by
  refine Filter.eventually_all.2 fun j => ?_
  have hc : IsCompact (closure (S.R.mid j)) := isClosed_closure.isCompact
  have himg : IsCompact (S.R.chart j '' closure (S.R.mid j)) :=
    hc.image_of_continuousOn ((S.R.chart j).continuousOn.mono (S.R.closure_mid j))
  have hsub : S.R.chart j '' closure (S.R.mid j) ⊆ (S.R.chart j).target := by
    rintro _ ⟨x, hx, rfl⟩
    exact (S.R.chart j).map_source (S.R.closure_mid j hx)
  obtain ⟨δ, hδ, hδs⟩ := himg.exists_cthickening_subset_open (S.R.chart j).open_target hsub
  filter_upwards [Ioo_mem_nhdsGT hδ] with t ht x hx
  exact (closedBall_subset_cthickening (Set.mem_image_of_mem _ hx) t).trans
    ((cthickening_mono ht.2.le _).trans hδs)

theorem LogLogRegularisationSetting.eventually_chartLevi (S : LogLogRegularisationSetting M Xo A) (hS : S.IsTied) :
    ∀ᶠ t in 𝓝[>] (0 : ℝ), M.atlas.Smooth (S.regWeight t) ∧
      ∀ k : Fin S.R.N, ∀ x ∈ S.R.mid k, ∀ w : Fin d → ℂ,
        -(4 * S.Cη * S.e1 t) * ‖w‖ ^ 2 ≤
          levi (S.R.chartFun (S.regWeight t) k) (S.R.chart k x) w := by
  filter_upwards [self_mem_nhdsWithin, S.eventually_closedBall_subset, hS.compare] with t ht hball hcmp
  have hε : 0 < S.e1 t := lt_of_lt_of_le ht (S.e1_ge t ht)
  exact GroundTheory.Heights₂.Heights.Regular.GlueRegularised.full M.Xc d M.atlas S.R S.ρ S.η S.Cη (S.K t) t (S.e1 t)
    S.cutoff ht hε hball hcmp

end GroundTheory.Heights₂.Heights.LowerBoundFree
