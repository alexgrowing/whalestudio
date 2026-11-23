import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.CpRegPhRegOfNonneg
import GroundTheory.HeightsAndTheta.Heights.Regularisation.PBoundedGlue
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open Filter Topology Metric ReciprocityTheory.ChartRestriction.G.Geo
open ReciprocityTheory.AnForm (levi)

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {P : Ideal (MRing ι)} {d : ℕ} {M : CxModel P d} {Xo : Set ((Σ k, ι k) → ℂ)} {a : K → ℤ}
  {w : ((Σ k, ι k) → ℂ) → ℝ}

theorem BoundedRegularisationSetting.eventually_closedBall_subset (S : BoundedRegularisationSetting M Xo a w) :
    ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ j, ∀ x ∈ closure (S.B.mid j),
      closedBall (S.B.chart j x) t ⊆ (S.B.chart j).target := by
  refine Filter.eventually_all.2 fun j => ?_
  have hc : IsCompact (closure (S.B.mid j)) := isClosed_closure.isCompact
  have himg : IsCompact (S.B.chart j '' closure (S.B.mid j)) :=
    hc.image_of_continuousOn ((S.B.chart j).continuousOn.mono (S.B.closure_mid j))
  have hsub : S.B.chart j '' closure (S.B.mid j) ⊆ (S.B.chart j).target := by
    rintro _ ⟨x, hx, rfl⟩
    exact (S.B.chart j).map_source (S.B.closure_mid j hx)
  obtain ⟨δ, hδ, hδs⟩ := himg.exists_cthickening_subset_open (S.B.chart j).open_target hsub
  filter_upwards [Ioo_mem_nhdsGT hδ] with t ht x hx
  exact (closedBall_subset_cthickening (Set.mem_image_of_mem _ hx) t).trans
    ((cthickening_mono ht.2.le _).trans hδs)

theorem BoundedRegularisationSetting.eventually_chartLevi (S : BoundedRegularisationSetting M Xo a w) (hS : S.IsTied) :
    ∀ᶠ t in 𝓝[>] (0 : ℝ), M.atlas.Smooth (S.bregWeight t) ∧
      ∀ k : Fin S.B.N, ∀ x ∈ S.B.mid k, ∀ v : Fin d → ℂ,
        -(4 * S.Cη * S.e1 t) * ‖v‖ ^ 2 ≤
          levi (S.B.chartFun (S.bregWeight t) k) (S.B.chart k x) v := by
  filter_upwards [self_mem_nhdsWithin, S.eventually_closedBall_subset, hS.compare] with t ht hball hcmp
  have hε : 0 < S.e1 t := lt_of_lt_of_le ht (S.e1_ge t ht)
  exact GroundTheory.Heights₂.Heights.Regular.BoundedGlue.proof M.Xc d M.atlas S.B S.ρ S.η S.Cη t (S.e1 t)
    S.cutoff ht hε hball hcmp

end GroundTheory.Heights₂.Heights.LowerBoundFree
