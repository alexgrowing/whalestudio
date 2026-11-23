import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StLelongLimitAtBranches
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StBranchIntDecompose
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSliceBranchInt
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StPolydiscLelongLimit
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StBranchProperAtPoint
import ReciprocityTheory.AnalyticForms.AnalyticCharts.Osgood
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
open scoped ContDiff

theorem LelongLimitAtBranches.proof (hDec : BranchIntDecompose.Statement) (hSl : SliceBranchInt.Statement)
    (hLim : PolydiscLelongLimit.Statement) (hPr : IndefiniteRowSideFullHecke.ComplexSets.BranchProperAtPoint.Statement) :
    LelongLimitAtBranches.Statement := by
  intro n d J W u q m γ ord π φ hJ hdim hu hW hq hφ hzW hcov hsl hdisj hord _
  obtain ⟨NA, hNA, hA⟩ := hDec n d J u q m γ ord hJ hdim hu hcov hdisj hord
  obtain ⟨NB, hNB, hB⟩ := hSl n d J W u q m γ ord hJ hdim hu hW hq hzW hcov hsl hdisj hord
  have hpr : ∀ b, ∃ e > 0, ∀ τ ∈ Metric.ball 0 (γ b).radius, (γ b).toFun τ ∈ Metric.ball q e →
      τ ∈ Metric.ball 0 ((γ b).radius / 2) := fun b =>
    hPr n (d + 1) J u q q m γ hJ hdim hu hcov hdisj b 0 (Metric.mem_ball_self (γ b).radius_pos)
      (γ b).map_zero _ (Metric.ball_mem_nhds _ (half_pos (γ b).radius_pos))
  choose e he hpe using hpr
  refine ⟨NA ∩ NB ∩ ⋂ b, Metric.ball q (e b), inter_mem (inter_mem hNA hNB)
    (iInter_mem.2 fun b => Metric.ball_mem_nhds q (he b)), fun f hf hfc hfN => ?_⟩
  have hcons : ∀ (g : (Fin n → ℂ) → ℝ) (b : Fin m), (fun k => vecCons g φ k ∘ (γ b).toFun) =
      vecCons (g ∘ (γ b).toFun) fun k => φ k ∘ (γ b).toFun := fun g b => by
    funext k; refine Fin.cases ?_ (fun j => ?_) k <;> simp
  have hsum : (fun ε => ∑ b, ReciprocityTheory.AnForm.maInt
      (vecCons (fun τ => Real.log (‖linEval u ((γ b).toFun τ)‖ ^ 2 + ε) / 2) fun k => φ k ∘ (γ b).toFun)
      (f ∘ (γ b).toFun) (Metric.ball 0 (γ b).radius)) =ᶠ[𝓝[>] 0]
      fun ε => varInt J (d + 1) f (vecCons (logReg u ε) φ) := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    rw [hA f _ hf hfc (hfN.trans (Set.inter_subset_left.trans Set.inter_subset_left))
      (fun i => Fin.cases ⟨Set.univ, isOpen_univ, Set.subset_univ _, (contDiff_logReg u hε).contDiffOn⟩
        (fun j => hφ j) i)]
    exact Finset.sum_congr rfl fun b _ => by rw [hcons]; rfl
  refine Tendsto.congr' hsum ?_
  have hlim : ∀ b, Tendsto (fun ε => ReciprocityTheory.AnForm.maInt
      (vecCons (fun τ => Real.log (‖linEval u ((γ b).toFun τ)‖ ^ 2 + ε) / 2) fun k => φ k ∘ (γ b).toFun)
      (f ∘ (γ b).toFun) (Metric.ball 0 (γ b).radius)) (𝓝[>] 0) (𝓝 ((ord b : ℝ) * varInt W d f φ)) := by
    intro b
    have han : AnalyticOnNhd ℂ (γ b).toFun (Metric.ball 0 (γ b).radius) := fun w hw =>
      AnalyticAt.pi fun i => ReciprocityTheory.AnForm.Osgood.osgood (d + 1) _ (fun z => (γ b).toFun z i)
        Metric.isOpen_ball (differentiableOn_pi.1 (γ b).differentiableOn i) w hw
    have hγ : ContDiffOn ℝ ∞ (γ b).toFun (Metric.ball 0 (γ b).radius) :=
      (han.contDiffOn_of_completeSpace (n := ∞)).restrict_scalars ℝ
    rw [hB b f φ hf hfc (hfN.trans (Set.inter_subset_left.trans Set.inter_subset_right)) hφ]
    refine hLim d (ord b) (γ b).radius ((γ b).radius / 2) _ (f ∘ (γ b).toFun) _
      (half_lt_self (γ b).radius_pos) (hord b) (hf.comp_contDiffOn hγ) (fun τ hτ hne => hpe b τ hτ ?_)
      (fun k => ?_)
    · exact Set.mem_iInter.1 (Set.inter_subset_right (hfN (subset_tsupport f hne))) b
    · obtain ⟨U, hU, hsub, hφU⟩ := hφ k
      exact hφU.comp hγ fun τ hτ => hsub ((γ b).mapsTo hτ)
  have := tendsto_finsetSum Finset.univ fun b _ => hlim b
  convert this using 2
  push_cast
  rw [Finset.sum_mul]

end GroundTheory.Heights₂.Heights
