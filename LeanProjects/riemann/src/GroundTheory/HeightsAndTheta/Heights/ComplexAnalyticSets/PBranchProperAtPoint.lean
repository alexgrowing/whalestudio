import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StBranchProperAtPoint
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StBranchAwayFromRim
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MvPolynomial Filter Topology

theorem BranchProperAtPoint.proof (hrim : BranchAwayFromRim.Statement) :
    BranchProperAtPoint.Statement := by
  intro n k J u p x m γ hJ hdim hu hcov hdisj b s hs hsx P hP
  obtain ⟨ε₀, hε₀, ρ, hρ, hrimb⟩ := hrim n k J u p x m γ hJ hdim hu hcov hdisj b
  obtain ⟨P', hP'P, hP'o, hsP'⟩ := mem_nhds_iff.mp hP
  set K : Set (Fin k → ℂ) := Metric.closedBall 0 ρ \ P' with hK
  have hKc : IsCompact K := (isCompact_closedBall 0 ρ).diff hP'o
  have hKD : K ⊆ Metric.ball 0 (γ b).radius := fun τ hτ =>
    mem_ball_zero_iff.mpr (lt_of_le_of_lt (mem_closedBall_zero_iff.mp hτ.1) hρ)
  have hcont : ContinuousOn (γ b).toFun K := (γ b).differentiableOn.continuousOn.mono hKD
  have hxK : x ∉ (γ b).toFun '' K := by
    rintro ⟨τ, hτK, hτx⟩
    have hτs : τ = s := (γ b).injOn (hKD hτK) hs (hτx.trans hsx.symm)
    exact hτK.2 (hτs ▸ hsP')
  obtain ⟨δ, hδ, hball⟩ :=
    Metric.isOpen_iff.mp (hKc.image_of_continuousOn hcont).isClosed.isOpen_compl x hxK
  refine ⟨min ε₀ δ, lt_min hε₀ hδ, fun τ hτ hfτ => ?_⟩
  have h1 : ‖τ‖ ≤ ρ := hrimb τ hτ (Metric.ball_subset_ball (min_le_left _ _) hfτ)
  by_contra hτP
  have hτK : τ ∈ K := ⟨mem_closedBall_zero_iff.mpr h1, fun h => hτP (hP'P h)⟩
  exact hball (Metric.ball_subset_ball (min_le_right _ _) hfτ) ⟨τ, hτK, rfl⟩

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
