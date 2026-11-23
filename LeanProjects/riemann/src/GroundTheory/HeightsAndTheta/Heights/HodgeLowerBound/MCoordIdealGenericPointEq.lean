import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.CoordinateIdeals
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.PermFinTwoUniv
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.DetLineSmooth
import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.PCurveComplexPoint
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PDualCurvePoint
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree.ComponentDataEquivalence

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

section Boundary

def bdPts (Bd : Finset (Ideal (MRing ι))) : Set ((Σ k, ι k) → ℂ) := ⋃ B ∈ Bd, mcPts B

theorem mcPts_torus {B : Ideal (MRing ι)} (hB : IsMultiHomogIdeal B) {z : (Σ k, ι k) → ℂ} (hz : z ∈ mcPts B)
    {c : K → ℂ} (hc : ∀ k, c k ≠ 0) : torusSmul c z ∈ mcPts B := by
  refine ⟨fun k => ?_, fun f hf => ?_⟩
  · obtain ⟨i, hi⟩ := hz.1 k
    exact ⟨i, mul_ne_zero (hc k) hi⟩
  obtain ⟨S, hS, rfl⟩ := hB
  induction hf using Submodule.span_induction with
  | mem s hs =>
    obtain ⟨a, ha⟩ := hS s hs
    rw [eval_map]
    unfold torusSmul
    rw [IndefiniteRowSideFullHecke.HeightsSet.CurveComplexPoint.eval₂_smul_homog s a ha, ← eval_map, hz.2 s (Ideal.subset_span hs),
      mul_zero]
  | zero => simp
  | add x y _ _ hx hy => rw [map_add, eval_add, hx, hy, add_zero]
  | smul r x _ hx => rw [smul_eq_mul, map_mul, eval_mul, hx, mul_zero]

end Boundary

section Ample

end Ample

end GroundTheory.Heights₂.Heights.LowerBoundFree.ComponentDataEquivalence
