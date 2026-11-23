import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSHSFG
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ExistsSmoothExt
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutSH.SFG

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem ckExt_proof : CkExt := by
  intro k r E _ _ F hF hc
  haveI : ProperSpace (B.Mat k r) := FiniteDimensional.proper ℝ _
  obtain ⟨R, hR⟩ := hc.isCompact.isBounded.subset_ball (0 : B.Mat k r)
  choose U f' hUo hmem hsm hag using hF
  let V : B.GV k r → Set (B.Mat k r) := fun i => U i.1 i.2 ∩ Metric.ball 0 R
  have hVo : ∀ i, IsOpen (V i) := fun i => (hUo i.1 i.2).inter Metric.isOpen_ball
  have hs : IsClosed (tsupport F ∩ B.GV k r) := (isClosed_tsupport F).inter B5.GV_closed
  have hcov : tsupport F ∩ B.GV k r ⊆ ⋃ i, V i := by
    intro x hx
    exact Set.mem_iUnion.2 ⟨⟨x, hx.2⟩, hmem x hx.2, hR hx.1⟩
  obtain ⟨ρ, hρ⟩ := @SmoothPartitionOfUnity.exists_isSubordinate _ (B.Mat k r) _ _ (B.Mat k r) _
    (modelWithCornersSelf ℝ (B.Mat k r)) (B.Mat k r) _ (chartedSpaceSelf _) _ _ _ _ _ hs V hVo hcov
  refine ⟨fun x => ∑ᶠ i, ρ i x • f' i.1 i.2 x, ?_, ?_, ?_⟩
  · rw [contDiff_iff_contDiffAt]
    intro x
    refine ρ.contDiffAt_finsum fun i hi => ?_
    have hx : x ∈ U i.1 i.2 := (hρ i hi).1
    exact (hsm i.1 i.2).contDiffAt ((hUo i.1 i.2).mem_nhds hx)
  · refine HasCompactSupport.intro (isCompact_closedBall (0 : B.Mat k r) R) fun x hx => ?_
    have h0 : ∀ i, ρ i x = 0 := fun i => by
      by_contra h
      exact hx (Metric.ball_subset_closedBall (hρ i (subset_tsupport _ h)).2)
    simp [h0]
  · intro g hg
    have key : ∀ i, ρ i g • f' i.1 i.2 g = ρ i g • F g := fun i => by
      by_cases h : ρ i g = 0
      · simp [h]
      · rw [← hag i.1 i.2 g (hρ i (subset_tsupport _ h)).1 hg]
    simp only [key]
    rw [← finsum_smul]
    by_cases hF0 : g ∈ tsupport F
    · rw [ρ.sum_eq_one ⟨hF0, hg⟩, one_smul]
    · rw [image_eq_zero_of_notMem_tsupport hF0, smul_zero]

end Formalism.FourierDecayAlt.P.CutSH.SFG
