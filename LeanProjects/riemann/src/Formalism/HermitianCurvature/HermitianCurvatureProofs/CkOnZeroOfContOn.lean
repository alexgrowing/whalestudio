import Formalism.HermitianCurvature.HermitianCurvatureProofs.SigmaContOn

noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace

namespace Formalism.FourierDecayAlt.P.S3dx4

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData

theorem gv_closed (k r : ℕ) : IsClosed (B.GV k r) := by
  show IsClosed {g : B.Mat k r | gᴴ * Formalism.QuantumDeterminants.Hpk k r * g = Formalism.QuantumDeterminants.Hpk k r}
  exact isClosed_eq ((continuous_id.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul continuous_id)
    continuous_const

theorem ckOn_zero_of_contOn {k r : ℕ} (f : Mx k r → ℂ) (hf : ContinuousOn f (B.GV k r)) :
    B.CkOn ((0 : ℕ) : ℕ∞) (B.GV k r) (fun g => f g • (1 : ℂ →L[ℂ] ℂ)) := by
  have hcl := gv_closed k r
  haveI : NormalSpace (B.Mat k r) :=
    inferInstanceAs (NormalSpace (Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → ℂ))
  obtain ⟨g, hg⟩ := ContinuousMap.exists_extension' hcl.isClosedEmbedding_subtypeVal
    (⟨fun x : B.GV k r => f x, hf.restrict⟩ : C(B.GV k r, ℂ))
  intro g₀ hg₀
  refine ⟨Set.univ, fun y => g y • (1 : ℂ →L[ℂ] ℂ), isOpen_univ, Set.mem_univ _, ?_, fun y _ hy => ?_⟩
  · show ContDiffOn ℝ 0 _ _
    rw [contDiffOn_zero]
    exact (g.continuous.smul continuous_const).continuousOn
  · exact congrArg (fun c : ℂ => c • (1 : ℂ →L[ℂ] ℂ)) (congrFun hg ⟨y, hy⟩).symm

end Formalism.FourierDecayAlt.P.S3dx4
