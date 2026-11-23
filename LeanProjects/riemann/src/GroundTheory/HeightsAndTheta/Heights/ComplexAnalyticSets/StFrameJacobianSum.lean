import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StatementsArea
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StAreaMultiplicity
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Module

noncomputable section

def frameProjLin {n : ℕ} (b : OrthonormalBasis (Fin n) ℂ (EuclideanSpace ℂ (Fin n)))
    (I : Finset (Fin n)) : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] EuclideanSpace ℂ I :=
  (WithLp.linearEquiv 2 ℂ (I → ℂ)).symm.toLinearMap ∘ₗ LinearMap.pi fun i : I => innerₛₗ ℂ (b i)

theorem frameProjLin_apply {n : ℕ} (b : OrthonormalBasis (Fin n) ℂ (EuclideanSpace ℂ (Fin n)))
    (I : Finset (Fin n)) (z : EuclideanSpace ℂ (Fin n)) :
    WithLp.ofLp (frameProjLin b I z) = frameProj b I z := rfl

def FrameJacobianSum.Statement : Prop :=
  ∀ (d n : ℕ) (T : EuclideanSpace ℂ (Fin d) →ₗ[ℂ] EuclideanSpace ℂ (Fin n))
    (b : OrthonormalBasis (Fin n) ℂ (EuclideanSpace ℂ (Fin n))),
    areaJacobian (T.restrictScalars ℝ) =
      ∑ I ∈ Finset.univ.powersetCard d, areaJacobian ((frameProjLin b I ∘ₗ T).restrictScalars ℝ)

end

end GroundTheory.Heights₂.Heights
