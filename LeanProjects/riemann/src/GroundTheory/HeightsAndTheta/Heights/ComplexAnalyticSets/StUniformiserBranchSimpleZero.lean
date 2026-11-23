import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StNormalCurvePointDVR
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

def UniformiserBranchSimpleZero.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (I : Ideal (MvPolynomial σ ℂ)) (w : σ → ℂ) (t : MvPolynomial σ ℂ)
    (r : ℝ) (φ : (Fin 1 → ℂ) → σ → ℂ),
    I.IsPrime → IsIntegrallyClosed (MvPolynomial σ ℂ ⧸ I) →
    ringKrullDim (MvPolynomial σ ℂ ⧸ I) = (1 : ℕ) →
    Irreducible (algebraMap (MvPolynomial σ ℂ) (pointLocalRing I w) t) → 0 < r →
    DifferentiableOn ℂ φ (Metric.ball 0 r) → Set.InjOn φ (Metric.ball 0 r) →
    Set.MapsTo φ (Metric.ball 0 r) (IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn I) → φ 0 = w →
      analyticOrderAt (fun τ : ℂ ↦ eval (φ fun _ ↦ τ) t) 0 = 1

def UniformiserBranchSimpleZero.lineDisc : (Fin 1 → ℂ) → Fin 1 → ℂ :=
  fun t _ ↦ t 0

end

end GroundTheory.Heights₂.Heights
