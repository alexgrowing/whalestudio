import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StNormalModelPlace
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StBranchLift
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

def NormalCurveBranchOrder.Statement : Prop :=
  ∀ (n : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (M : IndefiniteRowSideFullHecke.ComplexSets.NormalModel J)
    (w : Fin n ⊕ Fin M.m → ℂ) (r : ℝ) (φ : (Fin 1 → ℂ) → Fin n ⊕ Fin M.m → ℂ),
    J.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (1 : ℕ) → 0 < r →
    DifferentiableOn ℂ φ (Metric.ball 0 r) → Set.InjOn φ (Metric.ball 0 r) →
    Set.MapsTo φ (Metric.ball 0 r) (IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn M.ideal) → φ 0 = w →
      ∀ g : MvPolynomial (Fin n ⊕ Fin M.m) ℂ,
        Ring.ord (pointLocalRing M.ideal w)
            (algebraMap (MvPolynomial (Fin n ⊕ Fin M.m) ℂ) (pointLocalRing M.ideal w) g) =
          analyticOrderAt (fun τ : ℂ ↦ eval (φ fun _ ↦ τ) g) 0

def NormalCurveBranchOrder.diagonalDisc : (Fin 1 → ℂ) → Fin 1 ⊕ Fin IndefiniteRowSideFullHecke.ComplexSets.lineDiagonalModel.m → ℂ :=
  fun t _ ↦ t 0

end

end GroundTheory.Heights₂.Heights
