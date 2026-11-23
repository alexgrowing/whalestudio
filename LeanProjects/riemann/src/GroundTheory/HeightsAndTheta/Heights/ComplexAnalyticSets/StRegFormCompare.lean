import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StLelongRegularise
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
open scoped ContDiff

noncomputable section

def RegFormCompare.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin (d + 1)) (Fin n) ℂ)
    (φ : Fin d → (Fin n → ℂ) → ℝ) (f : (Fin n → ℂ) → ℝ),
    J.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (d + 1 : ℕ) → IsFiniteProjection J A →
    (∀ i, SmoothNear (zeroSet J) (φ i)) → Continuous f → HasCompactSupport f →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ (u : Fin n → ℂ) (ε : ℝ), 0 < ε →
        ∀ v w : (Fin n → ℂ) → ℝ, (∀ x, 0 ≤ w x) → (∀ x ∈ tsupport f, |v x| ≤ w x) →
          ∀ y, chartAbsDens J A (fun x => v x * f x) (vecCons (logReg u ε) φ) y ≤
            C * chartDens J A w (vecCons (logReg u ε) fun _ => euclPot) y

end

end GroundTheory.Heights₂.Heights
