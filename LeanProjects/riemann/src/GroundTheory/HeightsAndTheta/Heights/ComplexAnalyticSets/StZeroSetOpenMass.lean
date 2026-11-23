import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StatementsBranchesGoodPoint
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MvPolynomial MeasureTheory

noncomputable section

def ZeroSetOpenMass.Statement : Prop :=
  ∀ (n d : ℕ) (W : Ideal (MvPolynomial (Fin n) ℂ)), W.IsPrime →
    ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ W) = (d : ℕ) →
    ∀ (x : Fin n → ℂ) (O : Set (Fin n → ℂ)), IsOpen O → x ∈ O →
      x ∈ GroundTheory.Heights₂.Heights.ComplexSets.zeroSet W →
        0 < μH[((2 * d : ℕ) : ℝ)] (GroundTheory.Heights₂.Heights.ComplexSets.zeroSet W ∩ O)

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
