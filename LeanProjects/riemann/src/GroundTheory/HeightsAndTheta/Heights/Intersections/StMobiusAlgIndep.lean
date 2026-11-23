import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsFibreProduct
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsGrassHeight
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI

noncomputable section

def MobiusAlgIndep.Statement : Prop :=
  ∀ (Ω : Type) [Field Ω] (Φ : Type) [Field Φ] [Algebra Ω Φ] (n : ℕ) (a : Fin n → Φ) (p q p' q' : Ω),
    AlgebraicIndependent Ω a → p * q' - q * p' ≠ 0 →
      (∀ j, algebraMap Ω Φ p' + a j * algebraMap Ω Φ q' ≠ 0) ∧
      AlgebraicIndependent Ω fun j =>
        (algebraMap Ω Φ p + a j * algebraMap Ω Φ q) / (algebraMap Ω Φ p' + a j * algebraMap Ω Φ q')

end

end GroundTheory.Heights₂.Heights.Inter
