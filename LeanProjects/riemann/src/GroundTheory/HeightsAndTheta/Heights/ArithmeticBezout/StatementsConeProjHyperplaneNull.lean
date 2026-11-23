import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsConeSheetArea
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G.Geo (MRing PBlk IsArithVar IsGoodProj segre)

def ConeProjHyperplaneNull.Statement : Prop :=
  ∀ (n e : ℕ) (P : Ideal (MRing (PBlk n)))
    (Ψ : (((k : Unit) → PBlk n k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)),
    IsArithVar P (e + 1) → IsGoodProj P Ψ →
      Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ)
        {z : EuclideanSpace ℂ (Fin n) |
          (∀ q ∈ complexFibreIdeal P, eval (fun i => z i) q = 0) ∧
          Ψ (segre fun p : Σ k, PBlk n k => z p.2) 0 = 0} = 0

end GroundTheory.Heights₂.Heights
