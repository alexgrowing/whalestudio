import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsArith
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.IsSemipositiveRelTrivLine
import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsAntisym
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory

noncomputable section

def ShiftIntersectionPolynomial.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (II : IntersectionSystem) (P : Ideal (MRing ι))
    (n : ℕ) (A B : HermLine ι),
    IsIntersectionSystem II → IsArithVar P n → IsSmoothHerm A → IsSmoothHerm B →
    ∃ p : Polynomial ℝ, p.natDegree ≤ n ∧ p.coeff n = II K ι P n (fun _ => A) ∧
      ∀ q : ℕ, II K ι P n (fun _ => HermLine.zcomb A B (q : ℤ) 1) = p.eval (q : ℝ)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
