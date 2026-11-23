import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsArith
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory

noncomputable section

def ShiftDegreePolynomial.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (D : ℕ) (a b : K → ℤ),
    IsArithVar P (D + 1) →
    ∃ r : Polynomial ℝ, r.natDegree ≤ D ∧ r.coeff D = (genDeg P D a : ℝ) ∧
      ∀ q : ℕ, (genDeg P D ((q : ℤ) • a + b) : ℝ) = r.eval (q : ℝ)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
