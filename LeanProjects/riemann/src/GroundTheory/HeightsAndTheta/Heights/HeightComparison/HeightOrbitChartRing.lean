import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.HeightOrbitChart
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G

def OrbitChartRing.Statement : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (n : ι → ℕ) (x : Cone n (AlgebraicClosure ℚ))
    (c : (k : ι) → Fin (n k + 1)), (∀ k, x k (c k) ≠ 0) →
      Algebra.FiniteType ℤ (chartRing x c) ∧ IsFractionRing (chartRing x c) (ratioField x)

example : ∀ k, samplePoint k ((fun _ ↦ 0) k) ≠ 0 := fun _ ↦ by simp [samplePoint]

end GroundTheory.Heights₂.Heights
