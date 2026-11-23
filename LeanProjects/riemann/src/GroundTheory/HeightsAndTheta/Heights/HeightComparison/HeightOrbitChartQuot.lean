import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.HeightOrbitChart
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G

def OrbitChartQuot.Statement : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (n : ι → ℕ) (x : Cone n (AlgebraicClosure ℚ))
    (c : (k : ι) → Fin (n k + 1)), (∀ k, x k (c k) ≠ 0) →
    ∀ V : Ideal (MvPolynomial (Coord n) ℤ), orbitIdeal x ≤ V →
      Nonempty ((chartRing x c ⧸ chartPoint x c V) ≃+*
        (MvPolynomial (Coord n) ℤ ⧸
          (V ⊔ Ideal.span (Set.range fun k ↦ (X ⟨k, c k⟩ : MvPolynomial (Coord n) ℤ) - 1))))

example : (∀ k, samplePoint k ((fun _ ↦ 0) k) ≠ 0) ∧
    orbitIdeal samplePoint ≤ orbitIdeal samplePoint :=
  ⟨fun _ ↦ by simp [samplePoint], le_rfl⟩

end GroundTheory.Heights₂.Heights
