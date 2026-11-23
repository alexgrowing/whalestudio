import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.HeightOrbitChart
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G

def OrbitChartTerm.Statement : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (n : ι → ℕ)
    (A : HermLine n) (x : Cone n (AlgebraicClosure ℚ)) (s : MvPolynomial (Coord n) ℤ),
    Geo.IsSectionOn (orbitIdeal x) A.toGeo s → ∀ c : (k : ι) → Fin (n k + 1),
      (∀ k, x k (c k) ≠ 0) →
        chartEval x c s ≠ 0 ∧ ∀ v : FinitePlace (coordField x),
          (∀ k, (X ⟨k, c k⟩ : MvPolynomial (Coord n) ℤ) ∉ orbitCenter x v) →
            finiteTerm A v (coordVec x) - Real.log (v (evalCone (coordVec x) s)) =
              -Real.log (v (IntermediateField.inclusion (ratioField_le_coordField x)
                (chartEval x c s)))

example : BlockNonzero samplePoint ∧
    Geo.IsSectionOn (orbitIdeal samplePoint) (HermLine.standard _).toGeo
      (chartMonomial (fun _ ↦ 0) 1) ∧ ∀ k, samplePoint k ((fun _ ↦ 0) k) ≠ 0 :=
  ⟨samplePoint_blockNonzero,
    isSectionOn_chartMonomial _ _ _ (fun _ ↦ by simp [samplePoint]) 1 (fun _ ↦ rfl),
    fun _ ↦ by simp [samplePoint]⟩

end GroundTheory.Heights₂.Heights
