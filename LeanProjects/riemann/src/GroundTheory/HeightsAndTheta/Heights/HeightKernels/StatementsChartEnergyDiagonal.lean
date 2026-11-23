import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsChartEnergy
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo Matrix MeasureTheory
open scoped ComplexOrder

noncomputable section

def ChartEnergyDiagonal.Statement : Prop :=
  ∀ (e : ℕ) (l : Fin (e + 1) → ℝ), (∀ j, 0 < l j) →
    ∑ k ∈ Finset.range (e + 1),
        chartMixedEnergy (Matrix.diagonal fun j => (l j : ℂ)) (1 : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ) k =
      1 / 2 * (∑ j, Real.log (l j)) * chartMass (1 : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ)

example : ∀ j, 0 < (![4, 1] : Fin (1 + 1) → ℝ) j := fun j => by fin_cases j <;> norm_num

example (e : ℕ) (l : Fin (e + 1) → ℝ) (hl : ∀ j, 0 < l j) :
    (Matrix.diagonal fun j => (l j : ℂ)).PosDef :=
  Matrix.posDef_diagonal_iff.mpr fun j => by simpa using hl j

end

end GroundTheory.Heights₂.Heights
