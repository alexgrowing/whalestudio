import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsChartEnergy
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo Matrix MeasureTheory
open scoped ComplexOrder

noncomputable section

def ChartEnergyCocycle.Statement : Prop :=
  ∀ (e : ℕ) (M N P : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ), M.PosDef → N.PosDef → P.PosDef →
    ∑ k ∈ Finset.range (e + 1), chartMixedEnergy M P k =
      ∑ k ∈ Finset.range (e + 1), chartMixedEnergy M N k + ∑ k ∈ Finset.range (e + 1), chartMixedEnergy N P k

example : (Matrix.diagonal ![(4 : ℂ), 1] : Matrix (Fin (1 + 1)) (Fin (1 + 1)) ℂ).PosDef ∧
    (Matrix.diagonal ![(1 : ℂ), 9] : Matrix (Fin (1 + 1)) (Fin (1 + 1)) ℂ).PosDef ∧
    (1 : Matrix (Fin (1 + 1)) (Fin (1 + 1)) ℂ).PosDef ∧
    (Matrix.diagonal ![(4 : ℂ), 1] : Matrix (Fin (1 + 1)) (Fin (1 + 1)) ℂ) ≠
      (Matrix.diagonal ![(1 : ℂ), 9] : Matrix (Fin (1 + 1)) (Fin (1 + 1)) ℂ) :=
  ⟨Matrix.posDef_diagonal_iff.mpr fun j => by fin_cases j <;> norm_num,
    Matrix.posDef_diagonal_iff.mpr fun j => by fin_cases j <;> norm_num, Matrix.PosDef.one, fun h => by
    have h1 := congrFun (congrFun h 0) 0
    norm_num at h1⟩

end

end GroundTheory.Heights₂.Heights
