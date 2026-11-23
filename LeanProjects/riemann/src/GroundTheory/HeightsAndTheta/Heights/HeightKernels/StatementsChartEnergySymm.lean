import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsChartEnergy
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo Matrix MeasureTheory
open scoped ComplexOrder

noncomputable section

def ChartEnergySymm.Statement : Prop :=
  ∀ (e : ℕ) (A B C D : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ) (T : Fin e → Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ)
    (p : Fin e), A.PosDef → B.PosDef → C.PosDef → D.PosDef → (∀ j, (T j).PosDef) →
    ∫ y : Fin e → ℂ, (hermChartPot A y - hermChartPot B y) *
        (maDensity (fun j => hermChartPot (Function.update T p C j)) y -
          maDensity (fun j => hermChartPot (Function.update T p D j)) y) =
      ∫ y : Fin e → ℂ, (hermChartPot C y - hermChartPot D y) *
        (maDensity (fun j => hermChartPot (Function.update T p A j)) y -
          maDensity (fun j => hermChartPot (Function.update T p B j)) y)

example : (Matrix.diagonal ![(4 : ℂ), 1] : Matrix (Fin (1 + 1)) (Fin (1 + 1)) ℂ).PosDef ∧
    (1 : Matrix (Fin (1 + 1)) (Fin (1 + 1)) ℂ).PosDef ∧
    (Matrix.diagonal ![(1 : ℂ), 9] : Matrix (Fin (1 + 1)) (Fin (1 + 1)) ℂ).PosDef ∧
    (∀ j : Fin 1, ((fun _ => (1 : Matrix (Fin (1 + 1)) (Fin (1 + 1)) ℂ)) j).PosDef) :=
  ⟨Matrix.posDef_diagonal_iff.mpr fun j => by fin_cases j <;> norm_num, Matrix.PosDef.one,
    Matrix.posDef_diagonal_iff.mpr fun j => by fin_cases j <;> norm_num, fun _ => Matrix.PosDef.one⟩

example : ∀ j : Fin 2, ((![Matrix.diagonal ![(4 : ℂ), 1, 1], Matrix.diagonal ![(1 : ℂ), 1, 9]] :
    Fin 2 → Matrix (Fin (2 + 1)) (Fin (2 + 1)) ℂ) j).PosDef := by
  intro j
  fin_cases j
  · exact Matrix.posDef_diagonal_iff.mpr fun i => by fin_cases i <;> norm_num
  · exact Matrix.posDef_diagonal_iff.mpr fun i => by fin_cases i <;> norm_num

end

end GroundTheory.Heights₂.Heights
