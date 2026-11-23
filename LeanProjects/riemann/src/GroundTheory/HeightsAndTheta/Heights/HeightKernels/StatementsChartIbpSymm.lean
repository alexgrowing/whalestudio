import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsChartMass
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo Matrix MeasureTheory
open scoped ComplexOrder

noncomputable section

def ChartIbpSymm.Statement : Prop :=
  ∀ (n : ℕ) (A B C D : Matrix (Fin (n + 1 + 1)) (Fin (n + 1 + 1)) ℂ)
    (T : Fin n → Matrix (Fin (n + 1 + 1)) (Fin (n + 1 + 1)) ℂ),
    A.PosDef → B.PosDef → C.PosDef → D.PosDef → (∀ i, (T i).PosDef) →
    ∫ y : Fin (n + 1) → ℂ, (hermChartPot A y - hermChartPot B y) *
        maDensity (Fin.cons (fun y' => hermChartPot C y' - hermChartPot D y')
          fun i => hermChartPot (T i)) y =
      ∫ y : Fin (n + 1) → ℂ, (hermChartPot C y - hermChartPot D y) *
        maDensity (Fin.cons (fun y' => hermChartPot A y' - hermChartPot B y')
          fun i => hermChartPot (T i)) y

example : (Matrix.diagonal ![(4 : ℂ), 1, 1] : Matrix (Fin (1 + 1 + 1)) (Fin (1 + 1 + 1)) ℂ).PosDef ∧
    (1 : Matrix (Fin (1 + 1 + 1)) (Fin (1 + 1 + 1)) ℂ).PosDef ∧
    (Matrix.diagonal ![(1 : ℂ), 1, 9] : Matrix (Fin (1 + 1 + 1)) (Fin (1 + 1 + 1)) ℂ).PosDef ∧
    (∀ i : Fin 1, ((fun _ => Matrix.diagonal ![(1 : ℂ), 4, 1]) i :
      Matrix (Fin (1 + 1 + 1)) (Fin (1 + 1 + 1)) ℂ).PosDef) :=
  ⟨Matrix.posDef_diagonal_iff.mpr fun j => by fin_cases j <;> norm_num, Matrix.PosDef.one,
    Matrix.posDef_diagonal_iff.mpr fun j => by fin_cases j <;> norm_num,
    fun _ => Matrix.posDef_diagonal_iff.mpr fun j => by fin_cases j <;> norm_num⟩

end

end GroundTheory.Heights₂.Heights
