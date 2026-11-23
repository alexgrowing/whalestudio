import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsChartMass
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.PartsSt
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo Matrix MeasureTheory
open scoped ComplexOrder

noncomputable section

def chartCutoff {D : ℕ} (k : ℕ) (y : Fin D → ℂ) : ℝ :=
  Real.smoothTransition (2 - (∑ i, ‖y i‖ ^ 2) / ((k : ℝ) + 1) ^ 2)

def ChartCutoffEnergy.Statement : Prop :=
  ∀ (n : ℕ) (T : Fin n → Matrix (Fin (n + 1 + 1)) (Fin (n + 1 + 1)) ℂ), (∀ i, (T i).PosDef) →
    ∃ K : ℝ, ∀ k : ℕ,
      ∫ y : Fin (n + 1) → ℂ,
        ReciprocityTheory.AnForm.A.gradDens (fun i => hermChartPot (T i)) (chartCutoff k) (chartCutoff k) y ≤ K

example (D k : ℕ) : chartCutoff k (0 : Fin D → ℂ) = 1 := by
  simp only [chartCutoff, Pi.zero_apply, norm_zero]
  exact Real.smoothTransition.one_of_one_le (by norm_num)

example : chartCutoff 0 (fun _ : Fin 1 => (2 : ℂ)) = 0 := by
  simp only [chartCutoff, Finset.univ_unique, Finset.sum_singleton, Complex.norm_ofNat]
  exact Real.smoothTransition.zero_of_nonpos (by norm_num)

example : ∀ i : Fin 1, ((fun _ => Matrix.diagonal ![(1 : ℂ), 4, 1]) i :
    Matrix (Fin (1 + 1 + 1)) (Fin (1 + 1 + 1)) ℂ).PosDef :=
  fun _ => Matrix.posDef_diagonal_iff.mpr fun j => by fin_cases j <;> norm_num

end

end GroundTheory.Heights₂.Heights
