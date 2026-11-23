import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsSemipositiveOn
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo Matrix MeasureTheory
open scoped ComplexOrder

noncomputable section

def hermChartPot {e : ℕ} (M : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ) (y : Fin e → ℂ) : ℝ :=
  Real.log (Real.sqrt (star (Fin.cons 1 y : Fin (e + 1) → ℂ) ⬝ᵥ
    (M *ᵥ (Fin.cons 1 y : Fin (e + 1) → ℂ))).re)

def chartMass {e : ℕ} (M : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ) : ℝ :=
  ∫ y : Fin e → ℂ, maDensity (fun _ : Fin e => hermChartPot M) y

def ChartMassInvariant.Statement : Prop :=
  ∀ (e : ℕ) (M : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ), M.PosDef →
    chartMass M = chartMass (1 : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ)

example : (Matrix.diagonal ![(4 : ℂ), 1] : Matrix (Fin (1 + 1)) (Fin (1 + 1)) ℂ).PosDef :=
  Matrix.posDef_diagonal_iff.mpr fun j => by fin_cases j <;> norm_num

example (e : ℕ) : (1 : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ).PosDef := Matrix.PosDef.one

example (e : ℕ) (y : Fin e → ℂ) :
    hermChartPot (1 : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ) y =
      Real.log (Real.sqrt (star (Fin.cons 1 y : Fin (e + 1) → ℂ) ⬝ᵥ (Fin.cons 1 y : Fin (e + 1) → ℂ)).re) := by
  simp [hermChartPot]

end

end GroundTheory.Heights₂.Heights
