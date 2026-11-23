import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsChartMass
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo Matrix MeasureTheory
open scoped ComplexOrder

noncomputable section

def ChartDensityIntegrable.Statement : Prop :=
  ∀ (e : ℕ) (M : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ), M.PosDef →
    Integrable (fun y : Fin e → ℂ => maDensity (fun _ : Fin e => hermChartPot M) y)

example : (Matrix.diagonal ![(4 : ℂ), 1] : Matrix (Fin (1 + 1)) (Fin (1 + 1)) ℂ).PosDef :=
  Matrix.posDef_diagonal_iff.mpr fun j => by fin_cases j <;> norm_num

example : (!![(2 : ℂ), 1; 1, 2] : Matrix (Fin (1 + 1)) (Fin (1 + 1)) ℂ).PosDef := by
  have h : (!![(2 : ℂ), 1; 1, 2] : Matrix (Fin (1 + 1)) (Fin (1 + 1)) ℂ) =
      (!![(1 : ℂ), 1; 0, 0])ᴴ * !![(1 : ℂ), 1; 0, 0] + 1 := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.conjTranspose_apply, Matrix.mul_apply, Fin.sum_univ_two] <;> norm_num
  rw [h]
  exact Matrix.PosDef.posSemidef_add (Matrix.posSemidef_conjTranspose_mul_self _) Matrix.PosDef.one

end

end GroundTheory.Heights₂.Heights
