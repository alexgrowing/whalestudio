import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsChartEnergy
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo Matrix MeasureTheory
open scoped ComplexOrder

noncomputable section

def swapFirstTwo (e : ℕ) : Matrix (Fin (e + 1 + 1)) (Fin (e + 1 + 1)) ℂ :=
  (Equiv.swap (0 : Fin (e + 1 + 1)) 1).permMatrix ℂ

def ChartEnergySwapInvariant.Statement : Prop :=
  ∀ (e : ℕ) (M N : Matrix (Fin (e + 1 + 1)) (Fin (e + 1 + 1)) ℂ), M.PosDef → N.PosDef → ∀ k : ℕ,
    chartMixedEnergy ((swapFirstTwo e)ᴴ * M * swapFirstTwo e) ((swapFirstTwo e)ᴴ * N * swapFirstTwo e) k =
      chartMixedEnergy M N k

example : (Matrix.diagonal ![(4 : ℂ), 1] : Matrix (Fin (0 + 1 + 1)) (Fin (0 + 1 + 1)) ℂ).PosDef ∧
    (1 : Matrix (Fin (0 + 1 + 1)) (Fin (0 + 1 + 1)) ℂ).PosDef :=
  ⟨Matrix.posDef_diagonal_iff.mpr fun j => by fin_cases j <;> norm_num, Matrix.PosDef.one⟩

example (w : ℂ) : swapFirstTwo 0 *ᵥ ![1, w] = ![w, 1] := by
  ext i
  fin_cases i <;> simp [swapFirstTwo, PEquiv.toMatrix_toPEquiv_mulVec]

example (e : ℕ) : swapFirstTwo e 0 1 = 1 := by
  simp [swapFirstTwo, PEquiv.toMatrix_apply]

end

end GroundTheory.Heights₂.Heights
