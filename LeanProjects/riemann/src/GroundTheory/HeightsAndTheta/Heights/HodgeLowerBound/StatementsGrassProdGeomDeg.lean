import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsGrassHeight
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

def grassDeg (j m : ℕ) : ℚ :=
  ((j * m).factorial : ℚ) * ∏ i : Fin j, ((i : ℕ).factorial : ℚ) / ((m + i).factorial : ℚ)

def grassProdDeg (f j m : ℕ) : ℚ :=
  ((f * j * m).factorial : ℚ) / ((j * m).factorial : ℚ) ^ f * grassDeg j m ^ f

def GrassProdGeomDeg.Statement : Prop :=
  ∀ (f j m : ℕ), 1 ≤ f → 1 ≤ j → 1 ≤ m →
    geomDeg (grassIdeal f j m) (GroundTheory.Heights₂.Heights.fsMulti (plBlocks f j m)) (f * j * m) =
      (grassProdDeg f j m : ℝ)

example : 1 ≤ (1 : ℕ) ∧ 1 ≤ (1 : ℕ) ∧ 1 ≤ (1 : ℕ) := ⟨le_rfl, le_rfl, le_rfl⟩

example : grassProdDeg 1 1 1 = 1 := by
  simp [grassProdDeg, grassDeg]

example : grassDeg 2 2 = 2 := by
  simp [grassDeg, Fin.prod_univ_two, Nat.factorial]
  norm_num

example : grassProdDeg 2 1 1 = 2 := by
  simp [grassProdDeg, grassDeg, Nat.factorial]

example (m : ℕ) : grassDeg 1 m = 1 := by
  simp [grassDeg]
  exact mul_inv_cancel₀ (by exact_mod_cast (Nat.factorial_pos m).ne')

end

end GroundTheory.Heights₂.Heights.LowerBoundFree
