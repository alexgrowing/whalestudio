import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LevelOneTwelveMulFinrankModularFormLowerBound
import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteIndexOfGammaLe
open UpperHalfPlane Filter GlobalTheory.OddFrame
open ModularForm (E₄ E₆)
open scoped MatrixGroups ModularForm Manifold Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levelOne_twelve_mul_finrank_modularForm_lower_bound : ∀ n : ℤ, Even n → n + 5 + 3 * (if n % 4 = 0 then 1 else -1) + 4 * (if n % 6 = 0 then 1 else if n % 6 = 2 then -1 else 0) ≤ 12 * (Module.finrank ℂ (ModularForm 𝒮ℒ n) : ℤ) := by
  first | exact @GlobalTheory.OddFrame.levelOne_twelve_mul_finrank_lower_bound | exact GlobalTheory.OddFrame.levelOne_twelve_mul_finrank_lower_bound | (intros; apply GlobalTheory.OddFrame.levelOne_twelve_mul_finrank_lower_bound <;> assumption)
