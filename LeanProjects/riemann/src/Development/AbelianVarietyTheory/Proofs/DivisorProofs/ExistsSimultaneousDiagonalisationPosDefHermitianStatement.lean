import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSimultaneousDiagonalisationPosDefHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioOfWeight
open Filter Topology MeasureTheory GlobalTheory.HSAmp
open scoped ComplexOrder Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_simultaneous_diagonalisation_posDef_hermitian : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (G G' : Matrix ι ι ℂ), G.PosDef → G'.IsHermitian → ∃ (T : Matrix ι ι ℂ) (d : ι → ℝ), IsUnit T.det ∧ Tᴴ * G * T = 1 ∧ Tᴴ * G' * T = Matrix.diagonal fun i => (d i : ℂ) := by
  first | exact @GlobalTheory.HSAmp.simultaneous_diagonalisation | exact GlobalTheory.HSAmp.simultaneous_diagonalisation | (intros; apply GlobalTheory.HSAmp.simultaneous_diagonalisation <;> assumption)
