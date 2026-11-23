import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OneLeDetW
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SecondCountableHermC
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousBlkM
open MeasureTheory Matrix
open GlobalTheory.CompanionTheory.SiegelND.Integ.Arch GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.one_le_detW_of_isHermitian : ∀ (n : ℕ) (b : Matrix (Fin n) (Fin n) ℂ), b.IsHermitian → 1 ≤ detW b := by
  first | exact @GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt.one_le_detW | exact GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt.one_le_detW | (intros; apply GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt.one_le_detW <;> assumption)
