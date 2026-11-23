import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BlockIndexMonotone
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SquareIntegrableTempered.CasselmanCriterion.Zj
import GroundTheory.AutomorphicForms.SupercuspidalCoefficients
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.block_index_monotone : ∀ (h N : ℕ) (d : Fin h → ℕ) (hd : ∑ a, d a = N), Monotone (Zl.JC.blockIdx d hd) := by
  first | exact @GlobalTheory.CompanionTheory.BlockIndex.blockIdx_monotone | exact GlobalTheory.CompanionTheory.BlockIndex.blockIdx_monotone | (intros; apply GlobalTheory.CompanionTheory.BlockIndex.blockIdx_monotone <;> assumption)
