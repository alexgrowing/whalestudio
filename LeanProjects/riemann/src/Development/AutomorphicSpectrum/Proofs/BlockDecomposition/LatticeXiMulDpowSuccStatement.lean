import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LatticeXiMulDpowSucc
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.LatDefs
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.SplittingFieldLattices.GrSplit
open DividedPowers CrystallineSemistableComparison.Pb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_xi_mul_dpow_succ : ∀ {W B : Type} [CommRing W] [CommRing B] [Algebra ℚ B] (f : W →+* B) (ξ : W) (l M : ℕ), l ≠ 0 → ∀ i : ℕ, f ξ * Lat.dpE f ξ l M i = ((l : B) ^ M * ((i : B) + 1)) * Lat.dpE f ξ l M (i + 1) := by
  first | exact @GlobalTheory.CompanionTheory.LatDp.mul_divPow_eq | exact GlobalTheory.CompanionTheory.LatDp.mul_divPow_eq | (intros; apply GlobalTheory.CompanionTheory.LatDp.mul_divPow_eq <;> assumption)
