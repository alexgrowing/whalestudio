import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianBlockSolutionExists
import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.EisCellsDefs
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsBlockMatrixTwoByTwoFinEq
open scoped Matrix
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions.EC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitian_block_solution_exists : ∀ {K : Type} [Field K] (σ : K →+* K), (∀ x, σ (σ x) = x) → ∀ {n r : ℕ}, r ≤ n → ∀ (c : Matrix (Fin r) (Fin n) K) (a C D : Matrix (Fin n) (Fin n) K) (T : Matrix (Fin n) (Fin r) K) (L : Matrix (Fin r) (Fin n) K), IsCompl c a → C = T * c → L * T = 1 → C * cT σ D = D * cT σ C → ∃ b : Matrix (Fin r) (Fin r) K, cT σ b = b ∧ C * a⁻¹ * (1 - eId K n r - extB b) + D * cT σ a * eId K n r = 0 := by
  first | exact @GlobalTheory.CompanionTheory.BruhatCell.exists_hermitian_lowerLeft | exact GlobalTheory.CompanionTheory.BruhatCell.exists_hermitian_lowerLeft | (intros; apply GlobalTheory.CompanionTheory.BruhatCell.exists_hermitian_lowerLeft <;> assumption)
