import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SameSpanTransferMatrices
import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.EisCellsDefs
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsBlockMatrixTwoByTwoFinEq
open scoped Matrix
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions.EC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.same_span_transfer_matrices : ∀ {K : Type} [Field K] {n r : ℕ} (C : Matrix (Fin n) (Fin n) K) (c : Matrix (Fin r) (Fin n) K), LinearIndependent K c → Submodule.span K (Set.range c) = Submodule.span K (Set.range C) → ∃ (T : Matrix (Fin n) (Fin r) K) (L : Matrix (Fin r) (Fin n) K), C = T * c ∧ c = L * C ∧ L * T = 1 := by
  first | exact @GlobalTheory.CompanionTheory.BruhatCoeffs.exists_coeff_matrices_of_span_eq | exact GlobalTheory.CompanionTheory.BruhatCoeffs.exists_coeff_matrices_of_span_eq | (intros; apply GlobalTheory.CompanionTheory.BruhatCoeffs.exists_coeff_matrices_of_span_eq <;> assumption)
