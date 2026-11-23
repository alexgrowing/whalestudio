import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PerfectFrobeniusRootSolution
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.IsCompl
open TensorProduct CrystallineSemistableComparison.D
open scoped LaurentPolynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.perfect_frobenius_root_solution : ∀ (p : ℕ) [Fact p.Prime] (A : Type) [CommRing A](B : Type) [CommRing B] [Algebra A B] (m n k : ℕ) (a : Fin m → Fin n → A) (c : Fin m → A), Pf p B → Solv B (fun t j => a t j ^ p ^ k) (fun t => c t ^ p ^ k) → Solv B a c := by
  first | exact @GlobalTheory.CompanionTheory.PerfectRing.solv_of_solv_pow | exact GlobalTheory.CompanionTheory.PerfectRing.solv_of_solv_pow | (intros; apply GlobalTheory.CompanionTheory.PerfectRing.solv_of_solv_pow <;> assumption)
