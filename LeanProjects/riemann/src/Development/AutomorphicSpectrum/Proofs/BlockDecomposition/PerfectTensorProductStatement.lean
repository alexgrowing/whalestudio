import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PerfectTensorProduct
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.IsCompl
open TensorProduct CrystallineSemistableComparison.D
open scoped LaurentPolynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.perfect_tensor_product : ∀ (p : ℕ) [Fact p.Prime] (A : Type) [CommRing A](B : Type) [CommRing B] [Algebra A B] (K : Type) [CommRing K] [Algebra A K], Pf p A → Pf p B → Pf p K → Pf p (B ⊗[A] K) := by
  first | exact @GlobalTheory.CompanionTheory.PerfectRing.pf_tensor | exact GlobalTheory.CompanionTheory.PerfectRing.pf_tensor | (intros; apply GlobalTheory.CompanionTheory.PerfectRing.pf_tensor <;> assumption)
