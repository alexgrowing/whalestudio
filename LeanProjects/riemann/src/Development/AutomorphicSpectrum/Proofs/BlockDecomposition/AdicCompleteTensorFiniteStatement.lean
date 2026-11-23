import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AdicCompleteTensorFinite
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.TwistedRepresentations.Tens
open TensorProduct CrystallineSemistableComparison CrystallineSemistableComparison.Tw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adic_complete_tensor_finite : ∀ (W : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] (l : ℕ), Irreducible (l : W) → ∀ (A : Type) [CommRing A] [Algebra W A] [IsAdicComplete (Ideal.span {(l : A)}) A] (L : Type 1) [AddCommGroup L] [Module W L] [Module.Finite W L], IsAdicComplete (Ideal.span {(l : A)}) (A ⊗[W] L) := by
  first | exact @GlobalTheory.CompanionTheory.TensorCompleteFinite.isAdicComplete_tensor_finite | exact GlobalTheory.CompanionTheory.TensorCompleteFinite.isAdicComplete_tensor_finite | (intros; apply GlobalTheory.CompanionTheory.TensorCompleteFinite.isAdicComplete_tensor_finite <;> assumption)
