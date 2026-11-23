import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PhiPreservesIsomorphism
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SubsingletonOfGiso
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibOrd
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.phi_preserves_isomorphism : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle) (n : ℕ) (A B : MRep k (n + 1)), MIso A B → MIso (phiN ψ A) (phiN ψ B) := by
  first | exact @GlobalTheory.CompanionTheory.LeibOrd.miso_phiN | exact GlobalTheory.CompanionTheory.LeibOrd.miso_phiN | (intros; apply GlobalTheory.CompanionTheory.LeibOrd.miso_phiN <;> assumption)
