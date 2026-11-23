import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PsiPreservesIsomorphism
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SubsingletonOfGiso
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibOrd
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.psi_preserves_isomorphism : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (A B : MRep k n), MIso A B → GIso (psiN A) (psiN B) := by
  first | exact @GlobalTheory.CompanionTheory.LeibOrd.PsiIso.giso_psiN | exact GlobalTheory.CompanionTheory.LeibOrd.PsiIso.giso_psiN | (intros; apply GlobalTheory.CompanionTheory.LeibOrd.PsiIso.giso_psiN <;> assumption)
