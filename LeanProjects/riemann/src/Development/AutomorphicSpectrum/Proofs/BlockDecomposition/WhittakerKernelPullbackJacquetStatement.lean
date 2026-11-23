import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerKernelPullbackJacquet
import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.UnipotentDerivatives.DerUnipLeUnipB
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhitKerLeComapMap
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZMir GlobalTheory.CompanionTheory.BZNuPair
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.whittaker_kernel_pullback_jacquet : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle) (n j : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin (n + j + 1)) k) V) (hd : ∑ a, (![n, j + 1] a) = n + j + 1),
    (whitKer ψ ![n, j + 1] (jac (stdBlocks ![n, j + 1] hd) π)).comap
        (Submodule.mkQ (twKer π (unipRad k (stdBlocks ![n, j + 1] hd)) 1)) =
      twKer π (derUnip k (n + j + 1) n) (derChar k ψ (n + j + 1) n) := by
  first | exact @GlobalTheory.CompanionTheory.BZNuPair.DerComap.whitKer_jac_comap_eq_twKer_derUnip | exact GlobalTheory.CompanionTheory.BZNuPair.DerComap.whitKer_jac_comap_eq_twKer_derUnip | (intros; apply GlobalTheory.CompanionTheory.BZNuPair.DerComap.whitKer_jac_comap_eq_twKer_derUnip <;> assumption)
