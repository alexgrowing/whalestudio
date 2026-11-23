import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetThetaReverseBlocks
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProductTransposeInverseDualReverse
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL Zc.Cos GlobalTheory.CompanionTheory.ThetaProd
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jacquet_theta_reverse_blocks : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (h N : ℕ) (d : Fin h → ℕ) (hd : ∑ a, d a = N) (hd' : ∑ a, d (Fin.rev a) = N)
    (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V),
    Nonempty ((jac (stdBlocks d hd) (π.comp (thetaW k N))).Equiv
      ((jac (stdBlocks (fun a => d (Fin.rev a)) hd') π).comp (thetaL d))) := by
  first | exact @GlobalTheory.CompanionTheory.JacTheta.nonempty_jac_comp_thetaW | exact GlobalTheory.CompanionTheory.JacTheta.nonempty_jac_comp_thetaW | (intros; apply GlobalTheory.CompanionTheory.JacTheta.nonempty_jac_comp_thetaW <;> assumption)
