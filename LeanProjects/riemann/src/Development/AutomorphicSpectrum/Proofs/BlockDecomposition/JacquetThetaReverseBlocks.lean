import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProductTransposeInverseDualReverse
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JmThetaHolds

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL Zc.Cos GlobalTheory.CompanionTheory.ThetaProd

namespace GlobalTheory.CompanionTheory.JacTheta

theorem nonempty_jac_comp_thetaW : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (h N : ℕ) (d : Fin h → ℕ) (hd : ∑ a, d a = N) (hd' : ∑ a, d (Fin.rev a) = N)
    (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V),
    Nonempty ((jac (stdBlocks d hd) (π.comp (thetaW k N))).Equiv
      ((jac (stdBlocks (fun a => d (Fin.rev a)) hd') π).comp (thetaL d))) := by
  intro k _ _ _ _ h N d hd hd' V _ _ π
  exact ⟨GlobalTheory.CompanionTheory.JmThetaInv.jacCompThetaW d hd hd' π⟩

end GlobalTheory.CompanionTheory.JacTheta
