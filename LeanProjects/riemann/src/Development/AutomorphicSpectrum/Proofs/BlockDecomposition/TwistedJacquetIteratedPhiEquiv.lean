import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.UnipotentDerivatives.DerUnipLeUnipB
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicTwistedKernelDerivativeZeroStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistedJacquetPhiMinusEquivStatement
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZMir

namespace GlobalTheory.CompanionTheory.BZMir

theorem iterPhi_twJacquet_equiv (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle) (n j : ℕ) (τ : MRep k (n + j)) :
    Nonempty (TwJacquet (iterPhi k ψ j τ).ρ (MirUin k n) 1 ≃ₗ[ℂ]
      TwJacquet τ.ρ (derUnipM k (n + j) n) (derCharM k ψ (n + j) n)) := by
  induction j with
  | zero =>
    exact ⟨Submodule.quotEquivOfEq _ _ (GlobalTheory.T.mirabolic_twisted_kernel_derivative_zero k ψ n τ.V τ.ρ)⟩
  | succ j ih =>
    obtain ⟨e₁⟩ := ih (MRep.phiM k ψ τ)
    obtain ⟨e₂⟩ := GlobalTheory.T.twisted_jacquet_phi_minus_equiv k ψ (n + j) n (Nat.le_add_right n j) τ.V τ.ρ
    exact ⟨e₁.trans e₂⟩

end GlobalTheory.CompanionTheory.BZMir
