import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.TwistedKernels.ExPhiPlusOnto
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistedJacquetExactSmoothStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicFiltrationExhaustiveStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaOpenMirabolicStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicCharacterEqStatement

open GlobalTheory.PRep GlobalTheory.BZMir GlobalTheory.BZMir.Fun

namespace GlobalTheory.CompanionTheory.BZMir

theorem exPhiMinus (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] :
    GlobalTheory.BZMir.Fun.ExPhiMinus k := by
  intro ψ hψ n V₁ V₂ V₃ _ _ _ _ _ _ τ₁ τ₂ τ₃ h₁ h₂ h₃ f g hf hg hfg
  have hopen : IsOpen ((mirChar k ψ n).ker : Set (MirUin k (n + 1))) := by
    rw [GlobalTheory.T.mirabolic_character_eq k ψ n]
    exact GlobalTheory.T.theta_open_mirabolic k ψ hψ (n + 1) _
  exact GlobalTheory.T.twisted_jacquet_exact_smooth τ₁ τ₂ τ₃ h₁ h₂ h₃ (MirUin k (n + 1)) (mirChar k ψ n) hopen
    (GlobalTheory.T.mirabolic_filtration_exhaustive k (n + 1)) f g hf hg hfg

end GlobalTheory.CompanionTheory.BZMir
