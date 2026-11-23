import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.TwistedKernels.ExPhiPlusOnto
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicFiltrationExhaustiveStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistedJacquetExactSmoothStatement

open GlobalTheory.PRep GlobalTheory.BZMir GlobalTheory.BZMir.Fun

namespace GlobalTheory.CompanionTheory.BZMir

theorem exPsiMinus : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k],
    GlobalTheory.BZMir.Fun.ExPsiMinus k := by
  intro k _ _ _ _ n V₁ V₂ V₃ _ _ _ _ _ _ τ₁ τ₂ τ₃ h₁ h₂ h₃ f g hf hg hfg
  refine GlobalTheory.T.twisted_jacquet_exact_smooth τ₁ τ₂ τ₃ h₁ h₂ h₃ (MirUin k n) 1 ?_ (GlobalTheory.T.mirabolic_filtration_exhaustive k n) f g hf hg hfg
  have hker : ((1 : MirUin k n →* ℂˣ).ker : Set (MirUin k n)) = Set.univ := by
    ext x
    simp
  rw [hker]
  exact isOpen_univ

end GlobalTheory.CompanionTheory.BZMir
