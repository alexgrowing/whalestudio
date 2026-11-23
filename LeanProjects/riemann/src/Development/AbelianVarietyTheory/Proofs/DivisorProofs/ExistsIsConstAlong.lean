import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisAtMinusRho
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoreConcl
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.LanglandsSquareIntegrable
open scoped TensorProduct NNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.EisRes
open GlobalTheory.Doubling (absE)
open scoped ComplexConjugate

namespace GlobalTheory.StdPar

theorem exists_isConstAlong : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J →
      ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E), IsWittFrame σ J X Y →
        ∀ (S : Finset (Fin r)) (φ : GAd σ J → ℂ), Continuous φ → (∀ γ ∈ ratPts σ J, ∀ g, φ (γ * g) = φ g) →
          ∃ c, GlobalTheory.StdPar.IsConstAlong σ J X S φ c := by
  intro F E _ _ _ _ _ σ h n J hJ r X Y hW S φ _ hφ
  haveI : LocallyCompactSpace (unip σ J X S) := (isClosed_unip S h hJ hW).locallyCompactSpace
  exact ⟨_, GlobalTheory.UAut.isConstTermOn_constTermOn (N := unip σ J X S) fun γ hγ g => hφ γ hγ.1 g⟩

end GlobalTheory.StdPar
