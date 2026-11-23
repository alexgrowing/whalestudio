import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TorusExt

open NumberField ReciprocityTheory.GeometryOfNumbersTheory

namespace GlobalTheory.LieHt

def SecJets4 : Prop := ∀ (K : Type) [Field K] [NumberField K] (F : SemiFib K) (h : HermFam K (Fin F.P₀.g → K))
  (ρ : (K →+* ℂ) → ℝ), F.IsHerm h → F.IsRho ρ →
  ∀ (K' : Type) [Field K'] [NumberField K'] [Algebra K K'] (x : Fin F.P₀.g → K'), x ≠ 0 → ∀ n : ℕ, 2 ≤ n →
    ∃ (K'' : Type) (_ : Field K'') (_ : NumberField K'') (_ : Algebra K' K'') (_ : Algebra K K'') (_ : IsScalarTower K K' K'')
      (h'' : HermFam K'' (Fin F.P₀.g → K'')), IsBC h h'' ∧
      JetSys h'' (latBC K'' F.lieLat) (fun i => algebraMap K' K'' (x i)) n
        (-F.falt h / 2 + (F.P₀.g : ℝ) / 4 * Real.log ((4 * n : ℕ) / (2 * Real.pi)))
        fun i σ => jetBd F.P₀.g (4 * n) i (ρ (σ.comp (algebraMap K K'')))

end GlobalTheory.LieHt
