import Mathlib
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.TrivFlagMod
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.BundleChernComparison

namespace GlobalTheory.CompanionTheory.Ar.Num

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

def TrivFlagKills : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (Ω : Type) [Field Ω] [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
      [∀ k, Fintype (ι k)] (x : (Σ k, ι k) → Ω) (d : ℕ), IsModelOver (pointIdeal O x) d →
    ∀ (σ : Type) [Fintype σ] (T : LocPair ι O σ), T.IsVert (pointIdeal O x) ϖ →
    ∀ (N : ℕ) (e : Fin N → σ), TrivFlagMod O ϖ x N (fun i => T.x' (e i)) →
    ∀ k : ℕ, 1 ≤ k → k ≤ d + 1 → ∀ Q : MvPolynomial σ ℝ, Q.IsHomogeneous (d + 1 - k) →
    ∀ Gs : σ → MvPolynomial (σ ⊕ σ) ℝ,
      IsMixExpansion d ((∑ i : Fin N, X (Sum.inr (e i)) ^ k) * mixDiff Q) Gs →
      T.val (pointIdeal O x) Gs = 0

end GlobalTheory.CompanionTheory.Ar.Num
