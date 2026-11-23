import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsRelSecM
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def RelTorsionBound.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (R : Subalgebra ℤ Ω), IsNoetherianRing R → ∀ (y : (Σ k, ι k) → Ω) (c0 : ∀ k, ι k),
    (∀ k, y ⟨k, c0 k⟩ ≠ 0) → ∀ k0 : K, ∃ n₁ : ℕ, ∀ b : K → ℕ, (∀ k, n₁ ≤ b k) →
      ∀ f ∈ relSecM R y (b + Pi.single k0 1),
        (∀ c : ∀ k, ι k, (∀ k, y ⟨k, c k⟩ ≠ 0) → ∃ D : ℕ, ∃ g ∈ relSecM R y (b + fun _ => D),
          (∏ k, y ⟨k, c k⟩) ^ D * f = y ⟨k0, c0 k0⟩ * g) →
        ∃ g ∈ relSecM R y b, f = y ⟨k0, c0 k0⟩ * g

section Inhabitants

open ProjLine

end Inhabitants

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
