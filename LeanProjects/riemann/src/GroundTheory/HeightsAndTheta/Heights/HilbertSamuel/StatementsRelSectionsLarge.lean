import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsRelSecM
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def RelSectionsLarge.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (R : Subalgebra ℤ Ω), IsNoetherianRing R → ∀ y : (Σ k, ι k) → Ω, (∀ k, ∃ i, y ⟨k, i⟩ ≠ 0) →
      ∃ n₁ : ℕ, ∀ b : K → ℕ, (∀ k, n₁ ≤ b k) → relChartLat R y (fun k => (b k : ℤ)) 1 ≤ relSecM R y b

section Inhabitants

open ProjLine

end Inhabitants

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
