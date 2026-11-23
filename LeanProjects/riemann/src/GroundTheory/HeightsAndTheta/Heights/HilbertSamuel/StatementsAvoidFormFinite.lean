import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsArith
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial

noncomputable section

def AvoidFormFinite.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (S : Set (MRingOver ℂ ι)) (G : MRingOver ℂ ι) (e : K → ℕ),
    (∀ k, 1 ≤ e k) → IsMultiHomog G e → (∀ s ∈ S, ∃ a, IsMultiHomog s a) →
    (∀ z : (Σ k, ι k) → ℂ, (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) → (∀ s ∈ S, eval z s = 0) → eval z G ≠ 0) →
    ∃ T : Finset ((Σ k, ι k) → ℂ), ∀ z : (Σ k, ι k) → ℂ, (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) →
      (∀ s ∈ S, eval z s = 0) → ∃ t ∈ T, ∃ r : K → ℂ, (∀ k, r k ≠ 0) ∧ z = fun p => r p.1 * t p

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
