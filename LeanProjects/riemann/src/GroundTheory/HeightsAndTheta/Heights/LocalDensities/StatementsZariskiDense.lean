import Mathlib
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.FourB

def ZariskiDense.Hyp (A : Type*) [CommRing A] [Algebra ℂ A] (g : A) : Prop :=
  Algebra.FiniteType ℂ A ∧ IsDomain A ∧ g ≠ 0

def ZariskiDense.Statement : Prop :=
  ∀ (A : Type) [CommRing A] [Algebra ℂ A] (g : A), ZariskiDense.Hyp A g →
    ∀ (x : A →ₐ[ℂ] ℂ) (s : Finset A) (ε : ℝ), 0 < ε →
      ∃ y : A →ₐ[ℂ] ℂ, (∀ a ∈ s, ‖y a - x a‖ < ε) ∧ y g ≠ 0

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.FourB
