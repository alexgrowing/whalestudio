import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.FinalStep0
import Formalism.SharpRestriction.LevelLetterCocycles.LiftingTheory

noncomputable section

namespace Formalism.MainNotions.N.FrobeniusPowerSeries

theorem lift_le_ePA (l : ℕ) [Fact l.Prime] (hl : 11 ≤ l) (h η H M : ℕ) (h1 : 1 ≤ h) (hη : 20 * η ≤ h)
    (hH : H ≤ h + η) (hM : M ≤ h) (jumps : Finset ℤ)
    (hj : ∀ u ∈ jumps, -(M : ℤ) ≤ u ∧ u ≤ h) :
    (Formalism.MainNotions.LiftingTheory.ePA l M H jumps : ℝ) ≤
      71 / 10 * (h : ℝ) / l + 71 / 10 + 2 * Real.logb l (2 * (h : ℝ)) := by
  unfold Formalism.MainNotions.LiftingTheory.ePA Formalism.MainNotions.LiftingTheory.eUA Formalism.MainNotions.LiftingTheory.eWA Formalism.MainNotions.LiftingTheory.aA Formalism.MainNotions.LiftingTheory.JSet
  exact lift_le l hl h η H M h1 hη hH hM jumps hj

end Formalism.MainNotions.N.FrobeniusPowerSeries
