import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteFreeSpreadsOutFromLocalization
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
open CategoryTheory Limits AlgebraicGeometry
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_free_spreads_out_from_localization : ∀ (R : Type) [CommRing R] (q : PrimeSpectrum R) (B : Type) [CommRing B] [Algebra R B] [Algebra.FinitePresentation R B], Module.Finite (Localization.AtPrime q.asIdeal) ((Localization.AtPrime q.asIdeal) ⊗[R] B) → Module.Free (Localization.AtPrime q.asIdeal) ((Localization.AtPrime q.asIdeal) ⊗[R] B) → ∃ r : R, r ∉ q.asIdeal ∧ Module.Finite (Localization.Away r) (Localization.Away r ⊗[R] B) ∧ Module.Free (Localization.Away r) (Localization.Away r ⊗[R] B) := by
  first | exact @GlobalTheory.exists_finite_free_away_of_atPrime | exact GlobalTheory.exists_finite_free_away_of_atPrime | (intros; apply GlobalTheory.exists_finite_free_away_of_atPrime <;> assumption)
