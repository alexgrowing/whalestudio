import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TruncatedPotentialApproximation
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.truncated_potential_approximation : Hypotheses2 → HypothesesH → OnObj fun _ O _ T _ _ => ∀ c, ∃ C : ℝ, ∀ u σ (R : ℝ), 2 ≤ R → ∀ x, x ∉ (T.M c).Z σ → (T.M c).r σ x ≤ Real.sqrt R → |(T.F c).phR R u σ x - (T.F c).ph u σ x| ≤ C * ‖u‖ / R := by
  first | exact @GlobalTheory.InterpClose.interp_close_hodge | exact GlobalTheory.InterpClose.interp_close_hodge | (intros; apply GlobalTheory.InterpClose.interp_close_hodge <;> assumption)
