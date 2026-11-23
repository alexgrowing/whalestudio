import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceFormDivisibilityCriterion
import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.trace_form_divisibility_criterion : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) (N : ℕ), 0 < N → ∃ T : 𝓞 E →+ ℤ, (∀ c, T (H.bar c) = - T c) ∧ ∀ c : 𝓞 E, (∀ d : 𝓞 E, (N : ℤ) ∣ T (c * d)) → ∃ b : 𝓞 E, c = N • b := by
  first | exact @GlobalTheory.SkewTrace.exists_skew_perfect | exact GlobalTheory.SkewTrace.exists_skew_perfect | (intros; apply GlobalTheory.SkewTrace.exists_skew_perfect <;> assumption)
