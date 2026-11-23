import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TruncatedPotentialLogGrowth
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.truncated_potential_log_growth : Hypotheses2 → HypothesesH → OnObj fun _ O _ T _ _ => ∀ c, ∃ C : ℝ, ∀ u σ x, x ∉ (T.M c).Z σ → ∀ R : ℝ, 2 ≤ R → |(T.F c).phR R u σ x| ≤ C * ‖u‖ * Real.log ((T.M c).r σ x) := by
  first | exact @GlobalTheory.InterpMetricLog.abs_phR_le | exact GlobalTheory.InterpMetricLog.abs_phR_le | (intros; apply GlobalTheory.InterpMetricLog.abs_phR_le <;> assumption)
