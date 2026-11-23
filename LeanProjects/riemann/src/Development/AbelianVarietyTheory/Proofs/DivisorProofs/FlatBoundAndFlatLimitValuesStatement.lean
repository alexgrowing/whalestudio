import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatBoundAndFlatLimitValues
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsX
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flat_bound_and_flat_limit_values : GlobalTheory.CovTop.HypothesesXH → Hypotheses2 → HypothesesH → GlobalTheory.Published.ScholzeWeinsteinB → ∃ Cf : ℝ, OnObj fun _ O A _ _ _ => FewBad O.Y → FlatBd O.Y Cf ∧ ∀ Φ : ℝ → Fn O.Y, LimFam Φ → FlatVal A Φ := by
  first | exact @GlobalTheory.FlatObj.flat_line_onObj | exact GlobalTheory.FlatObj.flat_line_onObj | (intros; apply GlobalTheory.FlatObj.flat_line_onObj <;> assumption)
