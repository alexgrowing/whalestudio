import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiPolynomialBoundInDirection
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quasi_polynomial_bound_in_direction : Hypotheses2 → HypothesesH → OnObj fun _ _ A T _ _ => ∀ c, (T.F c).QPolBd A.dir := by
  first | exact @GlobalTheory.CovHt.qPolBd_onObj | exact GlobalTheory.CovHt.qPolBd_onObj | (intros; apply GlobalTheory.CovHt.qPolBd_onObj <;> assumption)
