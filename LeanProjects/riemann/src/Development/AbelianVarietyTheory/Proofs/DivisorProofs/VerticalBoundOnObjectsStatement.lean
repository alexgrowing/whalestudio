import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VerticalBoundOnObjects
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.vertical_bound_on_objects : Hypotheses2 → HypothesesH → OnObj fun _ _ _ T _ _ => VertBd T := by
  first | exact @GlobalTheory.VertObj.vertBd_onObj | exact GlobalTheory.VertObj.vertBd_onObj | (intros; apply GlobalTheory.VertObj.vertBd_onObj <;> assumption)
