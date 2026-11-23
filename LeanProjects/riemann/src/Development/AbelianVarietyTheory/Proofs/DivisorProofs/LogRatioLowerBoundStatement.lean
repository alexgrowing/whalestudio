import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogRatioLowerBound
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasAtOf
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop GlobalTheory.CovTop.MeasRd
open Formalism.MainNotions
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.log_ratio_lower_bound : Hypotheses2 → Closed FamHyp fun Fm _ => ∃ K : ℝ, 0 ≤ K ∧ EvTied Fm fun _ _ _ p => ∀ i, -(K * unitE p) ≤ Real.log (ratAt p i) := by
  first | exact @GlobalTheory.CovTop.MeasLow.lower | exact GlobalTheory.CovTop.MeasLow.lower | (intros; apply GlobalTheory.CovTop.MeasLow.lower <;> assumption)
