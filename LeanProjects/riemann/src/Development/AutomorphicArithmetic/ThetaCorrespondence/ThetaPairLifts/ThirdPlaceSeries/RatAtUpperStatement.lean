import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogRatioUpperBoundStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LiftLambdaBound
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RatAtUpper

set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop GlobalTheory.CovTop.MeasRd
open Formalism.MainNotions
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_log_ratAt_le_mul_unitE : (∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.OneMeasure D) → Closed FamHyp fun Fm _ => ∃ K : ℝ, 0 ≤ K ∧ _root_.GlobalTheory.CovTop.EventuallyAtAllPoints Fm fun _ _ _ p => ∀ i, 0 < ratAt p i ∧ Real.log (ratAt p i) ≤ K * unitE p := by
  first | exact @_root_.GlobalTheory.CovTop.MeasRd.ratAt_upper_alt | exact _root_.GlobalTheory.CovTop.MeasRd.ratAt_upper_alt | (intros; apply _root_.GlobalTheory.CovTop.MeasRd.ratAt_upper_alt <;> assumption)
end
