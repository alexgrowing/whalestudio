import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitaryTubeProductChartHasStrictFDerivAtEntry
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BlkExt
open MeasureTheory Matrix Filter Topology Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp GlobalTheory.Tube
open scoped InnerProductSpace ENNReal ComplexConjugate
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryTubeProductChart_hasStrictFDerivAt_entry : ∀ (k : ℕ) (η : ℝ) (i j : Fin (k + 1)), ∃ D : Par k →L[ℝ] ℂ, HasStrictFDerivAt (fun x : Par k => chart η x i j) D 0 ∧ ∀ v, D v = tang η v i j := by
  first | exact @GlobalTheory.TubeDeriv.chart_hasStrictFDerivAt | exact GlobalTheory.TubeDeriv.chart_hasStrictFDerivAt | (intros; apply GlobalTheory.TubeDeriv.chart_hasStrictFDerivAt <;> assumption)
