import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MeasurableCoshPow
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.StarMulOfMemKc
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.PolarU GlobalTheory.IndefiniteRowSideFullHecke.CartanCoshPower GlobalTheory.CartanInt Matrix MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.measurable_coshPow' : ∀ (p q : ℕ) (c : ℝ), Measurable (coshPow c : UpqT p q → ℝ) := by
  first | exact @GlobalTheory.CoshPowMeas.measurable_coshPow | exact GlobalTheory.CoshPowMeas.measurable_coshPow | (intros; apply GlobalTheory.CoshPowMeas.measurable_coshPow <;> assumption)
