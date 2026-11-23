import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnipotentHaarEqConstMulTransportedProduct
import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ConstC
open scoped Classical ENNReal
open MeasureTheory Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.LocWSOf GlobalTheory.TypeAsm
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unipotentHaar_eq_const_mul_transported_product : ∀ (D : D7) (X : HidaSetting D) (C : Choice X 1) (hB : WuBessel C), GoodLoc C hB → ∀ u : D.what₂.Word, ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧ ∀ A : Set X.B.I.Ginf, MeasurableSet A → X.muN u A = c * Measure.pi (fun _ : D.what₂.Tau => muNB D 1) (trI C '' A) := by
  first | exact @GlobalTheory.muN_eq_const_mul_pi_trI | exact GlobalTheory.muN_eq_const_mul_pi_trI | (intros; apply GlobalTheory.muN_eq_const_mul_pi_trI <;> assumption)
