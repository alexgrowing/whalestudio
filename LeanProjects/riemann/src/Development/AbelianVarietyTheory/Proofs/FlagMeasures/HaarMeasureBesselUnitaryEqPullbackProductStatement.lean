import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HaarMeasureBesselUnitaryEqPullbackProduct
import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ConstC
open scoped Classical ENNReal
open MeasureTheory Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.LocWSOf GlobalTheory.TypeAsm
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.haarMeasure_besselUnitary_eq_pullback_product : ∀ (D : D7) (X : HidaSetting D) (C : Choice X 1) (hB : WuBessel C), GoodLoc C hB → ∀ u : D.what₂.Word, ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧ X.muH u Set.univ = c ∧ ∀ A : Set X.B.I.Ginf, MeasurableSet A → X.muH u A = c * Measure.pi (C.muW u) (trI C '' A) := by
  first | exact @GlobalTheory.PullHaarW.pullH | exact GlobalTheory.PullHaarW.pullH | (intros; apply GlobalTheory.PullHaarW.pullH <;> assumption)
