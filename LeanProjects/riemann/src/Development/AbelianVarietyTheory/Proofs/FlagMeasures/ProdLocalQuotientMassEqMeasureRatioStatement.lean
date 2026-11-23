import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ProdLocalQuotientMassEqMeasureRatio
import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ConstC
open scoped Classical ENNReal
open MeasureTheory Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.LocWSOf GlobalTheory.TypeAsm
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.prod_localQuotientMass_eq_measureRatio : ∀ (D : D7) (X : HidaSetting D) (C : Choice X 1) (hB : WuBessel C), GoodLoc C hB → ∀ (u : D.what₂.Word) (cN cH : ℝ≥0∞), cN ≠ 0 → cN ≠ ⊤ → cH ≠ 0 → cH ≠ ⊤ → (∀ A : Set X.B.I.Ginf, MeasurableSet A → X.muN u A = cN * Measure.pi (fun _ : D.what₂.Tau => muNB D 1) (trI C '' A)) → (∀ A : Set X.B.I.Ginf, MeasurableSet A → X.muH u A = cH * Measure.pi (C.muW u) (trI C '' A)) → ∏ τ, l2SG (C.nuS u τ) (wT C u τ) = cN * cH := by
  first | exact @GlobalTheory.UnitW.prod_l2SG_eq | exact GlobalTheory.UnitW.prod_l2SG_eq | (intros; apply GlobalTheory.UnitW.prod_l2SG_eq <;> assumption)
