import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ContinuousOnMajorantFlagLengths
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.BlockAnti
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuousOn_majorantFlagLengths : ∀ (k r : ℕ) (z : (Fin (2 * r + k + 1) → ℂ)), (∀ a, ContinuousOn (fun x => lA k r z x a) (GG k r)) ∧ ContinuousOn (Sg k r z) (GG k r) := by
  first | exact @GlobalTheory.Amp.LenCont.lA_Sg_continuousOn | exact GlobalTheory.Amp.LenCont.lA_Sg_continuousOn | (intros; apply GlobalTheory.Amp.LenCont.lA_Sg_continuousOn <;> assumption)
