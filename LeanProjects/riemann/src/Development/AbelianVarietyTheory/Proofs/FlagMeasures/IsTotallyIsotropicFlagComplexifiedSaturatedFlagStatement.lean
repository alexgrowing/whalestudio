import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsTotallyIsotropicFlagComplexifiedSaturatedFlag
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsGaugeAll
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isTotallyIsotropicFlag_complexified_saturatedFlag : ∀ (I : AutInst) (Λ : Submodule (𝓞 I.E) (Fin I.n → I.E)) (a : ℕ) (j : Fin a → ℕ) (S : Fin (a + 1) → Submodule (𝓞 I.E) (Fin I.n → I.E)), IsSatFlag I Λ j S → ∀ v, IsIsoFlag (I.ε v) j (flagAt I S v) := by
  first | exact @GlobalTheory.FlagMeas.isIsoFlag_flagAt_of_isSatFlag | exact GlobalTheory.FlagMeas.isIsoFlag_flagAt_of_isSatFlag | (intros; apply GlobalTheory.FlagMeas.isIsoFlag_flagAt_of_isSatFlag <;> assumption)
