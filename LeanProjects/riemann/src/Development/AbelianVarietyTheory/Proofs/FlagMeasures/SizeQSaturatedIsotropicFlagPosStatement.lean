import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SizeQSaturatedIsotropicFlagPos
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SigmaFiniteOfRealSmul
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.LeviIso
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sizeQ_saturatedIsotropicFlag_pos : ∀ (I : AutInst) (x : I.GA) (a : ℕ) (j : Fin a → ℕ) (S : Fin (a + 1) → Submodule (𝓞 I.E) (Fin I.n → I.E)), IsSatFlag I (lamX I x) j S → ∀ i : Fin a, 0 < Formalism.HN.sizeQ (bas I) (frm I x) (S i.succ) (S i.castSucc) := by
  first | exact @GlobalTheory.LeviIso.sizeQ_flag_pos | exact GlobalTheory.LeviIso.sizeQ_flag_pos | (intros; apply GlobalTheory.LeviIso.sizeQ_flag_pos <;> assumption)
