import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ChamberCoefficientTranslation
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.LabesseWaldspurger
open MeasureTheory GlobalTheory.Chamber
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chamber_coefficient_translation : FamilySmooth → ∀ (k : ℕ) (𝔞 : Submodule ℝ (A0 k)), IsLevi 𝔞 → ∀ Q ∈ parF 𝔞 ∅, ∀ X Y : Finset (SV k) → A0 k, IsOrth 𝔞 X → ∀ h : A0 k, (∀ P ∈ parP 𝔞 Q, Y P = X P + pr P h) → cM 𝔞 Q (expFam Y) 0 = cM 𝔞 Q (expFam X) 0 := by
  first | exact @GlobalTheory.Chamber.cM_expFam_shift_zero | exact GlobalTheory.Chamber.cM_expFam_shift_zero | (intros; apply GlobalTheory.Chamber.cM_expFam_shift_zero <;> assumption)
