import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ChamberCoefficientProductFormula
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.LabesseWaldspurger
open MeasureTheory GlobalTheory.Chamber
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chamber_coefficient_product_formula : ExpFamilyIntegral → FamilyProduct → ∀ (k : ℕ) (𝔞 : Submodule ℝ (A0 k)), IsLevi 𝔞 → ∀ X Y W : Finset (SV k) → A0 k, IsOrth 𝔞 X → IsOrth 𝔞 Y → (∀ P ∈ parF 𝔞 ∅, W P = X P + Y P) → ((∫ H : aMQ 𝔞 ∅, gamM 𝔞 ∅ W H : ℝ) : ℂ) = cM 𝔞 ∅ (expFam W) 0 ∧ cM 𝔞 ∅ (expFam W) 0 = ∑ Q ∈ parF 𝔞 ∅, cM 𝔞 Q (expFam X) 0 * cP Q ∅ (expFam Y) 0 ∧ cP ∅ ∅ (expFam Y) 0 = 1 := by
  first | exact @GlobalTheory.Chamber.SumSplit.volume_sum_split | exact GlobalTheory.Chamber.SumSplit.volume_sum_split | (intros; apply GlobalTheory.Chamber.SumSplit.volume_sum_split <;> assumption)
