import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MapConjLebesgueCommonStabilizerNormalForm
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsNormalFormStabilizerMeasure
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.map_conj_lebesgueCommonStabilizerNormalForm : ∀ (k r j : ℕ) (hj : j ≤ r) (z z' : (Fin (2 * r + k + 1) → ℂ)), ∀ (g₀ : Mat k r) (β : Fin r → ℕ) (c : ℂ), inWb k r z → inWb k r z' → 0 < Tz k r z → IsNormal0 k r hj β c z z' g₀ → (lebR0 k r j β).map (conjM g₀) = lebR0 k r j β := by
  first | exact @GlobalTheory.Amp.RConj.lebR0_map_conjM_eq_of_isNormalZero | exact GlobalTheory.Amp.RConj.lebR0_map_conjM_eq_of_isNormalZero | (intros; apply GlobalTheory.Amp.RConj.lebR0_map_conjM_eq_of_isNormalZero <;> assumption)
