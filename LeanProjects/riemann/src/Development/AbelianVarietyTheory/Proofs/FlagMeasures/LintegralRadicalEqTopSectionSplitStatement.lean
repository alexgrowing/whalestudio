import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LintegralRadicalEqTopSectionSplit
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsNormalFormStabilizerMeasure
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lintegral_radical_eq_top_section_split : ∀ (k r j : ℕ) (f : Mat k r → ℝ≥0∞), Measurable (fun x : Mt k r => f (Matrix.of x)) → ∫⁻ q : PPar k r, f (pOf k r q) = ∫⁻ q' : PSec k r j, ∫⁻ q : PTop k r j, f (pTop k r j q * pSec k r j q') := by
  first | exact @GlobalTheory.Amp.PSplit.lintegral_split | exact GlobalTheory.Amp.PSplit.lintegral_split | (intros; apply GlobalTheory.Amp.PSplit.lintegral_split <;> assumption)
