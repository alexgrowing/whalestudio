import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HaarLieNilpotentEqLebesgue
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.BlockAnti
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.haar_lie_nilpotent_eq_lebesgue : ∀ k r : ℕ, haarLie (Nset k r) 1 = (2 ^ (r * (k + 1) + r * (r - 1)) : ℝ≥0∞) • lebN k r := by
  first | exact @GlobalTheory.Amp.NLie.haarLie_eq_lebN | exact GlobalTheory.Amp.NLie.haarLie_eq_lebN | (intros; apply GlobalTheory.Amp.NLie.haarLie_eq_lebN <;> assumption)
