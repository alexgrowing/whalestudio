import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.OneLeDedekindZetaRealValueAndLeZetaPow
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsGaugeAll
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.one_le_dedekindZetaRealValue_and_le_zeta_pow : ∀ (E : Type) [Field E] [NumberField E] (l : ℕ), 2 ≤ l → 1 ≤ zetaE E l ∧ zetaE E l ≤ (∑' m : ℕ, 1 / ((m : ℝ) + 1) ^ l) ^ Module.finrank ℚ E := by
  first | exact @GlobalTheory.DedekindZetaBound.one_le_zetaE_and_le | exact GlobalTheory.DedekindZetaBound.one_le_zetaE_and_le | (intros; apply GlobalTheory.DedekindZetaBound.one_le_zetaE_and_le <;> assumption)
