import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TiltOrthOfUntiltOrth
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ImportsAlt
open Formalism.Per GlobalTheory.PSer
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_sh_le_sh_int_sum_of_orthogonal : ∀ (l : ℕ) [Fact l.Prime] (h : ℕ) (m : Fin h → Fl l), (∀ i j, ‖sh (m i)‖ < l * ‖sh (m j)‖) →
    (∀ (c : Fin h → ℚ_[l]) (j : Fin h), ‖c j‖ * ‖sh (m j)‖ ≤ ‖∑ i, algebraMap ℚ_[l] ℂ_[l] (c i) * sh (m i)‖) →
    ∀ (c : Fin h → ℤ) (j : Fin h), ¬ (l : ℤ) ∣ c j → ‖sh (m j)‖ ≤ ‖sh (∑ i, (c i : Fl l) * m i)‖ := by
  first | exact @GlobalTheory.tilt_orth_of_untilt_orth | exact GlobalTheory.tilt_orth_of_untilt_orth | (intros; apply GlobalTheory.tilt_orth_of_untilt_orth <;> assumption)
