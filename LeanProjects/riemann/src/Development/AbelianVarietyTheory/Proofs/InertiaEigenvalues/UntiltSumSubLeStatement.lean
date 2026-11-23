import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UntiltSumSubLe
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ImportsAlt
open Formalism.Per GlobalTheory.PSer
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_sh_sum_sub_sum_sh_le : ∀ (l : ℕ) [Fact l.Prime] (ι : Type) (s : Finset ι) (r : ℝ) (x : ι → Fl l), 0 ≤ r → (∀ i ∈ s, ‖sh (x i)‖ ≤ r) → ‖sh (∑ i ∈ s, x i) - ∑ i ∈ s, sh (x i)‖ ≤ ‖(l : ℂ_[l])‖ * r ∧ ‖sh (∑ i ∈ s, x i)‖ ≤ r := by
  first | exact @GlobalTheory.untilt_sum_sub_le | exact GlobalTheory.untilt_sum_sub_le | (intros; apply GlobalTheory.untilt_sum_sub_le <;> assumption)
