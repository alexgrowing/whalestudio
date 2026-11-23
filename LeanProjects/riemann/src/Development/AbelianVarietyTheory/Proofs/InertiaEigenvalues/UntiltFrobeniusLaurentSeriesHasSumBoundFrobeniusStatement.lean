import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UntiltFrobeniusLaurentSeriesHasSumBoundFrobenius
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ImportsAlt
open Formalism.Per GlobalTheory.PSer
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.untiltFrobeniusLaurentSeries_hasSum_bound_frobenius : ∀ (l : ℕ) [Fact l.Prime] (h j : ℕ) (r : ℝ) (x : Fl l), 1 ≤ h → r < 1 → ‖sh x‖ ≤ r → HasSum (fun n : ℤ => (l : ℂ_[l]) ^ (-n) * sh (pw (n * h + j) x)) (lam h j x) ∧ ‖lam h j x‖ ≤ gam l h j r ∧ lam h j (x ^ l ^ h) = (l : ℂ_[l]) * lam h j x ∧ lam h j (x ^ l) = lam h (j + 1) x := by
  first | exact @GlobalTheory.PSer.lam_hasSum_norm_le_frob | exact GlobalTheory.PSer.lam_hasSum_norm_le_frob | (intros; apply GlobalTheory.PSer.lam_hasSum_norm_le_frob <;> assumption)
