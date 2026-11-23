import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormHasSumEqOfDominant
import Mathlib
open Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_eq_of_hasSum_of_dominant_term : ∀ (K : Type) [NormedField K] [IsUltrametricDist K] (ι : Type) (f : ι → K) (s : K) (i₀ : ι), HasSum f s → (∀ i, i ≠ i₀ → ‖f i‖ < ‖f i₀‖) → ‖s‖ = ‖f i₀‖ := by
  first | exact @GlobalTheory.norm_hasSum_eq_of_dominant | exact GlobalTheory.norm_hasSum_eq_of_dominant | (intros; apply GlobalTheory.norm_hasSum_eq_of_dominant <;> assumption)
