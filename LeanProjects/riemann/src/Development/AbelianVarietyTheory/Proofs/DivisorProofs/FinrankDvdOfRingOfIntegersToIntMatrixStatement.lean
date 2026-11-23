import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankDvdOfRingOfIntegersToIntMatrix
import Mathlib
open NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finrank_dvd_of_ringOfIntegers_to_int_matrix : ∀ (E : Type) [Field E] [NumberField E] {r : ℕ} (ρ : 𝓞 E →+* Matrix (Fin r) (Fin r) ℤ), ∃ s : ℕ, r = s * Module.finrank ℚ E := by
  first | exact @GlobalTheory.finrank_dvd_of_ringOfIntegers_to_matrix | exact GlobalTheory.finrank_dvd_of_ringOfIntegers_to_matrix | (intros; apply GlobalTheory.finrank_dvd_of_ringOfIntegers_to_matrix <;> assumption)
