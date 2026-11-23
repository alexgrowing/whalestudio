import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PadicIntExistsPowSubNormLeOfExactLevel
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.padicInt_exists_pow_sub_norm_le_of_exact_level' : ∀ (l : ℕ) [Fact l.Prime] (u v : ℤ_[l]) (m : ℕ), 1 ≤ m → ‖u - 1‖ = ‖((l : ℕ) : ℤ_[l])‖ ^ m → ‖v - 1‖ ≤ ‖((l : ℕ) : ℤ_[l])‖ ^ m → ∃ i : ℕ, ‖u ^ i - v‖ ≤ ‖((l : ℕ) : ℤ_[l])‖ ^ (m + 1) := by
  first | exact @GlobalTheory.padicInt_exists_pow_sub_norm_le_of_exact_level | exact GlobalTheory.padicInt_exists_pow_sub_norm_le_of_exact_level | (intros; apply GlobalTheory.padicInt_exists_pow_sub_norm_le_of_exact_level <;> assumption)
