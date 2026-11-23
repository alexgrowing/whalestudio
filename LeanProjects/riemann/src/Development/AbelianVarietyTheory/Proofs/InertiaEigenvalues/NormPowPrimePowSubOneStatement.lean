import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormPowPrimePowSubOne
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_pow_prime_pow_sub_one_of_norm_sub_one : ∀ (l : ℕ) [Fact l.Prime] (u : ℤ_[l]) (k : ℕ), 2 ≤ k → ‖u - 1‖ = ‖((l : ℕ) : ℤ_[l])‖ ^ k → ∀ n : ℕ, ‖u ^ l ^ n - 1‖ = ‖((l : ℕ) : ℤ_[l])‖ ^ (k + n) := by
  first | exact @GlobalTheory.PadicLte.norm_pow_prime_pow_sub_one | exact GlobalTheory.PadicLte.norm_pow_prime_pow_sub_one | (intros; apply GlobalTheory.PadicLte.norm_pow_prime_pow_sub_one <;> assumption)
