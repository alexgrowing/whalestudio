import Mathlib
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.PowPrimeRangeEqIteratedDifference
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.MemPowSub
open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pow_prime_range_eq_iterated_difference : ∀ (p : ℕ) (M : Type) [CommGroup M] (τ : M →* M) (lam : Monoid.End M), p.Prime → (∀ a, lam a = τ a / a) → (∀ a, nrm τ p a = 1) → pows p (⊤ : Subgroup M) = MonoidHom.range (lam ^ (p - 1) : Monoid.End M) ∧ ∀ a : M, a ^ p = 1 ↔ (lam ^ (p - 1) : Monoid.End M) a = 1 := by
  first | exact @GlobalTheory.CNorm.pows_eq_range_dif_pow | exact GlobalTheory.CNorm.pows_eq_range_dif_pow | (intros; apply GlobalTheory.CNorm.pows_eq_range_dif_pow <;> assumption)
