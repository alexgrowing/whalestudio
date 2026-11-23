import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeterminantExpansionBound
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExtFormAdjEqNegSecondForm
open Matrix GlobalTheory.HermFrame
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.determinant_expansion_bound : ∀ (n : ℕ) (J : Type) [Fintype J] (f : J → Fin n → (Fin n → ℂ) → (Fin n → ℂ) → ℂ) (π : J → Equiv.Perm (Fin n)) (G : Matrix (Fin n) (Fin n) ℂ) (K : ℝ), (∀ j k, GlobalTheory.HermFrame.IsSesq (f j k)) → G.PosSemidef → (∀ x y : Fin n → Fin n → ℂ, ‖∑ j, ∏ k, f j k (x k) (y (π j k))‖ ≤ K * ∏ k, (GlobalTheory.HermFrame.gnorm G (x k) * GlobalTheory.HermFrame.gnorm G (y k))) → ‖∑ s : Equiv.Perm (Fin n), ∑ t : Equiv.Perm (Fin n), (((Equiv.Perm.sign s * Equiv.Perm.sign t : ℤˣ) : ℤ) : ℂ) * ∑ j, ∏ k, f j k (Pi.single (s k) 1) (Pi.single (t (π j k)) 1)‖ ≤ (n.factorial : ℝ) ^ 2 * K * G.det.re := by
  first | exact @GlobalTheory.MixedDiscriminant.norm_double_alt_sum_le | exact GlobalTheory.MixedDiscriminant.norm_double_alt_sum_le | (intros; apply GlobalTheory.MixedDiscriminant.norm_double_alt_sum_le <;> assumption)
