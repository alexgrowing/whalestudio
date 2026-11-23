import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.COnePropertyFiniteExtension
import Mathlib
open IsLocalRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.c_one_property_finite_extension : ∀ (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L], (∀ (n d : ℕ) (f : MvPolynomial (Fin n) K), f.IsHomogeneous d → 0 < d → d < n → ∃ x : Fin n → K, x ≠ 0 ∧ MvPolynomial.eval x f = 0) → (∀ (n d : ℕ) (f : MvPolynomial (Fin n) L), f.IsHomogeneous d → 0 < d → d < n → ∃ x : Fin n → L, x ≠ 0 ∧ MvPolynomial.eval x f = 0) := by
  first | exact @GlobalTheory.c_one_of_finite_extension | exact GlobalTheory.c_one_of_finite_extension | (intros; apply GlobalTheory.c_one_of_finite_extension <;> assumption)
