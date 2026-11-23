import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DerivationExtendMvPolynomial
import Mathlib
open IsLocalRing TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_derivation_extend_mvPolynomial : ∀ (B τ : Type) [CommRing B] (D : Derivation ℤ B B), ∃ D' : Derivation ℤ (MvPolynomial τ B) (MvPolynomial τ B), (∀ x, D' (MvPolynomial.C x) = MvPolynomial.C (D x)) ∧ ∀ t, D' (MvPolynomial.X t) = 0 := by
  first | exact @GlobalTheory.derivation_extend_mvPolynomial | exact GlobalTheory.derivation_extend_mvPolynomial | (intros; apply GlobalTheory.derivation_extend_mvPolynomial <;> assumption)
