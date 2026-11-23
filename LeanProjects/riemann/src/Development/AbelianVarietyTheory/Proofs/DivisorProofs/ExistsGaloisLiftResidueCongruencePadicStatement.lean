import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGaloisLiftResidueCongruencePadic
import Mathlib
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_galois_lift_residue_congruence_padic : ∀ (l : ℕ) [Fact l.Prime] (L : IntermediateField ℚ_[l] (PadicAlgCl l)) [FiniteDimensional ℚ_[l] L] (J : Type) (a b : J → PadicAlgCl l), (∀ j, ‖a j‖ ≤ 1) → (∀ j, ‖b j‖ ≤ 1) → (∀ p : MvPolynomial J (PadicAlgCl l), (∀ n, p.coeff n ∈ L ∧ ‖p.coeff n‖ ≤ 1) → (‖MvPolynomial.eval a p‖ < 1 ↔ ‖MvPolynomial.eval b p‖ < 1)) → ∃ g : PadicAlgCl l ≃ₐ[L] PadicAlgCl l, ∀ j, ‖g (a j) - b j‖ < 1 := by
  first | exact @GlobalTheory.ResidueLift.main | exact GlobalTheory.ResidueLift.main | (intros; apply GlobalTheory.ResidueLift.main <;> assumption)
