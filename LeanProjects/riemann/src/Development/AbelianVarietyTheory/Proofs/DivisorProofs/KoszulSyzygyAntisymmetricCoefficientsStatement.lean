import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KoszulSyzygyAntisymmetricCoefficients
open MvPolynomial Finset
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.koszul_syzygy_antisymmetric_coefficients : ∀ (A : Type) [CommRing A] (r : ℕ) (G : Fin r → MvPolynomial (Fin r) A), ∑ i, X i * G i = 0 → ∃ H : Fin r → Fin r → MvPolynomial (Fin r) A, (∀ i j, H i j = -H j i) ∧ (∀ i, H i i = 0) ∧ ∀ i, G i = ∑ j, X j * H i j := by
  first | exact @GlobalTheory.koszul_relations_among_variables | exact GlobalTheory.koszul_relations_among_variables | (intros; apply GlobalTheory.koszul_relations_among_variables <;> assumption)
