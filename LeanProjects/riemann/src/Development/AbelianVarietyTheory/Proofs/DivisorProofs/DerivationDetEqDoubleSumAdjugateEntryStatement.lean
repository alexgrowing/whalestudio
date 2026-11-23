import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DerivationDetEqDoubleSumAdjugateEntry
import Mathlib
open MvPolynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.derivation_det_eq_double_sum_adjugate_entry : ∀ {K R : Type} [CommRing K] [CommRing R] [Algebra K R] (δ : Derivation K R R) {ι : Type} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι R), δ M.det = ∑ i, ∑ j, M.adjugate j i * δ (M i j) := by
  first | exact @GlobalTheory.DetDeriv.main | exact GlobalTheory.DetDeriv.main | (intros; apply GlobalTheory.DetDeriv.main <;> assumption)
