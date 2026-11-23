import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.ResidueOfTraceIsFiberSum

open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

private theorem det_submatrix_orderEmbOfFin_eq_subtype {R : Type*} [CommRing R] {d k : ℕ}
    (B : Matrix (Fin d) (Fin d) R) (s : Finset (Fin d)) (h : s.card = k) :
    (B.submatrix (s.orderEmbOfFin h) (s.orderEmbOfFin h)).det =
      (B.submatrix (Subtype.val : s → Fin d) Subtype.val).det := by
  rw [← Matrix.det_submatrix_equiv_self (s.orderIsoOfFin h).toEquiv
    (B.submatrix (Subtype.val : s → Fin d) Subtype.val)]
  rfl

theorem UpperTheory.Gal.productCup_of_system.minorSum_of :
    MinorSum := by
  intro d a A
  rw [Matrix.coeff_det_one_add_X_smul_eq_sum_minors]
  refine Finset.sum_congr rfl fun S _ => ?_
  exact (det_submatrix_orderEmbOfFin_eq_subtype A S _).symm
