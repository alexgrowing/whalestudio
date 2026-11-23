import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
open GlobalTheory.UnitLemma Polynomial

namespace GlobalTheory.UnitLemma.InvAlg

theorem gramDet_eq_norm_mul (K : UQ) (B : InvAlg K) (x : B.A) :
    B.gramDet x = Algebra.norm K.E x * B.gramDet 1 := by
  classical
  set b := Module.finBasis K.E B.A
  have hM : (Matrix.of fun i j => B.herm x (b i) (b j)) =
      (Algebra.leftMulMatrix b x).transpose * (Matrix.of fun i j => B.herm 1 (b i) (b j)) := by
    ext i j
    simp only [Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply, herm, one_mul,
      Algebra.leftMulMatrix_apply]
    have h := b.sum_repr (x * b i)
    conv_lhs => rw [← h]
    rw [Finset.sum_mul, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [smul_mul_assoc, map_smul, smul_eq_mul, LinearMap.toMatrix_apply]
    simp
  unfold gramDet
  rw [hM, Matrix.det_mul, Matrix.det_transpose, Algebra.norm_eq_matrix_det b]

end GlobalTheory.UnitLemma.InvAlg
