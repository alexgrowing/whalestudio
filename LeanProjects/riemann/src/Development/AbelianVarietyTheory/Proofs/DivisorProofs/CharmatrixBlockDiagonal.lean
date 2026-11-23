import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.TensorProductAction
open scoped TensorProduct nonZeroDivisors

namespace GlobalTheory.FibreCharpoly

theorem charmatrix_blockDiagonal {m o R : Type} [Fintype m] [DecidableEq m] [Fintype o]
    [DecidableEq o] [CommRing R] (B : o → Matrix m m R) :
    Matrix.charmatrix (Matrix.blockDiagonal B) =
      Matrix.blockDiagonal (fun k => Matrix.charmatrix (B k)) := by
  ext ⟨i, k⟩ ⟨j, k'⟩
  simp only [Matrix.charmatrix_apply, Matrix.blockDiagonal_apply, Matrix.diagonal_apply,
    Prod.mk.injEq]
  split_ifs <;> simp_all

theorem charpoly_blockDiagonal {m o R : Type} [Fintype m] [DecidableEq m] [Fintype o]
    [DecidableEq o] [CommRing R] (B : o → Matrix m m R) :
    (Matrix.blockDiagonal B).charpoly = ∏ k, (B k).charpoly := by
  rw [Matrix.charpoly, charmatrix_blockDiagonal, Matrix.det_blockDiagonal]
  rfl

theorem charpoly_lsmul_eq_pow (Λ O T : Type) [CommRing Λ] [CommRing O] [Algebra Λ O]
    [Module.Free Λ O] [Module.Finite Λ O] [AddCommGroup T] [Module Λ T] [Module O T]
    [IsScalarTower Λ O T] [Module.Free Λ T] [Module.Finite Λ T] {N : ℕ}
    (b : Module.Basis (Fin N) O T) (a : O) :
    LinearMap.charpoly (Algebra.lsmul Λ Λ T a) =
      (LinearMap.charpoly (LinearMap.mulLeft Λ a)) ^ N := by
  classical
  let c := Module.Free.chooseBasis Λ O
  rw [← LinearMap.charpoly_toMatrix _ (c.smulTower b),
    ← LinearMap.charpoly_toMatrix (LinearMap.mulLeft Λ a) c]
  have hM : LinearMap.toMatrix (c.smulTower b) (c.smulTower b) (Algebra.lsmul Λ Λ T a) =
      Matrix.blockDiagonal (fun _ => LinearMap.toMatrix c c (LinearMap.mulLeft Λ a)) := by
    ext ⟨i, k⟩ ⟨j, k'⟩
    simp only [LinearMap.toMatrix_apply, Module.Basis.smulTower_apply, Module.Basis.smulTower_repr,
      Matrix.blockDiagonal_apply, Algebra.lsmul_coe, smul_smul, Module.Basis.repr_smul,
      Module.Basis.repr_self, Finsupp.smul_single, Finsupp.single_apply, LinearMap.mulLeft_apply,
      smul_eq_mul, mul_one]
    split_ifs with h1 h2 h2 <;> simp_all
  rw [hM, charpoly_blockDiagonal, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

end GlobalTheory.FibreCharpoly
