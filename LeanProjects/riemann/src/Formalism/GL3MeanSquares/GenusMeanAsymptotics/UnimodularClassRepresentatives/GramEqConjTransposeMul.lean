import Mathlib
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.MassLandG

open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3

theorem gram_eq_conjTranspose_mul {K V : Type*} [Field K] [StarRing K] [AddCommGroup V] [Module K V]
    {n : ℕ} (h : V →ₗ⋆[K] V →ₗ[K] K) (b b' : Basis (Fin n) K V) :
    gram h b = (b'.toMatrix b).conjTranspose * gram h b' * b'.toMatrix b := by
  ext i j
  simp only [gram, Matrix.of_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Basis.toMatrix_apply]
  conv_lhs => rw [← b'.sum_repr (b i), ← b'.sum_repr (b j)]
  simp only [map_sum, LinearMap.sum_apply, LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul,
    starRingEnd_apply, RingHom.id_apply, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun m _ => ?_
  ring

theorem gram_det_change {K V : Type*} [Field K] [StarRing K] [AddCommGroup V] [Module K V] {n : ℕ}
    (h : V →ₗ⋆[K] V →ₗ[K] K) (b b' : Basis (Fin n) K V) :
    (gram h b).det = star (b'.det b) * b'.det b * (gram h b').det := by
  rw [gram_eq_conjTranspose_mul h b b', Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose,
    Basis.det_apply]
  ring

end Formalism.HermitianLattices.Ext.L3
