import Mathlib
open TensorProduct Module

theorem GlobalTheory.tensorBasisCoords : ∀ (F : Type) [Field F] (B : Type) [CommRing B] [Algebra F B] (V : Type) [AddCommGroup V] [Module F V] (n : Type) [Fintype n] [DecidableEq n] (b : Basis n F V), ∃ e : V ⊗[F] B ≃ₗ[F] (n → B), (∀ v x i, e (v ⊗ₜ[F] x) i = b.repr v i • x) ∧ (∀ y : n → B, e.symm y = ∑ i, b i ⊗ₜ[F] y i) ∧ ∀ (r : V →ₗ[F] V) (f : B →ₗ[F] B) (y : V ⊗[F] B), e (TensorProduct.map r f y) = ((LinearMap.toMatrix b b r).map (algebraMap F B)).mulVec (fun i => f (e y i)) := by
  intro F _ B _ _ V _ _ n _ _ b
  let e : V ⊗[F] B ≃ₗ[F] (n → B) :=
    (TensorProduct.comm F V B) ≪≫ₗ (TensorProduct.congr (LinearEquiv.refl F B) b.equivFun) ≪≫ₗ
      TensorProduct.piScalarRight F F B n
  have h1 : ∀ v x i, e (v ⊗ₜ[F] x) i = b.repr v i • x := by
    intro v x i
    simp [e, TensorProduct.piScalarRight_apply, TensorProduct.piScalarRightHom_tmul]
  have hadd : ∀ y z : V ⊗[F] B, e (y + z) = e y + e z := fun y z => map_add e y z
  refine ⟨e, h1, ?_, ?_⟩
  · intro y
    rw [LinearEquiv.symm_apply_eq]
    funext j
    rw [map_sum, Finset.sum_apply]
    simp only [h1, Basis.repr_self, Finsupp.single_apply]
    simp
  · intro r f y
    induction y using TensorProduct.induction_on with
    | zero =>
      simp only [map_zero]
      rw [show (fun _ : n => f ((0 : n → B) _)) = 0 from by funext i; simp, Matrix.mulVec_zero]
    | tmul v x =>
      funext i
      rw [TensorProduct.map_tmul, h1]
      simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, LinearMap.toMatrix_apply, h1, map_smul]
      simp_rw [← Algebra.smul_def, smul_smul]
      rw [← Finset.sum_smul]
      congr 1
      conv_lhs => rw [← b.sum_repr v]
      rw [map_sum, map_sum, Finsupp.finset_sum_apply]
      simp only [map_smul, Finsupp.smul_apply, smul_eq_mul]
      exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
    | add y z hy hz =>
      rw [map_add, hadd, hy, hz, hadd, ← Matrix.mulVec_add]
      congr 1
      funext i
      simp [map_add]
