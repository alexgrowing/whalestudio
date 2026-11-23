import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.CommonModel

noncomputable section

open TensorProduct

namespace UpperTheory.Gal.crystallineComparison

theorem detRingS_of :
    RingS := by
  intro F L U B C _ _ _ _ _ _ _ _ _ _ _ τL τU h
  letI : Algebra U C := τU.toAlgebra
  let S := TensorProduct U C B
  have hS : Nontrivial S :=
    Algebra.TensorProduct.nontrivial_of_algebraMap_injective_of_flat_right U C B τU.injective
  let ψ : B →+* S := (Algebra.TensorProduct.includeRight : B →ₐ[U] S).toRingHom
  have key : ∀ c : U, algebraMap C S (τU c) = (1 : C) ⊗ₜ[U] algebraMap U B c := by
    intro c
    rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
    have e : τU c = c • (1 : C) := by
      rw [Algebra.smul_def, mul_one]
      rfl
    rw [e, TensorProduct.smul_tmul, Algebra.algebraMap_eq_smul_one]
  letI : Algebra F S := (ψ.comp (algebraMap F B)).toAlgebra
  let φ : L →ₐ[F] S :=
    { (algebraMap C S).comp τL with
      commutes' := by
        intro z
        change algebraMap C S (τL (algebraMap F L z)) = ψ (algebraMap F B z)
        rw [h z, key, IsScalarTower.algebraMap_apply F U B z]
        rfl }
  let ψ' : B →ₐ[F] S := { ψ with commutes' := fun _ => rfl }
  let π : L ⊗[F] B →+* S :=
    (Algebra.TensorProduct.lift φ ψ' (fun _ _ => Commute.all _ _)).toRingHom
  refine ⟨S, inferInstance, inferInstance, π, hS, ?_, ?_⟩
  · intro x
    change φ x * ψ' 1 = _
    rw [map_one, mul_one]
    rfl
  · intro c
    change φ 1 * ψ' (algebraMap U B c) = _
    rw [map_one, one_mul, key]
    rfl

end UpperTheory.Gal.crystallineComparison
