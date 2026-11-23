import Mathlib
open TensorProduct

theorem GlobalTheory.flat_quot_of_flat_adicCompletion : ∀ (A : Type) [CommRing A] (f : A) (M : Type) [AddCommGroup M] [Module A M],
  Module.Flat (AdicCompletion (Ideal.span {f}) A) (TensorProduct A (AdicCompletion (Ideal.span {f}) A) M) →
  Module.Flat (A ⧸ Ideal.span {f}) (TensorProduct A (A ⧸ Ideal.span {f}) M) := by
  intro A _ f M _ _ hflat
  set I : Ideal A := Ideal.span {f}
  let φ : AdicCompletion I A →ₐ[A] A ⧸ I :=
    (Ideal.quotientEquivAlgOfEq A (pow_one I)).toAlgHom.comp (AdicCompletion.evalₐ I 1)
  letI : Algebra (AdicCompletion I A) (A ⧸ I) := φ.toRingHom.toAlgebra
  haveI : IsScalarTower A (AdicCompletion I A) (A ⧸ I) := by
    refine IsScalarTower.of_algebraMap_eq (fun a => ?_)
    exact (φ.commutes a).symm
  let e := TensorProduct.AlgebraTensorModule.cancelBaseChange A (AdicCompletion I A) (A ⧸ I) (A ⧸ I) M
  haveI : Module.Flat (A ⧸ I) ((A ⧸ I) ⊗[AdicCompletion I A] (AdicCompletion I A ⊗[A] M)) := inferInstance
  exact Module.Flat.of_linearEquiv e.symm
