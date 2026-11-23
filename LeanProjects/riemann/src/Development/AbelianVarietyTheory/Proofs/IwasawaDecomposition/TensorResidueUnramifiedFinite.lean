import Mathlib
open IsLocalRing TensorProduct

namespace GlobalTheory

theorem tensor_quot_maximalIdeal_finite_formallyUnramified :
    ∀ (A B R : Type) [CommRing A] [CommRing B] [CommRing R] [IsLocalRing R] [Algebra A B]
      [Algebra A R], ((IsLocalRing.residue R).comp (algebraMap A R)).Finite →
      ((IsLocalRing.residue R).comp (algebraMap A R)).FormallyUnramified →
      Algebra.FormallyUnramified B (TensorProduct A B R ⧸ (IsLocalRing.maximalIdeal R).map
        (Algebra.TensorProduct.includeRight : R →ₐ[A] TensorProduct A B R)) ∧
      Module.Finite B (TensorProduct A B R ⧸ (IsLocalRing.maximalIdeal R).map
        (Algebra.TensorProduct.includeRight : R →ₐ[A] TensorProduct A B R)) := by
  intro A B R _ _ _ _ _ _ hfin hfu
  have hf : Module.Finite A (R ⧸ maximalIdeal R) := by
    rw [← RingHom.finite_algebraMap]; exact hfin
  have hu : Algebra.FormallyUnramified A (R ⧸ maximalIdeal R) := by
    rw [← RingHom.formallyUnramified_algebraMap]; exact hfu
  let e := Algebra.TensorProduct.tensorQuotientEquiv (R := A) B R B (maximalIdeal R)
  haveI : Algebra.FormallyUnramified B (B ⊗[A] (R ⧸ maximalIdeal R)) :=
    Algebra.FormallyUnramified.base_change B
  haveI : Module.Finite B (B ⊗[A] (R ⧸ maximalIdeal R)) := Module.Finite.base_change A B _
  exact ⟨Algebra.FormallyUnramified.of_equiv e, Module.Finite.equiv e.toLinearEquiv⟩

end GlobalTheory
