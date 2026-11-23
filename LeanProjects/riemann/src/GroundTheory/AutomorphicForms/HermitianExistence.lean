import Mathlib
import GroundTheory.AutomorphicForms.HermitianExistenceLocal
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Automorphic

open Module Matrix TensorProduct NumberField IsDedekindDomain NumberField.InfinitePlace.Completion

section Conj

variable {R A B : Type*} [Field R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
  [Algebra.IsQuadraticExtension R A] [Algebra.IsQuadraticExtension R B]

end Conj

section BaseChange

variable {K E : Type*} [Field K] [Field E] [Algebra K E] [Algebra.IsQuadraticExtension K E]
variable (R : Type*) [Field R] [Algebra K R]

instance isQuadraticExtension_tensor : Algebra.IsQuadraticExtension R (R ⊗[K] E) where
  finrank_eq_two' := by
    rw [Module.finrank_baseChange, Algebra.IsQuadraticExtension.finrank_eq_two]

variable {R}

end BaseChange

section GramRing

variable {F A : Type*} [Field F] [CommRing A] [Algebra F A] [Algebra.IsQuadraticExtension F A]
variable {W : Type*} [AddCommGroup W] [Module A W] {ι : Type*} [Fintype ι] [DecidableEq ι]

end GramRing

section Local

variable {K E : Type*} [Field K] [Field E] [Algebra K E] [Algebra.IsQuadraticExtension K E]
variable (R : Type*) [Field R] [Algebra K R]
variable {V W : Type*} [AddCommGroup V] [Module E V] [AddCommGroup W] [Module (R ⊗[K] E) W]

def HermitianForm.IsometricLocal (h : HermitianForm K E V) (hR : HermitianForm R (R ⊗[K] E) W) :
    Prop :=
  ∃ (m : ℕ) (b : Basis (Fin m) E V) (c : Basis (Fin m) (R ⊗[K] E) W),
    IsCongr (conjHom R (R ⊗[K] E))
      ((gram h.toSesq b).map (Algebra.TensorProduct.includeRight : E →ₐ[K] R ⊗[K] E))
      (gram hR.toSesq c)

variable {R}

end Local

section Coordinates

variable {K E : Type*} [Field K] [Field E] [Algebra K E] [Algebra.IsQuadraticExtension K E]
variable {d : K} (ψ : E ≃ₐ[K] QuadraticAlgebra K d 0)
variable (R : Type*) [Field R] [Algebra K R]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

variable {R}

end Coordinates

section Real

variable {K E : Type*} [Field K] [NumberField K] [Field E] [Algebra K E] [Algebra.IsQuadraticExtension K E]
variable {d : K} (ψ : E ≃ₐ[K] QuadraticAlgebra K d 0)
variable {w : InfinitePlace K} (hw : w.IsReal)

end Real

section WeakApproximation

variable {K : Type*} [Field K] [NumberField K]

end WeakApproximation

section Main

variable {K E : Type*} [Field K] [NumberField K] [Field E] [Algebra K E]
  [Algebra.IsQuadraticExtension K E]

end Main

end GroundTheory.Automorphic
