import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralOfIsIdempotentElem

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj

namespace GlobalTheory

theorem exists_isIdempotentElem_tmul_one_eq_of_smooth :
    ∀ (R A : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [CommRing A] [Algebra R A],
      Algebra.Smooth R A → ∀ ε : A ⊗[R] FractionRing R, IsIdempotentElem ε →
        ∃ a : A, IsIdempotentElem a ∧ a ⊗ₜ[R] (1 : FractionRing R) = ε := by
  first
  | exact @_root_.GlobalTheory.IdempotentTensorOne.exists_idempotent_tmul_one_eq
  | exact _root_.GlobalTheory.IdempotentTensorOne.exists_idempotent_tmul_one_eq
  | (apply _root_.GlobalTheory.IdempotentTensorOne.exists_idempotent_tmul_one_eq <;> assumption)
  | (intros; apply _root_.GlobalTheory.IdempotentTensorOne.exists_idempotent_tmul_one_eq <;> assumption)
  | (intros; apply @_root_.GlobalTheory.IdempotentTensorOne.exists_idempotent_tmul_one_eq <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.IdempotentTensorOne.exists_idempotent_tmul_one_eq ..)

end GlobalTheory
