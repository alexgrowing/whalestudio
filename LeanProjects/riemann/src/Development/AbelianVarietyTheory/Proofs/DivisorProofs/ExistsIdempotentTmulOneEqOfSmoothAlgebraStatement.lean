import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIdempotentTmulOneEqOfSmoothAlgebra
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_idempotent_tmul_one_eq_of_smooth_algebra : ∀ (R A : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [CommRing A] [Algebra R A], Algebra.Smooth R A → ∀ ε : A ⊗[R] FractionRing R, IsIdempotentElem ε → ∃ a : A, IsIdempotentElem a ∧ a ⊗ₜ[R] (1 : FractionRing R) = ε := by
  first | exact @GlobalTheory.exists_isIdempotentElem_tmul_one_eq_of_smooth | exact GlobalTheory.exists_isIdempotentElem_tmul_one_eq_of_smooth | (intros; apply GlobalTheory.exists_isIdempotentElem_tmul_one_eq_of_smooth <;> assumption)
