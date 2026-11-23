import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjectiveBaseChangeOfPresentationMatrixSplit
import Mathlib
open CategoryTheory Limits TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.projective_baseChange_of_presentation_matrix_split : ∀ (R B M : Type) [CommRing R] [CommRing B] [Algebra R B] [AddCommGroup M]
    [Module R M] (n m : ℕ) (π : (Fin n → R) →ₗ[R] M), Function.Surjective π →
    ∀ (r : Fin m → Fin n → R), Submodule.span R (Set.range r) = LinearMap.ker π →
    ∀ (v : Fin n → Fin n → B) (w : Fin n → Fin m → B),
    (∀ b l, ∑ a, algebraMap R B (r b a) * v a l = 0) →
    (∀ a l, v a l = (if a = l then 1 else 0) + ∑ b, w a b * algebraMap R B (r b l)) →
    Module.Projective B (B ⊗[R] M) := by
  first | (exact @GlobalTheory.projective_baseChange_of_presentation_split) | (exact GlobalTheory.projective_baseChange_of_presentation_split) | (intros; apply GlobalTheory.projective_baseChange_of_presentation_split <;> assumption)
