import Mathlib

open Finset Matrix MeasureTheory
open scoped InnerProductSpace

namespace Bl.general_b_fact

theorem goal1 {R : Type*} [CommRing R] {i N : ℕ} (A : Matrix (Fin i) (Fin N) R)
    (B : Matrix (Fin N) (Fin i) R) :
    (A * B).det = ∑ f : Fin i → Fin N, (∏ a, A a (f a)) * (B.submatrix f id).det := by
  classical
  have h1 : (A * B : Matrix (Fin i) (Fin i) R) = fun a => ∑ k, A a k • B k := by
    funext a j
    simp only [Matrix.mul_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  have h2 : (A * B).det =
      (detRowAlternating : (Fin i → R) [⋀^Fin i]→ₗ[R] R).toMultilinearMap
        (fun a => ∑ k, A a k • B k) := by
    rw [Matrix.det, h1]
    rfl
  rw [h2, MultilinearMap.map_sum]
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [MultilinearMap.map_smul_univ, smul_eq_mul]
  rfl

end Bl.general_b_fact
