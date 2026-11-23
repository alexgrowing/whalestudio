import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms

open Formalism.MainNotions.S
open scoped InnerProductSpace

namespace GlobalTheory

theorem hsNormSq_eq_sum_stdBasis {V H : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V] [NormedAddCommGroup H] [InnerProductSpace ℂ H] (A : V →L[ℂ] H) :
    hsNormSq A = ∑ i, ‖A (stdOrthonormalBasis ℂ V i)‖ ^ 2 := by
  unfold hsNormSq hsInner
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact inner_self_eq_norm_sq (𝕜 := ℂ) _

theorem sum_norm_sq_le_hsNormSq {V H : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
    (A : V →L[ℂ] H) {ι : Type} [Fintype ι] (v : ι → V) (hv : Orthonormal ℂ v) :
    ∑ i, ‖A (v i)‖ ^ 2 ≤ hsNormSq A := by
  set e := stdOrthonormalBasis ℂ V with he
  set f := stdOrthonormalBasis ℂ H
  have key : ∀ (x : V) (y : H), ‖⟪y, A x⟫_ℂ‖ = ‖⟪x, (ContinuousLinearMap.adjoint A) y⟫_ℂ‖ := by
    intro x y
    rw [← ContinuousLinearMap.adjoint_inner_left, norm_inner_symm]
  calc ∑ i, ‖A (v i)‖ ^ 2
      = ∑ i, ∑ j, ‖⟪f j, A (v i)⟫_ℂ‖ ^ 2 := by
        simp_rw [f.sum_sq_norm_inner_right]
    _ = ∑ j, ∑ i, ‖⟪v i, (ContinuousLinearMap.adjoint A) (f j)⟫_ℂ‖ ^ 2 := by
        rw [Finset.sum_comm]
        simp_rw [key]
    _ ≤ ∑ j, ‖(ContinuousLinearMap.adjoint A) (f j)‖ ^ 2 :=
        Finset.sum_le_sum fun j _ => hv.sum_inner_products_le _
    _ = ∑ j, ∑ i, ‖⟪e i, (ContinuousLinearMap.adjoint A) (f j)⟫_ℂ‖ ^ 2 := by
        simp_rw [e.sum_sq_norm_inner_right]
    _ = ∑ i, ∑ j, ‖⟪f j, A (e i)⟫_ℂ‖ ^ 2 := by
        rw [Finset.sum_comm]
        simp_rw [key]
    _ = hsNormSq A := by
        rw [hsNormSq_eq_sum_stdBasis, ← he]
        simp_rw [f.sum_sq_norm_inner_right]

end GlobalTheory
