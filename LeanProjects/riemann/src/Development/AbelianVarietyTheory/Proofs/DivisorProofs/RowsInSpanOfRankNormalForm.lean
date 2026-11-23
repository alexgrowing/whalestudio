import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubMemTwistSpan
open ValuativeRel Matrix

namespace GlobalTheory

theorem rows_mem_span_of_isUnit_mul (K : Type) [Field K] (A D : Type) [Fintype A] [DecidableEq A]
    [Fintype D] [DecidableEq D] (r : ℕ) (X : Matrix A D K) (H : Matrix (Fin r) A K)
    (Q : Matrix D (Fin r) K) (hX : X.rank ≤ r) (hU : IsUnit (H * X * Q)) :
    ∀ i, ∃ s : Fin r → K, X i = s ᵥ* (H * X) := by
  intro i
  have hle : Submodule.span K (Set.range (H * X)) ≤ Submodule.span K (Set.range X) := by
    rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    have : (H * X) j = ∑ a, H j a • X a := by
      ext d; simp [Matrix.mul_apply, Finset.sum_apply]
    rw [this]
    exact Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)
  have h1 : r ≤ (H * X).rank := by
    have := Matrix.rank_mul_le_left (H * X) Q
    rw [Matrix.rank_of_isUnit _ hU] at this
    simpa using this
  have heq : Submodule.span K (Set.range (H * X)) = Submodule.span K (Set.range X) := by
    apply Submodule.eq_of_le_of_finrank_le hle
    have e1 : X.rank = Module.finrank K (Submodule.span K (Set.range X)) :=
      Matrix.rank_eq_finrank_span_row X
    have e2 : (H * X).rank = Module.finrank K (Submodule.span K (Set.range (H * X))) :=
      Matrix.rank_eq_finrank_span_row (H * X)
    omega
  have hi : X i ∈ Submodule.span K (Set.range (H * X)) := heq ▸ Submodule.subset_span ⟨i, rfl⟩
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun K).1 hi
  refine ⟨c, ?_⟩
  rw [← hc]
  ext d
  simp [Matrix.vecMul, dotProduct, Finset.sum_apply, mul_comm]

end GlobalTheory
