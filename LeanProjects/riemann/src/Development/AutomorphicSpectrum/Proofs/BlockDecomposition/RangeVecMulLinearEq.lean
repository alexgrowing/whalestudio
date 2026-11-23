import Mathlib

namespace GlobalTheory.CompanionTheory.MatrixRowSpace

variable {K : Type} [Field K]

theorem row_mul {m n r : ℕ} (x : Matrix (Fin m) (Fin r) K) (c : Matrix (Fin r) (Fin n) K)
    (i : Fin m) : (x * c) i = c.vecMulLinear (x i) := by
  ext j
  simp [Matrix.mul_apply, Matrix.vecMul, dotProduct]

theorem range_vecMulLinear_eq {n r : ℕ} (c : Matrix (Fin r) (Fin n) K) :
    LinearMap.range c.vecMulLinear = Submodule.span K (Set.range c) := by
  apply le_antisymm
  · rintro _ ⟨v, rfl⟩
    rw [Matrix.vecMulLinear_apply, Matrix.vecMul_eq_sum]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  · rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    refine ⟨Pi.single i 1, ?_⟩
    ext j
    simp [Matrix.vecMul, dotProduct, Pi.single_apply]

theorem span_rows_mul {m n r : ℕ} (x : Matrix (Fin m) (Fin r) K) (c : Matrix (Fin r) (Fin n) K) :
    Submodule.span K (Set.range (x * c)) =
      (Submodule.span K (Set.range x)).map c.vecMulLinear := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    rw [row_mul]
    exact Submodule.mem_map_of_mem (Submodule.subset_span ⟨i, rfl⟩)
  · rw [Submodule.map_le_iff_le_comap, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_comap, ← row_mul]
    exact Submodule.subset_span ⟨i, rfl⟩

theorem span_rows_eq_top_iff {m r : ℕ} (x : Matrix (Fin m) (Fin r) K) :
    x.rank = r ↔ Submodule.span K (Set.range x) = ⊤ := by
  rw [Matrix.rank_eq_finrank_span_row]
  constructor
  · intro h
    exact Submodule.eq_top_of_finrank_eq (h.trans (by simp))
  · intro h
    have h' : Submodule.span K (Set.range x.row) = ⊤ := h
    rw [h', finrank_top]
    simp

theorem span_rows_mul_of_rank {m n r : ℕ} (x : Matrix (Fin m) (Fin r) K)
    (c : Matrix (Fin r) (Fin n) K) (hx : x.rank = r) :
    Submodule.span K (Set.range (x * c)) = Submodule.span K (Set.range c) := by
  rw [span_rows_mul, (span_rows_eq_top_iff x).mp hx, Submodule.map_top, range_vecMulLinear_eq]

end GlobalTheory.CompanionTheory.MatrixRowSpace
