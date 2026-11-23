import Mathlib
open Matrix

namespace GlobalTheory

theorem exists_isotropic_dual_of_skew {V : Type*} [AddCommGroup V] [Module ℚ V] {g : ℕ}
    (B : V →ₗ[ℚ] V →ₗ[ℚ] ℚ) (ε ψ : Fin g → V) (hB : ∀ x y, B x y = -B y x)
    (hε : ∀ i j, B (ε i) (ε j) = 0)
    (hψ : ∀ i j, B (ψ j) (ε i) = if i = j then 1 else 0) :
    ∃ φ : Fin g → V, (∀ i j, B (φ i) (φ j) = 0) ∧
      (∀ i j, B (φ j) (ε i) = if i = j then 1 else 0) ∧
      ∀ j, φ j - ψ j ∈ Submodule.span ℚ (Set.range ε) := by
  classical
  have h1 : ∀ k l, B (ψ l) (ε k) = if k = l then 1 else 0 := fun k l => hψ k l
  have h2 : ∀ k l, B (ε k) (ψ l) = -(if k = l then 1 else 0) := fun k l => by
    rw [hB, h1]
  refine ⟨fun j => ψ j + ∑ k, (B (ψ j) (ψ k) / 2) • ε k, ?_, ?_, ?_⟩
  · intro i j
    simp only [map_add, map_sum, map_smul, LinearMap.add_apply, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, hε, h1, h2, mul_zero,
      Finset.sum_const_zero, add_zero, mul_ite, mul_one, mul_neg, Finset.sum_neg_distrib,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]
    linarith [hB (ψ i) (ψ j)]
  · intro i j
    simp only [map_add, map_sum, map_smul, LinearMap.add_apply, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, hε, h1, mul_zero,
      Finset.sum_const_zero, add_zero]
  · intro j
    simp only [add_sub_cancel_left]
    exact Submodule.sum_mem _ fun k _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)

theorem exists_isotropic_dual_of_skew_matrix (r g : ℕ) (Mq : Matrix (Fin r) (Fin r) ℚ)
    (ε ψ : Fin g → Fin r → ℚ) (hM : Mqᵀ = -Mq) (hε : ∀ i j, ε i ⬝ᵥ Mq *ᵥ ε j = 0)
    (hψ : ∀ i j, ψ j ⬝ᵥ Mq *ᵥ ε i = if i = j then 1 else 0) :
    ∃ φ : Fin g → Fin r → ℚ, (∀ i j, φ i ⬝ᵥ Mq *ᵥ φ j = 0) ∧
      (∀ i j, φ j ⬝ᵥ Mq *ᵥ ε i = if i = j then 1 else 0) ∧
      ∀ j, φ j - ψ j ∈ Submodule.span ℚ (Set.range ε) := by
  obtain ⟨φ, h₁, h₂, h₃⟩ := exists_isotropic_dual_of_skew (Matrix.toLinearMap₂' ℚ Mq) ε ψ
    (fun x y => by
      simp only [Matrix.toLinearMap₂'_apply']
      rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hM, Matrix.neg_mulVec,
        neg_dotProduct, dotProduct_comm])
    (fun i j => by simpa only [Matrix.toLinearMap₂'_apply'] using hε i j)
    (fun i j => by simpa only [Matrix.toLinearMap₂'_apply'] using hψ i j)
  exact ⟨φ, fun i j => by simpa only [Matrix.toLinearMap₂'_apply'] using h₁ i j,
    fun i j => by simpa only [Matrix.toLinearMap₂'_apply'] using h₂ i j, h₃⟩

end GlobalTheory
