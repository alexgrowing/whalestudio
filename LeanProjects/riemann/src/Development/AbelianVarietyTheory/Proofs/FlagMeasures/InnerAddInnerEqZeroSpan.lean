import Mathlib

namespace GlobalTheory.InnerSumZeroSpan

theorem main : (let d1 : ℕ → Type := @(fun (n : ℕ) ↦ EuclideanSpace ℂ (Fin n)); ∀ {n : ℕ} (L M : d1 n →L[ℂ] d1 n) (s t : Set (d1 n)), (∀ u ∈ s, ∀ z ∈ t, Inner.inner ℂ ((L : d1 n → d1 n) u) z + Inner.inner ℂ u ((M : d1 n → d1 n) z) = (0 : ℂ)) → ∀ u ∈ Submodule.span ℂ s, ∀ z ∈ Submodule.span ℂ t, Inner.inner ℂ ((L : d1 n → d1 n) u) z + Inner.inner ℂ u ((M : d1 n → d1 n) z) = (0 : ℂ)) := by
  intro d1 n L M s t h u hu z hz
  induction hz using Submodule.span_induction with
  | mem z hz' =>
    induction hu using Submodule.span_induction with
    | mem u hu' => exact h u hu' z hz'
    | zero => simp
    | add x y _ _ hx hy =>
      rw [map_add, inner_add_left, inner_add_left, add_add_add_comm, hx, hy, add_zero]
    | smul c x _ hx =>
      rw [map_smul, inner_smul_left, inner_smul_left, ← mul_add, hx, mul_zero]
  | zero => simp
  | add x y _ _ hx hy =>
    rw [map_add, inner_add_right, inner_add_right, add_add_add_comm, hx, hy, add_zero]
  | smul c x _ hx =>
    rw [map_smul, inner_smul_right, inner_smul_right, ← mul_add, hx, mul_zero]

end GlobalTheory.InnerSumZeroSpan
