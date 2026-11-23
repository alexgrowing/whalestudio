import Mathlib

namespace GlobalTheory.NormBoundOfSpan

theorem norm_le_of_mem_span {K E ι : Type} [NormedField K] [AddCommGroup E] [Module K E]
    (φ : ι → E →ₗ[K] K) :
    ∀ f ∈ Submodule.span K (Set.range φ), ∃ (C : ℝ), (0 : ℝ) ≤ C ∧ ∀ (p : E) (r : ℝ),
      (0 : ℝ) ≤ r → (∀ (j : ι), ‖(φ j : E → K) p‖ ≤ r) → ‖(f : E → K) p‖ ≤ C * r := by
  intro f hf
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨j, rfl⟩ := hx
    exact ⟨1, zero_le_one, fun p r _ h => by simpa using h j⟩
  | zero => exact ⟨0, le_rfl, fun p r _ _ => by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨C, hC, h1⟩ := hx
    obtain ⟨D, hD, h2⟩ := hy
    refine ⟨C + D, add_nonneg hC hD, fun p r hr h => ?_⟩
    rw [LinearMap.add_apply, add_mul]
    exact (norm_add_le _ _).trans (add_le_add (h1 p r hr h) (h2 p r hr h))
  | smul a x _ hx =>
    obtain ⟨C, hC, h1⟩ := hx
    refine ⟨‖a‖ * C, mul_nonneg (norm_nonneg a) hC, fun p r hr h => ?_⟩
    rw [LinearMap.smul_apply, smul_eq_mul, norm_mul, mul_assoc]
    exact mul_le_mul_of_nonneg_left (h1 p r hr h) (norm_nonneg a)

end GlobalTheory.NormBoundOfSpan
