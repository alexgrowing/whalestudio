import Mathlib
open MeasureTheory Filter Topology
open scoped InnerProductSpace BigOperators

namespace GlobalTheory

theorem adjoint_injective_surjective_and_positive_scalar :
    ∀ (E F : Type) [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
      [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F] (A : E →ₗ[ℂ] F),
      (Function.Injective (LinearMap.adjoint A) → Function.Surjective A) ∧
      (∀ (U : Submodule ℂ F) (l : ℂ), l ≠ 0 →
        (∀ x ∈ U, ∀ y, ⟪LinearMap.adjoint A x, LinearMap.adjoint A y⟫_ℂ = l * ⟪x, y⟫_ℂ) →
        ∃ l' : ℝ, 0 < l' ∧
          (∀ x ∈ U, ∀ y, ⟪LinearMap.adjoint A x, LinearMap.adjoint A y⟫_ℂ = (l' : ℂ) * ⟪x, y⟫_ℂ) ∧
          ∀ x ∈ U, A (LinearMap.adjoint A x) = (l' : ℂ) • x) := by
  intro E F _ _ _ _ _ _ A
  constructor
  · intro hinj
    have hbot : (LinearMap.range A)ᗮ = ⊥ := by
      rw [Submodule.eq_bot_iff]
      intro v hv
      have h0 : LinearMap.adjoint A v = 0 := by
        apply ext_inner_right ℂ
        intro e
        rw [LinearMap.adjoint_inner_left, inner_zero_left]
        exact (Submodule.mem_orthogonal' _ _).mp hv (A e) ⟨e, rfl⟩
      exact hinj (h0.trans (map_zero _).symm)
    have htop : LinearMap.range A = ⊤ := Submodule.orthogonal_eq_bot_iff.mp hbot
    exact LinearMap.range_eq_top.mp htop
  · intro U l hl h
    have key : ∀ l' : ℝ, 0 < l' → l = (l' : ℂ) →
        ∃ l' : ℝ, 0 < l' ∧
          (∀ x ∈ U, ∀ y, ⟪LinearMap.adjoint A x, LinearMap.adjoint A y⟫_ℂ = (l' : ℂ) * ⟪x, y⟫_ℂ) ∧
          ∀ x ∈ U, A (LinearMap.adjoint A x) = (l' : ℂ) • x := by
      intro l' hpos hl'
      subst hl'
      refine ⟨l', hpos, h, ?_⟩
      intro x hx
      apply ext_inner_right ℂ
      intro v
      rw [← LinearMap.adjoint_inner_right, h x hx v, inner_smul_left, Complex.conj_ofReal]
    by_cases hU : U = ⊥
    · refine ⟨1, one_pos, ?_, ?_⟩
      · intro x hx y
        rw [hU, Submodule.mem_bot] at hx
        subst hx
        simp
      · intro x hx
        rw [hU, Submodule.mem_bot] at hx
        subst hx
        simp
    · obtain ⟨x, hxU, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hU
      have hxx := h x hxU x
      rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at hxx
      have hn : (0 : ℝ) < ‖x‖ ^ 2 := by positivity
      have hlval : l = ((‖LinearMap.adjoint A x‖ ^ 2 / ‖x‖ ^ 2 : ℝ) : ℂ) := by
        have hne : ((‖x‖ : ℂ)) ^ 2 ≠ 0 := by
          have : (‖x‖ : ℂ) ≠ 0 := by exact_mod_cast (norm_ne_zero_iff.mpr hx0)
          exact pow_ne_zero _ this
        push_cast
        rw [eq_div_iff hne]
        exact hxx.symm
      apply key _ _ hlval
      rcases (div_nonneg (sq_nonneg ‖LinearMap.adjoint A x‖) hn.le).lt_or_eq with hlt | heq
      · exact hlt
      · exfalso; apply hl; rw [hlval, ← heq]; simp

end GlobalTheory
