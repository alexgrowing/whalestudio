import Mathlib
open SchwartzMap

namespace GlobalTheory

theorem coercive_of_re_pos (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (Q : V →ₗ[ℝ] V →ₗ[ℝ] ℂ) (hQ : ∀ x, x ≠ 0 → 0 < (Q x x).re) :
    ∃ c : ℝ, 0 < c ∧ ∀ x, c * ‖x‖ ^ 2 ≤ (Q x x).re := by
  by_cases hV : ∃ x : V, x ≠ 0
  · haveI : Nontrivial V := ⟨⟨_, 0, hV.choose_spec⟩⟩
    let Q1 : V →ₗ[ℝ] (V →L[ℝ] ℂ) :=
      (LinearMap.toContinuousLinearMap : (V →ₗ[ℝ] ℂ) ≃ₗ[ℝ] (V →L[ℝ] ℂ)).toLinearMap ∘ₗ Q
    let Q2 : V →L[ℝ] (V →L[ℝ] ℂ) := LinearMap.toContinuousLinearMap Q1
    have hQ2 : ∀ x y, Q2 x y = Q x y := fun x y => rfl
    have hcont : Continuous fun u : V => (Q u u).re := by
      have : Continuous fun u : V => Q2 u u := Q2.continuous.clm_apply continuous_id
      exact Complex.continuous_re.comp this
    obtain ⟨u0, hu0, hmin⟩ := (isCompact_sphere (0 : V) 1).exists_isMinOn
      (NormedSpace.sphere_nonempty.mpr zero_le_one) hcont.continuousOn
    have hu0ne : u0 ≠ 0 := by
      intro h; rw [h, mem_sphere_zero_iff_norm, norm_zero] at hu0; exact zero_ne_one hu0
    refine ⟨(Q u0 u0).re, hQ u0 hu0ne, fun x => ?_⟩
    by_cases hx : x = 0
    · subst hx; simp
    have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx
    set u : V := ‖x‖⁻¹ • x with hu
    have hus : u ∈ Metric.sphere (0 : V) 1 := by
      rw [mem_sphere_zero_iff_norm, hu, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn.ne']
    have hxu : x = ‖x‖ • u := by
      rw [hu, smul_smul, mul_inv_cancel₀ hn.ne', one_smul]
    have hsc : ∀ (r : ℝ) (v : V), (Q (r • v) (r • v)).re = r ^ 2 * (Q v v).re := by
      intro r v
      simp only [map_smul, LinearMap.smul_apply, smul_smul, Complex.smul_re, smul_eq_mul]
      ring
    have key : (Q x x).re = ‖x‖ ^ 2 * (Q u u).re := by
      rw [← hsc, ← hxu]
    rw [key]
    exact mul_comm (Q u0 u0).re (‖x‖ ^ 2) ▸
      mul_le_mul_of_nonneg_left (hmin hus) (by positivity)
  · push_neg at hV
    refine ⟨1, one_pos, fun x => ?_⟩
    rw [hV x]; simp

end GlobalTheory
