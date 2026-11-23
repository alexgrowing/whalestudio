import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzContinuousAtOfPointwiseOfBounded

open SchwartzMap Filter Topology
open scoped Nat

namespace GlobalTheory

theorem schwartz_tendsto_of_pointwise_of_uniform_bound :
    ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (F : ℕ → SchwartzMap V ℂ) (F0 : SchwartzMap V ℂ),
    (∀ v, Tendsto (fun m => F m v) atTop (𝓝 (F0 v))) →
    (∀ k n : ℕ, ∃ C : ℝ, ∀ m v, ‖v‖ ^ k * ‖iteratedFDeriv ℝ n (F m) v‖ ≤ C) →
    Tendsto F atTop (𝓝 F0) := by
  intro V _ _ _ F F0 hp hb
  have hp' : ∀ v, Tendsto (fun m => (F m - F0) v) atTop (𝓝 0) := fun v => by
    simpa using tendsto_sub_nhds_zero_iff.2 (hp v)
  have hb' : ∀ k n : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ m in (atTop : Filter ℕ), ∀ v,
      ‖v‖ ^ k * ‖iteratedFDeriv ℝ n (⇑(F m - F0)) v‖ ≤ C := by
    intro k n
    obtain ⟨C, hC⟩ := hb k n
    refine ⟨|C| + SchwartzMap.seminorm ℂ k n F0, by positivity, Eventually.of_forall fun m v => ?_⟩
    have key : SchwartzMap.seminorm ℂ k n (F m) ≤ |C| :=
      SchwartzMap.seminorm_le_bound ℂ k n _ (abs_nonneg C) fun v => (hC m v).trans (le_abs_self C)
    refine (SchwartzMap.le_seminorm ℂ k n (F m - F0) v).trans ((map_sub_le_add _ _ _).trans ?_)
    exact add_le_add key le_rfl
  rw [(schwartz_withSeminorms ℂ V ℂ).tendsto_nhds]
  rintro ⟨k, n⟩ ε hε
  obtain ⟨D, hD0, hD⟩ := hb' (k + 1) n
  set R : ℝ := D / (ε / 2) + 1 with hR
  have hR0 : 0 < R := by positivity
  filter_upwards [hD, eventually_forall_norm_iteratedFDeriv_le hp' hb' n (ε / 2 / R ^ k)
    (by positivity)] with x hx hs
  refine lt_of_le_of_lt ?_ (half_lt_self hε)
  refine SchwartzMap.seminorm_le_bound ℂ k n _ (by positivity) fun v => ?_
  by_cases hv : ‖v‖ ≤ R
  · calc _ ≤ R ^ k * (ε / 2 / R ^ k) :=
          mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hv k) (hs v) (norm_nonneg _) (by positivity)
      _ = ε / 2 := by field_simp
  · push_neg at hv
    have h0 := hx v
    set a := ‖v‖ ^ k * ‖iteratedFDeriv ℝ n (⇑(F x - F0)) v‖ with ha
    have ha0 : 0 ≤ a := by positivity
    have h1 : ‖v‖ * a ≤ D := by rw [ha, ← mul_assoc, ← pow_succ']; exact h0
    have h2 : R * (ε / 2) = D + ε / 2 := by rw [hR]; field_simp
    by_contra hc
    push_neg at hc
    nlinarith

end GlobalTheory
