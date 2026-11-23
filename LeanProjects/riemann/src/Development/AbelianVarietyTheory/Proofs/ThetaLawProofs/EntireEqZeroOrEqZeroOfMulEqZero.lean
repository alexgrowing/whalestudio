import Mathlib

namespace GlobalTheory

theorem entire_eq_zero_or_eq_zero_of_mul_eq_zero {g : ℕ} (A B : (Fin g → ℂ) → ℂ)
    (hA : Differentiable ℂ A) (hB : Differentiable ℂ B) (hAB : ∀ z, A z * B z = 0) :
    (∀ z, A z = 0) ∨ (∀ z, B z = 0) := by
  by_cases hz : ∀ z, A z = 0
  · exact Or.inl hz
  right
  obtain ⟨z0, hz0⟩ := not_forall.1 hz
  intro z
  have hLd : Differentiable ℂ (fun t : ℂ => z0 + t • (z - z0)) := by fun_prop
  have ha : Differentiable ℂ (fun t : ℂ => A (z0 + t • (z - z0))) := hA.comp hLd
  have hb : Differentiable ℂ (fun t : ℂ => B (z0 + t • (z - z0))) := hB.comp hLd
  have ha0 : ∀ᶠ t in nhds (0 : ℂ), A (z0 + t • (z - z0)) ≠ 0 := by
    have h0 : A (z0 + (0 : ℂ) • (z - z0)) ≠ 0 := by simpa using hz0
    exact ha.continuous.continuousAt.eventually_ne h0
  have hb0 : (fun t : ℂ => B (z0 + t • (z - z0))) =ᶠ[nhds (0 : ℂ)] 0 := by
    filter_upwards [ha0] with t ht
    exact (mul_eq_zero.1 (hAB (z0 + t • (z - z0)))).resolve_left ht
  have hbA : AnalyticOnNhd ℂ (fun t : ℂ => B (z0 + t • (z - z0))) Set.univ := fun t _ => hb.analyticAt t
  have h1 := hbA.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ (Set.mem_univ 0) hb0
    (Set.mem_univ (1 : ℂ))
  simpa using h1

theorem entire_eq_mul_of_sq_eq_mul_sq :
    ∀ (g : ℕ) (f h q : (Fin g → ℂ) → ℂ) (C : ℂ), Differentiable ℂ f → Differentiable ℂ h →
      Differentiable ℂ q → (∀ z, f z ^ 2 = C * Complex.exp (2 * q z) * h z ^ 2) →
      ∃ c : ℂ, c ^ 2 = C ∧ ∀ z, f z = c * Complex.exp (q z) * h z := by
  intro g f h q C hf hh hq hsq
  obtain ⟨c, hc⟩ := IsAlgClosed.exists_pow_nat_eq C (by norm_num : 0 < 2)
  have hF : Differentiable ℂ fun z => f z * Complex.exp (-q z) := hf.mul hq.neg.cexp
  have key : ∀ z, (f z * Complex.exp (-q z) - c * h z) * (f z * Complex.exp (-q z) + c * h z) = 0 := by
    intro z
    have e1 : Complex.exp (-q z) ^ 2 * Complex.exp (2 * q z) = 1 := by
      rw [← Complex.exp_nat_mul, ← Complex.exp_add]
      convert Complex.exp_zero using 2
      push_cast
      ring
    linear_combination Complex.exp (-q z) ^ 2 * hsq z + C * h z ^ 2 * e1 - h z ^ 2 * hc
  have e2 : ∀ z, Complex.exp (-q z) * Complex.exp (q z) = 1 := by
    intro z
    rw [← Complex.exp_add]
    simp
  rcases entire_eq_zero_or_eq_zero_of_mul_eq_zero (fun z => f z * Complex.exp (-q z) - c * h z)
      (fun z => f z * Complex.exp (-q z) + c * h z) (hF.sub ((differentiable_const c).mul hh))
      (hF.add ((differentiable_const c).mul hh)) key with h1 | h1
  · refine ⟨c, hc, fun z => ?_⟩
    linear_combination Complex.exp (q z) * h1 z - f z * e2 z
  · refine ⟨-c, by rw [neg_sq]; exact hc, fun z => ?_⟩
    linear_combination Complex.exp (q z) * h1 z - f z * e2 z

end GlobalTheory
