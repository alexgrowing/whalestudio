import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ZeroWindow.RightHalfWith

noncomputable section

open Complex Filter Topology

namespace PI.ZW

open DirichletCharacter

lemma differentiable_gammaFactor_inv {N : ℕ} (χ : DirichletCharacter ℂ N) :
    Differentiable ℂ (fun s => (gammaFactor χ s)⁻¹) := by
  by_cases h : χ.Even
  · simp only [DirichletCharacter.gammaFactor, h, if_true]
    exact Complex.differentiable_Gammaℝ_inv
  · simp only [DirichletCharacter.gammaFactor, h, if_false]
    exact Complex.differentiable_Gammaℝ_inv.comp (differentiable_id.add_const 1)

lemma gammaFactor_ne_zero_of_re_pos {N : ℕ} (χ : DirichletCharacter ℂ N) {s : ℂ}
    (hs : 0 < s.re) : gammaFactor χ s ≠ 0 := by
  by_cases h : χ.Even
  · simp only [DirichletCharacter.gammaFactor, h, if_true]
    exact Complex.Gammaℝ_ne_zero_of_re_pos hs
  · simp only [DirichletCharacter.gammaFactor, h, if_false]
    exact Complex.Gammaℝ_ne_zero_of_re_pos (by simp; linarith)

lemma isPrimitive_inv {N : ℕ} {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) :
    χ⁻¹.IsPrimitive := by
  rw [DirichletCharacter.isPrimitive_def, DirichletCharacter.conductor_inv]
  exact (DirichletCharacter.isPrimitive_def χ).mp hχ

lemma rootNumber_ne_zero {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) :
    rootNumber χ ≠ 0 := by
  intro h
  have h2 := hχ.completedLFunction_one_sub (-1)
  rw [h] at h2
  simp only [mul_zero, zero_mul] at h2
  norm_num at h2
  have hne := DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inr (by norm_num : (2 : ℂ) ≠ 1))
    (by norm_num : (1 : ℝ) ≤ (2 : ℂ).re)
  rw [DirichletCharacter.LFunction_eq_completed_div_gammaFactor χ 2 (Or.inl two_ne_zero), h2, zero_div] at hne
  exact hne rfl

lemma isOpen_strip : IsOpen {s : ℂ | 0 < s.re ∧ s.re < 1} := by
  exact (isOpen_lt continuous_const Complex.continuous_re).inter (isOpen_lt Complex.continuous_re continuous_const)

theorem transfer : Transfer := by
  intro N _ χ hχ ρ h0 h1 hz
  have hχi := isPrimitive_inv hχ
  have hstrip : ∀ s : ℂ, 0 < s.re → s.re < 1 → 0 < (1 - s).re := fun s _ h => by simp; linarith
  have hfun : ∀ s : ℂ, 0 < s.re → s.re < 1 → DirichletCharacter.LFunction χ⁻¹ (1 - s) =
      ((N : ℂ) ^ (s - 1 / 2) * rootNumber χ⁻¹ * gammaFactor χ s * (gammaFactor χ⁻¹ (1 - s))⁻¹) *
        DirichletCharacter.LFunction χ s := by
    intro s hs0 hs1
    have h1s := hstrip s hs0 hs1
    have hg1 := gammaFactor_ne_zero_of_re_pos χ⁻¹ h1s
    have hg0 := gammaFactor_ne_zero_of_re_pos χ hs0
    rw [DirichletCharacter.LFunction_eq_completed_div_gammaFactor χ⁻¹ (1 - s)
        (Or.inl fun h => by rw [h] at h1s; simp at h1s),
      hχi.completedLFunction_one_sub s, inv_inv,
      DirichletCharacter.LFunction_eq_completed_div_gammaFactor χ s (Or.inl fun h => by rw [h] at hs0; simp at hs0)]
    field_simp
  refine ⟨by rw [hfun ρ h0 h1, hz, mul_zero], ?_⟩
  have hρU : {s : ℂ | 0 < s.re ∧ s.re < 1} ∈ 𝓝 ρ := isOpen_strip.mem_nhds ⟨h0, h1⟩
  have hHd : DifferentiableOn ℂ (fun s : ℂ => (N : ℂ) ^ (s - 1 / 2) * rootNumber χ⁻¹ * gammaFactor χ s *
      (gammaFactor χ⁻¹ (1 - s))⁻¹) {s | 0 < s.re ∧ s.re < 1} := by
    intro s hs
    have hg0 := gammaFactor_ne_zero_of_re_pos χ hs.1
    have hdg : DifferentiableAt ℂ (gammaFactor χ) s := by
      have h := ((differentiable_gammaFactor_inv χ) s).inv (inv_ne_zero hg0)
      have e : (fun x => (gammaFactor χ x)⁻¹)⁻¹ = gammaFactor χ := funext fun x => by
        simp only [Pi.inv_apply, inv_inv]
      rwa [e] at h
    have hdg1 : DifferentiableAt ℂ (fun s => (gammaFactor χ⁻¹ (1 - s))⁻¹) s :=
      ((differentiable_gammaFactor_inv χ⁻¹) (1 - s)).comp s ((differentiableAt_const 1).sub differentiableAt_id)
    have hcp : DifferentiableAt ℂ (fun s : ℂ => (N : ℂ) ^ (s - 1 / 2)) s :=
      (differentiableAt_id.sub_const _).const_cpow (Or.inl (by exact_mod_cast NeZero.ne N))
    exact (((hcp.mul_const _).mul hdg).mul hdg1).differentiableWithinAt
  have hLd : DifferentiableOn ℂ (DirichletCharacter.LFunction χ) {s | 0 < s.re ∧ s.re < 1} :=
    fun s hs => (DirichletCharacter.differentiableAt_LFunction χ s
      (Or.inl fun h => by rw [h] at hs; simp at hs)).differentiableWithinAt
  have hHa := hHd.analyticAt hρU
  have hLa := hLd.analyticAt hρU
  have hH0 : (N : ℂ) ^ (ρ - 1 / 2) * rootNumber χ⁻¹ * gammaFactor χ ρ * (gammaFactor χ⁻¹ (1 - ρ))⁻¹ ≠ 0 := by
    refine mul_ne_zero (mul_ne_zero (mul_ne_zero ?_ (rootNumber_ne_zero hχi))
      (gammaFactor_ne_zero_of_re_pos χ h0)) (inv_ne_zero (gammaFactor_ne_zero_of_re_pos χ⁻¹ (hstrip ρ h0 h1)))
    rw [Ne, Complex.cpow_eq_zero_iff]
    simp [NeZero.ne N]
  have key : analyticOrderAt (DirichletCharacter.LFunction χ⁻¹) (1 - ρ) =
      analyticOrderAt (DirichletCharacter.LFunction χ) ρ := by
    have e1 := analyticOrderAt_comp_of_deriv_ne_zero (f := DirichletCharacter.LFunction χ⁻¹)
      (g := fun s : ℂ => 1 - s) (z₀ := ρ) (analyticAt_const.sub analyticAt_id) (by simp)
    rw [← e1]
    have e2 : (DirichletCharacter.LFunction χ⁻¹ ∘ fun s : ℂ => 1 - s) =ᶠ[𝓝 ρ]
        ((fun s : ℂ => (N : ℂ) ^ (s - 1 / 2) * rootNumber χ⁻¹ * gammaFactor χ s * (gammaFactor χ⁻¹ (1 - s))⁻¹) *
          DirichletCharacter.LFunction χ) :=
      Filter.eventually_of_mem hρU fun s hs => hfun s hs.1 hs.2
    rw [analyticOrderAt_congr e2, analyticOrderAt_mul hHa hLa, (hHa.analyticOrderAt_eq_zero).mpr hH0, zero_add]
  have e : analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ =
      analyticOrderNatAt (DirichletCharacter.LFunction χ⁻¹) (1 - ρ) := by
    simp only [analyticOrderNatAt, key]
  exact e.le

end PI.ZW
