import Mathlib
open Matrix
open scoped Topology ComplexOrder

namespace GlobalTheory

theorem norm_star_dotProduct_mulVec_le {n : Type} [Fintype n] (A : Matrix n n ℂ) (u : n → ℂ) :
    ‖star u ⬝ᵥ A *ᵥ u‖ ≤ (∑ i, ∑ j, ‖A i j‖) * ‖u‖ ^ 2 := by
  have key : ∀ i, ‖star (u i) * ∑ j, A i j * u j‖ ≤ ∑ j, ‖A i j‖ * ‖u‖ ^ 2 := by
    intro i
    rw [norm_mul, norm_star]
    calc ‖u i‖ * ‖∑ j, A i j * u j‖ ≤ ‖u‖ * ∑ j, ‖A i j‖ * ‖u‖ := by
          gcongr
          · exact norm_le_pi_norm u i
          · refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
            rw [norm_mul]
            gcongr
            exact norm_le_pi_norm u j
      _ = ∑ j, ‖A i j‖ * ‖u‖ ^ 2 := by
          rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun j _ => ?_; ring
  calc ‖star u ⬝ᵥ A *ᵥ u‖ = ‖∑ i, star (u i) * ∑ j, A i j * u j‖ := by
        simp [dotProduct, mulVec]
    _ ≤ ∑ i, ‖star (u i) * ∑ j, A i j * u j‖ := norm_sum_le _ _
    _ ≤ ∑ i, ∑ j, ‖A i j‖ * ‖u‖ ^ 2 := Finset.sum_le_sum fun i _ => key i
    _ = (∑ i, ∑ j, ‖A i j‖) * ‖u‖ ^ 2 := by simp [Finset.sum_mul]

theorem re_star_dotProduct_mulVec_ofReal_smul {n : Type} [Fintype n] (A : Matrix n n ℂ) (t : ℝ)
    (w : n → ℂ) :
    (star ((t : ℂ) • w) ⬝ᵥ A *ᵥ ((t : ℂ) • w)).re = t ^ 2 * (star w ⬝ᵥ A *ᵥ w).re := by
  rw [star_smul, mulVec_smul, smul_dotProduct, dotProduct_smul]
  simp only [smul_eq_mul, Complex.star_def, Complex.conj_ofReal, Complex.re_ofReal_mul]
  ring

theorem exists_pos_mul_sq_norm_le_re_of_posDef {n : Type} [Fintype n] (A : Matrix n n ℂ)
    (hA : A.PosDef) : ∃ m : ℝ, 0 < m ∧ ∀ u : n → ℂ, m * ‖u‖ ^ 2 ≤ (star u ⬝ᵥ A *ᵥ u).re := by
  set f : (n → ℂ) → ℝ := fun u => (star u ⬝ᵥ A *ᵥ u).re with hf
  have hfc : Continuous f := by
    simp only [hf]
    fun_prop
  have hsc : ∀ u : n → ℂ, u ≠ 0 →
      ‖((‖u‖⁻¹ : ℝ) : ℂ) • u‖ = 1 ∧ f u = ‖u‖ ^ 2 * f (((‖u‖⁻¹ : ℝ) : ℂ) • u) := by
    intro u hu
    have hn : ‖u‖ ≠ 0 := norm_ne_zero_iff.mpr hu
    refine ⟨?_, ?_⟩
    · rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_inv, abs_norm, inv_mul_cancel₀ hn]
    · simp only [hf]
      rw [re_star_dotProduct_mulVec_ofReal_smul]
      field_simp
  by_cases hne : (Metric.sphere (0 : n → ℂ) 1).Nonempty
  · obtain ⟨v, hv, hmin⟩ := (isCompact_sphere (0 : n → ℂ) 1).exists_isMinOn hne hfc.continuousOn
    have hv0 : v ≠ 0 := by
      intro h
      rw [h, mem_sphere_iff_norm, sub_zero, norm_zero] at hv
      exact zero_ne_one hv
    refine ⟨f v, ?_, fun u => ?_⟩
    · have := hA.re_dotProduct_pos hv0
      simpa [hf] using this
    · by_cases hu : u = 0
      · subst hu
        simp [hf]
      · obtain ⟨h1, h2⟩ := hsc u hu
        have hw : ((‖u‖⁻¹ : ℝ) : ℂ) • u ∈ Metric.sphere (0 : n → ℂ) 1 := by
          rw [mem_sphere_iff_norm, sub_zero]; exact h1
        have := hmin hw
        change f u ≥ _
        rw [h2, mul_comm]
        exact mul_le_mul_of_nonneg_right this (sq_nonneg _)
  · refine ⟨1, one_pos, fun u => ?_⟩
    by_cases hu : u = 0
    · subst hu
      simp
    · exact absurd ⟨_, by rw [mem_sphere_iff_norm, sub_zero]; exact (hsc u hu).1⟩ hne

theorem posDef_uniform_bounds_nhds : ∀ (Y : Type) [TopologicalSpace Y] (n : Type) [Fintype n]
    (K : Y → Matrix n n ℂ) (y₀ : Y), ContinuousAt K y₀ → (K y₀).PosDef →
    ∃ c C : ℝ, 0 < c ∧ 0 ≤ C ∧ ∀ᶠ y in 𝓝 y₀, ∀ u : n → ℂ,
      c * ‖u‖ ^ 2 ≤ (star u ⬝ᵥ K y *ᵥ u).re ∧ (star u ⬝ᵥ K y *ᵥ u).re ≤ C * ‖u‖ ^ 2 := by
  intro Y _ n _ K y₀ hK hpd
  obtain ⟨m, hm, hlow⟩ := exists_pos_mul_sq_norm_le_re_of_posDef (K y₀) hpd
  have hent : ∀ i j, ContinuousAt (fun y => K y i j) y₀ := fun i j =>
    ((Continuous.matrix_elem continuous_id i j).continuousAt).comp hK
  set S : Y → ℝ := fun y => ∑ i, ∑ j, ‖K y i j‖ with hS
  set D : Y → ℝ := fun y => ∑ i, ∑ j, ‖(K y - K y₀) i j‖ with hD
  have hSc : ContinuousAt S y₀ := by
    simp only [hS]
    exact tendsto_finset_sum _ fun i _ => tendsto_finset_sum _ fun j _ => (hent i j).norm
  have hDc : ContinuousAt D y₀ := by
    simp only [hD, Matrix.sub_apply]
    exact tendsto_finset_sum _ fun i _ => tendsto_finset_sum _ fun j _ =>
      ((hent i j).sub continuousAt_const).norm
  have hD0 : D y₀ = 0 := by simp [hD]
  have hev1 : ∀ᶠ y in 𝓝 y₀, D y < m / 2 := by
    have := hDc.eventually (gt_mem_nhds (show D y₀ < m / 2 by rw [hD0]; linarith))
    exact this
  have hev2 : ∀ᶠ y in 𝓝 y₀, S y < S y₀ + 1 :=
    hSc.eventually (gt_mem_nhds (lt_add_one (S y₀)))
  have hS0 : 0 ≤ S y₀ := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => norm_nonneg _
  refine ⟨m / 2, S y₀ + 1, by linarith, by linarith, ?_⟩
  filter_upwards [hev1, hev2] with y hy1 hy2 u
  have hsq : 0 ≤ ‖u‖ ^ 2 := sq_nonneg _
  refine ⟨?_, ?_⟩
  · have hsplit : (star u ⬝ᵥ K y *ᵥ u).re =
        (star u ⬝ᵥ K y₀ *ᵥ u).re + (star u ⬝ᵥ (K y - K y₀) *ᵥ u).re := by
      rw [sub_mulVec, dotProduct_sub, Complex.sub_re]; ring
    have hE := norm_star_dotProduct_mulVec_le (K y - K y₀) u
    have hre := Complex.abs_re_le_norm (star u ⬝ᵥ (K y - K y₀) *ᵥ u)
    have h3 : D y * ‖u‖ ^ 2 ≤ m / 2 * ‖u‖ ^ 2 := mul_le_mul_of_nonneg_right hy1.le hsq
    have h4 := hlow u
    have h5 := neg_abs_le (star u ⬝ᵥ (K y - K y₀) *ᵥ u).re
    rw [hsplit]
    simp only [hD] at h3
    nlinarith
  · have hE := norm_star_dotProduct_mulVec_le (K y) u
    have hre := Complex.re_le_norm (star u ⬝ᵥ K y *ᵥ u)
    have h3 : S y * ‖u‖ ^ 2 ≤ (S y₀ + 1) * ‖u‖ ^ 2 := mul_le_mul_of_nonneg_right hy2.le hsq
    simp only [hS] at h3
    linarith

end GlobalTheory
