import Mathlib

private theorem UpperTheory.Reformulated.B.NoSmallSubgroupsNormedAlgebra.step {A : Type} [NormedRing A] [NormedAlgebra ℝ A] (a : A)
    (h : ‖a - 1‖ ≤ (1 / 2 : ℝ)) : ‖a - 1‖ ≤ (2 / 3 : ℝ) * ‖a * a - 1‖ := by
  have e : (2 : ℝ) • (a - 1) = (a * a - 1) - (a - 1) * (a - 1) := by
    rw [two_smul]; noncomm_ring
  have h1 : ‖(2 : ℝ) • (a - 1)‖ = 2 * ‖a - 1‖ := by
    rw [norm_smul]; simp
  have h2 : ‖(a * a - 1) - (a - 1) * (a - 1)‖ ≤ ‖a * a - 1‖ + ‖a - 1‖ * ‖a - 1‖ :=
    (norm_sub_le _ _).trans (by gcongr; exact norm_mul_le _ _)
  rw [← e, h1] at h2
  have h3 : ‖a - 1‖ * ‖a - 1‖ ≤ ‖a - 1‖ * (1 / 2) :=
    mul_le_mul_of_nonneg_left h (norm_nonneg _)
  linarith

theorem UpperTheory.Reformulated.B.NoSmallSubgroupsNormedAlgebra.nss :
    ∀ {G A : Type} [inst : Group G]
    [inst_1 : NormedRing A] [NormedAlgebra ℝ A] (ρ : G →* A) (H : Subgroup G),
    (∀ g ∈ H, ‖(ρ : G → A) g - (1 : A)‖ ≤ (1 / 2 : ℝ)) → ∀ g ∈ H, (ρ : G → A) g = (1 : A) := by
  intro G A _ _ _ ρ H h
  have key : ∀ n : ℕ, ∀ g ∈ H, ‖ρ g - 1‖ ≤ (2 / 3 : ℝ) ^ n := by
    intro n
    induction n with
    | zero => intro g hg; have := h g hg; rw [pow_zero]; linarith
    | succ n ih =>
      intro g hg
      have h1 := UpperTheory.Reformulated.B.NoSmallSubgroupsNormedAlgebra.step (ρ g) (h g hg)
      have h2 := ih (g * g) (H.mul_mem hg hg)
      rw [map_mul] at h2
      rw [pow_succ]
      linarith
  intro g hg
  have lim : Filter.Tendsto (fun n : ℕ => (2 / 3 : ℝ) ^ n) Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have h0 : ‖ρ g - 1‖ ≤ 0 := ge_of_tendsto' lim (fun n => key n g hg)
  exact sub_eq_zero.mp (norm_le_zero_iff.mp h0)
