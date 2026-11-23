import Mathlib
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsVariableChangeEqLatticeCurve
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.WeierstrassPAddOfNeOfDerivNeZero
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsPolynomialModularJOfHasQExpansion
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.HasSumLocallyUniformlyWeierstrassZetaExcept

open Filter PeriodPair
open scoped Topology Real UpperHalfPlane

noncomputable section

namespace GlobalTheory

theorem lattice_le_of_g₂_eq_of_g₃_eq {L L' : PeriodPair} (h₂ : L.g₂ = L'.g₂)
    (h₃ : L.g₃ = L'.g₃) : L.lattice ≤ L'.lattice := by
  have hz := L.ω₁_div_two_notMem_lattice
  set z := L.ω₁ / 2
  obtain ⟨w, hw, hw1, hw2⟩ := exists_weierstrassP_eq_and_derivWeierstrassP_eq L' (x := ℘[L] z) (y := ℘'[L] z)
    (by rw [← h₂, ← h₃]; exact L.derivWeierstrassP_sq z hz)
  obtain ⟨c, rfl⟩ : ∃ c, w = z + c := ⟨w - z, by ring⟩
  have h1 := eventuallyEq_of_weierstrass_system
    (weierstrass_system_add_const L 0 (z := z) (by simpa using hz))
    (h₂ ▸ weierstrass_system_add_const L' c hw) (by simp [hw1]) (by simp [hw2])
  have h2 := eqOn_compl_of_countable
    ((countable_add_mem_periodLattice L 0).union (countable_add_mem_periodLattice L' c))
    (fun t ht ↦ analyticAt_weierstrassP_add L 0 fun h ↦ ht (.inl h))
    (fun t ht ↦ analyticAt_weierstrassP_add L' c fun h ↦ ht (.inr h))
    (z := z) (by rintro (h | h); exacts [hz (by simpa using h), hw h]) h1
  have key : ∀ l ∈ L.lattice, l + c ∈ L'.lattice := fun l hl ↦ by
    by_contra h0
    refine not_eventually_weierstrassP_eq L hl
      (analyticAt_weierstrassP_add L' c h0).continuousAt ?_
    filter_upwards [eventually_ne_notMem_periodLattice L l, mem_nhdsWithin_of_mem_nhds
      ((continuous_add_const c).continuousAt.eventually
        (eventually_notMem_periodLattice L' h0))] with t h3 h4
    simpa using h2 (x := t) (by rintro (h | h); exacts [h3 (by simpa using h), h4 h])
  intro l hl
  simpa using sub_mem (key l hl) (key 0 (zero_mem _))

theorem lattice_eq_of_g₂_eq_of_g₃_eq {L L' : PeriodPair} (h₂ : L.g₂ = L'.g₂)
    (h₃ : L.g₃ = L'.g₃) : L.lattice = L'.lattice :=
  le_antisymm (lattice_le_of_g₂_eq_of_g₃_eq h₂ h₃) (lattice_le_of_g₂_eq_of_g₃_eq h₂.symm h₃.symm)

theorem g₂_cube_sub_g₃_sq_ne_zero (L : PeriodPair) : L.g₂ ^ 3 - 27 * L.g₃ ^ 2 ≠ 0 :=
  latticeCurve_Δ L ▸ latticeCurve_Δ_ne_zero L

theorem IsHomothetic.g₂_eq {L L' : PeriodPair} {c : ℂ} (h : IsHomothetic c L L') :
    L'.g₂ = (c ^ 4)⁻¹ * L.g₂ := by
  rw [g₂, g₂, h.G_eq]; ring

theorem IsHomothetic.g₃_eq {L L' : PeriodPair} {c : ℂ} (h : IsHomothetic c L L') :
    L'.g₃ = (c ^ 6)⁻¹ * L.g₃ := by
  rw [g₃, g₃, h.G_eq]; ring

theorem exists_scale_of_j_eq {a b a' b' : ℂ} (h : a ^ 3 - 27 * b ^ 2 ≠ 0)
    (h' : a' ^ 3 - 27 * b' ^ 2 ≠ 0)
    (e : a ^ 3 * (a' ^ 3 - 27 * b' ^ 2) = a' ^ 3 * (a ^ 3 - 27 * b ^ 2)) :
    ∃ u : ℂ, u ≠ 0 ∧ a' = u ^ 2 * a ∧ b' = u ^ 3 * b := by
  have e' : a ^ 3 * b' ^ 2 = a' ^ 3 * b ^ 2 := by linear_combination -e / 27
  by_cases ha : a = 0
  · subst ha
    have hb : b ≠ 0 := by rintro rfl; simp at h
    have ha' : a' = 0 := by simpa [hb] using e'
    subst ha'
    have hb' : b' ≠ 0 := by rintro rfl; simp at h'
    obtain ⟨u, hu⟩ := IsAlgClosed.exists_pow_nat_eq (b' / b) (n := 3) (by norm_num)
    refine ⟨u, ?_, by simp, by rw [hu]; field_simp⟩
    rintro rfl
    exact div_ne_zero hb' hb (by simpa using hu.symm)
  by_cases hb : b = 0
  · subst hb
    have hb' : b' = 0 := by simpa [ha] using e'
    subst hb'
    have ha' : a' ≠ 0 := by rintro rfl; simp at h'
    obtain ⟨u, hu⟩ := IsAlgClosed.exists_pow_nat_eq (a' / a) (n := 2) (by norm_num)
    refine ⟨u, ?_, by rw [hu]; field_simp, by simp⟩
    rintro rfl
    exact div_ne_zero ha' ha (by simpa using hu.symm)
  have ha' : a' ≠ 0 := by
    rintro rfl
    have : b' = 0 := by simpa [ha] using e'
    simp [this] at h'
  have hb' : b' ≠ 0 := by
    rintro rfl
    simp [ha', hb] at e'
  refine ⟨b' * a / (b * a'), by simp [*], ?_, ?_⟩
  · field_simp
    linear_combination -e'
  · field_simp
    linear_combination -e'

theorem exists_isHomothetic_of_j_eq {L L' : PeriodPair}
    (e : L.g₂ ^ 3 * (L'.g₂ ^ 3 - 27 * L'.g₃ ^ 2) = L'.g₂ ^ 3 * (L.g₂ ^ 3 - 27 * L.g₃ ^ 2)) :
    ∃ c : ℂ, IsHomothetic c L L' := by
  obtain ⟨u, hu, h2, h3⟩ := exists_scale_of_j_eq (g₂_cube_sub_g₃_sq_ne_zero L)
    (g₂_cube_sub_g₃_sq_ne_zero L') e
  obtain ⟨c, hc⟩ := IsAlgClosed.exists_pow_nat_eq u⁻¹ (n := 2) (by norm_num)
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact inv_ne_zero hu (by simpa using hc.symm)
  have H := isHomothetic_scalePeriods L c hc0
  have : (scalePeriods L c hc0).lattice = L'.lattice := by
    refine lattice_eq_of_g₂_eq_of_g₃_eq ?_ ?_
    · rw [H.g₂_eq, h2, show c ^ 4 = (c ^ 2) ^ 2 by ring, hc]; simp
    · rw [H.g₃_eq, h3, show c ^ 6 = (c ^ 2) ^ 3 by ring, hc]; simp
  exact ⟨c, fun x ↦ this ▸ H x⟩

theorem lattice_determined_by_invariants (L L' : PeriodPair) :
    (L.g₂ = L'.g₂ → L.g₃ = L'.g₃ → L.lattice = L'.lattice) ∧
    (L.g₂ ^ 3 * (L'.g₂ ^ 3 - 27 * L'.g₃ ^ 2) = L'.g₂ ^ 3 * (L.g₂ ^ 3 - 27 * L.g₃ ^ 2) →
      ∃ c : ℂ, c ≠ 0 ∧ ∀ z, z ∈ L'.lattice ↔ ∃ w ∈ L.lattice, z = c * w) := by
  refine ⟨lattice_eq_of_g₂_eq_of_g₃_eq, fun e ↦ ?_⟩
  obtain ⟨c, h⟩ := exists_isHomothetic_of_j_eq e
  refine ⟨c, h.ne_zero, fun z ↦ ⟨fun hz ↦ ⟨c⁻¹ * z, (h _).1 (by simpa [h.ne_zero] using hz),
    by simp [h.ne_zero]⟩, ?_⟩⟩
  rintro ⟨w, hw, rfl⟩
  exact (h w).2 hw

section

variable {L : PeriodPair} {a : ℂ} {τ : ℍ} (ha : a ≠ 0)
  (h : ∀ x, x ∈ L.lattice ↔ ∃ m n : ℤ, a * (m * (τ : ℂ) + n) = x)
include ha h

theorem g₂_cube_sub_g₃_sq_eq_discriminant :
    L.g₂ ^ 3 - 27 * L.g₃ ^ 2 = (2 * π / a) ^ 12 * ModularForm.discriminant τ := by
  rw [← latticeCurve_Δ, latticeCurve_Δ_eq_discriminant ha h]

theorem g₂_cube_sub_g₃_sq_eq_eta :
    L.g₂ ^ 3 - 27 * L.g₃ ^ 2 = (2 * π / a) ^ 12 * ModularForm.eta τ ^ 24 :=
  g₂_cube_sub_g₃_sq_eq_discriminant ha h

theorem g₂_cube_div_eq_modularJ :
    1728 * L.g₂ ^ 3 / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2) = modularJ τ := by
  rw [modularJ_def, ← latticeCurve_j ha h, WeierstrassCurve.j, Units.val_inv_eq_inv_val,
    WeierstrassCurve.coe_Δ', latticeCurve_Δ, latticeCurve_c₄]
  ring

end

theorem mem_lattice_iff_of_periods_eq {L : PeriodPair} {τ : ℍ}
    (h : (L.ω₁ = 1 ∧ L.ω₂ = τ) ∨ (L.ω₁ = τ ∧ L.ω₂ = 1)) (x : ℂ) :
    x ∈ L.lattice ↔ ∃ m n : ℤ, 1 * (m * (τ : ℂ) + n) = x := by
  rw [mem_lattice]
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2]
  · constructor <;> rintro ⟨m, n, rfl⟩ <;> exact ⟨n, m, by ring⟩
  · simp

theorem invariants_of_periods_eq {L : PeriodPair} {τ : ℍ}
    (h : (L.ω₁ = 1 ∧ L.ω₂ = τ) ∨ (L.ω₁ = τ ∧ L.ω₂ = 1)) :
    L.g₂ ^ 3 - 27 * L.g₃ ^ 2 = (2 * π) ^ 12 * ModularForm.discriminant τ ∧
    L.g₂ ^ 3 - 27 * L.g₃ ^ 2 = (2 * π) ^ 12 * ModularForm.eta τ ^ 24 ∧
    1728 * L.g₂ ^ 3 / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2) = modularJ τ :=
  ⟨by simpa using g₂_cube_sub_g₃_sq_eq_discriminant one_ne_zero (mem_lattice_iff_of_periods_eq h),
    by simpa using g₂_cube_sub_g₃_sq_eq_eta one_ne_zero (mem_lattice_iff_of_periods_eq h),
    g₂_cube_div_eq_modularJ one_ne_zero (mem_lattice_iff_of_periods_eq h)⟩

end GlobalTheory
