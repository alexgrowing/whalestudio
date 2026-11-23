import Mathlib
import Formalism.LandauZeroFreeBounds.Statement

open Finset Classical

noncomputable section

namespace Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds

theorem inRegion_of_lt {c Z β : ℝ} {q : ℕ} (hc : 0 < c) (hZ : 3 ≤ Z) (hq1 : 1 ≤ q) (hq : (q : ℝ) ≤ Z ^ 2)
    (hβ : 1 - c / 3 / Real.log Z < β) : Formalism.ZeroFreeDirichlet.InRegion c q (β : ℂ) := by
  unfold Formalism.ZeroFreeDirichlet.InRegion
  rw [Complex.ofReal_im, Complex.ofReal_re, abs_zero, zero_add]
  have hZpos : 0 < Z := by linarith
  have hq1' : (1 : ℝ) ≤ q := by exact_mod_cast hq1
  have h2q : 0 < Real.log ((q : ℝ) * 2) := Real.log_pos (by linarith)
  have hZ3 : Real.log (Z ^ 3) = 3 * Real.log Z := by rw [Real.log_pow]; norm_num
  have hle : Real.log ((q : ℝ) * 2) ≤ 3 * Real.log Z := by
    rw [← hZ3]
    apply Real.log_le_log (by linarith)
    nlinarith
  have hdiv : c / 3 / Real.log Z ≤ c / Real.log ((q : ℝ) * 2) := by
    rw [div_div]
    exact div_le_div_of_nonneg_left hc.le h2q hle
  linarith

theorem isLZero_changeLevel {M q : ℕ} [NeZero M] [NeZero q] (h : M ∣ q) (χ : DirichletCharacter ℂ M) (hχ : χ ≠ 1)
    {s : ℂ} (hs : DirichletCharacter.LFunction χ s = 0) :
    Formalism.ZeroFreeDirichlet.IsLZero (DirichletCharacter.changeLevel h χ) s := by
  refine ⟨Or.inl ?_, ?_⟩
  · intro h1
    apply hχ
    apply DirichletCharacter.changeLevel_injective h
    rw [h1, map_one]
  · rw [DirichletCharacter.LFunction_changeLevel h χ (Or.inl hχ), hs, zero_mul]

theorem page_across (hZ : Formalism.ZeroFreeDirichlet.ZFRDirichlet) :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ (Z : ℝ) (M₁ M₂ : ℕ) [NeZero M₁] [NeZero M₂] (χ₁ : DirichletCharacter ℂ M₁)
      (χ₂ : DirichletCharacter ℂ M₂) (β₁ β₂ : ℝ), 3 ≤ Z → (M₁ : ℝ) ≤ Z → (M₂ : ℝ) ≤ Z →
      χ₁ ^ 2 = 1 → χ₂ ^ 2 = 1 → χ₁ ≠ 1 → χ₂ ≠ 1 →
      DirichletCharacter.LFunction χ₁ (β₁ : ℂ) = 0 → DirichletCharacter.LFunction χ₂ (β₂ : ℂ) = 0 →
      1 - c₀ / Real.log Z < β₁ → 1 - c₀ / Real.log Z < β₂ → β₁ < 1 → β₂ < 1 →
      ∀ n : ℕ, n.Coprime (M₁ * M₂) → χ₁ (n : ZMod M₁) = χ₂ (n : ZMod M₂) := by
  obtain ⟨c, hc, hzfr⟩ := hZ
  refine ⟨c / 3, by positivity, ?_⟩
  intro Z M₁ M₂ _ _ χ₁ χ₂ β₁ β₂ hZ3 hM₁ hM₂ _ _ hne₁ hne₂ hz₁ hz₂ hb₁ hb₂ _ _ n hn
  haveI : NeZero (M₁ * M₂) := ⟨mul_ne_zero (NeZero.ne _) (NeZero.ne _)⟩
  have hq1 : 1 ≤ M₁ * M₂ := Nat.one_le_iff_ne_zero.mpr (NeZero.ne _)
  have hqZ : ((M₁ * M₂ : ℕ) : ℝ) ≤ Z ^ 2 := by
    push_cast
    rw [pow_two]
    exact mul_le_mul hM₁ hM₂ (Nat.cast_nonneg _) (by linarith)

  have hr₁ := inRegion_of_lt hc hZ3 hq1 hqZ hb₁
  have hr₂ := inRegion_of_lt hc hZ3 hq1 hqZ hb₂
  have hL₁ := isLZero_changeLevel (dvd_mul_right M₁ M₂) χ₁ hne₁ hz₁
  have hL₂ := isLZero_changeLevel (dvd_mul_left M₂ M₁) χ₂ hne₂ hz₂
  obtain ⟨-, -, -, -, huniq⟩ := hzfr (M₁ * M₂) _ _ hr₁ hL₁
  have heq := (huniq _ _ hr₂ hL₂).1
  have hv := congrArg (fun ψ : DirichletCharacter ℂ (M₁ * M₂) =>
    ψ ((ZMod.unitOfCoprime n hn : (ZMod (M₁ * M₂))ˣ) : ZMod (M₁ * M₂))) heq
  rw [DirichletCharacter.changeLevel_eq_cast_of_dvd, DirichletCharacter.changeLevel_eq_cast_of_dvd,
    ZMod.coe_unitOfCoprime, ZMod.cast_natCast (dvd_mul_left M₂ M₁),
    ZMod.cast_natCast (dvd_mul_right M₁ M₂)] at hv
  exact hv.symm

end Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds
