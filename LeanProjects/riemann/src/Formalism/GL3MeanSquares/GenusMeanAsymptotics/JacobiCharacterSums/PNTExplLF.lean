import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.PNTExplDefs

open Complex Classical

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimesInProgressions

open Formalism.ZeroFreeDirichlet

variable {M : ℕ} [NeZero M]

theorem exLF_of_ne {χ : DirichletCharacter ℂ M} (h : χ ≠ 1) : exLF χ = DirichletCharacter.LFunction χ := by
  unfold exLF; rw [if_neg h]

theorem exLF_one_char : exLF (1 : DirichletCharacter ℂ M) = DirichletCharacter.LFunctionTrivChar₁ M := by
  unfold exLF; rw [if_pos rfl]

theorem exLF_one_char_apply {s : ℂ} (hs : s ≠ 1) :
    exLF (1 : DirichletCharacter ℂ M) s = (s - 1) * DirichletCharacter.LFunction (1 : DirichletCharacter ℂ M) s := by
  rw [exLF_one_char, DirichletCharacter.LFunctionTrivChar₁, Function.update_of_ne hs]

theorem exLF_differentiable (χ : DirichletCharacter ℂ M) : Differentiable ℂ (exLF χ) := by
  by_cases h : χ = 1
  · subst h; rw [exLF_one_char]; exact DirichletCharacter.differentiable_LFunctionTrivChar₁ M
  · rw [exLF_of_ne h]; exact DirichletCharacter.differentiable_LFunction h

theorem exLF_one_ne_zero (χ : DirichletCharacter ℂ M) : exLF χ 1 ≠ 0 := by
  by_cases h : χ = 1
  · subst h; rw [exLF_one_char]; exact DirichletCharacter.LFunctionTrivChar₁_apply_one_ne_zero M
  · rw [exLF_of_ne h]; exact DirichletCharacter.LFunction_apply_one_ne_zero h

theorem exLF_eq_zero_iff (χ : DirichletCharacter ℂ M) {s : ℂ} (hs : s ≠ 1) :
    exLF χ s = 0 ↔ DirichletCharacter.LFunction χ s = 0 := by
  by_cases h : χ = 1
  · subst h; rw [exLF_one_char_apply hs, mul_eq_zero]
    exact ⟨fun h => h.resolve_left (sub_ne_zero_of_ne hs), Or.inr⟩
  · rw [exLF_of_ne h]

theorem isLZero_iff_exLF (χ : DirichletCharacter ℂ M) (s : ℂ) : IsLZero χ s ↔ exLF χ s = 0 := by
  unfold IsLZero
  by_cases hs : s = 1
  · subst hs
    constructor
    · rintro ⟨h1, h2⟩
      exact absurd h2 (DirichletCharacter.LFunction_ne_zero_of_one_le_re χ h1 (by simp))
    · intro h; exact absurd h (exLF_one_ne_zero χ)
  · rw [exLF_eq_zero_iff χ hs]
    exact ⟨fun h => h.2, fun h => ⟨Or.inr hs, h⟩⟩

theorem exLF_re_lt_one (χ : DirichletCharacter ℂ M) {s : ℂ} (hs : exLF χ s = 0) : s.re < 1 := by
  by_contra hlt
  obtain ⟨h1, h2⟩ := (isLZero_iff_exLF χ s).2 hs
  exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ h1 (not_lt.1 hlt) h2

theorem negLD_eq_exLF (χ : DirichletCharacter ℂ M) {s : ℂ} (hs : s ≠ 1) (h0 : exLF χ s ≠ 0) :
    negLD χ s = (if χ = 1 then 1 / (s - 1) else 0) - deriv (exLF χ) s / exLF χ s := by
  unfold negLD
  by_cases h : χ = 1
  · subst h
    have hL : DirichletCharacter.LFunction (1 : DirichletCharacter ℂ M) s ≠ 0 :=
      fun hz => h0 ((exLF_eq_zero_iff _ hs).2 hz)
    have hs1 : s - 1 ≠ 0 := sub_ne_zero_of_ne hs
    rw [if_pos rfl, exLF_one_char_apply hs, exLF_one_char,
      DirichletCharacter.deriv_LFunctionTrivChar₁_apply_of_ne_one M hs]
    simp only [DirichletCharacter.LFunctionTrivChar]
    field_simp
    ring
  · rw [if_neg h, exLF_of_ne h, zero_sub]

theorem exLF_deriv_ne_zero (χ : DirichletCharacter ℂ M) {ρ : ℂ} (hρ : exLF χ ρ = 0)
    (hd : deriv (DirichletCharacter.LFunction χ) ρ ≠ 0) : deriv (exLF χ) ρ ≠ 0 := by
  by_cases h : χ = 1
  · subst h
    have hs : ρ ≠ 1 := by
      rintro rfl; exact exLF_one_ne_zero _ hρ
    have hL := (exLF_eq_zero_iff _ hs).1 hρ
    rw [exLF_one_char, DirichletCharacter.deriv_LFunctionTrivChar₁_apply_of_ne_one M hs]
    simp only [DirichletCharacter.LFunctionTrivChar]
    rw [hL, add_zero]
    exact mul_ne_zero (sub_ne_zero_of_ne hs) hd
  · rw [exLF_of_ne h]; exact hd

theorem exLF_analyticAt (χ : DirichletCharacter ℂ M) (z : ℂ) : AnalyticAt ℂ (exLF χ) z :=
  (exLF_differentiable χ).analyticAt z

theorem exLF_order_ne_top (χ : DirichletCharacter ℂ M) (ρ : ℂ) : analyticOrderAt (exLF χ) ρ ≠ ⊤ := by
  intro h
  have := (AnalyticOnNhd.analyticOrderAt_eq_top_iff_eq_zero ρ (exLF_analyticAt χ)).1 h
  exact exLF_one_ne_zero χ (by rw [this]; rfl)

theorem exOrd_pos (χ : DirichletCharacter ℂ M) {ρ : ℂ} (hρ : exLF χ ρ = 0) : 1 ≤ exOrd χ ρ := by
  unfold exOrd
  rw [Nat.one_le_iff_ne_zero]
  intro h
  have h1 : analyticOrderAt (exLF χ) ρ = 0 := by
    rw [← Nat.cast_analyticOrderNatAt (exLF_order_ne_top χ ρ), h]; rfl
  exact ((exLF_analyticAt χ ρ).analyticOrderAt_eq_zero.1 h1) hρ

theorem exOrd_eq_one (χ : DirichletCharacter ℂ M) {ρ : ℂ} (hρ : exLF χ ρ = 0) (hd : deriv (exLF χ) ρ ≠ 0) :
    exOrd χ ρ = 1 := by
  unfold exOrd analyticOrderNatAt
  rw [(exLF_analyticAt χ ρ).analyticOrderAt_eq_one_of_zero_deriv_ne_zero hρ hd]
  rfl

theorem exLF_prod_le (M : ℕ) [NeZero M] (s : ℂ) (hs : 1 / 2 ≤ s.re) :
    ‖∏ p ∈ M.primeFactors, (1 - (p : ℂ) ^ (-s))‖ ≤ M := by
  have h1 : ‖∏ p ∈ M.primeFactors, (1 - (p : ℂ) ^ (-s))‖ ≤ ∏ p ∈ M.primeFactors, (p : ℝ) := by
    rw [norm_prod]
    refine Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun p hp => ?_)
    have hp2 : 2 ≤ p := (Nat.prime_of_mem_primeFactors hp).two_le
    have hp0 : (0 : ℝ) < p := by exact_mod_cast (by omega : 0 < p)
    have hn : ‖(p : ℂ) ^ (-s)‖ ≤ 1 := by
      rw [← Complex.ofReal_natCast, Complex.norm_cpow_eq_rpow_re_of_pos hp0]
      apply Real.rpow_le_one_of_one_le_of_nonpos
      · exact_mod_cast (by omega : 1 ≤ p)
      · simp only [Complex.neg_re]; linarith
    calc ‖1 - (p : ℂ) ^ (-s)‖ ≤ ‖(1 : ℂ)‖ + ‖(p : ℂ) ^ (-s)‖ := norm_sub_le _ _
      _ ≤ 1 + 1 := by rw [norm_one]; linarith
      _ ≤ p := by
        have : (2 : ℝ) ≤ p := by exact_mod_cast hp2
        linarith
  have h2 : ∏ p ∈ M.primeFactors, (p : ℝ) ≤ M := by
    have := Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne M)) (Nat.prod_primeFactors_dvd M)
    calc ∏ p ∈ M.primeFactors, (p : ℝ) = ((∏ p ∈ M.primeFactors, p : ℕ) : ℝ) := by push_cast; rfl
      _ ≤ M := by exact_mod_cast this
  exact h1.trans h2

theorem exLF_growth : ∃ C : ℝ, 1 ≤ C ∧ ∀ (M : ℕ) [NeZero M] (χ : DirichletCharacter ℂ M) (s : ℂ), 1 / 2 ≤ s.re →
    ‖exLF χ s‖ ≤ C * M * (1 + ‖s‖) ^ 2 := by
  obtain ⟨C0, hC0⟩ := lfunction_polynomial_growth
  refine ⟨max C0 6, le_trans (by norm_num) (le_max_right _ _), ?_⟩
  intro M _ χ s hs
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast NeZero.one_le
  have hn : 0 ≤ ‖s‖ := norm_nonneg s
  by_cases h : χ = 1
  · subst h
    have h6 : 6 * (M : ℝ) * (1 + ‖s‖) ^ 2 ≤ max C0 6 * M * (1 + ‖s‖) ^ 2 := by
      gcongr; exact le_max_right _ _
    refine le_trans ?_ h6
    by_cases hs1 : s = 1
    · subst hs1
      rw [exLF_one_char]
      simp only [Function.update_self]
      have := exLF_prod_le M 1 (by norm_num)
      have he : ∏ p ∈ M.primeFactors, (1 - (p : ℂ) ^ (-(1 : ℂ))) = ∏ p ∈ M.primeFactors, (1 - (p : ℂ)⁻¹) := by
        refine Finset.prod_congr rfl (fun p _ => ?_)
        rw [Complex.cpow_neg_one]
      rw [he] at this
      refine this.trans ?_
      rw [norm_one]; nlinarith
    · rw [exLF_one_char_apply hs1]
      have hz := DirichletCharacter.LFunctionTrivChar_eq_mul_riemannZeta (N := M) hs1
      simp only [DirichletCharacter.LFunctionTrivChar] at hz
      rw [hz]
      have hP := exLF_prod_le M s hs
      have hZ := Formalism.ZF.growthBound s (by linarith) hs1
      have hpos : 0 < ‖s - 1‖ := norm_pos_iff.2 (sub_ne_zero_of_ne hs1)
      have hle : ‖s - 1‖ ≤ 1 + ‖s‖ := by
        calc ‖s - 1‖ ≤ ‖s‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
          _ = 1 + ‖s‖ := by rw [norm_one]; ring
      have hre : 1 / s.re ≤ 2 := by
        rw [div_le_iff₀ (by linarith)]; linarith
      have hA : ‖s - 1‖ * ‖riemannZeta s‖ ≤ 6 * (1 + ‖s‖) ^ 2 := by
        calc ‖s - 1‖ * ‖riemannZeta s‖ ≤ ‖s - 1‖ * (1 + 1 / ‖s - 1‖ + ‖s‖ * (1 + 1 / s.re)) := by gcongr
          _ = ‖s - 1‖ + 1 + ‖s - 1‖ * (‖s‖ * (1 + 1 / s.re)) := by field_simp
          _ ≤ (1 + ‖s‖) + 1 + (1 + ‖s‖) * (‖s‖ * (1 + 2)) := by gcongr
          _ ≤ 6 * (1 + ‖s‖) ^ 2 := by nlinarith
      calc ‖(s - 1) * ((∏ p ∈ M.primeFactors, (1 - (p : ℂ) ^ (-s))) * riemannZeta s)‖
          = ‖∏ p ∈ M.primeFactors, (1 - (p : ℂ) ^ (-s))‖ * (‖s - 1‖ * ‖riemannZeta s‖) := by
            rw [norm_mul, norm_mul]; ring
        _ ≤ M * (6 * (1 + ‖s‖) ^ 2) := by gcongr
        _ = 6 * (M : ℝ) * (1 + ‖s‖) ^ 2 := by ring
  · rw [exLF_of_ne h]
    have h1 := hC0 M χ h s hs
    have h2 : C0 * M * (1 + ‖s‖) ≤ max C0 6 * M * (1 + ‖s‖) := by
      gcongr; exact le_max_left _ _
    have h3 : max C0 6 * M * (1 + ‖s‖) ≤ max C0 6 * M * (1 + ‖s‖) ^ 2 := by
      have hc : 0 ≤ max C0 6 * M := by
        have : (0 : ℝ) ≤ max C0 6 := le_trans (by norm_num) (le_max_right _ _)
        positivity
      have : (1 + ‖s‖) ≤ (1 + ‖s‖) ^ 2 := by nlinarith
      exact mul_le_mul_of_nonneg_left this hc
    linarith

theorem exLF_lower (χ : DirichletCharacter ℂ M) (s : ℂ) (hs : 1 < s.re) :
    min 1 ‖s - 1‖ * ((s.re - 1) / s.re) ≤ ‖exLF χ s‖ := by
  have hI := inverseBound M χ s hs
  have hs1 : s ≠ 1 := by rintro rfl; simp at hs
  have hne : DirichletCharacter.LFunction χ s ≠ 0 :=
    DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inr hs1) hs.le
  have hpos : 0 < ‖DirichletCharacter.LFunction χ s‖ := norm_pos_iff.2 hne
  have hq : 0 < (s.re - 1) / s.re := div_pos (by linarith) (by linarith)
  have hL : (s.re - 1) / s.re ≤ ‖DirichletCharacter.LFunction χ s‖ := by
    have h1 : (s.re / (s.re - 1))⁻¹ ≤ (‖DirichletCharacter.LFunction χ s‖⁻¹)⁻¹ :=
      inv_anti₀ (inv_pos.2 hpos) hI
    rwa [inv_inv, inv_div] at h1
  by_cases h : χ = 1
  · subst h
    rw [exLF_one_char_apply hs1, norm_mul]
    exact mul_le_mul (min_le_right _ _) hL hq.le (norm_nonneg _)
  · rw [exLF_of_ne h]
    calc min 1 ‖s - 1‖ * ((s.re - 1) / s.re) ≤ 1 * ((s.re - 1) / s.re) :=
          mul_le_mul_of_nonneg_right (min_le_left _ _) hq.le
      _ ≤ _ := by rw [one_mul]; exact hL

end Formalism.HermitianLattices.Ext.PrimesInProgressions
