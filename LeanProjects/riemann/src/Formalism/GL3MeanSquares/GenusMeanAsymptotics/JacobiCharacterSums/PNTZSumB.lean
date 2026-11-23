import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.DeuringHeilbronnM

open Finset Complex Classical

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimesInProgressions

open Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds Formalism.ZeroFreeDirichlet

theorem density_norm (h : LogDensityM) :
    ∃ a B C : ℝ, 1 ≤ a ∧ 0 ≤ B ∧ 1 ≤ C ∧
      ∀ (M : ℕ) [NeZero M] (T v : ℝ) (S : Finset (DirichletCharacter ℂ M × ℂ)), 3 ≤ M → 2 ≤ T →
      (∀ p ∈ S, 1 / 2 ≤ p.2.re ∧ p.2.re ≤ 1 ∧ Real.log ((M : ℝ) * T) * (1 - p.2.re) ≤ v ∧ |p.2.im| ≤ T ∧
        IsLZero p.1 p.2) →
      (∀ p ∈ S, ∀ p' ∈ S, p ≠ p' → p.1 = p'.1 → 1 ≤ |p.2.im - p'.2.im|) →
      (S.card : ℝ) ≤ C * Real.exp (a * v) * Real.log ((M : ℝ) * T) ^ B := by
  obtain ⟨A, B, C, h⟩ := h
  refine ⟨max A 1, max B 0, max C 1, le_max_right _ _, le_max_right _ _, le_max_right _ _, ?_⟩
  intro M _ T v S hM hT hS hsp
  have hM' : (3 : ℝ) ≤ M := by exact_mod_cast hM
  have hMT : (6 : ℝ) ≤ (M : ℝ) * T := by nlinarith
  set ℓ : ℝ := Real.log ((M : ℝ) * T) with hℓ
  have hℓ1 : 1 ≤ ℓ := by
    rw [hℓ, Real.le_log_iff_exp_le (by linarith)]
    have := Real.exp_one_lt_d9
    linarith
  have hℓ0 : 0 < ℓ := by linarith
  rcases S.eq_empty_or_nonempty with rfl | ⟨p0, hp0⟩
  · simp only [card_empty, Nat.cast_zero]
    have : 0 < max C 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
    positivity
  have hv : 0 ≤ v := by
    obtain ⟨_, h2, h3, _⟩ := hS p0 hp0
    have : 0 ≤ ℓ * (1 - p0.2.re) := mul_nonneg hℓ0.le (by linarith)
    linarith
  set σ : ℝ := max (1 / 2) (1 - v / ℓ) with hσ
  have hσ1 : σ ≤ 1 := by
    apply max_le (by norm_num)
    have : 0 ≤ v / ℓ := div_nonneg hv hℓ0.le
    linarith
  have hσ2 : 1 - σ ≤ v / ℓ := by
    have := le_max_right (1 / 2 : ℝ) (1 - v / ℓ)
    linarith
  have key := h M T σ S hM hT (le_max_left _ _) (by
    intro p hp
    obtain ⟨h1, h2, h3, h4, h5⟩ := hS p hp
    refine ⟨max_le h1 ?_, h4, h5⟩
    have : 1 - p.2.re ≤ v / ℓ := by rw [le_div_iff₀ hℓ0]; linarith
    linarith) hsp
  refine key.trans ?_
  have e1 : ((M : ℝ) * T) ^ (A * (1 - σ)) ≤ Real.exp (max A 1 * v) := by
    rw [Real.rpow_def_of_pos (by linarith)]
    apply Real.exp_le_exp.mpr
    have h1 : A * (1 - σ) ≤ max A 1 * (v / ℓ) := by
      have hA0 : 0 ≤ max A 1 := le_trans zero_le_one (le_max_right _ _)
      calc A * (1 - σ) ≤ max A 1 * (1 - σ) := mul_le_mul_of_nonneg_right (le_max_left _ _) (by linarith)
        _ ≤ max A 1 * (v / ℓ) := mul_le_mul_of_nonneg_left hσ2 hA0
    calc ℓ * (A * (1 - σ)) ≤ ℓ * (max A 1 * (v / ℓ)) := mul_le_mul_of_nonneg_left h1 hℓ0.le
      _ = max A 1 * v := by field_simp
  have e2 : ℓ ^ B ≤ ℓ ^ (max B 0) := Real.rpow_le_rpow_of_exponent_le hℓ1 (le_max_left _ _)
  have p1 : 0 ≤ ((M : ℝ) * T) ^ (A * (1 - σ)) := Real.rpow_nonneg (by linarith) _
  have p2 : 0 ≤ ℓ ^ B := Real.rpow_nonneg hℓ0.le _
  have hC0 : 0 ≤ max C 1 := le_trans zero_le_one (le_max_right _ _)
  calc C * ((M : ℝ) * T) ^ (A * (1 - σ)) * ℓ ^ B
      ≤ max C 1 * ((M : ℝ) * T) ^ (A * (1 - σ)) * ℓ ^ B := by
        apply mul_le_mul_of_nonneg_right _ p2
        exact mul_le_mul_of_nonneg_right (le_max_left _ _) p1
    _ ≤ max C 1 * Real.exp (max A 1 * v) * ℓ ^ (max B 0) := by
        apply mul_le_mul _ e2 p2 (by positivity)
        exact mul_le_mul_of_nonneg_left e1 hC0

theorem ell_bounds (M : ℕ) (hM : 8 ≤ M) (A₁ : ℝ) (hA : 1 ≤ A₁) :
    2 ≤ Real.log M ∧ Real.log M ≤ Real.log ((M : ℝ) * ((M : ℝ) ^ A₁ + 3)) ∧
      Real.log ((M : ℝ) * ((M : ℝ) ^ A₁ + 3)) ≤ (A₁ + 2) * Real.log M := by
  have hM' : (8 : ℝ) ≤ M := by exact_mod_cast hM
  have hM0 : (0 : ℝ) < M := by linarith
  have hp : (M : ℝ) ≤ (M : ℝ) ^ A₁ := by
    conv_lhs => rw [← Real.rpow_one (M : ℝ)]
    exact Real.rpow_le_rpow_of_exponent_le (by linarith) hA
  refine ⟨?_, ?_, ?_⟩
  · have h1 : Real.log 8 ≤ Real.log M := Real.log_le_log (by norm_num) hM'
    have h2 : Real.log 8 = 3 * Real.log 2 := by
      rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]; norm_num
    have := Real.log_two_gt_d9
    linarith
  · apply Real.log_le_log hM0
    nlinarith
  · have h1 : (M : ℝ) * ((M : ℝ) ^ A₁ + 3) ≤ (M : ℝ) ^ (A₁ + 2) := by
      rw [Real.rpow_add hM0, show ((M : ℝ) ^ (2 : ℝ)) = (M : ℝ) * M by
        rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; ring]
      have h2 : (M : ℝ) ^ A₁ + 3 ≤ (M : ℝ) ^ A₁ * M := by nlinarith
      calc (M : ℝ) * ((M : ℝ) ^ A₁ + 3) ≤ (M : ℝ) * ((M : ℝ) ^ A₁ * M) :=
            mul_le_mul_of_nonneg_left h2 hM0.le
        _ = _ := by ring
    calc _ ≤ Real.log ((M : ℝ) ^ (A₁ + 2)) := Real.log_le_log (by positivity) h1
      _ = _ := Real.log_rpow hM0 _

end Formalism.HermitianLattices.Ext.PrimesInProgressions
