import Mathlib

namespace PI.QmIndepW

def IndepPoly : Prop :=
  ∀ Y Y' : ℂ, Y' ≠ Y + 1 → ∀ z : Fin 2 × Fin 2 → Fin 2 × Fin 2 → ℂ,
    (∀ β α : ℂ, (∃ n : ℤ, α = β + n) →
      (Y - β) * (Y' - β) * ((Y' + α) * (Y + α)) * z (0, 0) (0, 0) = 0 ∧
      (Y - β) * (Y' - β) * ((Y' + α - 1) * z (0, 0) (0, 1) + (Y + α) * z (0, 0) (1, 0)) = 0 ∧
      (Y - β) * (Y' - β) * z (0, 0) (1, 1) = 0 ∧
      ((Y' - β) * z (0, 1) (0, 0) + (Y - β + 1) * z (1, 0) (0, 0)) * ((Y' + α) * (Y + α)) = 0 ∧
      (Y' - β) * (Y' + α - 1) * z (0, 1) (0, 1) + (Y' - β) * (Y + α) * z (0, 1) (1, 0) +
          (Y - β + 1) * (Y' + α - 1) * z (1, 0) (0, 1) + (Y - β + 1) * (Y + α) * z (1, 0) (1, 0) = 0 ∧
      (Y' - β) * z (0, 1) (1, 1) + (Y - β + 1) * z (1, 0) (1, 1) = 0 ∧
      (Y' + α) * (Y + α) * z (1, 1) (0, 0) = 0 ∧
      (Y' + α - 1) * z (1, 1) (0, 1) + (Y + α) * z (1, 1) (1, 0) = 0 ∧
      z (1, 1) (1, 1) = 0) →
    ∀ A B, z A B = 0

theorem indepPoly : IndepPoly := by
  intro Y Y' hYY' z hz
  have hD : Y' - Y - 1 ≠ 0 := fun h => hYY' (by linear_combination h)
  have two : ∀ A B p q : ℂ, A - B = Y' - Y - 1 → A * p + B * q = 0 →
      (A + 1) * p + (B + 1) * q = 0 → p = 0 ∧ q = 0 := by
    intro A B p q hAB e1 e2
    have hpq : p + q = 0 := by linear_combination e2 - e1
    have hp : (A - B) * p = 0 := by linear_combination e1 - B * hpq
    rw [hAB] at hp
    have hp0 : p = 0 := (mul_eq_zero.mp hp).resolve_left hD
    exact ⟨hp0, by linear_combination hpq - hp0⟩
  obtain ⟨R, hR⟩ : ∃ R : ℝ, R = ‖Y‖ + ‖Y'‖ + 1 := ⟨_, rfl⟩
  have hRpos : 0 < R := by rw [hR]; positivity
  have nz : ∀ w : ℂ, ‖w‖ < R → w - R ≠ 0 ∧ w + R ≠ 0 := by
    intro w hw
    constructor
    · intro h
      have hw' : w = R := by linear_combination h
      rw [hw', Complex.norm_real, Real.norm_eq_abs, abs_of_pos hRpos] at hw
      exact lt_irrefl _ hw
    · intro h
      have hw' : w = -R := by linear_combination h
      rw [hw', norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hRpos] at hw
      exact lt_irrefl _ hw
  have hY := nz Y (by rw [hR]; linarith [norm_nonneg Y'])
  have hY' := nz Y' (by rw [hR]; linarith [norm_nonneg Y])
  obtain ⟨a1, a2, a3, a4, -, a6, a7, a8, a9⟩ := hz R R ⟨0, by simp⟩
  obtain ⟨-, b2, -, -, -, -, -, b8, -⟩ := hz R (R + 1) ⟨1, by simp⟩
  obtain ⟨-, -, -, c4, -, c6, -, -, -⟩ := hz (R + 1) R ⟨-1, by push_cast; ring⟩
  obtain ⟨-, -, -, -, d5, -, -, -, -⟩ := hz Y' Y' ⟨0, by simp⟩
  obtain ⟨-, -, -, -, e5, -, -, -, -⟩ := hz Y' (Y' + 1) ⟨1, by simp⟩
  obtain ⟨-, -, -, -, f5, -, -, -, -⟩ := hz (Y + 1) (Y + 1) ⟨0, by simp⟩
  obtain ⟨-, -, -, -, g5, -, -, -, -⟩ := hz (Y + 1) (Y + 2) ⟨1, by push_cast; ring⟩
  have F1 : (Y - R) * (Y' - R) ≠ 0 := mul_ne_zero hY.1 hY'.1
  have F2 : (Y' + R) * (Y + R) ≠ 0 := mul_ne_zero hY'.2 hY.2
  have z0000 : z (0, 0) (0, 0) = 0 := (mul_eq_zero.mp a1).resolve_left (mul_ne_zero F1 F2)
  have z0011 : z (0, 0) (1, 1) = 0 := (mul_eq_zero.mp a3).resolve_left F1
  have z1100 : z (1, 1) (0, 0) = 0 := (mul_eq_zero.mp a7).resolve_left F2
  obtain ⟨z0001, z0010⟩ := two (Y' + R - 1) (Y + R) (z (0, 0) (0, 1)) (z (0, 0) (1, 0)) (by ring)
    ((mul_eq_zero.mp a2).resolve_left F1)
    (by linear_combination (mul_eq_zero.mp b2).resolve_left F1)
  obtain ⟨z1101, z1110⟩ := two (Y' + R - 1) (Y + R) (z (1, 1) (0, 1)) (z (1, 1) (1, 0)) (by ring)
    (by linear_combination a8) (by linear_combination b8)
  obtain ⟨z0100, z1000⟩ := two (Y' - R - 1) (Y - R) (z (0, 1) (0, 0)) (z (1, 0) (0, 0)) (by ring)
    (by linear_combination (mul_eq_zero.mp c4).resolve_right F2)
    (by linear_combination (mul_eq_zero.mp a4).resolve_right F2)
  obtain ⟨z0111, z1011⟩ := two (Y' - R - 1) (Y - R) (z (0, 1) (1, 1)) (z (1, 0) (1, 1)) (by ring)
    (by linear_combination c6) (by linear_combination a6)
  have hL : Y - Y' + 1 ≠ 0 := fun h => hD (by linear_combination -h)
  have i1 : (Y - Y' + 1) * ((2 * Y' - 1) * z (1, 0) (0, 1) + (Y + Y') * z (1, 0) (1, 0)) = 0 := by
    linear_combination d5
  have i2 : (Y - Y' + 1) * ((2 * Y') * z (1, 0) (0, 1) + (Y + Y' + 1) * z (1, 0) (1, 0)) = 0 := by
    linear_combination e5
  obtain ⟨z1001, z1010⟩ := two (2 * Y' - 1) (Y + Y') (z (1, 0) (0, 1)) (z (1, 0) (1, 0)) (by ring)
    ((mul_eq_zero.mp i1).resolve_left hL)
    (by linear_combination (mul_eq_zero.mp i2).resolve_left hL)
  have j1 : (Y' - Y - 1) * ((Y' + Y) * z (0, 1) (0, 1) + (2 * Y + 1) * z (0, 1) (1, 0)) = 0 := by
    linear_combination f5
  have j2 : (Y' - Y - 1) * ((Y' + Y + 1) * z (0, 1) (0, 1) + (2 * Y + 2) * z (0, 1) (1, 0)) = 0 := by
    linear_combination g5
  obtain ⟨z0101, z0110⟩ := two (Y' + Y) (2 * Y + 1) (z (0, 1) (0, 1)) (z (0, 1) (1, 0)) (by ring)
    ((mul_eq_zero.mp j1).resolve_left hD)
    (by linear_combination (mul_eq_zero.mp j2).resolve_left hD)
  simp only [Prod.forall, Fin.forall_fin_two]
  repeat' constructor
  all_goals assumption

end PI.QmIndepW
