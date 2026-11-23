import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PointsNonemptyUnitaryRankOne
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

namespace GlobalTheory.Div

theorem conj_of_twist : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (β : G.Cˣ) (y₁ y₂ : grp G β) (y₀ c₁ c₂ w : G.Cˣ) (r : ℚ),
    (((y₁ : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) = c₁ * y₀ * ((c₁⁻¹ : G.Cˣ) : G.C) →
    (((y₂ : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) = c₂ * y₀ * ((c₂⁻¹ : G.Cˣ) : G.C) →
    (y₁ : G.Cˣ × ℚˣ).2 = (y₂ : G.Cˣ × ℚˣ).2 → Commute (w : G.C) y₀ → 0 < r →
    (((c₂⁻¹ : G.Cˣ) : G.C) * β * sh G ((c₂⁻¹ : G.Cˣ) : G.C) * ((β⁻¹ : G.Cˣ) : G.C)) = algebraMap ℚ G.C r * ((w : G.C) * (((c₁⁻¹ : G.Cˣ) : G.C) * β * sh G ((c₁⁻¹ : G.Cˣ) : G.C) * ((β⁻¹ : G.Cˣ) : G.C)) * ((β : G.C) * sh G (w : G.C) * ((β⁻¹ : G.Cˣ) : G.C))) →
    ∃ γ : grp G β, y₂ = γ * y₁ * γ⁻¹ := by
  intro p _ G β y₁ y₂ y₀ c₁ c₂ w r h1 h2 hs hw hr H
  have shm : ∀ a b : G.C, sh G (a * b) = sh G b * sh G a := by
    intro a b; simp only [sh, map_mul, MulOpposite.unop_mul]
  have shc : sh G ((c₂⁻¹ : G.Cˣ) : G.C) * sh G (c₂ : G.C) = 1 := by
    rw [← shm, Units.mul_inv]; simp [sh]
  have hR : algebraMap ℚ G.C r⁻¹ * algebraMap ℚ G.C r = 1 := by
    rw [← map_mul, inv_mul_cancel₀ hr.ne', map_one]
  set ru : ℚˣ := Units.mk0 r hr.ne' with hru

  have HX : (w : G.C) * (((c₁⁻¹ : G.Cˣ) : G.C) * β * sh G ((c₁⁻¹ : G.Cˣ) : G.C) * ((β⁻¹ : G.Cˣ) : G.C)) *
      ((β : G.C) * sh G (w : G.C) * ((β⁻¹ : G.Cˣ) : G.C)) = algebraMap ℚ G.C r⁻¹ *
      (((c₂⁻¹ : G.Cˣ) : G.C) * β * sh G ((c₂⁻¹ : G.Cˣ) : G.C) * ((β⁻¹ : G.Cˣ) : G.C)) := by
    rw [H, ← mul_assoc (algebraMap ℚ G.C r⁻¹), hR, one_mul]
  have mem : ((c₂ * w * c₁⁻¹, ru⁻¹) : G.Cˣ × ℚˣ) ∈ grp G β := by
    refine ⟨?_, ?_⟩
    · change ((c₂ * w * c₁⁻¹ : G.Cˣ) : G.C) * β * sh G ((c₂ * w * c₁⁻¹ : G.Cˣ) : G.C) =
        algebraMap ℚ G.C ((ru⁻¹ : ℚˣ) : ℚ) * β
      rw [Units.val_inv_eq_inv_val, hru, Units.val_mk0]
      simp only [Units.val_mul, shm]
      calc (c₂ : G.C) * w * ((c₁⁻¹ : G.Cˣ) : G.C) * β * (sh G ((c₁⁻¹ : G.Cˣ) : G.C) * (sh G (w : G.C) * sh G (c₂ : G.C)))
          = c₂ * ((w : G.C) * (((c₁⁻¹ : G.Cˣ) : G.C) * β * sh G ((c₁⁻¹ : G.Cˣ) : G.C) * ((β⁻¹ : G.Cˣ) : G.C)) *
            ((β : G.C) * sh G (w : G.C) * ((β⁻¹ : G.Cˣ) : G.C))) * β * sh G (c₂ : G.C) := by
            simp only [mul_assoc, Units.inv_mul_cancel_left]
        _ = algebraMap ℚ G.C r⁻¹ * ((c₂ : G.C) * ((c₂⁻¹ : G.Cˣ) : G.C) * β *
              (sh G ((c₂⁻¹ : G.Cˣ) : G.C) * sh G (c₂ : G.C))) := by
            rw [HX, Algebra.left_comm]
            simp only [mul_assoc, Units.inv_mul_cancel_left]
        _ = _ := by rw [shc, Units.mul_inv, one_mul, mul_one]
    · change 0 < ((ru⁻¹ : ℚˣ) : ℚ)
      rw [Units.val_inv_eq_inv_val, hru, Units.val_mk0]; exact inv_pos.2 hr
  refine ⟨⟨_, mem⟩, ?_⟩
  have e1 : (y₁ : G.Cˣ × ℚˣ).1 = c₁ * y₀ * c₁⁻¹ := Units.ext (by rw [h1]; simp)
  have e2 : (y₂ : G.Cˣ × ℚˣ).1 = c₂ * y₀ * c₂⁻¹ := Units.ext (by rw [h2]; simp)
  have hwu : w * y₀ = y₀ * w := Units.ext (by simpa using hw.eq)
  have hwu' : ∀ x : G.Cˣ, w * (y₀ * x) = y₀ * (w * x) := fun x => by rw [← mul_assoc, hwu, mul_assoc]
  apply Subtype.ext
  apply Prod.ext
  · show (y₂ : G.Cˣ × ℚˣ).1 = (c₂ * w * c₁⁻¹) * (y₁ : G.Cˣ × ℚˣ).1 * (c₂ * w * c₁⁻¹)⁻¹
    rw [e1, e2]
    simp only [_root_.mul_inv_rev, inv_inv, mul_assoc, inv_mul_cancel_left, hwu', mul_inv_cancel_left]
  · show (y₂ : G.Cˣ × ℚˣ).2 = ru⁻¹ * (y₁ : G.Cˣ × ℚˣ).2 * ru⁻¹⁻¹
    rw [hs, mul_comm ru⁻¹, mul_assoc, mul_inv_cancel, mul_one]

end GlobalTheory.Div
