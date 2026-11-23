import Mathlib
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.GaussPart
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ImportsRestExtra

noncomputable section

open MeasureTheory Matrix Set Filter Topology MvPolynomial

namespace PositivityTheory.Rg.Sw.AbsSt.DF

open PositivityTheory.Rg.Sw

variable {m n : ℕ}

def ept (x : Fin m → Fin n → ℂ) : Fin m × Fin n × Bool → ℂ :=
  fun k => if k.2.2 then star (x k.1 k.2.1) else x k.1 k.2.1

theorem evX_eq (P : PX m n) (x : Fin m → Fin n → ℂ) : evX P x = MvPolynomial.eval (ept x) P := rfl

theorem norm_ept_le (x : Fin m → Fin n → ℂ) (k : Fin m × Fin n × Bool) : ‖ept x k‖ ≤ ‖x‖ := by
  have h : ‖x k.1 k.2.1‖ ≤ ‖x‖ := (norm_le_pi_norm (x k.1) k.2.1).trans (norm_le_pi_norm x k.1)
  unfold ept
  split_ifs
  · simpa using h
  · exact h

theorem continuous_ept : Continuous (ept : (Fin m → Fin n → ℂ) → _) := by
  refine continuous_pi fun k => ?_
  unfold ept
  split_ifs
  · exact continuous_star.comp ((continuous_apply k.2.1).comp (continuous_apply k.1))
  · exact (continuous_apply k.2.1).comp (continuous_apply k.1)

theorem continuous_evX (P : PX m n) : Continuous fun x : Fin m → Fin n → ℂ => evX P x :=
  (MvPolynomial.continuous_eval P).comp continuous_ept

theorem poly_bound (P : PX m n) : ∃ C : ℝ, ∃ k : ℕ, 0 ≤ C ∧ ∀ x, ‖evX P x‖ ≤ C * (1 + ‖x‖) ^ k := by
  induction P using MvPolynomial.induction_on with
  | C a => exact ⟨‖a‖, 0, norm_nonneg _, fun x => by simp [evX_eq]⟩
  | add p q hp hq =>
    obtain ⟨C₁, k₁, h₁, hb₁⟩ := hp
    obtain ⟨C₂, k₂, h₂, hb₂⟩ := hq
    refine ⟨C₁ + C₂, k₁ + k₂, add_nonneg h₁ h₂, fun x => ?_⟩
    have h1 : (1 : ℝ) ≤ 1 + ‖x‖ := le_add_of_nonneg_right (norm_nonneg x)
    have e1 : (1 + ‖x‖) ^ k₁ ≤ (1 + ‖x‖) ^ (k₁ + k₂) := pow_le_pow_right₀ h1 (Nat.le_add_right _ _)
    have e2 : (1 + ‖x‖) ^ k₂ ≤ (1 + ‖x‖) ^ (k₁ + k₂) := pow_le_pow_right₀ h1 (Nat.le_add_left _ _)
    rw [evX_eq, map_add]
    calc ‖eval (ept x) p + eval (ept x) q‖ ≤ ‖eval (ept x) p‖ + ‖eval (ept x) q‖ := norm_add_le _ _
      _ ≤ C₁ * (1 + ‖x‖) ^ k₁ + C₂ * (1 + ‖x‖) ^ k₂ := add_le_add (hb₁ x) (hb₂ x)
      _ ≤ C₁ * (1 + ‖x‖) ^ (k₁ + k₂) + C₂ * (1 + ‖x‖) ^ (k₁ + k₂) :=
          add_le_add (mul_le_mul_of_nonneg_left e1 h₁) (mul_le_mul_of_nonneg_left e2 h₂)
      _ = (C₁ + C₂) * (1 + ‖x‖) ^ (k₁ + k₂) := by ring
  | mul_X p i hp =>
    obtain ⟨C, k, h0, hb⟩ := hp
    refine ⟨C, k + 1, h0, fun x => ?_⟩
    rw [evX_eq, map_mul, eval_X, norm_mul, pow_succ, ← mul_assoc]
    exact mul_le_mul (hb x) ((norm_ept_le x i).trans (le_add_of_nonneg_left zero_le_one)) (norm_nonneg _)
      (mul_nonneg h0 (pow_nonneg (by positivity) _))

theorem sq_norm_le_sum (x : Fin m → Fin n → ℂ) : ‖x‖ ^ 2 ≤ ∑ a, ∑ j, ‖x a j‖ ^ 2 :=
  _root_.UpperTheory.Reformulated.B.Yhb3.main x

theorem decay (k : ℕ) (κ : ℝ) (hκ : 0 < κ) (r : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℝ, 0 ≤ s → (1 + s) ^ k * Real.exp (-(κ * s ^ 2)) ≤ C * (1 + s) ^ (-r) := by
  obtain ⟨N, hN⟩ := exists_nat_ge ((k : ℝ) + r)
  refine ⟨2 ^ N * (1 + N.factorial / κ ^ N), by positivity, fun s hs => ?_⟩
  have h1 : (1 : ℝ) ≤ 1 + s := le_add_of_nonneg_right hs
  have hpos : 0 < 1 + s := by linarith
  have hE : 0 < Real.exp (-(κ * s ^ 2)) := Real.exp_pos _

  have hA : (1 + s) ^ N ≤ 2 ^ N * (1 + (s ^ 2) ^ N) := by
    rcases le_total s 1 with h | h
    · calc (1 + s) ^ N ≤ 2 ^ N := pow_le_pow_left₀ hpos.le (by linarith) N
        _ ≤ 2 ^ N * (1 + (s ^ 2) ^ N) := le_mul_of_one_le_right (by positivity)
            (le_add_of_nonneg_right (by positivity))
    · have : 1 + s ≤ 2 * s ^ 2 := by nlinarith
      calc (1 + s) ^ N ≤ (2 * s ^ 2) ^ N := pow_le_pow_left₀ hpos.le this N
        _ = 2 ^ N * (s ^ 2) ^ N := by rw [mul_pow]
        _ ≤ 2 ^ N * (1 + (s ^ 2) ^ N) := by nlinarith [pow_nonneg (by positivity : (0:ℝ) ≤ 2) N]
  have hB : (s ^ 2) ^ N * Real.exp (-(κ * s ^ 2)) ≤ N.factorial / κ ^ N := by
    have := Real.pow_div_factorial_le_exp (x := κ * s ^ 2) (by positivity) N
    rw [div_le_iff₀ (by positivity)] at this
    rw [le_div_iff₀ (by positivity)]
    have e : Real.exp (-(κ * s ^ 2)) * Real.exp (κ * s ^ 2) = 1 := by rw [← Real.exp_add]; simp
    calc (s ^ 2) ^ N * Real.exp (-(κ * s ^ 2)) * κ ^ N = (κ * s ^ 2) ^ N * Real.exp (-(κ * s ^ 2)) := by ring
      _ ≤ (Real.exp (κ * s ^ 2) * N.factorial) * Real.exp (-(κ * s ^ 2)) :=
          mul_le_mul_of_nonneg_right this hE.le
      _ = N.factorial := by rw [mul_comm (Real.exp _), mul_assoc, mul_comm (Real.exp _), e, mul_one]
  have hC : (1 + s) ^ N * Real.exp (-(κ * s ^ 2)) ≤ 2 ^ N * (1 + N.factorial / κ ^ N) := by
    calc (1 + s) ^ N * Real.exp (-(κ * s ^ 2)) ≤ 2 ^ N * (1 + (s ^ 2) ^ N) * Real.exp (-(κ * s ^ 2)) :=
          mul_le_mul_of_nonneg_right hA hE.le
      _ = 2 ^ N * (Real.exp (-(κ * s ^ 2)) + (s ^ 2) ^ N * Real.exp (-(κ * s ^ 2))) := by ring
      _ ≤ 2 ^ N * (1 + N.factorial / κ ^ N) := by
          gcongr
          · exact Real.exp_le_one_iff.2 (by nlinarith [sq_nonneg s])
  have hR : (1 + s) ^ k * (1 + s) ^ r ≤ (1 + s) ^ N := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hpos, ← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le h1 hN
  have hr : (1 + s) ^ r * (1 + s) ^ (-r) = 1 := by
    rw [← Real.rpow_add hpos]; simp
  calc (1 + s) ^ k * Real.exp (-(κ * s ^ 2))
      = ((1 + s) ^ k * (1 + s) ^ r * Real.exp (-(κ * s ^ 2))) * (1 + s) ^ (-r) := by
        rw [show ((1 + s) ^ k * (1 + s) ^ r * Real.exp (-(κ * s ^ 2))) * (1 + s) ^ (-r) =
          (1 + s) ^ k * Real.exp (-(κ * s ^ 2)) * ((1 + s) ^ r * (1 + s) ^ (-r)) by ring, hr, mul_one]
    _ ≤ ((1 + s) ^ N * Real.exp (-(κ * s ^ 2))) * (1 + s) ^ (-r) := by
        gcongr
    _ ≤ (2 ^ N * (1 + N.factorial / κ ^ N)) * (1 + s) ^ (-r) := by gcongr

end PositivityTheory.Rg.Sw.AbsSt.DF
