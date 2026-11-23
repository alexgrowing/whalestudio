import Development.AbelianVarietyTheory.Definitions.Foundations.PetIPSmulRight
import Development.AbelianVarietyTheory.Definitions.Foundations.RepL
import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.Newform
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory

theorem norm_le_of_bounded_two_step_recursion (x y : ℂ) (c : ℕ → ℂ) (C R : ℝ) (hR : 0 ≤ R)
    (h0 : c 0 = 1) (h1 : c 1 = x + y)
    (hrec : ∀ r, c (r + 2) = (x + y) * c (r + 1) - x * y * c r)
    (hb : ∀ r, ‖c r‖ ≤ C * R ^ r) : ‖x‖ ≤ R := by
  have hd : ∀ r : ℕ, c (r + 1) - y * c r = x ^ (r + 1) := by
    intro r
    induction r with
    | zero => simp [h0, h1]
    | succ n ih =>
      rw [show n + 1 + 1 = n + 2 by ring]
      linear_combination hrec n + x * ih
  have key : ∀ r : ℕ, ‖x‖ ^ (r + 1) ≤ C * (R + ‖y‖) * R ^ r := by
    intro r
    calc ‖x‖ ^ (r + 1) = ‖c (r + 1) - y * c r‖ := by rw [hd r, norm_pow]
      _ ≤ ‖c (r + 1)‖ + ‖y‖ * ‖c r‖ := by
          refine (norm_sub_le _ _).trans ?_
          rw [norm_mul]
      _ ≤ C * R ^ (r + 1) + ‖y‖ * (C * R ^ r) :=
          add_le_add (hb _) (mul_le_mul_of_nonneg_left (hb _) (norm_nonneg _))
      _ = C * (R + ‖y‖) * R ^ r := by ring
  by_contra hlt
  push_neg at hlt
  have hxpos : 0 < ‖x‖ := lt_of_le_of_lt hR hlt
  have hq0 : 0 ≤ R / ‖x‖ := div_nonneg hR hxpos.le
  have hq1 : R / ‖x‖ < 1 := (div_lt_one hxpos).2 hlt
  have ht : Tendsto (fun r : ℕ => C * (R + ‖y‖) * (R / ‖x‖) ^ r) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1).const_mul (C * (R + ‖y‖))
  have hle : ∀ r : ℕ, ‖x‖ ≤ C * (R + ‖y‖) * (R / ‖x‖) ^ r := by
    intro r
    have hpos : 0 < ‖x‖ ^ r := pow_pos hxpos r
    rw [div_pow, ← mul_div_assoc, le_div_iff₀ hpos, ← pow_succ']
    exact key r
  have : ‖x‖ ≤ 0 := ge_of_tendsto' ht hle
  linarith

theorem roots_norm_le_of_bounded_two_step_recursion :
    ∀ (x y : ℂ) (c : ℕ → ℂ) (C R : ℝ), 0 ≤ R → c 0 = 1 → c 1 = x + y →
      (∀ r, c (r + 2) = (x + y) * c (r + 1) - x * y * c r) → (∀ r, ‖c r‖ ≤ C * R ^ r) →
      ‖x‖ ≤ R ∧ ‖y‖ ≤ R := by
  intro x y c C R hR h0 h1 hrec hb
  refine ⟨norm_le_of_bounded_two_step_recursion x y c C R hR h0 h1 hrec hb,
    norm_le_of_bounded_two_step_recursion y x c C R hR h0 (by rw [h1, add_comm]) ?_ hb⟩
  intro r
  rw [hrec r]
  ring

end GlobalTheory
