import Mathlib
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.TorBasic
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.TorHensel

noncomputable section
open scoped Classical

namespace ReciprocityTheory.ChartRestriction.L1

open Formalism.L2.Th1.CM Formalism.ELL WeierstrassCurve
open Formalism.L2.Th1.E (px py IntCurve)
open Formalism.L2.Th1.A (shortW)

variable {l : ℕ} [Fact l.Prime] {g2 g3 : ℂ_[l]}

theorem cubic_coeff_ind (p : ℂ_[l] → Prop) (T : Cubic ℂ_[l]) (h0 : p 0) (ha : p T.a) (hb : p T.b)
    (hc : p T.c) (hd : p T.d) (i : ℕ) : p (T.toPoly.coeff i) := by
  rcases i with _ | _ | _ | _ | i
  · simpa [Cubic.coeff_eq_d] using hd
  · simpa [Cubic.coeff_eq_c] using hc
  · simpa [Cubic.coeff_eq_b] using hb
  · simpa [Cubic.coeff_eq_a] using ha
  · rw [Cubic.coeff_eq_zero (by omega)]
    exact h0

theorem tor_two (h : GoodPair l g2 g3) (P : (shortW g2 g3).toAffine.Point) (hP0 : P ≠ 0)
    (h2 : P + P = 0) : px _ P ∈ MaximalUnramifiedExtension l ∧ py _ P ∈ MaximalUnramifiedExtension l := by
  have hl2 : ¬ l ∣ 2 := fun hd => by
    have := Nat.le_of_dvd (by norm_num) hd
    have := h.five
    omega
  have hl4 : ¬ l ∣ 4 := fun hd => by
    have := Nat.le_of_dvd (by norm_num) hd
    have := h.five
    omega
  have hE : ¬ InFormalGroupPoints P := torsion_not_mem_formalGroup h P 2 hl2 (by rw [two_nsmul]; exact h2) hP0
  obtain ⟨-, hx, hy⟩ := integral_of_not_mem_formalGroup h P hE
  obtain ⟨hpsi, hkap⟩ :=
    Formalism.L2.Th1.E.UnitKap_of Formalism.L2.Th1.E.nonsingular_norm ℂ_[l] (shortW g2 g3) (good_int h) P hP0 h2 hx hy
  cases P with
  | zero => exact absurd rfl hP0
  | some x y hns =>
    change ‖x‖ ≤ 1 at hx
    change 2 * y + (shortW g2 g3).a₁ * x + (shortW g2 g3).a₃ = 0 at hpsi
    change ‖3 * x ^ 2 + 2 * (shortW g2 g3).a₂ * x + (shortW g2 g3).a₄ - (shortW g2 g3).a₁ * y‖ = 1 at hkap
    change x ∈ MaximalUnramifiedExtension l ∧ y ∈ MaximalUnramifiedExtension l
    have hy0 : y = 0 := by
      simp only [shortW, zero_mul, add_zero] at hpsi
      simpa using hpsi
    have heq := hns.1
    rw [WeierstrassCurve.Affine.equation_iff] at heq
    simp only [shortW] at heq hkap
    have n4 : ‖(4 : ℂ_[l])‖ = 1 := by exact_mod_cast norm_natCast_Cl_of_not_dvd (l := l) hl4
    have m4 : (4 : ℂ_[l]) ∈ MaximalUnramifiedExtension l := by exact_mod_cast natCast_mem (MaximalUnramifiedExtension l) 4
    refine ⟨?_, hy0 ▸ zero_mem _⟩
    refine hensel_mem l (Cubic.toPoly ⟨1, 0, -g2 / 4, -g3 / 4⟩) ?_ ?_ x hx ?_ ?_
    · exact cubic_coeff_ind (· ∈ MaximalUnramifiedExtension l) _ (zero_mem _) (one_mem _) (zero_mem _)
        (div_mem (neg_mem h.mem2) m4) (div_mem (neg_mem h.mem3) m4)
    · refine cubic_coeff_ind (‖·‖ ≤ 1) _ (by simp) (by simp) (by simp) ?_ ?_
      · simpa [norm_div, n4] using h.norm2
      · simpa [norm_div, n4] using h.norm3
    · simp only [Cubic.toPoly, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
        Polynomial.eval_pow, Polynomial.eval_X]
      rw [hy0] at heq
      linear_combination -heq
    · have : (Cubic.toPoly (⟨1, 0, -g2 / 4, -g3 / 4⟩ : Cubic ℂ_[l])).derivative.eval x
          = 3 * x ^ 2 + 2 * 0 * x + -g2 / 4 - 0 * y := by
        simp only [Cubic.toPoly, Polynomial.derivative_add, Polynomial.derivative_mul,
          Polynomial.derivative_C, Polynomial.derivative_X_pow, Polynomial.derivative_X,
          Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
          Polynomial.eval_X, Polynomial.eval_zero, Polynomial.eval_one, Polynomial.eval_natCast,
          map_natCast]
        push_cast
        ring
      rw [this]
      exact hkap

end ReciprocityTheory.ChartRestriction.L1
