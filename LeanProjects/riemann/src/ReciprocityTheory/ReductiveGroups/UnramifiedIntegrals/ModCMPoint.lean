import Mathlib
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModDefs

noncomputable section
open scoped BigOperators Classical UpperHalfPlane MatrixGroups CongruenceSubgroup Manifold
open ModularForm EisensteinSeries ModularFormClass UpperHalfPlane Formalism.L2.Th1.CM

namespace ReciprocityTheory.ChartRestriction.L1

theorem omegaK_sq (d : ℕ) : 4 * omegaK d ^ 2 = 4 * omegaK d - (1 + d) := by
  have hs : (Complex.I * ((Real.sqrt d : ℝ) : ℂ)) ^ 2 = -(d : ℂ) := by
    rw [mul_pow, Complex.I_sq, ← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg d)]
    push_cast
    ring
  unfold omegaK
  linear_combination hs

theorem omegaK_lin {d : ℕ} (hd : 0 < d) {t n : ℤ} (h : (t : ℂ) * omegaK d + n = 0) :
    t = 0 ∧ n = 0 := by
  have h2 : (t : ℂ) * (1 + Complex.I * ((Real.sqrt d : ℝ) : ℂ)) + 2 * n = 0 := by
    rw [omegaK] at h
    linear_combination 2 * h
  have hsq : 0 < Real.sqrt d := Real.sqrt_pos.mpr (by exact_mod_cast hd)
  have h3 : (((t : ℝ) + 2 * n : ℝ) : ℂ) + (((t : ℝ) * Real.sqrt d : ℝ) : ℂ) * Complex.I = 0 := by
    push_cast
    linear_combination h2
  have him : (t : ℝ) * Real.sqrt d = 0 := by
    have := congrArg Complex.im h3
    simpa using this
  have hre : (t : ℝ) + 2 * n = 0 := by
    have := congrArg Complex.re h3
    simpa using this
  have ht : (t : ℝ) = 0 := by
    rcases mul_eq_zero.mp him with h | h
    · exact h
    · exact absurd h hsq.ne'
  have hn : (n : ℝ) = 0 := by linarith
  exact ⟨by exact_mod_cast ht, by exact_mod_cast hn⟩

theorem cmPoint {d : ℕ} (hd : 0 < d) {L : PeriodPair} (hL : HasCMBy d L) {c : ℂ} {τ : ℍ}
    (h : IsTauOf L c τ) (x y : ℤ) :
    ∃ A B C D : ℤ, ((x : ℂ) + y * omegaK d) * τ = A * τ + B ∧ (x : ℂ) + y * omegaK d = C * τ + D ∧
      4 * (A * D - B * C) = 4 * x ^ 2 + 4 * x * y + y ^ 2 * (1 + d) := by
  obtain ⟨hc, hmem⟩ := h
  have hmul : ∀ w ∈ L.lattice, ((x : ℂ) + y * omegaK d) * w ∈ L.lattice := by
    intro w hw
    have h1 : (x : ℂ) * w ∈ L.lattice := by
      rw [← zsmul_eq_mul]
      exact zsmul_mem hw x
    have h2 : (y : ℂ) * (omegaK d * w) ∈ L.lattice := by
      rw [← zsmul_eq_mul]
      exact zsmul_mem (hL w hw) y
    have e : ((x : ℂ) + y * omegaK d) * w = (x : ℂ) * w + (y : ℂ) * (omegaK d * w) := by ring
    rw [e]
    exact add_mem h1 h2
  have hcτ : c * (τ : ℂ) ∈ L.lattice := (hmem _).2 ⟨1, 0, by push_cast; ring⟩
  have hc1 : c ∈ L.lattice := (hmem _).2 ⟨0, 1, by push_cast; ring⟩
  obtain ⟨A, B, hAB⟩ := (hmem _).1 (hmul _ hcτ)
  obtain ⟨C, D, hCD⟩ := (hmem _).1 (hmul _ hc1)
  have e1 : ((x : ℂ) + y * omegaK d) * τ = A * τ + B := by
    apply mul_left_cancel₀ hc
    linear_combination hAB
  have e2 : (x : ℂ) + y * omegaK d = C * τ + D := by
    apply mul_left_cancel₀ hc
    linear_combination hCD
  refine ⟨A, B, C, D, e1, e2, ?_⟩

  have key : ((x : ℂ) + y * omegaK d - A) * ((x : ℂ) + y * omegaK d - D) = B * C := by
    linear_combination ((x : ℂ) + y * omegaK d - A) * e2 + (C : ℂ) * e1
  have hω := omegaK_sq d
  obtain ⟨ht, hn⟩ := omegaK_lin hd (t := 8 * x * y + 4 * y ^ 2 - 4 * (A + D) * y)
    (n := 4 * x ^ 2 - y ^ 2 * (1 + d) - 4 * (A + D) * x + 4 * (A * D - B * C)) (by
      push_cast
      linear_combination 4 * key - (y : ℂ) ^ 2 * hω)
  by_cases hy : y = 0
  · subst hy
    simp only [Int.cast_zero, zero_mul, add_zero] at e1 e2
    have hτ : 0 < (τ : ℂ).im := τ.im_pos
    have e2' : (x : ℂ) - D = (C : ℂ) * τ := by linear_combination e2
    have e1' : ((x : ℂ) - A) * τ = (B : ℂ) := by linear_combination e1
    have hC : C = 0 := by
      have := congrArg Complex.im e2'
      simp only [Complex.sub_im, Complex.intCast_im, Complex.mul_im, Complex.intCast_re] at this
      have h0 : (C : ℝ) * (τ : ℂ).im = 0 := by linarith
      rcases mul_eq_zero.mp h0 with h0 | h0
      · exact_mod_cast h0
      · exact absurd h0 hτ.ne'
    have hA : A = x := by
      have := congrArg Complex.im e1'
      simp only [Complex.sub_im, Complex.intCast_im, Complex.mul_im, Complex.intCast_re,
        Complex.sub_re] at this
      have h0 : ((x : ℝ) - A) * (τ : ℂ).im = 0 := by linarith
      rcases mul_eq_zero.mp h0 with h0 | h0
      · have : (A : ℝ) = x := by linarith
        exact_mod_cast this
      · exact absurd h0 hτ.ne'
    subst hC hA
    have hD : D = A := by
      have : ((A : ℤ) : ℂ) = D := by linear_combination e2'
      exact_mod_cast this.symm
    subst hD
    ring
  · have h4 : 4 * (y * (2 * x + y - (A + D))) = 0 := by linear_combination ht
    have hs : 2 * x + y - (A + D) = 0 :=
      (mul_eq_zero.mp ((mul_eq_zero.mp h4).resolve_left (by norm_num))).resolve_left hy
    linear_combination hn - 4 * x * hs

end ReciprocityTheory.ChartRestriction.L1
