import Mathlib

open Matrix
open scoped ComplexOrder

theorem UpperTheory.V.KT.hadam :
    ∀ (N : ℕ) (G : Matrix (Fin N) (Fin N) ℂ), G.PosSemidef → (∀ a, (G a a).re ≤ 1) →
    0 ≤ G.det.re ∧ G.det.re ≤ 1 ∧ ‖G.det‖ = G.det.re := by
  intro N G hG hdiag
  have hH : G.IsHermitian := hG.1
  have hnn : ∀ i, 0 ≤ hH.eigenvalues i := fun i => hG.eigenvalues_nonneg i
  have hdet : G.det = ((∏ i, hH.eigenvalues i : ℝ) : ℂ) := by
    rw [hH.det_eq_prod_eigenvalues]
    push_cast
    rfl
  have htr : ∑ i, hH.eigenvalues i ≤ N := by
    have h2 : (G.trace).re = ∑ i, hH.eigenvalues i := by
      rw [hH.trace_eq_sum_eigenvalues, Complex.re_sum]
      simp
    have h3 : (G.trace).re ≤ N := by
      rw [Matrix.trace, Complex.re_sum]
      calc ∑ a, (G a a).re ≤ ∑ _a : Fin N, (1 : ℝ) := Finset.sum_le_sum fun a _ => hdiag a
        _ = N := by simp
    linarith
  have hp0 : 0 ≤ ∏ i, hH.eigenvalues i := Finset.prod_nonneg fun i _ => hnn i
  have hp1 : ∏ i, hH.eigenvalues i ≤ 1 := by
    calc ∏ i, hH.eigenvalues i ≤ ∏ i, Real.exp (hH.eigenvalues i - 1) :=
          Finset.prod_le_prod (fun i _ => hnn i) fun i _ => by
            linarith [Real.add_one_le_exp (hH.eigenvalues i - 1)]
      _ = Real.exp (∑ i, (hH.eigenvalues i - 1)) := (Real.exp_sum _ _).symm
      _ ≤ 1 := by
        rw [Real.exp_le_one_iff, Finset.sum_sub_distrib]
        simp
        linarith
  rw [hdet]
  simp only [Complex.ofReal_re, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hp0]
  exact ⟨hp0, hp1, trivial⟩
