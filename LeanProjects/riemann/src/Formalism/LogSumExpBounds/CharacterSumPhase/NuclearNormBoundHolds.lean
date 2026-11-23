import Formalism.LogSumExpBounds.NuclearBound

namespace Formalism.NuclearRankWeightBounds.P

open Finset Matrix

theorem sum_sq_eigenvalues {N : ℕ} (Y : Matrix (Fin N) (Fin N) ℂ) (hY : Y.IsHermitian) :
    ∑ j, hY.eigenvalues j ^ 2 = ∑ a, ∑ b, ‖Y a b‖ ^ 2 := by
  set U : Matrix (Fin N) (Fin N) ℂ := (hY.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℂ) with hUdef
  set D : Matrix (Fin N) (Fin N) ℂ := diagonal (RCLike.ofReal ∘ hY.eigenvalues) with hDdef
  have hsp : Y = U * D * star U := by
    conv_lhs => rw [hY.spectral_theorem]
    rfl
  have hu : star U * U = 1 := Unitary.coe_star_mul_self hY.eigenvectorUnitary
  have h1 : (Y * Y).trace = (D * D).trace := by
    have : Y * Y = U * (D * D) * star U := by
      rw [hsp]
      simp only [mul_assoc]
      rw [← mul_assoc (star U) U, hu, one_mul]
    rw [this, trace_mul_cycle, hu, one_mul]
  have h2 : (D * D).trace = ∑ j, ((hY.eigenvalues j ^ 2 : ℝ) : ℂ) := by
    rw [hDdef, diagonal_mul_diagonal, trace_diagonal]
    simp [pow_two]
  have h3 : (Y * Y).trace = ∑ a, ∑ b, ((‖Y a b‖ ^ 2 : ℝ) : ℂ) := by
    conv_lhs => rw [show Y * Y = Yᴴ * Y by rw [hY.eq]]
    simp only [trace, Matrix.diag, mul_apply, conjTranspose_apply]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [show star (Y a b) = (starRingEnd ℂ) (Y a b) from rfl, Complex.conj_mul']
    push_cast; ring
  have h4 : ((∑ j, hY.eigenvalues j ^ 2 : ℝ) : ℂ) = ((∑ a, ∑ b, ‖Y a b‖ ^ 2 : ℝ) : ℂ) := by
    simp only [Complex.ofReal_sum]
    rw [← h3, h1, h2]
  exact_mod_cast h4

theorem nuclear_norm_bound_holds : Formalism.NuclearRankWeightBounds.D.NuclearBound := by
  intro N Y hY
  classical
  set μ := hY.eigenvalues
  have hrank : (Y.rank : ℝ) = ∑ j, (if μ j ≠ 0 then (1 : ℝ) else 0) ^ 2 := by
    rw [hY.rank_eq_card_non_zero_eigs, Fintype.card_subtype]
    simp only [ite_pow, one_pow, ne_eq, zero_pow two_ne_zero]
    rw [Finset.sum_boole]
  have hhs : Formalism.NuclearRankWeightBounds.D.hs Y = Real.sqrt (∑ j, |μ j| ^ 2) := by
    unfold Formalism.NuclearRankWeightBounds.D.hs
    rw [← sum_sq_eigenvalues Y hY]
    simp only [sq_abs]
    rfl
  have hsum : ∑ j, |μ j| = ∑ j, (if μ j ≠ 0 then (1 : ℝ) else 0) * |μ j| := by
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases h : μ j = 0 <;> simp [h]
  rw [hrank, hhs, hsum]
  exact Real.sum_mul_le_sqrt_mul_sqrt _ _ _

end Formalism.NuclearRankWeightBounds.P
