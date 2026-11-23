import ReciprocityTheory.SemistableReduction.ShareSt
import ReciprocityTheory.SemistableReduction.Unipotent

noncomputable section

namespace ReciprocityTheory.MultiplicativeHeights

open Matrix NumberField
open scoped ComplexOrder MatrixOrder

theorem sb_re_star_dot {r : ℕ} (v : Fin r → ℂ) : (star v ⬝ᵥ v).re = normSq v := by
  unfold normSq dotProduct
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Pi.star_apply, Complex.star_def, Complex.conj_mul']
  norm_cast

theorem sb_normSq_pos {r : ℕ} {v : Fin r → ℂ} (hv : v ≠ 0) : 0 < normSq v := by
  obtain ⟨k, hk⟩ := Function.ne_iff.mp hv
  exact Finset.sum_pos' (fun i _ => by positivity)
    ⟨k, Finset.mem_univ _, pow_pos (norm_pos_iff.mpr hk) 2⟩

theorem sb_exists_root {r : ℕ} {H : Matrix (Fin r) (Fin r) ℂ} (hH : H.PosDef) :
    ∃ Q : Matrix (Fin r) (Fin r) ℂ, Q.det ≠ 0 ∧ ∀ u, hq H u = normSq (Q *ᵥ u) := by
  have hnn : 0 ≤ H := Matrix.nonneg_iff_posSemidef.mpr hH.posSemidef
  obtain ⟨Q, hQ⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hnn
  rw [Matrix.star_eq_conjTranspose] at hQ
  refine ⟨Q, ?_, fun u => ?_⟩
  · intro h0
    have := hH.det_pos
    rw [hQ, det_mul, h0, mul_zero] at this
    exact lt_irrefl _ this
  · have e : star u ᵥ* Qᴴ = star (Q *ᵥ u) := (star_mulVec Q u).symm
    unfold hq
    rw [hQ, ← mulVec_mulVec, dotProduct_mulVec, e, sb_re_star_dot]

theorem sb_normSq_mulVec_le {r : ℕ} (A : Matrix (Fin r) (Fin r) ℂ) (v : Fin r → ℂ) :
    normSq (A *ᵥ v) ≤ (∑ a, ∑ b, ‖A a b‖ ^ 2) * normSq v := by
  unfold normSq
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun a _ => ?_
  calc ‖(A *ᵥ v) a‖ ^ 2 = ‖∑ b, A a b * v b‖ ^ 2 := rfl
    _ ≤ (∑ b, ‖A a b‖ * ‖v b‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) ((norm_sum_le _ _).trans (le_of_eq (by simp [norm_mul]))) 2
    _ ≤ (∑ b, ‖A a b‖ ^ 2) * (∑ b, ‖v b‖ ^ 2) := Finset.sum_mul_sq_le_sq_mul_sq _ _ _

theorem sb_ballRatio_nonneg {r : ℕ} (hr : 0 < r) : 0 ≤ ballRatio r := by
  have h1 : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have h7 : 1 / (7 * (r : ℝ)) ≤ 1 / 7 :=
    one_div_le_one_div_of_le (by norm_num) (by linarith)
  have hx : 0 < 1 / (7 * (r : ℝ)) := by positivity
  unfold ballRatio
  apply div_nonneg <;> linarith

theorem sb_ballRatio_le {r : ℕ} (hr : 0 < r) : ballRatio r ≤ Real.exp (1 / (3 * (r : ℝ))) := by
  have h1 : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have h7 : 1 / (7 * (r : ℝ)) ≤ 1 / 7 :=
    one_div_le_one_div_of_le (by norm_num) (by linarith)
  have hx : 0 < 1 / (7 * (r : ℝ)) := by positivity
  have he : 1 / (3 * (r : ℝ)) = 7 * (1 / (7 * (r : ℝ))) / 3 := by
    field_simp
    try ring

  have key : ballRatio r ≤ 7 * (1 / (7 * (r : ℝ))) / 3 + 1 := by
    unfold ballRatio
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  rw [he]
  exact key.trans (Real.add_one_le_exp _)

theorem sb_exp_third_lt_two : Real.exp (1 / 3) < 2 := by
  calc Real.exp (1 / 3) < Real.exp (Real.log 2) :=
        Real.exp_lt_exp.mpr (by have := Real.log_two_gt_d9; linarith)
    _ = 2 := Real.exp_log (by norm_num)

end ReciprocityTheory.MultiplicativeHeights
