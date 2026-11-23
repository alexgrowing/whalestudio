import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.JFrameA

noncomputable section

open Matrix
open scoped ComplexConjugate

namespace ReciprocityTheory.ChartRestriction.DS.Mult1

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

theorem stFrame : StFrame := by
  intro k r z _hk hz hT
  set T := Tz k r z with hTdef
  set s : ℝ := (Real.sqrt T)⁻¹ with hs

  have hTeq : T = ‖z (wI k r (Fin.last k))‖ ^ 2 - ∑ l : Fin k, ‖z (wI k r l.castSucc)‖ ^ 2 := by
    have h := frame_herm k r z hz
    simp only [frameMat_star_mul_self] at h
    rw [hTdef, Tz, h, ← Complex.ofReal_sum, ← Complex.ofReal_sub, Complex.ofReal_re]
    ring
  have hsT : s ^ 2 * T = 1 := by
    rw [hs, inv_pow, Real.sq_sqrt hT.le, inv_mul_cancel₀ hT.ne']
  have hs0 : 0 ≤ s := by rw [hs]; positivity
  refine ⟨frameMat k (fun j => (s : ℂ) * z (wI k r j)), ?_⟩
  unfold IsZFrame
  constructor
  · apply frameMat_unitary
    simp only [frameMat_star_mul_self]
    have key : ∑ l : Fin k, ‖(s : ℂ) * z (wI k r l.castSucc)‖ ^ 2 =
        ‖(s : ℂ) * z (wI k r (Fin.last k))‖ ^ 2 - 1 := by
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs0, mul_pow,
        ← Finset.mul_sum]
      linear_combination (-1 : ℝ) * hsT + s ^ 2 * hTeq
    rw [← Complex.ofReal_sum, key, Complex.ofReal_sub, Complex.ofReal_one]
  · have hlast : (wI k r (Fin.last k)).val = r + k := by simp [frame_wI_val]
    funext i
    simp only [bvec, Matrix.mulVec, dotProduct, Pi.single_apply, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, if_true, Pi.smul_apply, smul_eq_mul]
    unfold embWb
    by_cases hi : r ≤ i.val ∧ i.val ≤ r + k
    · rw [dif_pos ⟨hi, by omega, by omega⟩]
      rw [show ∀ p, (⟨(wI k r (Fin.last k)).val - r, p⟩ : Fin (k + 1)) = Fin.last k from
        fun p => Fin.ext (by simp only [Fin.val_last]; omega)]
      rw [frameMat_col]
      rw [show ∀ p, wI k r (⟨i.val - r, p⟩ : Fin (k + 1)) = i from
        fun p => Fin.ext (by rw [frame_wI_val]; show r + (i.val - r) = i.val; omega)]
    · rw [dif_neg (fun h => hi h.1)]
      have hne : ¬ (i = wI k r (Fin.last k) ∧ ¬ (r ≤ i.val ∧ i.val ≤ r + k)) := by
        rintro ⟨rfl, h⟩
        exact h ⟨by omega, by omega⟩
      rw [if_neg hne, hz i (by omega), mul_zero]

end ReciprocityTheory.ChartRestriction.DS.Mult1
