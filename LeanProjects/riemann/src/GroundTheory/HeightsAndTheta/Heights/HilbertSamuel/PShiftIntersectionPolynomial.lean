import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsShiftIntersectionPolynomial
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PZCombLimit
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
open GroundTheory.Heights₂.Heights.Inter (famExt famExt_apply)

noncomputable section

namespace ShiftIntersectionPolynomial

theorem prod_weights {n : ℕ} (q : ℝ) (s : Fin n → Fin 2) :
    ∏ j, (![q, 1] : Fin 2 → ℝ) (s j) = q ^ (Finset.univ.filter fun j => s j = 0).card := by
  have h : ∀ j, (![q, 1] : Fin 2 → ℝ) (s j) = if s j = 0 then q else 1 := by
    intro j
    rcases Fin.exists_fin_two.mp ⟨s j, rfl⟩ with h | h <;> rw [h] <;> simp
  simp only [h, Finset.prod_ite, Finset.prod_const, one_pow, mul_one]

theorem proof : ShiftIntersectionPolynomial.Statement := by
  intro K _ ι _ II P n A B hII hP hA hB
  have hI : IsIntersectionFamily (II K ι) := hII K ι
  set e : Fin 2 → HermLine ι := ![A, B] with he_def
  have he : ∀ i, IsSmoothHerm (e i) := by
    intro i
    rcases Fin.exists_fin_two.mp ⟨i, rfl⟩ with h | h <;> rw [h] <;> simpa [e]
  refine ⟨∑ s : Fin n → Fin 2, Polynomial.C (II K ι P n (e ∘ s)) *
      Polynomial.X ^ (Finset.univ.filter fun j => s j = 0).card, ?_, ?_, ?_⟩
  · refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun s _ => ?_
    refine (Polynomial.natDegree_C_mul_X_pow_le _ _).trans ?_
    exact (Finset.card_filter_le _ _).trans (by simp)
  · rw [Polynomial.finsetSum_coeff, Finset.sum_eq_single (fun _ => 0)]
    · rw [Polynomial.coeff_C_mul_X_pow]
      have hc : (Finset.univ.filter fun j : Fin n => (fun _ : Fin n => (0 : Fin 2)) j = 0).card = n := by simp
      rw [if_pos hc.symm]
      rfl
    · intro s _ hs
      rw [Polynomial.coeff_C_mul_X_pow, if_neg]
      intro hc
      apply hs
      have hu : (Finset.univ.filter fun j => s j = 0) = Finset.univ :=
        Finset.eq_univ_of_card _ (by rw [← hc, Fintype.card_fin])
      funext j
      have := Finset.filter_eq_self.mp hu j (Finset.mem_univ j)
      exact this
    · intro h
      exact absurd (Finset.mem_univ _) h
  · intro q
    set Z := HermLine.zcomb A B (q : ℤ) 1 with hZ_def
    have hZ : IsSmoothHerm Z := ZCombLimit.isSmoothHerm_zcomb_int hA hB _ _
    have hposition : ∀ (L : Fin n → HermLine ι) (a : Fin n), (∀ j, IsSmoothHerm (L j)) →
        II K ι P n (Function.update L a Z) =
          (![(q : ℝ), 1] : Fin 2 → ℝ) 0 * II K ι P n (Function.update L a (e 0)) +
            (![(q : ℝ), 1] : Fin 2 → ℝ) 1 * II K ι P n (Function.update L a (e 1)) := by
      intro L a hL
      cases n with
      | zero => exact a.elim0
      | succ m =>
        have h := ZCombLimit.fam_update_zcomb_int hI hP L hL a hA hB (q : ℤ) 1
        simp only [Int.cast_natCast, Int.cast_one, one_mul] at h
        simpa [e] using h
    have key := ZCombLimit.eq_famExt_of_position (J := II K ι) (P := P) IsSmoothHerm e Z ![(q : ℝ), 1] he hZ hposition
      Finset.univ (fun _ => 0)
    simp only [Finset.mem_univ, if_true] at key
    rw [key, famExt_apply, Polynomial.eval_finsetSum]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [prod_weights, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]

end ShiftIntersectionPolynomial

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
