import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ResidueLatticeCount.UnitPreserving

open NumberField NumberField.mixedEmbedding NumberField.InfinitePlace MeasureTheory
open scoped ENNReal Classical

noncomputable section

namespace PI.Residue

theorem real_hit_ineq (A N s : ℝ) (hA : 0 < A) (hN : 0 < N) (hs : 1 < s) (h : N ≤ 2 * A) :
    A / N ≤ A * (2 * A) ^ (s - 1) * N ^ (-s) := by
  have hP : 0 < N ^ (s - 1) := Real.rpow_pos_of_pos hN _
  have hPB : N ^ (s - 1) ≤ (2 * A) ^ (s - 1) := Real.rpow_le_rpow hN.le h (by linarith)
  have hNs : N ^ s = N ^ (s - 1) * N := by
    rw [← Real.rpow_add_one hN.ne']; ring_nf
  rw [Real.rpow_neg hN.le, hNs]
  have e : A * (2 * A) ^ (s - 1) * (N ^ (s - 1) * N)⁻¹ = A / N * ((2 * A) ^ (s - 1) / N ^ (s - 1)) := by
    field_simp
  rw [e]
  exact le_mul_of_one_le_right (by positivity) ((one_le_div hP).2 hPB)

theorem hitBound_of (hbox : BoxVolume) : HitBound := by
  intro K _ _ ρ s x hρ hs hx
  have hpos : ∀ w, 0 < normAtPlace w x := fun w =>
    lt_of_le_of_ne (normAtPlace_nonneg w x) (Ne.symm (mixedEmbedding.norm_ne_zero_iff.1 hx.ne' w))
  have hhit : hit K ρ x = box K (fun w => ρ / normAtPlace w x) := by
    ext y
    simp only [hit, box, Set.mem_ofPred_eq]
    exact forall_congr' fun w => (lt_div_iff₀ (hpos w)).symm
  have hprod : ∏ w, (ρ / normAtPlace w x) ^ mult w
      = ρ ^ Module.finrank ℚ K / mixedEmbedding.norm x := by
    simp_rw [div_pow]
    rw [Finset.prod_div_distrib, Finset.prod_pow_eq_pow_sum, sum_mult_eq, mixedEmbedding.norm_apply]
  have hA : 0 < ρ ^ Module.finrank ℚ K := by positivity
  by_cases h : mixedEmbedding.norm x ≤ 2 * ρ ^ Module.finrank ℚ K
  · calc volume ({y | 1 / 2 < mixedEmbedding.norm y} ∩ hit K ρ x) ≤ volume (hit K ρ x) :=
          measure_mono Set.inter_subset_right
      _ = vfac K * ENNReal.ofReal (ρ ^ Module.finrank ℚ K / mixedEmbedding.norm x) := by
          rw [hhit, hbox K _ (fun w => div_pos hρ (hpos w)), hprod]
      _ ≤ _ := by
          gcongr
          exact real_hit_ineq _ _ s hA hx hs h
  · have hempty : {y | 1 / 2 < mixedEmbedding.norm y} ∩ hit K ρ x = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      rintro y ⟨hy1, hy2⟩
      rw [hhit] at hy2
      have hle : mixedEmbedding.norm y ≤ ρ ^ Module.finrank ℚ K / mixedEmbedding.norm x := by
        rw [← hprod, mixedEmbedding.norm_apply]
        exact Finset.prod_le_prod (fun w _ => pow_nonneg (normAtPlace_nonneg w y) _)
          (fun w _ => pow_le_pow_left₀ (normAtPlace_nonneg w y) (hy2 w).le _)
      have hhalf : ρ ^ Module.finrank ℚ K / mixedEmbedding.norm x ≤ 1 / 2 := by
        rw [div_le_iff₀ hx]
        rw [not_le] at h
        linarith
      have hy1' : 1 / 2 < mixedEmbedding.norm y := hy1
      linarith
    rw [hempty, measure_empty]
    exact zero_le

end PI.Residue
