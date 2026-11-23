import Mathlib
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.ExistsIdealInClassOfNormLeSqrtDiscr

open NumberField Finset

namespace GlobalTheory.IdealBoundedNorm

theorem finite_setOf_absNorm_le (K : Type) [Field K] [NumberField K] (Y : ℝ) :
    {I : Ideal (𝓞 K) | I ≠ ⊥ ∧ (Ideal.absNorm I : ℝ) ≤ Y}.Finite := by
  refine ((Finset.range (⌊Y⌋₊ + 1) : Set ℕ).toFinite.biUnion
    fun n _ => Ideal.finite_setOfPred_absNorm_eq (S := 𝓞 K) n).subset ?_
  rintro I ⟨-, hI⟩
  refine Set.mem_biUnion (x := Ideal.absNorm I) ?_ rfl
  simpa [Nat.lt_succ_iff] using Nat.le_floor hI

theorem ncard_absNorm_le_pow_pred (K : Type) [Field K] [NumberField K] (Y : ℝ) (hY : 1 ≤ Y) :
    ((({I : Ideal (𝓞 K) | I ≠ ⊥ ∧ (Ideal.absNorm I : ℝ) ≤ Y}).ncard : ℕ) : ℝ)
      ≤ Y * (1 + Real.log Y) ^ (Module.finrank ℚ K - 1) := by
  classical
  have hS := finite_setOf_absNorm_le K Y

  have key : ({I : Ideal (𝓞 K) | I ≠ ⊥ ∧ (Ideal.absNorm I : ℝ) ≤ Y}).ncard
      ≤ ∑ n ∈ Ioc 0 ⌊Y⌋₊, (ArithmeticFunction.zeta ^ Module.finrank ℚ K : ArithmeticFunction ℕ) n := by
    rw [← hS.coe_toFinset, Set.ncard_coe_finset]
    rw [Finset.card_eq_sum_card_fiberwise (f := fun I => Ideal.absNorm I) (t := Ioc 0 ⌊Y⌋₊) ?_]
    · refine Finset.sum_le_sum fun n hn => ?_
      refine le_trans ?_ (GlobalTheory.ncard_ideal_absNorm_eq_le K (Finset.mem_Ioc.1 hn).1.ne')
      rw [← Set.ncard_coe_finset]
      refine Set.ncard_le_ncard ?_ (Ideal.finite_setOfPred_absNorm_eq n)
      intro I hI
      simp only [Finset.coe_filter, Set.mem_setOf_eq] at hI ⊢
      exact hI.2
    · intro I hI
      simp only [Set.Finite.coe_toFinset, Set.mem_setOf_eq] at hI
      simp only [Finset.coe_Ioc, Set.mem_Ioc]
      exact ⟨Nat.pos_of_ne_zero (mt Ideal.absNorm_eq_zero_iff.1 hI.1), Nat.le_floor hI.2⟩
  have hm : 1 ≤ Module.finrank ℚ K := Module.finrank_pos
  calc ((({I : Ideal (𝓞 K) | I ≠ ⊥ ∧ (Ideal.absNorm I : ℝ) ≤ Y}).ncard : ℕ) : ℝ)
      ≤ ((∑ n ∈ Ioc 0 ⌊Y⌋₊,
          (ArithmeticFunction.zeta ^ Module.finrank ℚ K : ArithmeticFunction ℕ) n : ℕ) : ℝ) := by
        exact_mod_cast key
    _ ≤ Y * (1 + Real.log Y) ^ (Module.finrank ℚ K - 1) := GlobalTheory.sum_zeta_pow_le hm hY

theorem ncard_absNorm_le : ∀ (K : Type) [Field K] [NumberField K] (Y : ℝ), 1 ≤ Y →
    ((({I : Ideal (𝓞 K) | I ≠ ⊥ ∧ (Ideal.absNorm I : ℝ) ≤ Y}).ncard : ℕ) : ℝ)
      ≤ Y * (1 + Real.log Y) ^ Module.finrank ℚ K := by
  intro K _ _ Y hY
  refine (ncard_absNorm_le_pow_pred K Y hY).trans ?_
  have hl : 1 ≤ 1 + Real.log Y := by linarith [Real.log_nonneg hY]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hl (Nat.sub_le _ _)) (by linarith)

end GlobalTheory.IdealBoundedNorm
