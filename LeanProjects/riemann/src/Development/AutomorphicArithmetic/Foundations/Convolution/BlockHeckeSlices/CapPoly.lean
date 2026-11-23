import Mathlib
import GroundTheory.IdeleRoots.ConstantFrames.GaugeExistence.QdetSub

open Polynomial GroundTheory.BlockD.FourierDecayAlt.GaugeExists

theorem UpperTheory.ConvolutionTheory.BW.exists_capPoly {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ} (F : Fin n → Fin n → A) (ℓ : A →ₗ[ℂ] ℂ) :
    ∃ p : ℂ[X], p.natDegree ≤ n ∧ p.coeff n = ℓ 1 ∧ (∀ m, m + 1 = n → p.coeff m = ℓ (∑ i, F i i)) ∧
      ∀ u, p.eval u = ℓ (Formalism.REAL.qdet F (u + ((n : ℂ) - 1) / 2)) := by
  obtain ⟨-, htop, hsub⟩ := prod_linear n fun k => F k k - algebraMap ℂ A ((k : ℕ) : ℂ)
  have hN : (qdetPoly F).coeff n = 1 := by rw [coeff_qdetPoly_top F n (by omega), htop]
  refine ⟨∑ j ∈ Finset.range (n + 1), C (ℓ ((qdetPoly F).coeff j)) * (X + C (((n : ℂ) - 1) / 2)) ^ j, ?_, ?_, ?_, ?_⟩
  · refine natDegree_sum_le_of_forall_le _ _ fun j hj => (natDegree_C_mul_le _ _).trans ?_
    rw [natDegree_pow_X_add_C]
    exact Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
  · rw [finsetSum_coeff, Finset.sum_range_succ, Finset.sum_eq_zero, hN]
    · simp [coeff_X_add_C_pow]
    · intro j hj
      rw [coeff_C_mul, coeff_X_add_C_pow, Nat.choose_eq_zero_of_lt (Finset.mem_range.1 hj)]
      simp
  · rintro m rfl
    have h1 : (qdetPoly F).coeff m = ∑ i, F i i - (((m + 1 : ℕ) : ℂ) * (((m + 1 : ℕ) : ℂ) - 1) / 2) • 1 := by
      rw [coeff_qdetPoly_top F m le_rfl, hsub m rfl, Finset.sum_sub_distrib, ← map_sum, sum_fin_cast,
        Algebra.algebraMap_eq_smul_one]
    rw [finsetSum_coeff, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_eq_zero, hN, h1]
    · rw [coeff_C_mul, coeff_C_mul]
      simp only [coeff_X_add_C_pow, map_sub, map_smul, smul_eq_mul, Nat.sub_self, Nat.choose_self,
        Nat.add_sub_cancel_left, Nat.choose_succ_self_right]
      push_cast
      ring
    · intro j hj
      rw [coeff_C_mul, coeff_X_add_C_pow, Nat.choose_eq_zero_of_lt (Finset.mem_range.1 hj)]
      simp
  · intro u
    rw [← evU_qdetPoly, evU_apply, eval₂_eq_sum_range' _ (Nat.lt_succ_of_le (natDegree_qdetPoly_le F)), map_sum,
      eval_finset_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [RingHom.id_apply, ← map_pow, ← Algebra.commutes, ← Algebra.smul_def, map_smul]
    simp [mul_comm]
