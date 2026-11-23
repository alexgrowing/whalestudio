import CompanionTheory.RealGroups.FormalDegrees.ArchimedeanFormalDegrees.HlamStable
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.PhiFacts
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.ExpInPPosDef
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.FiPmatEqFiOneSmulPmat

noncomputable section

open Finset Matrix
open scoped ComplexOrder

namespace CompanionTheory.RgFd

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

theorem inP_entry_zero {ε : Fin n → Bool} {X : Matrix (Fin n) (Fin n) ℂ} (hX : inP ε X) {a b : Fin n}
    (h : ε a = ε b) : X a b = 0 := by
  have h1 := congrFun (congrFun hX.2 a) b
  simp only [Matrix.mul_apply, Matrix.neg_apply, Jm, Matrix.diagonal_apply, mul_ite, mul_zero, ite_mul, zero_mul,
    Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true] at h1
  rw [h] at h1
  split_ifs at h1 with hb
  · have : (2 : ℂ) * X a b = 0 := by linear_combination h1
    simpa using this
  · have : (2 : ℂ) * X a b = 0 := by linear_combination -h1
    simpa using this

theorem exists_pmat {ε : Fin n → Bool} {X : Matrix (Fin n) (Fin n) ℂ} (hX : inP ε X) :
    ∃ z : PCoord ε → ℂ, pmat z = X := by
  refine ⟨fun ab => X ab.1.1 ab.1.2, ?_⟩
  have hH := isHermitian_of_mem_noncompactPart' hX
  ext a b
  simp only [pmat]
  by_cases h1 : b < a ∧ ε a ≠ ε b
  · rw [dif_pos h1]
  · rw [dif_neg h1]
    by_cases h2 : a < b ∧ ε b ≠ ε a
    · rw [dif_pos h2]
      have := congrFun (congrFun hH a) b
      simp only [Matrix.conjTranspose_apply] at this
      exact this
    · rw [dif_neg h2]
      by_cases he : ε a = ε b
      · exact (inP_entry_zero hX he).symm
      · have hab : a = b := by
          by_contra hne
          rcases lt_or_gt_of_ne hne with h | h
          · exact h2 ⟨h, Ne.symm he⟩
          · exact h1 ⟨h, he⟩
        subst hab
        exact absurd rfl he

theorem one_le_lead_exp {ε : Fin n → Bool} {X : Matrix (Fin n) (Fin n) ℂ} (hX : inP ε X) (i : ℕ) (hi : i ≤ n) :
    1 ≤ (lead i (NormedSpace.exp X)).re := by
  obtain ⟨z, rfl⟩ := exists_pmat hX
  have h0 := fi_nonneg z i
  have hp := (lead_posDef (exp_noncompactPart_posDef hX) i hi).1
  unfold Fi at h0
  have e : Del (NormedSpace.exp (pmat z)) i = lead i (NormedSpace.exp (pmat z)) := rfl
  rw [e] at h0
  exact (Real.log_nonneg_iff hp).1 h0

theorem dz_sub_muNext_nonneg (i : Fin n) : 0 ≤ Dz n i - muNext (Dz n) i := by
  unfold muNext Dz
  split_ifs with h
  · simp only
    omega
  · have : (i : ℕ) + 1 = n := by omega
    omega

theorem phiLe : PhiLe := by
  intro n ε X hX k
  obtain ⟨hP, hE⟩ := inP_conj k⁻¹ hX
  rw [inv_inv] at hP hE
  unfold phiK
  rw [← hE]
  set Y := toMK k⁻¹ * X * toMK k with hY
  have hpd := exp_noncompactPart_posDef hP
  have hr : ∀ i : Fin n, lead ((i : ℕ) + 1) (NormedSpace.exp Y) = ((lead ((i : ℕ) + 1) (NormedSpace.exp Y)).re : ℂ) :=
    fun i => Complex.ext (by simp) (by simp [(lead_posDef hpd _ i.isLt).2])
  have hphi : PhiM (Dz n) (NormedSpace.exp Y) =
      ((∏ i : Fin n, (lead ((i : ℕ) + 1) (NormedSpace.exp Y)).re ^ (-(Dz n i - muNext (Dz n) i)) : ℝ) : ℂ) := by
    unfold PhiM
    rw [Complex.ofReal_prod]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [hr i, Complex.ofReal_zpow, Complex.ofReal_re]
  rw [hphi, Complex.ofReal_re]
  refine Finset.prod_le_one (fun i _ => zpow_nonneg (zero_le_one.trans (one_le_lead_exp hP _ i.isLt)) _) fun i _ => ?_
  exact zpow_le_one_of_nonpos₀ (one_le_lead_exp hP _ i.isLt) (neg_nonpos.2 (dz_sub_muNext_nonneg i))

end CompanionTheory.RgFd
