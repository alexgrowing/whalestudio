import Formalism.SharpRestriction.GrowthBounds.FockGramWindow.PhiPair

noncomputable section

namespace Formalism.MainNotions.G.GramWindowAlt

open Polynomial Finset Formalism.GM

section
variable (K : Type) [Field K] [CharZero K]

theorem binK_natDegree (k : ℕ) : (binK K k).natDegree = k := by
  unfold binK
  have h : ((k.factorial : K))⁻¹ ≠ 0 := inv_ne_zero (by exact_mod_cast k.factorial_ne_zero)
  rw [natDegree_C_mul h, descPochhammer_natDegree]

theorem binK_coeff_top (k : ℕ) : (binK K k).coeff k = ((k.factorial : K))⁻¹ := by
  unfold binK
  rw [coeff_C_mul]
  have h := (monic_descPochhammer K k).coeff_natDegree
  rw [descPochhammer_natDegree] at h
  rw [h, mul_one]

theorem binMat_natDegree_le {n : ℕ} (J : ℕ) (c : Fin n → Fin n → ℕ → K) (a b : Fin n) :
    (binMatK K J c a b).natDegree ≤ J := by
  unfold binMatK
  refine natDegree_sum_le_of_forall_le _ _ fun k hk => ?_
  refine (natDegree_C_mul_le _ _).trans ?_
  rw [binK_natDegree]
  simp only [mem_range] at hk; omega

theorem binMat_coeff_top {n : ℕ} (J : ℕ) (c : Fin n → Fin n → ℕ → K) (a b : Fin n) :
    (binMatK K J c a b).coeff J = c a b J * ((J.factorial : K))⁻¹ := by
  unfold binMatK
  rw [finsetSum_coeff, Finset.sum_eq_single J]
  · rw [coeff_C_mul, binK_coeff_top]
  · intro k hk hne
    rw [coeff_C_mul, coeff_eq_zero_of_natDegree_lt, mul_zero]
    rw [binK_natDegree]
    simp only [mem_range] at hk; omega
  · intro h; simp at h

end

theorem lead_bound (p : ℕ) [hp : Fact p.Prime] (n J : ℕ) (c : Fin n → Fin n → ℕ → ℚ_[p]) (d : Fin n → ℚ_[p])
    (hc : ∀ a b, c a b J = if a = b then d a else 0) (R Λ : ℝ) (hd : ∀ a, d a ≠ 0 ∧ -Real.logb p ‖d a‖ ≤ R)
    (hV : (J : ℝ) / ((p : ℝ) - 1) - padicValNat p J.factorial ≤ Λ) :
    (binMatK ℚ_[p] J c).det ≠ 0 ∧
      -Real.logb p ‖(binMatK ℚ_[p] J c).det.leadingCoeff‖ +
        ((binMatK ℚ_[p] J c).det.natDegree : ℝ) / ((p : ℝ) - 1) ≤ (n : ℝ) * (R + Λ) := by
  have hJ0 : ((J.factorial : ℚ_[p])) ≠ 0 := by exact_mod_cast J.factorial_ne_zero
  obtain ⟨h1, h2⟩ := Formalism.CountingSumsFrames.Top.detLeadDiag ℚ_[p] n J (binMatK ℚ_[p] J c) (fun a => d a * ((J.factorial : ℚ_[p]))⁻¹)
    (binMat_natDegree_le ℚ_[p] J c) (fun a b => by
      rw [binMat_coeff_top, hc]; split_ifs <;> simp)
  have hne : ∏ a, d a * ((J.factorial : ℚ_[p]))⁻¹ ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun a _ => mul_ne_zero (hd a).1 (inv_ne_zero hJ0)
  have hdet : (binMatK ℚ_[p] J c).det ≠ 0 := by
    intro h0; rw [h0, coeff_zero] at h2; exact hne h2.symm
  have hdeg : (binMatK ℚ_[p] J c).det.natDegree = n * J :=
    le_antisymm h1 (le_natDegree_of_ne_zero (by rw [h2]; exact hne))
  have hlead : (binMatK ℚ_[p] J c).det.leadingCoeff = ∏ a, d a * ((J.factorial : ℚ_[p]))⁻¹ := by
    rw [leadingCoeff, hdeg, h2]
  refine ⟨hdet, ?_⟩
  rw [hlead, hdeg, norm_prod, Real.logb_prod _ _ (fun a _ => norm_ne_zero_iff.2 (mul_ne_zero (hd a).1 (inv_ne_zero hJ0)))]
  have hterm : ∀ a, Real.logb p ‖d a * ((J.factorial : ℚ_[p]))⁻¹‖ =
      Real.logb p ‖d a‖ + padicValNat p J.factorial := by
    intro a
    rw [norm_mul, norm_inv, Real.logb_mul (norm_ne_zero_iff.2 (hd a).1) (inv_ne_zero (norm_ne_zero_iff.2 hJ0)),
      Real.logb_inv, Formalism.GM.MeanGammaLemmas.neglog_nat p _ J.factorial_ne_zero]
  simp_rw [hterm]
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hs : -∑ a, Real.logb p ‖d a‖ ≤ n * R := by
    rw [← Finset.sum_neg_distrib]
    calc ∑ a, -Real.logb p ‖d a‖ ≤ ∑ _a : Fin n, R := Finset.sum_le_sum fun a _ => (hd a).2
      _ = n * R := by simp
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have := mul_le_mul_of_nonneg_left hV hn
  push_cast
  have e1 : (n : ℝ) * J / ((p : ℝ) - 1) = n * ((J : ℝ) / ((p : ℝ) - 1)) := by ring
  rw [e1]
  nlinarith

end Formalism.MainNotions.G.GramWindowAlt

end
