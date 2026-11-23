import Formalism.GradedWeylDivisibility.StatementB
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.LRowdivLemmas

open MvPolynomial

noncomputable section

namespace Formalism.GradedWeylDivisibility

def lgraded_wa {r n : ℕ} (a : Fin r) : Fin r × Fin n → ℕ := fun v => if v.1 = a then 1 else 0

theorem lgraded_rowGen_X {r n : ℕ} (a : Fin r) (v : Fin r × Fin n) :
    rowGen ℚ a a (X v) = Polynomial.C (X v) * (1 + Polynomial.X) ^ (lgraded_wa (n := n) a v) := by
  obtain ⟨b, j⟩ := v
  simp only [rowGen, aeval_X, lgraded_wa]
  by_cases h : b = a
  · subst h
    rw [if_pos rfl, if_pos rfl, pow_one]
    ring
  · simp [h]

theorem lgraded_rowGen_C {r n : ℕ} (a : Fin r) (c : ℚ) :
    rowGen ℚ a a (C c : MvPolynomial (Fin r × Fin n) ℚ) = Polynomial.C (C c) := by
  rw [rowGen, aeval_C, Polynomial.algebraMap_apply, MvPolynomial.algebraMap_eq]

theorem lgraded_rowGen_monomial {r n : ℕ} (a : Fin r) (m : Fin r × Fin n →₀ ℕ) (c : ℚ) :
    rowGen ℚ a a (monomial m c) =
      Polynomial.C (monomial m c) * (1 + Polynomial.X) ^ (Finsupp.weight (lgraded_wa a) m) := by
  induction m using Finsupp.induction
  next => rw [monomial_zero', lgraded_rowGen_C]; simp
  next v k m _ _ ih =>
    have hw : Finsupp.weight (lgraded_wa a) (Finsupp.single v k) = k * lgraded_wa a v := by
      simp [Finsupp.weight_apply, Finsupp.sum_single_index]
    rw [add_comm, monomial_add_single, map_mul, ih, map_pow, lgraded_rowGen_X, map_add, map_mul,
      map_pow, hw, mul_pow, ← pow_mul, pow_add, mul_comm (lgraded_wa a v) k]
    ring

theorem lgraded_euler_monomial {r n : ℕ} (a : Fin r) (m : Fin r × Fin n →₀ ℕ) (c : ℚ) :
    rowDiv ℚ a a 1 (monomial m c) = ((Finsupp.weight (lgraded_wa a) m : ℕ) : ℚ) • monomial m c := by
  rw [rowDiv, lgraded_rowGen_monomial, Polynomial.coeff_C_mul, Polynomial.coeff_one_add_X_pow,
    Nat.choose_one_right, Nat.cast_smul_eq_nsmul, nsmul_eq_mul, mul_comm]

theorem lgraded_coeff_euler {r n : ℕ} (a : Fin r) (f : MvPolynomial (Fin r × Fin n) ℚ)
    (m : Fin r × Fin n →₀ ℕ) :
    coeff m (rowDiv ℚ a a 1 f) = ((Finsupp.weight (lgraded_wa a) m : ℕ) : ℚ) * coeff m f := by
  induction f using MvPolynomial.induction_on'
  next m' c' =>
    rw [lgraded_euler_monomial, coeff_smul, coeff_monomial, smul_eq_mul]
    split_ifs with h
    · rw [h]
    · simp
  next p q hp hq =>
    have hpq : rowDiv ℚ a a 1 (p + q) = rowDiv ℚ a a 1 p + rowDiv ℚ a a 1 q := by
      simp only [rowDiv, map_add, Polynomial.coeff_add]
    rw [hpq, coeff_add, coeff_add, hp, hq, mul_add]

theorem lgraded_weight_rowW {r n : ℕ} (m : Fin r × Fin n →₀ ℕ) (a : Fin r) :
    Finsupp.weight (rowW r n) m a = Finsupp.weight (lgraded_wa a) m := by
  simp only [Finsupp.weight_apply, rowW, lgraded_wa]
  simp only [Finsupp.sum, Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro v _
  simp only [Pi.smul_apply, Pi.single_apply, smul_eq_mul]
  by_cases h : v.1 = a
  · simp [h]
  · simp [h, Ne.symm h]

private lemma exists_mem_coeff_eq_prod_weight_sub_mul_coeff {r n : ℕ} (M : Submodule ℚ (MvPolynomial (Fin r × Fin n) ℚ))
    (hM : RowDivClosed M) (a : Fin r) (T : Finset ℕ) : ∀ g ∈ M, ∃ h ∈ M, ∀ m, coeff m h =
      (∏ s ∈ T, (((Finsupp.weight (lgraded_wa a) m : ℕ) : ℚ) - (s : ℚ))) * coeff m g := by
  classical
  induction T using Finset.induction_on
  next => intro g hg; exact ⟨g, hg, fun m => by simp⟩
  next s T hs ih =>
    intro g hg
    obtain ⟨h, hh, hc⟩ := ih g hg
    refine ⟨rowDiv ℚ a a 1 h - (s : ℚ) • h, M.sub_mem (hM a a 1 h hh) (M.smul_mem _ hh), fun m => ?_⟩
    rw [coeff_sub, coeff_smul, lgraded_coeff_euler, hc, Finset.prod_insert hs, smul_eq_mul]
    ring

theorem lgraded_sep {r n : ℕ} (M : Submodule ℚ (MvPolynomial (Fin r × Fin n) ℚ)) (hM : RowDivClosed M)
    (a : Fin r) (V : Finset ℕ) :
    ∀ f ∈ M, (∀ m ∈ f.support, Finsupp.weight (lgraded_wa a) m ∈ V) →
      ∀ t, weightedHomogeneousComponent (lgraded_wa a) t f ∈ M := by
  intro f hf hV t
  classical
  obtain ⟨h, hh, hc⟩ := exists_mem_coeff_eq_prod_weight_sub_mul_coeff M hM a (V.erase t) f hf
  have key : weightedHomogeneousComponent (lgraded_wa a) t f =
      (∏ s ∈ V.erase t, ((t : ℚ) - (s : ℚ)))⁻¹ • h := by
    ext m
    rw [coeff_weightedHomogeneousComponent, coeff_smul, hc, smul_eq_mul]
    by_cases hm : m ∈ f.support
    · have hmV := hV m hm
      split_ifs with hw
      · rw [hw]
        have hne : (∏ s ∈ V.erase t, ((t : ℚ) - (s : ℚ))) ≠ 0 := by
          rw [Finset.prod_ne_zero_iff]
          intro s hs
          have hst := (Finset.mem_erase.1 hs).1
          exact sub_ne_zero.2 (by exact_mod_cast hst.symm)
        rw [← mul_assoc, inv_mul_cancel₀ hne, one_mul]
      · have hmem : Finsupp.weight (lgraded_wa a) m ∈ V.erase t := Finset.mem_erase.2 ⟨hw, hmV⟩
        have h0 : ∏ s ∈ V.erase t,
            (((Finsupp.weight (lgraded_wa a) m : ℕ) : ℚ) - (s : ℚ)) = 0 :=
          Finset.prod_eq_zero hmem (sub_self _)
        rw [h0]
        simp
    · rw [mem_support_iff, not_not] at hm
      simp [hm]
  rw [key]
  exact M.smul_mem _ hh

theorem lgraded_multi {r n : ℕ} (M : Submodule ℚ (MvPolynomial (Fin r × Fin n) ℚ)) (hM : RowDivClosed M)
    (μ : Fin r → ℕ) (A : Finset (Fin r)) :
    ∀ f ∈ M, ∃ h ∈ M, ∀ m, coeff m h =
      if (∀ a ∈ A, Finsupp.weight (lgraded_wa a) m = μ a) then coeff m f else 0 := by
  classical
  induction A using Finset.induction_on
  next => intro f hf; exact ⟨f, hf, fun m => by simp⟩
  next b A hb ih =>
    intro f hf
    obtain ⟨h, hh, hc⟩ := ih f hf
    refine ⟨weightedHomogeneousComponent (lgraded_wa b) (μ b) h,
      lgraded_sep M hM b (h.support.image (Finsupp.weight (lgraded_wa b))) h hh
        (fun m hm => Finset.mem_image_of_mem _ hm) (μ b), fun m => ?_⟩
    rw [coeff_weightedHomogeneousComponent, hc]
    simp only [Finset.mem_insert, forall_eq_or_imp]
    by_cases h1 : Finsupp.weight (lgraded_wa b) m = μ b <;> simp [h1]

end Formalism.GradedWeylDivisibility
