import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PolynomialDifferentialWords.KappaRight

open MvPolynomial Finsupp

noncomputable section

namespace PI.OpWords

variable {K : Type} [Field K] {k d : ℕ}

lemma mapDomain_inl_add_inr (u g : Fin k →₀ ℕ) :
    u.mapDomain Sum.inl + g.mapDomain Sum.inr = Finsupp.sumElim u g := by
  ext v
  rcases v with i | i
  · simp [Finsupp.mapDomain_apply Sum.inl_injective, Finsupp.mapDomain_notin_range]
  · simp [Finsupp.mapDomain_apply Sum.inr_injective, Finsupp.mapDomain_notin_range]

lemma sumElim_inj {u g u' g' : Fin k →₀ ℕ} :
    Finsupp.sumElim u g = Finsupp.sumElim u' g' ↔ u = u' ∧ g = g' := by
  constructor
  · intro h
    constructor
    · ext i
      have h1 := congrArg (fun f => f (Sum.inl i)) h
      simpa using h1
    · ext i
      have h1 := congrArg (fun f => f (Sum.inr i)) h
      simpa using h1
  · rintro ⟨rfl, rfl⟩
    rfl

lemma exists_sumElim (n : Fin k ⊕ Fin k →₀ ℕ) : ∃ m g : Fin k →₀ ℕ, n = Finsupp.sumElim m g := by
  refine ⟨Finsupp.comapDomain Sum.inl n Sum.inl_injective.injOn,
    Finsupp.comapDomain Sum.inr n Sum.inr_injective.injOn, ?_⟩
  ext v
  rcases v with i | i <;> simp [Finsupp.comapDomain_apply]

lemma pol_ext {P Q : Pol K k}
    (h : ∀ m g : Fin k →₀ ℕ, coeff (Finsupp.sumElim m g) P = coeff (Finsupp.sumElim m g) Q) : P = Q := by
  ext n
  obtain ⟨m, g, rfl⟩ := exists_sumElim n
  exact h m g

lemma sumElim_sub_single_inr (m g : Fin k →₀ ℕ) (b : Fin k) :
    Finsupp.sumElim m g - single (Sum.inr b) 1 = Finsupp.sumElim m (g - single b 1) := by
  ext v
  rcases v with i | i <;> simp [Finsupp.single_apply]

lemma sumElim_add_single_inr (m g : Fin k →₀ ℕ) (b : Fin k) :
    Finsupp.sumElim m g + single (Sum.inr b) 1 = Finsupp.sumElim m (g + single b 1) := by
  ext v
  rcases v with i | i <;> simp [Finsupp.single_apply]

lemma coeff_term (P : MvPolynomial (Fin k) K) (m g g' : Fin k →₀ ℕ) :
    coeff (Finsupp.sumElim m g) (rename Sum.inl P * monomial (g'.mapDomain Sum.inr) (1 : K)) =
      if g' = g then coeff m P else 0 := by
  classical
  induction P using MvPolynomial.induction_on'
  next u c =>
    rw [rename_monomial, monomial_mul, mapDomain_inl_add_inr]
    simp only [coeff_monomial, sumElim_inj, mul_one]
    by_cases h1 : u = m <;> by_cases h2 : g' = g <;> simp [h1, h2]
  next p q hp hq =>
    rw [map_add, add_mul, coeff_add, hp, hq]
    split_ifs <;> simp [coeff_add]

lemma mono_val (g : Fin k →₀ ℕ) :
    (mono K k d g : MvPolynomial (Fin k) K) = if g.degree = d then monomial g 1 else 0 := by
  unfold mono
  split_ifs <;> rfl

lemma mem_antidiag_iff (g : Fin k →₀ ℕ) :
    g ∈ (Finset.univ : Finset (Fin k)).finsuppAntidiag d ↔ g.degree = d := by
  rw [Finset.mem_finsuppAntidiag, Finsupp.degree_eq_sum]
  simp

lemma kappa_apply (A : Module.End K ↥(homogeneousSubmodule (Fin k) K d)) :
    kappa K k d A = ∑ g ∈ (Finset.univ : Finset (Fin k)).finsuppAntidiag d,
      invFact K g • (rename Sum.inl ((A (mono K k d g) : MvPolynomial (Fin k) K)) *
        monomial (g.mapDomain Sum.inr) (1 : K)) := by
  simp [kappa]

lemma coeff_kappa (A : Module.End K ↥(homogeneousSubmodule (Fin k) K d)) (m g : Fin k →₀ ℕ) :
    coeff (Finsupp.sumElim m g) (kappa K k d A) =
      invFact K g * coeff m (A (mono K k d g) : MvPolynomial (Fin k) K) := by
  classical
  rw [kappa_apply, coeff_sum]
  simp only [coeff_smul, coeff_term, smul_eq_mul, mul_ite, mul_zero, Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · rw [mem_antidiag_iff] at h
    have h0 : mono K k d g = 0 := by
      unfold mono
      rw [dif_neg h]
    rw [h0, map_zero]
    simp

lemma degree_of_coeff_ne (F : ↥(homogeneousSubmodule (Fin k) K d)) {m : Fin k →₀ ℕ}
    (h : coeff m (F : MvPolynomial (Fin k) K) ≠ 0) : m.degree = d := by
  have hF := (mem_homogeneousSubmodule d _).1 F.2
  rw [Finsupp.degree_eq_weight_one]
  exact hF h

lemma eq_sum_mono (F : ↥(homogeneousSubmodule (Fin k) K d)) :
    F = ∑ g ∈ (F : MvPolynomial (Fin k) K).support,
      coeff g (F : MvPolynomial (Fin k) K) • mono K k d g := by
  apply Subtype.ext
  rw [Submodule.coe_sum]
  conv_lhs => rw [(F : MvPolynomial (Fin k) K).as_sum]
  refine Finset.sum_congr rfl fun g hg => ?_
  rw [Submodule.coe_smul, mono_val, if_pos (degree_of_coeff_ne F (MvPolynomial.mem_support_iff.1 hg)),
    smul_monomial, smul_eq_mul, mul_one]

lemma prodFact_fintype (g : Fin k →₀ ℕ) :
    g.prod (fun _ n => (n.factorial : K)) = ∏ i, ((g i).factorial : K) := by
  exact Finsupp.prod_fintype _ _ (fun _ => by simp)

lemma prodFact_ne_zero [CharZero K] (g : Fin k →₀ ℕ) :
    g.prod (fun _ n => (n.factorial : K)) ≠ 0 := by
  rw [prodFact_fintype]
  exact Finset.prod_ne_zero_iff.2 (fun i _ => Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _))

lemma invFact_ne_zero [CharZero K] (g : Fin k →₀ ℕ) : invFact K g ≠ 0 := by
  unfold invFact
  exact inv_ne_zero (prodFact_ne_zero g)

lemma prodFact_add_single (g : Fin k →₀ ℕ) (i : Fin k) :
    (g + single i 1).prod (fun _ n => (n.factorial : K)) =
      ((g i : K) + 1) * g.prod (fun _ n => (n.factorial : K)) := by
  rw [prodFact_fintype, prodFact_fintype, ← Finset.mul_prod_erase _ _ (Finset.mem_univ i),
    ← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
  have h1 : ∏ j ∈ Finset.univ.erase i, (((g + single i 1 : Fin k →₀ ℕ) j).factorial : K) =
      ∏ j ∈ Finset.univ.erase i, ((g j).factorial : K) := by
    refine Finset.prod_congr rfl fun j hj => ?_
    simp [Finsupp.single_apply, Finset.ne_of_mem_erase hj, Ne.symm (Finset.ne_of_mem_erase hj)]
  rw [h1, Finsupp.add_apply, Finsupp.single_eq_same, Nat.factorial_succ, Nat.cast_mul]
  push_cast
  ring

lemma invFact_add_single [CharZero K] (g : Fin k →₀ ℕ) (i : Fin k) :
    invFact K (g + single i 1) * ((g i : K) + 1) = invFact K g := by
  unfold invFact
  rw [prodFact_add_single, mul_inv]
  have h1 : ((g i : K) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero (g i)
  rw [mul_comm ((g i : K) + 1)⁻¹ _, mul_assoc, inv_mul_cancel₀ h1, mul_one]

lemma degree_sub_add (g : Fin k →₀ ℕ) (a b : Fin k) (hb : g b ≠ 0) :
    (g - single b 1 + single a 1).degree = g.degree := by
  have hle : single b 1 ≤ g := by
    rw [Finsupp.single_le_iff]
    omega
  have hs : ∀ c : Fin k, (single c 1 : Fin k →₀ ℕ).degree = 1 := fun c => by
    rw [Finsupp.degree_eq_sum]
    simp [Finsupp.single_apply]
  conv_rhs => rw [← tsub_add_cancel_of_le hle]
  rw [map_add, map_add, hs, hs]

lemma Ed_val (a b : Fin k) (F : ↥(homogeneousSubmodule (Fin k) K d)) :
    (Formalism.MainNotions.TestSideCounting.Ed K k d a b F : MvPolynomial (Fin k) K) = X a * pderiv b (F : MvPolynomial (Fin k) K) :=
  rfl

lemma Ed_mono (a b : Fin k) (g : Fin k →₀ ℕ) :
    Formalism.MainNotions.TestSideCounting.Ed K k d a b (mono K k d g) =
      ((g b : ℕ) : K) • mono K k d (g - single b 1 + single a 1) := by
  apply Subtype.ext
  rw [Ed_val, Submodule.coe_smul, mono_val, mono_val]
  by_cases hb : g b = 0
  · split_ifs <;> simp [pderiv_monomial, hb]
  · rw [degree_sub_add g a b hb]
    split_ifs with h
    · rw [pderiv_monomial, X, monomial_mul, smul_monomial, add_comm (Finsupp.single a 1)]
      simp
    · simp

lemma pderiv_inl_xi (b : Fin k) (g : Fin k →₀ ℕ) :
    pderiv (Sum.inl b) (monomial (g.mapDomain Sum.inr) (1 : K) : Pol K k) = 0 := by
  simp [pderiv_monomial, Finsupp.mapDomain_notin_range]

lemma weight_wx (m g : Fin k →₀ ℕ) : Finsupp.weight (wx k) (Finsupp.sumElim m g) = m.degree := by
  simp [Finsupp.weight_apply, Finsupp.sum_fintype, wx, Fintype.sum_sum_type, Finsupp.degree_eq_sum]

lemma weight_wxi (m g : Fin k →₀ ℕ) : Finsupp.weight (wxi k) (Finsupp.sumElim m g) = g.degree := by
  simp [Finsupp.weight_apply, Finsupp.sum_fintype, wxi, Fintype.sum_sum_type, Finsupp.degree_eq_sum]

end PI.OpWords
