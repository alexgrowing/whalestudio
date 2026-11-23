import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PolynomialDifferentialWords.KappaRight

open MvPolynomial Finsupp

noncomputable section

namespace PI.OpWords

theorem rop_apply_eq (K : Type) [Field K] (k : ℕ) (a b : Fin k) (f : Pol K k) :
    Rop K k a b f = X (Sum.inl a) * pderiv (Sum.inl b) f - X (Sum.inr b) * pderiv (Sum.inr a) f := rfl

theorem pderiv_inl_tt (K : Type) [Field K] (k : ℕ) (b : Fin k) :
    pderiv (Sum.inl b) (tt K k) = X (Sum.inr b) := by
  simp [tt, Derivation.leibniz, pderiv_X, Pi.single_apply]

theorem pderiv_inr_tt (K : Type) [Field K] (k : ℕ) (a : Fin k) :
    pderiv (Sum.inr a) (tt K k) = X (Sum.inl a) := by
  simp [tt, Derivation.leibniz, pderiv_X, Pi.single_apply]

theorem rttRelation : RTT := by
  intro K _ _ k a b g
  rw [rop_apply_eq, rop_apply_eq]
  simp only [Derivation.leibniz, pderiv_inl_tt, pderiv_inr_tt, smul_eq_mul]
  ring

theorem iwh_X_pderiv {σ : Type} {K : Type} [Field K] (w : σ → ℕ) (i j : σ) (hij : w i = w j)
    {f : MvPolynomial σ K} {n : ℕ} (hf : IsWeightedHomogeneous w f n) :
    IsWeightedHomogeneous w (X i * pderiv j f) n := by
  classical
  rw [f.as_sum, map_sum, Finset.mul_sum]
  apply IsWeightedHomogeneous.sum
  intro m hm
  have hwm : weight w m = n := hf (MvPolynomial.mem_support_iff.1 hm)
  rw [pderiv_monomial]
  by_cases hmj : m j = 0
  · simp [hmj, isWeightedHomogeneous_zero]
  · have hle : Finsupp.single j 1 ≤ m := by
      rw [Finsupp.single_le_iff]
      omega
    have hs : ∀ v, weight w (Finsupp.single v 1) = w v := by
      intro v
      simp [Finsupp.weight_apply, Finsupp.sum_single_index]
    have h1 : weight w (m - Finsupp.single j 1) + w j = n := by
      rw [← hs j, ← map_add, tsub_add_cancel_of_le hle, hwm]
    rw [X, monomial_mul, one_mul]
    apply isWeightedHomogeneous_monomial
    rw [map_add, hs i, hij, add_comm, h1]

theorem polarizationBihomogeneous : RBihom := by
  intro K _ _ k d a b f hf
  have hf' : f ∈ weightedHomogeneousSubmodule K (wx k) d ⊓ weightedHomogeneousSubmodule K (wxi k) d := hf
  obtain ⟨h1, h2⟩ := Submodule.mem_inf.1 hf'
  rw [mem_weightedHomogeneousSubmodule] at h1 h2
  show Rop K k a b f ∈ weightedHomogeneousSubmodule K (wx k) d ⊓ weightedHomogeneousSubmodule K (wxi k) d
  rw [rop_apply_eq]
  refine Submodule.mem_inf.2 ⟨Submodule.sub_mem _ ?_ ?_, Submodule.sub_mem _ ?_ ?_⟩ <;>
    rw [mem_weightedHomogeneousSubmodule]
  · exact iwh_X_pderiv _ _ _ (by simp [wx]) h1
  · exact iwh_X_pderiv _ _ _ (by simp [wx]) h1
  · exact iwh_X_pderiv _ _ _ (by simp [wxi]) h2
  · exact iwh_X_pderiv _ _ _ (by simp [wxi]) h2

theorem coeff_X_pderiv_self {σ : Type} {K : Type} [Field K] (i : σ) (f : MvPolynomial σ K)
    (m : σ →₀ ℕ) : coeff m (X i * pderiv i f) = coeff m f * (m i : K) := by
  classical
  induction f using MvPolynomial.induction_on'
  next u a =>
    rw [pderiv_monomial]
    by_cases hu : u i = 0
    · by_cases h : u = m
      · subst h
        simp [hu]
      · simp [hu, coeff_monomial, h]
    · have hle : Finsupp.single i 1 ≤ u := by
        rw [Finsupp.single_le_iff]
        omega
      rw [X, monomial_mul, one_mul, add_tsub_cancel_of_le hle, coeff_monomial, coeff_monomial]
      split_ifs with h
      · subst h
        rfl
      · simp
  next p q hp hq =>
    simp only [map_add, mul_add, coeff_add, hp, hq, add_mul]

theorem weightOfEigenvector : WtOfEig := by
  intro K _ _ k a w f h m hm
  have h1 := congrArg (coeff m) h
  rw [rop_apply_eq, coeff_sub, coeff_X_pderiv_self, coeff_X_pderiv_self, coeff_smul] at h1
  have hc : coeff m f ≠ 0 := MvPolynomial.mem_support_iff.1 hm
  have h2 : (((m (Sum.inl a) : ℤ) - m (Sum.inr a) : ℤ) : K) = (w : K) := by
    apply mul_left_cancel₀ hc
    push_cast
    linear_combination h1
  exact_mod_cast h2

def va (k : ℕ) (a : Fin k) : Fin k ⊕ Fin k → ℤ :=
  Sum.elim (fun i => if i = a then 1 else 0) (fun i => if i = a then -1 else 0)

theorem weight_va (k : ℕ) (a : Fin k) (m : Fin k ⊕ Fin k →₀ ℕ) :
    weight (va k a) m = (m (Sum.inl a) : ℤ) - m (Sum.inr a) := by
  simp [Finsupp.weight_apply, Finsupp.sum_fintype, va, Fintype.sum_sum_type, sub_eq_add_neg]

theorem tt_va (K : Type) [Field K] (k : ℕ) (a : Fin k) :
    IsWeightedHomogeneous (va k a) (tt K k) 0 := by
  show IsWeightedHomogeneous (va k a) (∑ i, X (Sum.inl i) * X (Sum.inr i) : Pol K k) 0
  apply IsWeightedHomogeneous.sum
  intro i _
  have h := (isWeightedHomogeneous_X K (va k a) (Sum.inl i)).mul
    (isWeightedHomogeneous_X K (va k a) (Sum.inr i))
  by_cases hi : i = a <;> simpa [va, hi] using h

theorem comp_mul_zero {σ : Type} {K : Type} [Field K] (w : σ → ℤ) {φ : MvPolynomial σ K}
    (hφ : IsWeightedHomogeneous w φ 0) (n : ℤ) (ψ : MvPolynomial σ K) :
    weightedHomogeneousComponent w n (φ * ψ) = φ * weightedHomogeneousComponent w n ψ := by
  classical
  ext d
  rw [coeff_weightedHomogeneousComponent, coeff_mul, coeff_mul]
  split_ifs with hd
  · refine Finset.sum_congr rfl fun x hx => ?_
    rw [coeff_weightedHomogeneousComponent]
    by_cases h0 : coeff x.1 φ = 0
    · simp [h0]
    · have hx0 := hφ h0
      have hsum := by simpa using hx
      have hw : weight w x.2 = n := by
        rw [← hd, ← hsum, map_add, hx0, zero_add]
      rw [if_pos hw]
  · symm
    refine Finset.sum_eq_zero fun x hx => ?_
    rw [coeff_weightedHomogeneousComponent]
    by_cases h0 : coeff x.1 φ = 0
    · simp [h0]
    · have hx0 := hφ h0
      have hsum := by simpa using hx
      have hw : weight w x.2 ≠ n := by
        rw [← hsum, map_add, hx0, zero_add] at hd
        exact hd
      rw [if_neg hw, mul_zero]

theorem tt_ne_zero (K : Type) [Field K] [CharZero K] (k : ℕ) (hk : 0 < k) : tt K k ≠ 0 := by
  intro h
  have h1 := congrArg (eval (fun _ : Fin k ⊕ Fin k => (1 : K))) h
  simp [tt] at h1
  omega

theorem pairingWeightCancel : TTWt := by
  intro K _ _ k c g h m hm a
  by_contra hlt
  push_neg at hlt
  obtain ⟨n, hn⟩ : ∃ n : ℤ, n = (m (Sum.inl a) : ℤ) - m (Sum.inr a) := ⟨_, rfl⟩
  have hwm : weight (va k a) m = n := by rw [weight_va, hn]
  have hk : 0 < k := Fin.pos a
  have hcomp : weightedHomogeneousComponent (va k a) n g ≠ 0 := by
    intro h0
    have h3 := congrArg (coeff m) h0
    rw [coeff_weightedHomogeneousComponent, if_pos hwm] at h3
    exact (MvPolynomial.mem_support_iff.1 hm) (by simpa using h3)
  have hprod : weightedHomogeneousComponent (va k a) n (tt K k * g) ≠ 0 := by
    rw [comp_mul_zero (va k a) (tt_va K k a) n g]
    exact mul_ne_zero (tt_ne_zero K k hk) hcomp
  apply hprod
  ext m'
  rw [coeff_weightedHomogeneousComponent, coeff_zero]
  split_ifs with hw
  · by_contra hne
    have h4 := h m' (MvPolynomial.mem_support_iff.2 hne) a
    rw [weight_va] at hw
    omega
  · rfl

end PI.OpWords
