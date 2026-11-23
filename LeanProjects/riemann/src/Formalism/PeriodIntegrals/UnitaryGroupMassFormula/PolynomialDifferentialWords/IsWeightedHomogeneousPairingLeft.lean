import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PolynomialDifferentialWords.KappaRight

open MvPolynomial

noncomputable section

namespace PI.OpWords.WeightedHomogeneousPolynomialDifferentialWords

variable {K : Type} [Field K] [CharZero K] {k : ℕ}

theorem homog_of_mul {σ : Type} (w : σ → ℕ) {s g : MvPolynomial σ K} {n : ℕ}
    (hs : IsWeightedHomogeneous w s 1) (hs0 : s ≠ 0)
    (h : IsWeightedHomogeneous w (s * g) (1 + n)) : IsWeightedHomogeneous w g n := by
  classical
  have hA : ∀ j, weightedHomogeneousComponent w (1 + j) (s * g) = s * weightedHomogeneousComponent w j g := by
    intro j
    ext d
    rw [coeff_weightedHomogeneousComponent, coeff_mul, coeff_mul]
    split_ifs with hd
    · refine Finset.sum_congr rfl fun x hx => ?_
      rw [coeff_weightedHomogeneousComponent]
      by_cases h0 : coeff x.1 s = 0
      · simp [h0]
      · have hx0 := hs h0
        have hsum : x.1 + x.2 = d := by simpa using hx
        have hw : Finsupp.weight w x.2 = j := by
          rw [← hsum, map_add, hx0] at hd
          omega
        rw [if_pos hw]
    · symm
      refine Finset.sum_eq_zero fun x hx => ?_
      rw [coeff_weightedHomogeneousComponent]
      by_cases h0 : coeff x.1 s = 0
      · simp [h0]
      · have hx0 := hs h0
        have hsum : x.1 + x.2 = d := by simpa using hx
        have hw : Finsupp.weight w x.2 ≠ j := by
          rw [← hsum, map_add, hx0] at hd
          omega
        rw [if_neg hw, mul_zero]
  intro m hm
  by_contra hne
  have hc : weightedHomogeneousComponent w (Finsupp.weight w m) g ≠ 0 := by
    intro h0
    have h3 := congrArg (coeff m) h0
    rw [coeff_weightedHomogeneousComponent, if_pos rfl, coeff_zero] at h3
    exact hm h3
  apply hc
  have h4 : s * weightedHomogeneousComponent w (Finsupp.weight w m) g = 0 := by
    rw [← hA]
    ext d
    rw [coeff_weightedHomogeneousComponent, coeff_zero]
    split_ifs with hd
    · by_contra hne2
      have h5 := h hne2
      omega
    · rfl
  exact (mul_eq_zero.1 h4).resolve_left hs0

theorem isWeightedHomogeneous_pairing_left : IsWeightedHomogeneous (wx k) (tt K k) 1 := by
  show IsWeightedHomogeneous (wx k) (∑ i, X (Sum.inl i) * X (Sum.inr i) : Pol K k) 1
  apply IsWeightedHomogeneous.sum
  intro i _
  have h := (isWeightedHomogeneous_X K (wx k) (Sum.inl i)).mul
    (isWeightedHomogeneous_X K (wx k) (Sum.inr i))
  simpa [wx] using h

theorem tt_homog_xi : IsWeightedHomogeneous (wxi k) (tt K k) 1 := by
  show IsWeightedHomogeneous (wxi k) (∑ i, X (Sum.inl i) * X (Sum.inr i) : Pol K k) 1
  apply IsWeightedHomogeneous.sum
  intro i _
  have h := (isWeightedHomogeneous_X K (wxi k) (Sum.inl i)).mul
    (isWeightedHomogeneous_X K (wxi k) (Sum.inr i))
  simpa [wxi] using h

theorem eval_tt (p : Fin k ⊕ Fin k → K) :
    eval p (tt K k) = ∑ i, p (Sum.inl i) * p (Sum.inr i) := by
  simp [tt]

theorem tt_ne_zero (hk : 1 ≤ k) : tt K k ≠ 0 := by
  intro h
  have h1 := congrArg (eval (fun _ : Fin k ⊕ Fin k => (1 : K))) h
  rw [eval_tt] at h1
  simp at h1
  omega

theorem not_X_dvd_tt (i0 j : Fin k) (hj : j ≠ i0) :
    ¬ (X (Sum.inl i0) : Pol K k) ∣ tt K k := by
  rintro ⟨q, hq⟩
  have h := congrArg (eval (Sum.elim (fun i : Fin k => if i = j then (1 : K) else 0) (fun _ => 1))) hq
  rw [eval_tt] at h
  simp [Ne.symm hj] at h

theorem dvd_of_dvd_X_pow {i : Fin k ⊕ Fin k} {s f : Pol K k} (hs : ¬ (X i : Pol K k) ∣ s) :
    ∀ n : ℕ, s ∣ X i ^ n * f → s ∣ f
  | 0, h => by simpa using h
  | n + 1, h => by
    rw [pow_succ', mul_assoc] at h
    rcases dvd_X_mul_iff.1 h with h' | ⟨h', _⟩
    · exact dvd_of_dvd_X_pow hs n h'
    · exact absurd h' hs

variable (K) in

def chiF (i0 : Fin k) : Fin k ⊕ Fin k → Pol K k :=
  Sum.elim (fun j => X (Sum.inl j)) (fun j => X (Sum.inl i0) * X (Sum.inr j))

variable (K) in

def tp (i0 : Fin k) : Pol K k := ∑ j ∈ Finset.univ.erase i0, X (Sum.inl j) * X (Sum.inr j)

variable (K) in

def psiF (i0 : Fin k) : Fin k ⊕ Fin k → Pol K k :=
  Sum.elim (fun j => X (Sum.inl j))
    (fun j => if j = i0 then - tp K i0 else X (Sum.inl i0) * X (Sum.inr j))

theorem chiF_eq (i0 : Fin k) (v : Fin k ⊕ Fin k) :
    (chiF K i0 v : Pol K k) = X v * X (Sum.inl i0) ^ (wxi k v) := by
  rcases v with j | j <;> simp [chiF, wxi, mul_comm]

theorem chi_monomial (i0 : Fin k) (m : Fin k ⊕ Fin k →₀ ℕ) (c : K) :
    aeval (chiF K i0) (monomial m c : Pol K k) =
      X (Sum.inl i0) ^ (Finsupp.weight (wxi k) m) * monomial m c := by
  rw [aeval_monomial, monomial_eq, Finsupp.weight_apply, algebraMap_eq]
  simp only [chiF_eq, mul_pow, Finsupp.prod_mul, ← pow_mul']
  simp only [Finsupp.prod, Finsupp.sum, Finset.prod_pow_eq_pow_sum, smul_eq_mul]
  ring

theorem chi_eq (i0 : Fin k) (d : ℕ) (f : Pol K k) (hf : IsWeightedHomogeneous (wxi k) f d) :
    aeval (chiF K i0) f = X (Sum.inl i0) ^ d * f := by
  conv_lhs => rw [f.as_sum]
  conv_rhs => rw [f.as_sum]
  rw [map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [chi_monomial, hf (mem_support_iff.1 hm)]

theorem chi_psi_dvd (i0 : Fin k) (f : Pol K k) :
    tt K k ∣ aeval (chiF K i0) f - aeval (psiF K i0) f := by
  rw [← Ideal.mem_span_singleton, ← Ideal.Quotient.eq]
  have key : (Ideal.Quotient.mkₐ K (Ideal.span {tt K k})).comp (aeval (chiF K i0)) =
      (Ideal.Quotient.mkₐ K (Ideal.span {tt K k})).comp (aeval (psiF K i0)) := by
    ext v
    simp only [AlgHom.comp_apply, aeval_X, Ideal.Quotient.mkₐ_eq_mk]
    rw [Ideal.Quotient.eq, Ideal.mem_span_singleton]
    rcases v with j | j
    · simp [chiF, psiF]
    · by_cases hj : j = i0
      · subst hj
        simp only [chiF, psiF, Sum.elim_inr, if_true, eq_self_iff_true]
        have e : X (Sum.inl j) * X (Sum.inr j) - -tp K j = tt K k := by
          rw [sub_neg_eq_add, tp, tt, ← Finset.add_sum_erase _ _ (Finset.mem_univ j)]
        rw [e]
      · simp [chiF, psiF, hj]
  exact AlgHom.congr_fun key f

theorem eval_aeval' (g : Fin k ⊕ Fin k → Pol K k) (p : Fin k ⊕ Fin k → K) (f : Pol K k) :
    eval p (aeval g f) = eval (fun v => eval p (g v)) f := by
  induction f using MvPolynomial.induction_on <;> simp_all

theorem psi_zero (i0 : Fin k) (f : Pol K k)
    (hv : ∀ p : Fin k ⊕ Fin k → K, ∑ i, p (Sum.inl i) * p (Sum.inr i) = 0 → eval p f = 0) :
    aeval (psiF K i0) f = 0 := by
  haveI : Infinite K := Infinite.of_injective (Nat.cast : ℕ → K) Nat.cast_injective
  apply MvPolynomial.funext
  intro p
  rw [eval_aeval', map_zero]
  apply hv
  have key : ∀ i, eval p (psiF K i0 (Sum.inr i)) =
      if i = i0 then -(∑ j ∈ Finset.univ.erase i0, p (Sum.inl j) * p (Sum.inr j))
      else p (Sum.inl i0) * p (Sum.inr i) := by
    intro i
    by_cases h : i = i0
    · subst h
      simp [psiF, tp]
    · simp [psiF, h]
  have key2 : ∀ i, eval p (psiF K i0 (Sum.inl i)) = p (Sum.inl i) := by
    intro i
    simp [psiF]
  simp only [key, key2]
  have h3 : ∑ i ∈ Finset.univ.erase i0, p (Sum.inl i) *
      (if i = i0 then -(∑ j ∈ Finset.univ.erase i0, p (Sum.inl j) * p (Sum.inr j))
        else p (Sum.inl i0) * p (Sum.inr i))
      = p (Sum.inl i0) * ∑ j ∈ Finset.univ.erase i0, p (Sum.inl j) * p (Sum.inr j) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [if_neg (Finset.ne_of_mem_erase hi)]
    ring
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i0), h3, if_pos rfl]
  ring

theorem dvd_pow_mul (i0 : Fin k) (d : ℕ) (f : Pol K k) (hf : f ∈ Bihom K k d)
    (hv : ∀ p : Fin k ⊕ Fin k → K, ∑ i, p (Sum.inl i) * p (Sum.inr i) = 0 → eval p f = 0) :
    tt K k ∣ X (Sum.inl i0) ^ d * f := by
  have hf' : f ∈ weightedHomogeneousSubmodule K (wx k) d ⊓ weightedHomogeneousSubmodule K (wxi k) d := hf
  have hfxi : IsWeightedHomogeneous (wxi k) f d := by
    have h2 := (Submodule.mem_inf.1 hf').2
    rwa [mem_weightedHomogeneousSubmodule] at h2
  have h := chi_psi_dvd i0 f
  rw [psi_zero i0 f hv, sub_zero, chi_eq i0 d f hfxi] at h
  exact h

theorem divT_one (d : ℕ) (hd : 1 ≤ d) (f : Pol K 1) (hf : f ∈ Bihom K 1 d) : tt K 1 ∣ f := by
  have hf' : f ∈ weightedHomogeneousSubmodule K (wx 1) d ⊓ weightedHomogeneousSubmodule K (wxi 1) d := hf
  have hx := (Submodule.mem_inf.1 hf').1
  have hxi := (Submodule.mem_inf.1 hf').2
  rw [mem_weightedHomogeneousSubmodule] at hx hxi
  obtain ⟨s, hs⟩ : ∃ s : Fin 1 ⊕ Fin 1 →₀ ℕ,
      s = Finsupp.single (Sum.inl 0) 1 + Finsupp.single (Sum.inr 0) 1 := ⟨_, rfl⟩
  rw [f.as_sum]
  refine Finset.dvd_sum fun m hm => ?_
  have h1 := hx (mem_support_iff.1 hm)
  have h2 := hxi (mem_support_iff.1 hm)
  simp [Finsupp.weight_apply, Finsupp.sum_fintype, wx, wxi, Fintype.sum_sum_type] at h1 h2
  have hsm : s ≤ m := by
    rw [hs, Finsupp.le_def]
    intro v
    rcases v with i | i <;> obtain rfl := Subsingleton.elim i 0 <;> simp <;> omega
  have key : monomial m (coeff m f) = tt K 1 * monomial (m - s) (coeff m f) := by
    simp only [tt, Fin.sum_univ_one, X, monomial_mul, one_mul]
    rw [← hs, add_tsub_cancel_of_le hsm]
  rw [key]
  exact dvd_mul_right _ _

theorem divT : PI.OpWords.DivT := by
  intro K _ _ k d hd f hf hv
  have hf' : f ∈ weightedHomogeneousSubmodule K (wx k) d ⊓ weightedHomogeneousSubmodule K (wxi k) d := hf
  have hfx : IsWeightedHomogeneous (wx k) f d := by
    have h1 := (Submodule.mem_inf.1 hf').1
    rwa [mem_weightedHomogeneousSubmodule] at h1
  have hfxi : IsWeightedHomogeneous (wxi k) f d := by
    have h2 := (Submodule.mem_inf.1 hf').2
    rwa [mem_weightedHomogeneousSubmodule] at h2
  rcases Nat.eq_zero_or_pos k with hk0 | hk1
  · subst hk0
    refine ⟨0, Submodule.zero_mem _, ?_⟩
    rw [mul_zero]
    ext m
    rw [coeff_zero]
    by_contra h
    have h1 := hfx h
    have h2 : m = 0 := by
      ext v
      rcases v with i | i <;> exact i.elim0
    rw [h2, map_zero] at h1
    omega
  · have hdvd : tt K k ∣ f := by
      rcases Nat.lt_or_ge k 2 with hk | hk
      · obtain rfl : k = 1 := by omega
        exact divT_one d hd f hf
      · exact dvd_of_dvd_X_pow (not_X_dvd_tt (⟨0, by omega⟩ : Fin k) ⟨1, by omega⟩
          (by simp [Fin.ext_iff])) d (dvd_pow_mul _ d f hf hv)
    obtain ⟨g, rfl⟩ := hdvd
    have e : 1 + (d - 1) = d := by omega
    refine ⟨g, Submodule.mem_inf.2 ⟨?_, ?_⟩, rfl⟩
    · rw [mem_weightedHomogeneousSubmodule]
      exact homog_of_mul (wx k) isWeightedHomogeneous_pairing_left (tt_ne_zero hk1) (by rw [e]; exact hfx)
    · rw [mem_weightedHomogeneousSubmodule]
      exact homog_of_mul (wxi k) tt_homog_xi (tt_ne_zero hk1) (by rw [e]; exact hfxi)

end PI.OpWords.WeightedHomogeneousPolynomialDifferentialWords

theorem PI.OpWords.pairingDivisibility : PI.OpWords.DivT := PI.OpWords.WeightedHomogeneousPolynomialDifferentialWords.divT
