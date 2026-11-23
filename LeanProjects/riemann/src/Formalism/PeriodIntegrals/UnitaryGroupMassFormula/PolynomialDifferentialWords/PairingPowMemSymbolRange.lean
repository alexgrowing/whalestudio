import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PolynomialDifferentialWords.PolarizationBihomogeneous
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PolynomialDifferentialWords.KappaMain

open MvPolynomial Finsupp

noncomputable section

namespace PI.OpWords

variable (K : Type) [Field K] [CharZero K] (k d : ℕ)

def Sc (c : ℕ) : Submodule K (Pol K k) :=
  ((Wc K k d c).map (kappa K k d)).comap (LinearMap.mulLeft K (tt K k ^ (d - c)))

theorem mem_Sc (c : ℕ) (g : Pol K k) :
    g ∈ Sc K k d c ↔ tt K k ^ (d - c) * g ∈ (Wc K k d c).map (kappa K k d) := Iff.rfl

theorem Wc_mono {c c' : ℕ} (h : c ≤ c') : Wc K k d c ≤ Wc K k d c' := by
  unfold Wc
  apply Submodule.span_mono
  rintro Bx ⟨l, hl, rfl⟩
  exact ⟨l, le_trans hl h, rfl⟩

theorem Ed_mul_Wc (c : ℕ) (a b : Fin k) {B : Module.End K ↥(homogeneousSubmodule (Fin k) K d)}
    (hB : B ∈ Wc K k d c) : Formalism.MainNotions.TestSideCounting.Ed K k d a b * B ∈ Wc K k d (c + 1) := by
  unfold Wc at hB ⊢
  induction hB using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨l, hl, rfl⟩ := hx
    apply Submodule.subset_span
    exact ⟨(a, b) :: l, by simpa using hl, by simp [Formalism.MainNotions.TestSideCounting.EdWord]⟩
  | zero => simp
  | add x y _ _ hx hy =>
    rw [mul_add]
    exact Submodule.add_mem _ hx hy
  | smul r x _ hx =>
    rw [mul_smul_comm]
    exact Submodule.smul_mem _ r hx

theorem wtXSum (m : Fin k ⊕ Fin k →₀ ℕ) : weight (wx k) m = ∑ i, m (Sum.inl i) := by
  simp [Finsupp.weight_apply, Finsupp.sum_fintype, wx, Fintype.sum_sum_type]

theorem wtXiSum (m : Fin k ⊕ Fin k →₀ ℕ) : weight (wxi k) m = ∑ i, m (Sum.inr i) := by
  simp [Finsupp.weight_apply, Finsupp.sum_fintype, wxi, Fintype.sum_sum_type]

theorem bihom_zero_const (g : Pol K k) (hg : g ∈ Bihom K k 0) : ∃ r : K, g = C r := by
  have hg' : g ∈ weightedHomogeneousSubmodule K (wx k) 0 ⊓ weightedHomogeneousSubmodule K (wxi k) 0 := hg
  obtain ⟨h1, h2⟩ := Submodule.mem_inf.1 hg'
  rw [mem_weightedHomogeneousSubmodule] at h1 h2
  refine ⟨coeff 0 g, ?_⟩
  ext m
  rw [coeff_C]
  split_ifs with hm
  · rw [← hm]
  · by_contra hne
    apply hm
    have e1 := h1 hne
    have e2 := h2 hne
    rw [wtXSum] at e1
    rw [wtXiSum] at e2
    ext v
    rcases v with i | i
    · have h3 := (Finset.sum_eq_zero_iff.1 e1) i (Finset.mem_univ i)
      simp [h3]
    · have h3 := (Finset.sum_eq_zero_iff.1 e2) i (Finset.mem_univ i)
      simp [h3]

theorem bihom_le_Sc : ∀ c, c ≤ d → Bihom K k c ≤ Sc K k d c
  | 0, _ => by
    intro g hg
    obtain ⟨r, rfl⟩ := bihom_zero_const K k g hg
    rw [mem_Sc]
    refine ⟨(r * (d.factorial : K)) • 1, Submodule.smul_mem _ _
      (Submodule.subset_span ⟨[], by simp, by simp [Formalism.MainNotions.TestSideCounting.EdWord]⟩), ?_⟩
    rw [map_smul, symbolMapOne, smul_smul, mul_assoc,
      mul_inv_cancel₀ (Nat.cast_ne_zero.2 (Nat.factorial_ne_zero d)), mul_one, Nat.sub_zero,
      smul_eq_C_mul, mul_comm]
  | c + 1, hc => by
    have IH := bihom_le_Sc c (by omega)
    obtain ⟨n, hn⟩ : ∃ n, d - c = n + 1 := ⟨d - c - 1, by omega⟩
    have hn2 : d - (c + 1) = n := by omega
    intro g hg
    have hg' := hg
    rw [Bihom, Submodule.mem_inf, mem_weightedHomogeneousSubmodule,
      mem_weightedHomogeneousSubmodule] at hg'
    rw [as_sum g]
    apply Submodule.sum_mem
    intro m hmS
    have hne : coeff m g ≠ 0 := MvPolynomial.mem_support_iff.1 hmS
    have hw1 := hg'.1 hne
    have hw2 := hg'.2 hne
    rw [show monomial m (coeff m g) = coeff m g • monomial m (1 : K) by rw [smul_monomial, smul_eq_mul, mul_one]]
    apply Submodule.smul_mem

    rw [wtXSum] at hw1
    rw [wtXiSum] at hw2
    obtain ⟨a, -, ha⟩ := Finset.exists_ne_zero_of_sum_ne_zero (by rw [hw1]; omega)
    obtain ⟨b, -, hb⟩ := Finset.exists_ne_zero_of_sum_ne_zero (by rw [hw2]; omega)
    obtain ⟨m', rfl⟩ : ∃ m' : Fin k ⊕ Fin k →₀ ℕ,
        m = m' + single (Sum.inl a) 1 + single (Sum.inr b) 1 := by
      refine ⟨m - single (Sum.inl a) 1 - single (Sum.inr b) 1, ?_⟩
      ext i
      rcases i with i | i
      · simp only [Finsupp.coe_add, Finsupp.coe_tsub, Pi.add_apply, Pi.sub_apply, single_apply,
          Sum.inl.injEq, reduceCtorEq, if_false]
        split_ifs with h
        · subst h; omega
        · omega
      · simp only [Finsupp.coe_add, Finsupp.coe_tsub, Pi.add_apply, Pi.sub_apply, single_apply,
          Sum.inr.injEq, reduceCtorEq, if_false]
        split_ifs with h
        · subst h; omega
        · omega
    have hmono : X (Sum.inl a) * X (Sum.inr b) * monomial m' (1 : K) =
        monomial (m' + single (Sum.inl a) 1 + single (Sum.inr b) 1) 1 := by
      simp only [X, monomial_mul, one_mul]
      congr 1
      abel
    have hw1' : weight (wx k) m' = c := by
      have := hw1
      rw [← wtXSum, map_add, map_add, weight_single, weight_single] at this
      have e1 : wx k (Sum.inl a) = 1 := rfl
      have e2 : wx k (Sum.inr b) = 0 := rfl
      rw [e1, e2, smul_eq_mul, smul_eq_mul] at this
      omega
    have hw2' : weight (wxi k) m' = c := by
      have := hw2
      rw [← wtXiSum, map_add, map_add, weight_single, weight_single] at this
      have e1 : wxi k (Sum.inl a) = 0 := rfl
      have e2 : wxi k (Sum.inr b) = 1 := rfl
      rw [e1, e2, smul_eq_mul, smul_eq_mul] at this
      omega
    have hh : monomial m' (1 : K) ∈ Bihom K k c := by
      rw [Bihom, Submodule.mem_inf, mem_weightedHomogeneousSubmodule,
        mem_weightedHomogeneousSubmodule]
      exact ⟨isWeightedHomogeneous_monomial _ _ _ hw1', isWeightedHomogeneous_monomial _ _ _ hw2'⟩
    have hh' : X (Sum.inl a) * pderiv (Sum.inl b) (monomial m' (1 : K)) ∈ Bihom K k c := by
      rw [Bihom, Submodule.mem_inf, mem_weightedHomogeneousSubmodule,
        mem_weightedHomogeneousSubmodule] at hh ⊢
      exact ⟨iwh_X_pderiv _ _ _ (by simp [wx]) hh.1, iwh_X_pderiv _ _ _ (by simp [wxi]) hh.2⟩
    obtain ⟨B, hB, hBk⟩ := (mem_Sc K k d c _).1 (IH hh)
    obtain ⟨B', hB', hB'k⟩ := (mem_Sc K k d c _).1 (IH hh')
    rw [hn] at hBk hB'k
    rw [mem_Sc, hn2, ← hmono]
    refine ⟨(((n + 1 : ℕ) : K)⁻¹) • (Formalism.MainNotions.TestSideCounting.Ed K k d a b * B - B'),
      Submodule.smul_mem _ _ (Submodule.sub_mem _ (Ed_mul_Wc K k d c a b hB)
        (Wc_mono K k d (Nat.le_succ c) hB')), ?_⟩
    rw [map_smul, map_sub, symbolMapMulLeft, hBk, hB'k, Derivation.leibniz, Derivation.leibniz_pow,
      pderiv_inl_tt, Nat.add_sub_cancel, smul_eq_C_mul]
    simp only [smul_eq_mul, nsmul_eq_mul]
    have hC : (C (((n + 1 : ℕ) : K)⁻¹) : Pol K k) * ((n + 1 : ℕ) : Pol K k) = 1 := by
      rw [← map_natCast (C : K →+* Pol K k), ← map_mul,
        inv_mul_cancel₀ (Nat.cast_ne_zero.2 (Nat.succ_ne_zero n)), map_one]
    linear_combination (tt K k ^ n * (X (Sum.inl a) * X (Sum.inr b) * monomial m' (1 : K))) * hC

theorem pairingPowMemSymbolRange : Surj := by
  intro K _ _ k d c hc g hg
  exact (mem_Sc K k d c g).1 (bihom_le_Sc K k d c hc hg)

end PI.OpWords
