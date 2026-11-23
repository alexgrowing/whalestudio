import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.HasympAll

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]

def killB (T : Finset K) : MRing ι →ₐ[ℤ] MRing ι :=
  aeval (fun p => if p.1 ∈ T then 0 else X p)

theorem killB_X (T : Finset K) (p : Σ k, ι k) :
    killB T (X p : MRing ι) = if p.1 ∈ T then 0 else X p := by
  unfold killB
  rw [MvPolynomial.aeval_X]

open Classical in
theorem killB_monomial (T : Finset K) (m : (Σ k, ι k) →₀ ℕ) (c : ℤ) :
    killB T (monomial m c : MRing ι) = if (∃ p, p.1 ∈ T ∧ m p ≠ 0) then 0 else monomial m c := by
  unfold killB
  rw [MvPolynomial.aeval_monomial]
  split_ifs with h
  · obtain ⟨p, hpT, hp⟩ := h
    apply mul_eq_zero_of_right
    rw [Finsupp.prod]
    apply Finset.prod_eq_zero (Finsupp.mem_support_iff.mpr hp)
    simp [hpT, hp]
  · push_neg at h
    rw [Finsupp.prod]
    have hc : ∀ p ∈ m.support, (if p.1 ∈ T then (0 : MRing ι) else X p) ^ m p = X p ^ m p := by
      intro p hp
      rw [if_neg]
      intro hT
      exact (Finsupp.mem_support_iff.mp hp) (h p hT)
    rw [Finset.prod_congr rfl hc, ← Finsupp.prod, MvPolynomial.monomial_eq, MvPolynomial.algebraMap_eq]

theorem killB_multiHomog (T : Finset K) {s : MRing ι} {c : K → ℕ} (hs : IsMultiHomog s c) :
    killB T s = 0 ∨ killB T s = s := by
  classical
  by_cases hT : ∃ k ∈ T, c k ≠ 0
  · left
    obtain ⟨k, hkT, hck⟩ := hT
    rw [s.as_sum, map_sum]
    apply Finset.sum_eq_zero
    intro m hm
    have h := hs m hm k
    rw [← h] at hck
    obtain ⟨i, -, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero hck
    rw [killB_monomial, if_pos ⟨⟨k, i⟩, hkT, hi⟩]
  · right
    push_neg at hT
    have key : ∀ m ∈ s.support, killB T (monomial m (coeff m s)) = monomial m (coeff m s) := by
      intro m hm
      rw [killB_monomial, if_neg]
      rintro ⟨p, hpT, hp⟩
      have h := hs m hm p.1
      rw [hT p.1 hpT] at h
      exact hp ((Finset.sum_eq_zero_iff.mp h) p.2 (Finset.mem_univ _))
    calc killB T s = killB T (∑ m ∈ s.support, monomial m (coeff m s)) := by rw [← s.as_sum]
      _ = ∑ m ∈ s.support, killB T (monomial m (coeff m s)) := map_sum _ _ _
      _ = ∑ m ∈ s.support, monomial m (coeff m s) := Finset.sum_congr rfl key
      _ = s := s.as_sum.symm

theorem le_comap_killB {P : Ideal (MRing ι)} (hP : IsMultiHomogIdeal P) (T : Finset K) :
    P ≤ P.comap (killB T) := by
  obtain ⟨S, hS, rfl⟩ := hP
  rw [Ideal.span_le]
  intro f hf
  obtain ⟨a, ha⟩ := hS f hf
  rw [SetLike.mem_coe, Ideal.mem_comap]
  rcases killB_multiHomog T ha with h | h
  · rw [h]; exact Ideal.zero_mem _
  · rw [h]; exact Ideal.subset_span hf

theorem killB_comp {T T' : Finset K} (h : T ⊆ T') :
    (killB T' : MRing ι →ₐ[ℤ] MRing ι).comp (killB T) = killB T' := by
  apply MvPolynomial.algHom_ext
  intro p
  rw [AlgHom.comp_apply, killB_X]
  split_ifs with hp
  · rw [map_zero, killB_X, if_pos (h hp)]
  · rfl

theorem comap_killB_mono {P : Ideal (MRing ι)} (hP : IsMultiHomogIdeal P) {T T' : Finset K}
    (h : T ⊆ T') : P.comap (killB T) ≤ P.comap (killB T') := by
  intro x hx
  rw [Ideal.mem_comap] at hx ⊢
  rw [← killB_comp h, AlgHom.comp_apply]
  exact Ideal.mem_comap.mp (le_comap_killB hP T' hx)

theorem card_le_dim {P : Ideal (MRing ι)} (hPp : P.IsPrime) (hPm : IsMultiHomogIdeal P)
    (hrel : IsRelevant P) : ((Fintype.card K : ℕ) : WithBot ℕ∞) ≤ ringKrullDim (MRing ι ⧸ P) := by
  classical
  haveI := hPp
  let T : ℕ → Finset K := fun j => Finset.univ.filter fun k => ((Fintype.equivFin K k : ℕ) < j)
  let Q : ℕ → Ideal (MRing ι) := fun j => P.comap (killB (T j))
  have hQp : ∀ j, (Q j).IsPrime := fun j => Ideal.comap_isPrime _ _
  have hPQ : ∀ j, P ≤ Q j := fun j => le_comap_killB hPm (T j)
  have hT : ∀ j, T j ⊆ T (j + 1) := by
    intro j k hk
    simp only [T, Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
    omega
  have hlt : ∀ j < Fintype.card K, Q j < Q (j + 1) := by
    intro j hj
    refine lt_of_le_of_ne (comap_killB_mono hPm (hT j)) ?_
    intro heq
    set k := (Fintype.equivFin K).symm ⟨j, hj⟩ with hk
    have hkv : ((Fintype.equivFin K k : Fin _) : ℕ) = j := by simp [hk]
    obtain ⟨i, hi⟩ := hrel k
    have hin : k ∈ T (j + 1) := by
      simp only [T, Finset.mem_filter, Finset.mem_univ, true_and]; omega
    have hout : k ∉ T j := by
      simp only [T, Finset.mem_filter, Finset.mem_univ, true_and]; omega
    have h1 : (X ⟨k, i⟩ : MRing ι) ∈ Q (j + 1) := by
      rw [Ideal.mem_comap, killB_X, if_pos hin]
      exact P.zero_mem
    have h2 : (X ⟨k, i⟩ : MRing ι) ∉ Q j := by
      rw [Ideal.mem_comap, killB_X, if_neg hout]
      exact hi
    exact h2 (heq ▸ h1)
  let f : Fin (Fintype.card K + 1) → PrimeSpectrum.zeroLocus (P : Set (MRing ι)) :=
    fun j => ⟨⟨Q j, hQp j⟩, fun x hx => hPQ j hx⟩
  let s : LTSeries (PrimeSpectrum.zeroLocus (P : Set (MRing ι))) :=
    ⟨Fintype.card K, f, fun j => by
      first
      | exact Subtype.mk_lt_mk.mpr (PrimeSpectrum.asIdeal_lt_asIdeal.mp (hlt j j.isLt))
      | exact (hlt j j.isLt)⟩
  rw [ringKrullDim_quotient]
  exact Order.LTSeries.length_le_krullDim s

theorem not_relevant_of_dim_zero {W : Ideal (MRing ι)} [W.IsPrime] (hWm : IsMultiHomogIdeal W)
    (hd : ringKrullDim (MRing ι ⧸ W) = ((0 + Fintype.card K : ℕ) : WithBot ℕ∞))
    {s : MRing ι} {c : K → ℕ} (hs : IsMultiHomog s c) (hsW : s ∉ W) {W' : Ideal (MRing ι)}
    (hW' : W' ∈ (W ⊔ Ideal.span {s}).minimalPrimes) : ¬ IsRelevant W' := by
  classical
  intro hrel
  have hW'p : W'.IsPrime := hW'.1.1
  have hJ : IsMultiHomogIdeal (W ⊔ Ideal.span {s}) := isMultiHomogIdeal_sup_span hWm hs
  have hW'm : IsMultiHomogIdeal W' := by
    let e := Fintype.equivFin K
    letI : DecidableEq (Lex (Fin (Fintype.card K) → ℕ)) := lexDecEq (Fintype.card K)
    letI : GradedAlgebra (weightedHomogeneousSubmodule ℤ (lexW (ι := ι) e)) :=
      MvPolynomial.weightedGradedAlgebra ℤ (lexW (ι := ι) e)
    rw [← isHomogeneous_lex_iff e] at hJ ⊢
    have hcore := hW'p.homogeneousCore (𝒜 := weightedHomogeneousSubmodule ℤ (lexW (ι := ι) e))
    have hle : W ⊔ Ideal.span {s} ≤
        (W'.homogeneousCore (weightedHomogeneousSubmodule ℤ (lexW (ι := ι) e))).toIdeal := by
      rw [← hJ.toIdeal_homogeneousCore_eq_self]
      exact Ideal.homogeneousCore_mono _ hW'.1.2
    have hge := hW'.2 ⟨hcore, hle⟩ (Ideal.toIdeal_homogeneousCore_le _ _)
    have heq : (W'.homogeneousCore (weightedHomogeneousSubmodule ℤ (lexW (ι := ι) e))).toIdeal = W' :=
      le_antisymm (Ideal.toIdeal_homogeneousCore_le _ _) hge
    rw [← heq]
    exact (W'.homogeneousCore (weightedHomogeneousSubmodule ℤ (lexW (ι := ι) e))).isHomogeneous
  have h1 := card_le_dim hW'p hW'm hrel
  have hWW' : W ≤ W' := le_trans le_sup_left hW'.1.2
  have hsW' : s ∈ W' :=
    hW'.1.2 ((le_sup_right : Ideal.span {s} ≤ W ⊔ Ideal.span {s}) (Ideal.mem_span_singleton_self s))
  let g : MRing ι ⧸ W →+* MRing ι ⧸ W' := Ideal.Quotient.factor hWW'
  have hg : ∀ a ∈ Ideal.span {Ideal.Quotient.mk W s}, g a = 0 := by
    intro a ha
    obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.mp ha
    rw [map_mul]
    have : g (Ideal.Quotient.mk W s) = 0 := by
      simp only [g, Ideal.Quotient.factor_mk]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr hsW'
    rw [this, mul_zero]
  let f : (MRing ι ⧸ W) ⧸ Ideal.span {Ideal.Quotient.mk W s} →+* MRing ι ⧸ W' :=
    Ideal.Quotient.lift _ g hg
  have hf : Function.Surjective f := by
    intro y
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
    exact ⟨Ideal.Quotient.mk _ (Ideal.Quotient.mk W x), rfl⟩
  have hnz : Ideal.Quotient.mk W s ∈ nonZeroDivisors (MRing ι ⧸ W) := by
    apply mem_nonZeroDivisors_of_ne_zero
    intro h0
    exact hsW (Ideal.Quotient.eq_zero_iff_mem.mp h0)
  have h2 : ((Fintype.card K : ℕ) : WithBot ℕ∞) + 1 ≤ ((0 + Fintype.card K : ℕ) : WithBot ℕ∞) := by
    calc ((Fintype.card K : ℕ) : WithBot ℕ∞) + 1 ≤ ringKrullDim (MRing ι ⧸ W') + 1 := by
          gcongr
      _ ≤ ringKrullDim ((MRing ι ⧸ W) ⧸ Ideal.span {Ideal.Quotient.mk W s}) + 1 := by
          gcongr
          exact ringKrullDim_le_of_surjective f hf
      _ ≤ ringKrullDim (MRing ι ⧸ W) := ringKrullDim_quotient_succ_le_of_nonZeroDivisor hnz
      _ = _ := hd
  rw [zero_add] at h2
  have h3 : (((Fintype.card K + 1 : ℕ)) : WithBot ℕ∞) ≤ ((Fintype.card K : ℕ) : WithBot ℕ∞) := by
    exact_mod_cast h2
  have h4 := WithBot.coe_le_coe.mp h3
  have h5 : ((Fintype.card K + 1 : ℕ) : ℕ∞) ≤ ((Fintype.card K : ℕ) : ℕ∞) := h4
  exact absurd (Nat.cast_le.mp h5) (by omega)

end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
