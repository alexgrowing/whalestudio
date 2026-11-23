import Development.AutomorphicArithmetic.Foundations.Convolution.BlockEvaluation.TruncSpec

open MeasureTheory NumberField IsDedekindDomain MvPolynomial Filter Topology UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Ci

private theorem exists_esymm_ne {s t : Multiset ℂ} {n : ℕ} (hs : s.card = n) (ht : t.card = n) (h : s ≠ t) :
    ∃ k : Fin n, s.esymm (k + 1) ≠ t.esymm (k + 1) := by
  by_contra hc
  push Not at hc
  apply h
  have hp : (s.map fun a => Polynomial.X - Polynomial.C a).prod = (t.map fun a => Polynomial.X - Polynomial.C a).prod := by
    rw [Multiset.prod_X_sub_X_eq_sum_esymm, Multiset.prod_X_sub_X_eq_sum_esymm, hs, ht]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hj' : j < n + 1 := Finset.mem_range.mp hj
    have : s.esymm j = t.esymm j := by
      rcases j with _ | j
      · simp [Multiset.esymm]
      · exact hc ⟨j, by omega⟩
    rw [this]
  rw [← Polynomial.roots_multiset_prod_X_sub_C s, hp, Polynomial.roots_multiset_prod_X_sub_C]

private theorem one_factor (K : Type) [Field K] [NumberField K] (n : ℕ) (S : Set (Pl K))
    (Λ : (K →+* ℂ) → Multiset ℂ) (t : Pl K → Multiset ℂ) (Λ' : (K →+* ℂ) → Multiset ℂ) (t' : Pl K → Multiset ℂ)
    (h1 : ∀ τ, (Λ τ).card = n) (h2 : ∀ w ∉ S, (t w).card = n) (h3 : ∀ τ, (Λ' τ).card = n)
    (h4 : ∀ w ∉ S, (t' w).card = n) (h : ¬ (Λ = Λ' ∧ ∀ w ∉ S, t w = t' w)) :
    ∃ P : PR K n, (∀ y ∈ P.vars, y.1 ∉ S) ∧ (∀ x : ℝ, x ≠ 0 → val x Λ t P ≠ 0) ∧ ∀ x : ℝ, val x Λ' t' P = 0 := by
  classical
  by_cases hΛ : Λ = Λ'
  · have : ∃ w, w ∉ S ∧ t w ≠ t' w := by
      by_contra hc
      push Not at hc
      exact h ⟨hΛ, hc⟩
    obtain ⟨w, hw, hne⟩ := this
    obtain ⟨k, hk⟩ := exists_esymm_ne (h2 w hw) (h4 w hw) hne
    refine ⟨X (w, k) - C (C ((t' w).esymm (k + 1))), ?_, ?_, ?_⟩
    · intro y hy
      have := vars_sub_subset _ hy
      rw [vars_C, vars_X, Finset.union_empty, Finset.mem_singleton] at this
      rw [this]; exact hw
    · intro x _
      simpa [val, hval, sub_eq_zero] using hk
    · intro x
      simp [val, hval]
  · obtain ⟨τ, hne⟩ := Function.ne_iff.mp hΛ
    obtain ⟨k, hk⟩ := exists_esymm_ne (h1 τ) (h3 τ) hne
    refine ⟨C (X (some (τ, k)) - C ((Λ' τ).esymm (k + 1)) * X none), ?_, ?_, ?_⟩
    · intro y hy
      rw [vars_C] at hy
      exact absurd hy (Finset.notMem_empty _)
    · intro x hx
      have hx' : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx
      have e : val x Λ t (C (X (some (τ, k)) - C ((Λ' τ).esymm (k + 1)) * X none) : PR K n) =
          x * ((Λ τ).esymm (k + 1) - (Λ' τ).esymm (k + 1)) := by
        rw [val, eval₂Hom_C]
        simp
        ring
      rw [e]
      exact mul_ne_zero hx' (sub_ne_zero.mpr hk)
    · intro x
      rw [val, eval₂Hom_C]
      simp
      ring

theorem UpperTheory.ConvolutionTheory.Ci.sepPoly :
    SepPoly := by
  classical
  intro K _ _ n S Λ t I _ Λ' t' h1 h2 h3 h4 h
  choose P hP1 hP2 hP3 using fun i => one_factor K n S Λ t (Λ' i) (t' i) h1 h2 (h3 i) (h4 i) (h i)
  set Q : PR K n := ∏ i, P i with hQ
  refine ⟨Q, Q.vars.image Prod.fst, max Q.totalDegree (Q.support.sup fun β => (Q.coeff β).totalDegree), ?_,
    ⟨?_, le_max_left _ _, ?_⟩, ?_, ?_⟩
  · intro w hw
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hw
    obtain ⟨i, -, hi⟩ := Finset.mem_biUnion.mp (vars_prod P hy)
    exact hP1 i y hi
  · intro y hy
    exact Finset.mem_image_of_mem _ hy
  · intro β
    by_cases hβ : β ∈ Q.support
    · exact le_max_of_le_right (Finset.le_sup (f := fun β => (Q.coeff β).totalDegree) hβ)
    · rw [notMem_support_iff.mp hβ, totalDegree_zero]
      exact Nat.zero_le _
  · intro x hx
    rw [hQ, map_prod]
    exact Finset.prod_ne_zero_iff.mpr fun i _ => hP2 i x hx
  · intro i x
    rw [hQ, map_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (hP3 i x)
